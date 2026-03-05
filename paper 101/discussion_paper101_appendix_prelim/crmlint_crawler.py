"""
CRMlint Mathlib Crawler: Automated CRM Signature Analysis of Lean 4 Proofs
===========================================================================

Parses Lean 4 source files from Mathlib, extracts:
  1. Import graph (dependency structure)
  2. Theorem/lemma declarations and their proof tactics
  3. Type universe usage (Prop vs Type vs noncomputable)
  4. Classical axiom invocations

Then applies CRM heuristic classification based on:
  - Tactic signatures (classical vs constructive)
  - Import domain (Analysis vs Algebra vs NumberTheory etc.)
  - Noncomputable declarations
  - Classical.em / Classical.choice usage
  - Type structure (decidability instances, completeness axioms)

Author: Paul Chun-Kit Lee
Date: March 2026
"""

from __future__ import annotations
import os
import re
from dataclasses import dataclass, field
from enum import IntEnum
from pathlib import Path
from collections import Counter, defaultdict
import json


# =====================================================================
# 1. CRM LEVEL (imported concept from crmlint.py)
# =====================================================================

class CRMLevel(IntEnum):
    BISH  = 0
    MP    = 1
    LLPO  = 2
    WKL   = 3
    WLPO  = 4
    LPO   = 5
    CLASS = 6

    def __str__(self):
        return self.name


# =====================================================================
# 2. TACTIC AND IMPORT CLASSIFICATION
# =====================================================================

# Tactics and terms that signal classical content
CLASSICAL_INDICATORS = {
    # Direct classical axiom usage
    "Classical.em":          (CRMLevel.CLASS, "Law of excluded middle"),
    "Classical.choice":      (CRMLevel.CLASS, "Axiom of choice"),
    "Classical.byContradiction": (CRMLevel.CLASS, "Proof by contradiction (classical)"),
    "Classical.propDecidable": (CRMLevel.CLASS, "Classical decidability of all propositions"),
    "Classical.dec":         (CRMLevel.CLASS, "Classical decidability instance"),
    "Decidable.em":          (CRMLevel.CLASS, "Excluded middle via decidability"),

    # Tactics requiring classical logic
    "by_contra":             (CRMLevel.CLASS, "Proof by contradiction tactic"),
    "push_neg":              (CRMLevel.WLPO, "Negation pushing (requires decidability)"),
    "tauto":                 (CRMLevel.CLASS, "Classical tautology checker"),
    "omega":                 (CRMLevel.BISH,  "Linear arithmetic (constructive)"),
    "decide":                (CRMLevel.BISH,  "Decidable computation"),
    "norm_num":              (CRMLevel.BISH,  "Numeric normalization (constructive)"),
    "ring":                  (CRMLevel.BISH,  "Ring tactic (algebraic)"),
    "field_simp":            (CRMLevel.BISH,  "Field simplification (algebraic)"),
    "linarith":              (CRMLevel.BISH,  "Linear arithmetic"),
    "polyrith":              (CRMLevel.BISH,  "Polynomial arithmetic"),
    "simp":                  (CRMLevel.BISH,  "Simplification"),
    "exact":                 (CRMLevel.BISH,  "Exact term"),
    "apply":                 (CRMLevel.BISH,  "Apply lemma"),
    "rfl":                   (CRMLevel.BISH,  "Reflexivity"),
    "ext":                   (CRMLevel.BISH,  "Extensionality"),
    "induction":             (CRMLevel.BISH,  "Induction"),
    "cases":                 (CRMLevel.BISH,  "Case analysis (constructive if on decidable)"),
    "rcases":                (CRMLevel.BISH,  "Recursive case split"),
    "constructor":           (CRMLevel.BISH,  "Constructor"),
    "refine":                (CRMLevel.BISH,  "Refine with holes"),
    "intro":                 (CRMLevel.BISH,  "Introduction"),
    "have":                  (CRMLevel.BISH,  "Local hypothesis"),
    "let":                   (CRMLevel.BISH,  "Local definition"),
    "calc":                  (CRMLevel.BISH,  "Calculation chain"),
    "conv":                  (CRMLevel.BISH,  "Conversion"),
    "rw":                    (CRMLevel.BISH,  "Rewrite"),
    "gcongr":                (CRMLevel.BISH,  "Generalized congruence"),
    "positivity":            (CRMLevel.BISH,  "Positivity"),
    "continuity":            (CRMLevel.WLPO, "Continuity tactic (may use classical)"),
    "measurability":         (CRMLevel.CLASS, "Measurability (measure theory is classical)"),
    "fun_prop":              (CRMLevel.WLPO, "Function property dispatch"),
    "aesop":                 (CRMLevel.BISH,  "Automated search (depends on lemma db)"),
}

# Import domains and their heuristic CRM signatures
IMPORT_DOMAIN_SIGNATURES = {
    # Algebraic domains: generally BISH
    "Mathlib.Algebra":                CRMLevel.BISH,
    "Mathlib.RingTheory":             CRMLevel.BISH,
    "Mathlib.FieldTheory":            CRMLevel.BISH,
    "Mathlib.GroupTheory":            CRMLevel.BISH,
    "Mathlib.LinearAlgebra":          CRMLevel.BISH,
    "Mathlib.Data":                   CRMLevel.BISH,
    "Mathlib.Logic":                  CRMLevel.BISH,
    "Mathlib.Combinatorics":          CRMLevel.BISH,
    "Mathlib.CategoryTheory":         CRMLevel.BISH,
    "Mathlib.RepresentationTheory":   CRMLevel.BISH,

    # Topological domains: WKL (compactness)
    "Mathlib.Topology":               CRMLevel.WKL,
    "Mathlib.Order.Filter":           CRMLevel.WKL,

    # Analytic domains: CLASS
    "Mathlib.Analysis":               CRMLevel.CLASS,
    "Mathlib.MeasureTheory":          CRMLevel.CLASS,

    # Number theory: mixed, but imports alone suggest BISH core
    "Mathlib.NumberTheory":           CRMLevel.BISH,
    "Mathlib.NumberTheory.Padics":    CRMLevel.BISH,

    # Algebraic geometry: BISH core
    "Mathlib.AlgebraicGeometry":      CRMLevel.BISH,
}

# Noncomputable markers
NONCOMPUTABLE_PATTERN = re.compile(r'\bnoncomputable\b')

# Declaration patterns
THEOREM_PATTERN = re.compile(
    r'^(theorem|lemma|proposition|corollary)\s+(\w[\w\'\.]*)',
    re.MULTILINE,
)
DEF_PATTERN = re.compile(
    r'^(def|noncomputable\s+def|noncomputable\s+instance|instance)\s+(\w[\w\'\.]*)',
    re.MULTILINE,
)
IMPORT_PATTERN = re.compile(r'^(?:public\s+)?import\s+([\w\.]+)', re.MULTILINE)
OPEN_PATTERN = re.compile(r'^open\s+([\w\.]+(?:\s+[\w\.]+)*)', re.MULTILINE)

# Classical axiom patterns (in proof terms / bodies)
CLASSICAL_TERM_PATTERNS = [
    (re.compile(r'Classical\.em\b'),           CRMLevel.CLASS, "Classical.em"),
    (re.compile(r'Classical\.choice\b'),       CRMLevel.CLASS, "Classical.choice"),
    (re.compile(r'Classical\.byContradiction'), CRMLevel.CLASS, "Classical.byContradiction"),
    (re.compile(r'Classical\.propDecidable'),  CRMLevel.CLASS, "Classical.propDecidable"),
    (re.compile(r'Classical\.dec\b'),          CRMLevel.CLASS, "Classical.dec"),
    (re.compile(r'Decidable\.em\b'),           CRMLevel.CLASS, "Decidable.em"),
    (re.compile(r'not_not\b'),                 CRMLevel.CLASS, "Double negation elimination"),
    (re.compile(r'byContradiction\b'),         CRMLevel.CLASS, "byContradiction"),
    (re.compile(r'\bby_contra\b'),             CRMLevel.CLASS, "by_contra"),
    (re.compile(r'noncomputable\b'),           CRMLevel.WLPO, "noncomputable declaration"),
    (re.compile(r'CompleteLattice\b'),         CRMLevel.WKL,  "CompleteLattice (completeness)"),
    (re.compile(r'IsCompact\b'),              CRMLevel.WKL,  "IsCompact (compactness)"),
    (re.compile(r'MeasureTheory\b'),          CRMLevel.CLASS, "MeasureTheory namespace"),
    (re.compile(r'InnerProductSpace\b'),      CRMLevel.CLASS, "InnerProductSpace (Hilbert space)"),
    (re.compile(r'spectral\b'),               CRMLevel.CLASS, "Spectral theory"),
    (re.compile(r'integral\b'),               CRMLevel.CLASS, "Integration"),
    (re.compile(r'tsum\b'),                   CRMLevel.WKL,  "Infinite sum (topological)"),
    (re.compile(r'HasSum\b'),                 CRMLevel.WKL,  "HasSum (convergence)"),
    (re.compile(r'Summable\b'),              CRMLevel.WKL,  "Summable"),
]


# =====================================================================
# 3. LEAN FILE PARSER
# =====================================================================

@dataclass
class LeanDeclaration:
    """A parsed theorem/def from a Lean 4 file."""
    name: str
    kind: str              # theorem, lemma, def, instance, etc.
    line_number: int
    body: str              # the proof/definition body
    is_noncomputable: bool
    tactics_used: list[str] = field(default_factory=list)
    classical_markers: list[tuple[str, CRMLevel]] = field(default_factory=list)
    heuristic_level: CRMLevel = CRMLevel.BISH

    def __str__(self):
        nc = " [noncomputable]" if self.is_noncomputable else ""
        return f"{self.kind} {self.name}{nc}: {self.heuristic_level}"


@dataclass
class LeanFileAnalysis:
    """Complete analysis of a single Lean 4 source file."""
    filepath: str
    filename: str
    domain: str                                    # inferred domain
    imports: list[str] = field(default_factory=list)
    opens: list[str] = field(default_factory=list)
    declarations: list[LeanDeclaration] = field(default_factory=list)
    total_lines: int = 0
    noncomputable_count: int = 0
    classical_axiom_count: int = 0

    # Aggregate CRM analysis
    import_signature: CRMLevel = CRMLevel.BISH
    max_declaration_level: CRMLevel = CRMLevel.BISH
    file_signature: CRMLevel = CRMLevel.BISH

    # Tactic statistics
    tactic_counts: dict[str, int] = field(default_factory=dict)
    classical_tactic_count: int = 0
    constructive_tactic_count: int = 0


def parse_lean_file(filepath: str) -> LeanFileAnalysis:
    """Parse a Lean 4 source file and extract all structure."""
    with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
        content = f.read()

    lines = content.split('\n')
    filename = os.path.basename(filepath)

    analysis = LeanFileAnalysis(
        filepath=filepath,
        filename=filename,
        domain=_infer_domain(filename),
        total_lines=len(lines),
    )

    # Parse imports
    analysis.imports = IMPORT_PATTERN.findall(content)

    # Parse opens
    for match in OPEN_PATTERN.finditer(content):
        analysis.opens.extend(match.group(1).split())

    # Compute import signature
    analysis.import_signature = _compute_import_signature(analysis.imports)

    # Count noncomputable declarations
    analysis.noncomputable_count = len(NONCOMPUTABLE_PATTERN.findall(content))

    # Parse declarations (theorems, lemmas, defs)
    _extract_declarations(content, lines, analysis)

    # Compute file-level signature
    if analysis.declarations:
        analysis.max_declaration_level = max(d.heuristic_level for d in analysis.declarations)
    analysis.file_signature = CRMLevel(max(
        analysis.import_signature.value,
        analysis.max_declaration_level.value,
    ))

    # Aggregate tactic statistics
    tactic_counter = Counter()
    for decl in analysis.declarations:
        for t in decl.tactics_used:
            tactic_counter[t] += 1
    analysis.tactic_counts = dict(tactic_counter)

    for tactic, count in tactic_counter.items():
        level, _ = CLASSICAL_INDICATORS.get(tactic, (CRMLevel.BISH, ""))
        if level >= CRMLevel.CLASS:
            analysis.classical_tactic_count += count
        else:
            analysis.constructive_tactic_count += count

    # Count classical axiom usages
    for pattern, level, name in CLASSICAL_TERM_PATTERNS:
        matches = pattern.findall(content)
        if matches and level >= CRMLevel.CLASS:
            analysis.classical_axiom_count += len(matches)

    return analysis


def _infer_domain(filename: str) -> str:
    """Infer the mathematical domain from filename."""
    name = filename.replace('.lean', '')
    parts = name.split('_')
    if parts:
        domain_map = {
            "NumberTheory": "Number Theory",
            "RingTheory": "Algebra (Ring Theory)",
            "FieldTheory": "Algebra (Field Theory)",
            "LinearAlgebra": "Algebra (Linear)",
            "Analysis": "Analysis",
            "MeasureTheory": "Analysis (Measure Theory)",
            "Topology": "Topology",
            "AlgebraicGeometry": "Algebraic Geometry",
            "RepresentationTheory": "Representation Theory",
            "Combinatorics": "Combinatorics",
        }
        return domain_map.get(parts[0], parts[0])
    return "Unknown"


def _compute_import_signature(imports: list[str]) -> CRMLevel:
    """Compute CRM signature from imports."""
    sig = CRMLevel.BISH
    for imp in imports:
        for prefix, level in IMPORT_DOMAIN_SIGNATURES.items():
            if imp.startswith(prefix):
                sig = CRMLevel(max(sig.value, level.value))
                break
    return sig


def _extract_declarations(content: str, lines: list[str], analysis: LeanFileAnalysis):
    """Extract theorem/lemma declarations and analyze their proofs."""

    # Find all theorem/lemma positions
    for match in THEOREM_PATTERN.finditer(content):
        kind = match.group(1)
        name = match.group(2)
        start_pos = match.start()
        line_num = content[:start_pos].count('\n') + 1

        # Extract the proof body (heuristic: from := to next top-level declaration or blank line)
        body = _extract_body(content, match.end())

        is_nc = bool(re.search(r'noncomputable\s+' + re.escape(kind), 
                                content[max(0, start_pos-20):start_pos+10]))

        decl = LeanDeclaration(
            name=name,
            kind=kind,
            line_number=line_num,
            body=body,
            is_noncomputable=is_nc,
        )

        # Analyze tactics in body
        _analyze_tactics(decl)

        # Analyze classical markers in body
        _analyze_classical_markers(decl)

        # Compute heuristic level
        decl.heuristic_level = _compute_declaration_level(decl, analysis.import_signature)

        analysis.declarations.append(decl)

    # Also find def/instance declarations
    for match in DEF_PATTERN.finditer(content):
        full_kind = match.group(1)
        name = match.group(2)
        start_pos = match.start()
        line_num = content[:start_pos].count('\n') + 1

        body = _extract_body(content, match.end())
        is_nc = 'noncomputable' in full_kind

        decl = LeanDeclaration(
            name=name,
            kind=full_kind.strip(),
            line_number=line_num,
            body=body,
            is_noncomputable=is_nc,
        )

        _analyze_tactics(decl)
        _analyze_classical_markers(decl)
        decl.heuristic_level = _compute_declaration_level(decl, analysis.import_signature)

        analysis.declarations.append(decl)


def _extract_body(content: str, start: int) -> str:
    """Extract the body of a declaration (heuristic)."""
    # Find := or where
    rest = content[start:start+5000]  # limit search

    # Find the start of the body
    body_start = None
    for marker in [':= by', ':= fun', ':= calc', ':= show', ':=', 'where']:
        idx = rest.find(marker)
        if idx >= 0:
            body_start = idx + len(marker)
            break

    if body_start is None:
        return rest[:500]

    # Heuristic end: next top-level declaration or double newline
    body_rest = rest[body_start:]

    # Find end by looking for next theorem/lemma/def at column 0
    end_match = re.search(r'\n(?:theorem|lemma|def|noncomputable|instance|section|namespace|end |/-|#)', body_rest)
    if end_match:
        return body_rest[:end_match.start()].strip()

    return body_rest[:2000].strip()


def _analyze_tactics(decl: LeanDeclaration):
    """Extract tactics used in a declaration's body."""
    body = decl.body
    tactics_found = []

    for tactic in CLASSICAL_INDICATORS:
        # Match tactic as a word boundary
        pattern = r'\b' + re.escape(tactic) + r'\b'
        if re.search(pattern, body):
            tactics_found.append(tactic)

    decl.tactics_used = tactics_found


def _analyze_classical_markers(decl: LeanDeclaration):
    """Find classical axiom markers in a declaration."""
    body = decl.body
    markers = []

    for pattern, level, name in CLASSICAL_TERM_PATTERNS:
        if pattern.search(body):
            markers.append((name, level))

    decl.classical_markers = markers


def _compute_declaration_level(decl: LeanDeclaration, import_sig: CRMLevel) -> CRMLevel:
    """
    Compute the heuristic CRM level of a declaration.
    
    The level is determined by:
    1. Classical markers in the proof body (strongest signal)
    2. Tactics used (medium signal)
    3. Noncomputable flag (weak signal for WLPO)
    4. Import context (background signal)
    """
    level = CRMLevel.BISH

    # Classical markers are the strongest signal
    for name, marker_level in decl.classical_markers:
        level = CRMLevel(max(level.value, marker_level.value))

    # Tactic signatures
    for tactic in decl.tactics_used:
        tactic_level, _ = CLASSICAL_INDICATORS.get(tactic, (CRMLevel.BISH, ""))
        level = CRMLevel(max(level.value, tactic_level.value))

    # Noncomputable flag suggests at least WLPO
    if decl.is_noncomputable and level < CRMLevel.WLPO:
        level = CRMLevel.WLPO

    return level


# =====================================================================
# 4. BATCH ANALYSIS AND REPORTING
# =====================================================================

@dataclass
class MathLibCRMReport:
    """Aggregate report across multiple Lean files."""
    files: list[LeanFileAnalysis]

    @property
    def total_declarations(self) -> int:
        return sum(len(f.declarations) for f in self.files)

    @property
    def total_theorems(self) -> int:
        return sum(1 for f in self.files for d in f.declarations
                   if d.kind in ('theorem', 'lemma', 'proposition', 'corollary'))

    @property
    def total_defs(self) -> int:
        return sum(1 for f in self.files for d in f.declarations
                   if 'def' in d.kind or 'instance' in d.kind)

    def signature_distribution(self) -> dict[str, int]:
        dist = Counter()
        for f in self.files:
            for d in f.declarations:
                dist[str(d.heuristic_level)] += 1
        return dict(dist)

    def domain_signatures(self) -> dict[str, dict]:
        """Per-domain analysis."""
        domains = defaultdict(lambda: {"files": [], "decls": 0, "max_level": CRMLevel.BISH,
                                        "levels": Counter()})
        for f in self.files:
            d = domains[f.domain]
            d["files"].append(f.filename)
            for decl in f.declarations:
                d["decls"] += 1
                d["levels"][str(decl.heuristic_level)] += 1
                if decl.heuristic_level > d["max_level"]:
                    d["max_level"] = decl.heuristic_level
        return dict(domains)

    def format_report(self) -> str:
        lines = []
        lines.append("╔" + "═"*70 + "╗")
        lines.append("║" + "  CRMlint Mathlib Analysis Report".center(70) + "║")
        lines.append("║" + "  Heuristic CRM Signature Classification".center(70) + "║")
        lines.append("╚" + "═"*70 + "╝")
        lines.append("")

        # Overview
        lines.append(f"  Files analyzed:        {len(self.files)}")
        lines.append(f"  Total declarations:    {self.total_declarations}")
        lines.append(f"  Theorems/lemmas:       {self.total_theorems}")
        lines.append(f"  Definitions/instances: {self.total_defs}")
        lines.append("")

        # Signature distribution
        dist = self.signature_distribution()
        total = sum(dist.values()) or 1
        lines.append(f"  {'─'*66}")
        lines.append(f"  CRM SIGNATURE DISTRIBUTION (all declarations)")
        lines.append(f"  {'─'*66}")
        for level in CRMLevel:
            count = dist.get(str(level), 0)
            pct = count / total * 100
            bar = "█" * int(pct / 2)
            lines.append(f"    {str(level):<8} {count:>5}  ({pct:5.1f}%)  {bar}")
        lines.append("")

        # Per-domain analysis
        lines.append(f"  {'─'*66}")
        lines.append(f"  PER-DOMAIN ANALYSIS")
        lines.append(f"  {'─'*66}")
        for domain, info in sorted(self.domain_signatures().items()):
            lines.append(f"")
            lines.append(f"  ▸ {domain}")
            lines.append(f"    Declarations: {info['decls']}  |  "
                         f"Max level: {info['max_level']}")
            level_str = ", ".join(f"{k}: {v}" for k, v in 
                                  sorted(info['levels'].items()))
            lines.append(f"    Distribution: {level_str}")

        # Per-file detail
        lines.append("")
        lines.append(f"  {'─'*66}")
        lines.append(f"  PER-FILE DETAIL")
        lines.append(f"  {'─'*66}")
        for f in self.files:
            lines.append(f"")
            lines.append(f"  ▸ {f.filename}")
            lines.append(f"    Domain: {f.domain}  |  Lines: {f.total_lines}  |  "
                         f"Declarations: {len(f.declarations)}")
            lines.append(f"    Import signature: {f.import_signature}  |  "
                         f"File signature: {f.file_signature}")
            lines.append(f"    Noncomputable: {f.noncomputable_count}  |  "
                         f"Classical axioms: {f.classical_axiom_count}")

            # Show classical declarations
            classical_decls = [d for d in f.declarations if d.heuristic_level >= CRMLevel.WKL]
            if classical_decls:
                lines.append(f"    Classical declarations ({len(classical_decls)}):")
                for d in classical_decls[:8]:  # limit display
                    markers = ", ".join(name for name, _ in d.classical_markers[:3])
                    marker_str = f" [{markers}]" if markers else ""
                    lines.append(f"      {d.kind} {d.name}: {d.heuristic_level}{marker_str}")
                if len(classical_decls) > 8:
                    lines.append(f"      ... and {len(classical_decls) - 8} more")

        # Archimedean obstruction verification
        lines.append("")
        lines.append(f"  {'─'*66}")
        lines.append(f"  ARCHIMEDEAN OBSTRUCTION THESIS VERIFICATION")
        lines.append(f"  {'─'*66}")
        lines.append(f"  Prediction: Algebraic domains → BISH, Analytic domains → CLASS")
        lines.append(f"")

        domain_sigs = self.domain_signatures()
        for domain, info in sorted(domain_sigs.items()):
            max_lvl = info["max_level"]
            is_algebraic = any(k in domain.lower()
                               for k in ["algebra", "ring", "field", "linear",
                                          "representation", "number", "geometry"])
            is_analytic = any(k in domain.lower()
                              for k in ["analysis", "measure", "topology"])

            if is_algebraic and max_lvl <= CRMLevel.WLPO:
                verdict = "✓ CONFIRMED (algebraic → ≤ WLPO)"
            elif is_analytic and max_lvl >= CRMLevel.WKL:
                verdict = "✓ CONFIRMED (analytic → ≥ WKL)"
            elif is_algebraic and max_lvl >= CRMLevel.CLASS:
                verdict = "⚠ MIXED (algebraic domain but CLASS content found)"
            elif is_analytic and max_lvl <= CRMLevel.BISH:
                verdict = "⚠ UNEXPECTED (analytic domain but only BISH)"
            else:
                verdict = "— (neutral)"

            lines.append(f"    {domain:<35} {str(max_lvl):<8} {verdict}")

        # Top classical hotspots
        lines.append("")
        lines.append(f"  {'─'*66}")
        lines.append(f"  TOP CLASSICAL HOTSPOTS (highest CRM cost declarations)")
        lines.append(f"  {'─'*66}")
        all_decls = []
        for f in self.files:
            for d in f.declarations:
                all_decls.append((f.filename, d))

        all_decls.sort(key=lambda x: x[1].heuristic_level.value, reverse=True)
        for fname, d in all_decls[:15]:
            markers = ", ".join(name for name, _ in d.classical_markers[:2])
            marker_str = f" [{markers}]" if markers else ""
            lines.append(f"    {str(d.heuristic_level):<6} {d.kind} {d.name}{marker_str}")
            lines.append(f"           in {fname}")

        lines.append("")
        lines.append("═" * 72)
        return "\n".join(lines)


# =====================================================================
# 5. MAIN: CRAWL AND ANALYZE
# =====================================================================

def crawl_directory(dirpath: str) -> MathLibCRMReport:
    """Crawl a directory of Lean files and produce a CRM report."""
    files = []
    for fname in sorted(os.listdir(dirpath)):
        if fname.endswith('.lean'):
            filepath = os.path.join(dirpath, fname)
            try:
                analysis = parse_lean_file(filepath)
                files.append(analysis)
            except Exception as e:
                print(f"  ERROR parsing {fname}: {e}")
    return MathLibCRMReport(files=files)


def main():
    cache_dir = "/home/claude/mathlib_cache"

    if not os.path.isdir(cache_dir):
        print(f"No Lean files found in {cache_dir}")
        return

    lean_files = [f for f in os.listdir(cache_dir) if f.endswith('.lean')]
    if not lean_files:
        print("No .lean files found")
        return

    print(f"Found {len(lean_files)} Lean files in {cache_dir}\n")

    report = crawl_directory(cache_dir)
    output = report.format_report()
    print(output)

    # Save report
    with open("/home/claude/crmlint_mathlib_report.txt", "w") as f:
        f.write(output)
    print(f"\nReport saved to /home/claude/crmlint_mathlib_report.txt")


if __name__ == "__main__":
    main()
