"""
CRMlint Proof Structure & Complexity Analyzer
==============================================

Computes a VECTOR of structural invariants for each formalized proof,
combining three independent axes:

  AXIS 1: CRM Signature (logical cost)
    - From crmlint.py and crmlint_crawler.py
    - What axioms does the proof require?

  AXIS 2: Proof Complexity (structural cost)
    - Size: total steps, term size, de Bruijn factor estimate
    - Depth: max dependency chain, critical path length
    - Width: max active hypotheses, fan-in, fan-out
    - Branching: case splits, number of independent subgoals

  AXIS 3: Modularity & Coupling (architectural cost)
    - External dependencies (imports, lemma citations)
    - Internal cohesion (self-containedness)
    - Cyclomatic complexity (independent paths through the proof)
    - Rewrite density (ratio of computation to reasoning)

The combination produces a ProofProfile: a complete fingerprint of
a proof's logical, structural, and architectural properties.

References:
  - Cook & Reckhow (1979): proof length as complexity measure
  - Kohlenbach (2008): proof mining and proof-theoretic metatheorems
  - Barendregt & Geuvers (2001): de Bruijn factor
  - McCabe (1976): cyclomatic complexity (adapted for proofs)

Author: Paul Chun-Kit Lee
Date: March 2026
"""

from __future__ import annotations
import os
import re
import math
from dataclasses import dataclass, field
from enum import IntEnum
from typing import Optional
from collections import Counter, defaultdict


# =====================================================================
# 1. CRM LEVEL (from crmlint.py)
# =====================================================================

class CRMLevel(IntEnum):
    BISH  = 0
    MP    = 1
    LLPO  = 2
    WKL   = 3
    WLPO  = 4
    LPO   = 5
    CLASS = 6
    def __str__(self): return self.name


# =====================================================================
# 2. PROOF STRUCTURAL INVARIANTS
# =====================================================================

@dataclass
class ProofSizeMetrics:
    """Axis 2a: Size invariants."""
    total_lines: int = 0             # raw line count of proof body
    total_tokens: int = 0            # approximate token count
    tactic_count: int = 0            # number of tactic invocations
    term_depth: int = 0              # max nesting depth of proof term
    de_bruijn_estimate: float = 0.0  # estimated formal/informal ratio
    comment_lines: int = 0           # documentation lines
    code_density: float = 0.0        # (lines - comments - blanks) / lines

    def complexity_score(self) -> float:
        """Normalized size complexity [0, 1]."""
        # Log scale: a 10-line proof scores ~0.3, 100-line ~0.6, 1000-line ~0.9
        if self.total_lines <= 0:
            return 0.0
        return min(1.0, math.log10(max(self.total_lines, 1)) / 3.5)


@dataclass
class ProofDepthMetrics:
    """Axis 2b: Depth invariants (dependency chain analysis)."""
    max_depth: int = 0               # longest dependency chain
    critical_path_length: int = 0    # longest chain of non-trivial steps
    avg_depth: float = 0.0           # average depth across all leaves
    depth_variance: float = 0.0      # variance in leaf depths (measures balance)

    def complexity_score(self) -> float:
        """Normalized depth complexity [0, 1]."""
        if self.max_depth <= 0:
            return 0.0
        return min(1.0, self.max_depth / 20.0)


@dataclass
class ProofWidthMetrics:
    """Axis 2c: Width invariants (parallel structure)."""
    max_active_hypotheses: int = 0   # max hypotheses in context at any point
    max_fan_in: int = 0              # max dependencies of a single step
    max_fan_out: int = 0             # max steps depending on a single step
    avg_fan_in: float = 0.0
    avg_fan_out: float = 0.0
    case_split_count: int = 0        # number of case analyses
    independent_branches: int = 0    # independent subgoals at widest point

    def complexity_score(self) -> float:
        """Normalized width complexity [0, 1]."""
        return min(1.0, (self.max_active_hypotheses + self.case_split_count) / 30.0)


@dataclass
class ProofModularityMetrics:
    """Axis 3: Modularity & coupling invariants."""
    external_lemma_count: int = 0    # distinct external lemmas cited
    import_count: int = 0            # number of imports
    self_contained_ratio: float = 0.0  # fraction of steps not citing externals
    cyclomatic_complexity: int = 1   # McCabe: 1 + case_splits + branches
    rewrite_density: float = 0.0     # fraction of steps that are rewrites
    simp_density: float = 0.0        # fraction using simp/norm_num/ring
    automation_ratio: float = 0.0    # fraction resolved by automation

    def coupling_score(self) -> float:
        """Normalized coupling [0, 1]. Higher = more coupled."""
        return min(1.0, self.external_lemma_count / 50.0)


# =====================================================================
# 3. THE PROOF PROFILE: COMPLETE FINGERPRINT
# =====================================================================

@dataclass
class ProofProfile:
    """
    Complete structural fingerprint of a formalized proof.
    
    This is the central data structure: a vector of invariants
    spanning the logical, structural, and architectural axes.
    """
    # Identity
    name: str
    kind: str               # theorem, lemma, def
    file: str
    domain: str
    line_number: int = 0

    # Axis 1: CRM (logical cost)
    crm_level: CRMLevel = CRMLevel.BISH
    crm_markers: list[str] = field(default_factory=list)
    is_noncomputable: bool = False
    archimedean: bool = False

    # Axis 2: Proof complexity (structural cost)
    size: ProofSizeMetrics = field(default_factory=ProofSizeMetrics)
    depth: ProofDepthMetrics = field(default_factory=ProofDepthMetrics)
    width: ProofWidthMetrics = field(default_factory=ProofWidthMetrics)

    # Axis 3: Modularity (architectural cost)
    modularity: ProofModularityMetrics = field(default_factory=ProofModularityMetrics)

    # Tactic breakdown
    tactic_histogram: dict[str, int] = field(default_factory=dict)

    # Derived classification
    proof_type: str = ""
    overall_complexity: float = 0.0

    def compute_derived(self):
        """Compute derived metrics from raw invariants."""
        # Overall complexity: geometric mean of the three axis scores
        s = self.size.complexity_score()
        d = self.depth.complexity_score()
        w = self.width.complexity_score()
        c = self.modularity.coupling_score()

        # Weighted combination: CRM level dominates, structure secondary
        crm_weight = self.crm_level.value / 6.0  # normalized to [0,1]
        structural = (s + d + w + c) / 4.0

        self.overall_complexity = 0.4 * crm_weight + 0.6 * structural

        # Proof type classification
        self.proof_type = self._classify()

    def _classify(self) -> str:
        """
        Classify proof into structural types based on the invariant vector.
        
        Types (extending the CRMlint classification with structural data):
          TRIVIAL:      Small, shallow, BISH, low coupling
          ALGEBRAIC:    Medium, BISH/WLPO, high rewrite density
          COMPUTATIONAL: High automation ratio, BISH, mechanical
          TOPOLOGICAL:  WKL, compactness arguments, medium depth
          ANALYTIC:     CLASS, high depth, InnerProductSpace/integral markers
          MODULAR:      Large but well-factored (low coupling despite size)
          MONOLITHIC:   Large and highly coupled
          BIFURCATING:  Multiple independent branches at different CRM levels
        """
        if self.size.total_lines <= 5 and self.crm_level <= CRMLevel.BISH:
            return "TRIVIAL"

        if self.modularity.automation_ratio > 0.5 and self.crm_level <= CRMLevel.BISH:
            return "COMPUTATIONAL"

        if self.modularity.rewrite_density > 0.4 and self.crm_level <= CRMLevel.WLPO:
            return "ALGEBRAIC"

        if self.crm_level == CRMLevel.WKL:
            return "TOPOLOGICAL"

        if self.crm_level >= CRMLevel.CLASS and self.archimedean:
            return "ANALYTIC"

        if self.crm_level >= CRMLevel.CLASS:
            return "CLASSICAL"

        if (self.size.total_lines > 50 and
                self.modularity.coupling_score() < 0.3):
            return "MODULAR"

        if (self.size.total_lines > 50 and
                self.modularity.coupling_score() > 0.6):
            return "MONOLITHIC"

        if self.width.independent_branches > 2:
            return "BIFURCATING"

        return "STANDARD"

    def summary_vector(self) -> dict:
        """Return the proof profile as a flat dictionary (for export/comparison)."""
        return {
            "name": self.name,
            "kind": self.kind,
            "domain": self.domain,
            "crm_level": str(self.crm_level),
            "crm_value": self.crm_level.value,
            "is_noncomputable": self.is_noncomputable,
            "archimedean": self.archimedean,
            "lines": self.size.total_lines,
            "tactic_count": self.size.tactic_count,
            "term_depth": self.size.term_depth,
            "max_proof_depth": self.depth.max_depth,
            "max_active_hyps": self.width.max_active_hypotheses,
            "case_splits": self.width.case_split_count,
            "fan_in_max": self.width.max_fan_in,
            "fan_out_max": self.width.max_fan_out,
            "external_lemmas": self.modularity.external_lemma_count,
            "cyclomatic": self.modularity.cyclomatic_complexity,
            "rewrite_density": self.modularity.rewrite_density,
            "automation_ratio": self.modularity.automation_ratio,
            "coupling_score": self.modularity.coupling_score(),
            "size_score": self.size.complexity_score(),
            "depth_score": self.depth.complexity_score(),
            "width_score": self.width.complexity_score(),
            "overall_complexity": self.overall_complexity,
            "proof_type": self.proof_type,
        }


# =====================================================================
# 4. LEAN 4 PROOF STRUCTURE EXTRACTOR
# =====================================================================

# Tactic categories for structural analysis
REWRITE_TACTICS = {"rw", "rfl", "simp", "norm_num", "ring", "field_simp",
                   "ring_nf", "norm_cast", "push_cast"}
AUTOMATION_TACTICS = {"simp", "norm_num", "ring", "omega", "linarith",
                      "polyrith", "decide", "aesop", "tauto", "positivity",
                      "gcongr", "fun_prop", "continuity", "measurability"}
CASE_TACTICS = {"cases", "rcases", "obtain", "match", "by_cases", "split"}
INTRO_TACTICS = {"intro", "intros", "rintro"}

# Patterns for structural parsing
LEMMA_CITATION = re.compile(r'(?:exact|apply|have\s+:=)\s+([\w\.]+)')
HAVE_PATTERN = re.compile(r'\bhave\b')
LET_PATTERN = re.compile(r'\blet\b')
BY_PATTERN = re.compile(r'\bby\b')

# Classical / Archimedean markers (refined from crawler)
ARCHIMEDEAN_MARKERS = {
    "InnerProductSpace", "MeasureTheory", "integral", "spectral",
    "L2", "Hilbert", "HasSum", "Summable", "tsum",
}

CLASSICAL_TERM_PATTERNS = [
    (re.compile(r'Classical\.em\b'), CRMLevel.CLASS),
    (re.compile(r'Classical\.choice\b'), CRMLevel.CLASS),
    (re.compile(r'Classical\.byContradiction\b'), CRMLevel.CLASS),
    (re.compile(r'Classical\.propDecidable\b'), CRMLevel.CLASS),
    (re.compile(r'Classical\.dec\b'), CRMLevel.CLASS),
    (re.compile(r'\bby_contra\b'), CRMLevel.CLASS),
    (re.compile(r'\bnot_not\b'), CRMLevel.CLASS),
    (re.compile(r'\bnoncomputable\b'), CRMLevel.WLPO),
    (re.compile(r'\bIsCompact\b'), CRMLevel.WKL),
    (re.compile(r'\bCompactSpace\b'), CRMLevel.WKL),
    (re.compile(r'\bCompleteLattice\b'), CRMLevel.WKL),
    (re.compile(r'\bpush_neg\b'), CRMLevel.WLPO),
]

ALL_KNOWN_TACTICS = (
    REWRITE_TACTICS | AUTOMATION_TACTICS | CASE_TACTICS | INTRO_TACTICS |
    {"exact", "apply", "refine", "constructor", "ext", "induction",
     "calc", "conv", "have", "let", "show", "use", "exists",
     "specialize", "revert", "clear", "rename_i", "subst",
     "contradiction", "absurd", "exfalso", "trivial",
     "congr", "injections", "left", "right",
     "by_contra", "push_neg", "tauto",
     "continuity", "measurability", "fun_prop", "bound",
     "norm_num", "ring", "linarith", "omega", "polyrith",
     "simp", "aesop", "decide", "gcongr", "positivity", "rel"}
)


def extract_proof_profile(
    name: str,
    kind: str,
    body: str,
    filename: str,
    domain: str,
    line_number: int = 0,
    imports: list[str] | None = None,
    is_noncomputable: bool = False,
) -> ProofProfile:
    """
    Extract a complete ProofProfile from a Lean 4 proof body.
    
    This is the main analysis function for individual declarations.
    """
    profile = ProofProfile(
        name=name, kind=kind, file=filename, domain=domain,
        line_number=line_number, is_noncomputable=is_noncomputable,
    )

    lines = body.strip().split('\n')
    body_clean = body.strip()

    # ----- SIZE METRICS -----
    profile.size.total_lines = len(lines)
    profile.size.total_tokens = len(body_clean.split())
    profile.size.comment_lines = sum(1 for l in lines
                                     if l.strip().startswith('--') or
                                     l.strip().startswith('/-'))
    non_blank = sum(1 for l in lines if l.strip())
    profile.size.code_density = (
        (non_blank - profile.size.comment_lines) / max(len(lines), 1)
    )

    # Count tactics
    tactic_hist = Counter()
    for tactic in ALL_KNOWN_TACTICS:
        pattern = r'\b' + re.escape(tactic) + r'\b'
        count = len(re.findall(pattern, body_clean))
        if count > 0:
            tactic_hist[tactic] = count

    profile.tactic_histogram = dict(tactic_hist)
    profile.size.tactic_count = sum(tactic_hist.values())

    # Term depth: approximate by max indentation depth
    max_indent = 0
    for line in lines:
        stripped = line.lstrip()
        if stripped:
            indent = len(line) - len(stripped)
            max_indent = max(max_indent, indent)
    profile.size.term_depth = max_indent // 2  # 2-space indents

    # de Bruijn estimate: tactic proofs are ~4-6x informal
    if profile.size.tactic_count > 0:
        profile.size.de_bruijn_estimate = 4.5
    else:
        profile.size.de_bruijn_estimate = 6.0  # term-mode proofs are more verbose

    # ----- DEPTH METRICS -----
    # Approximate: count sequential `have` and `let` chains
    have_count = len(HAVE_PATTERN.findall(body_clean))
    let_count = len(LET_PATTERN.findall(body_clean))
    by_count = len(BY_PATTERN.findall(body_clean))

    profile.depth.max_depth = have_count + let_count
    profile.depth.critical_path_length = max(have_count, by_count)
    profile.depth.avg_depth = profile.depth.max_depth / max(profile.size.tactic_count, 1)

    # ----- WIDTH METRICS -----
    # Active hypotheses: count `have` and `intro` accumulation
    intro_count = sum(tactic_hist.get(t, 0) for t in INTRO_TACTICS)
    profile.width.max_active_hypotheses = have_count + intro_count

    # Case splits
    case_count = sum(tactic_hist.get(t, 0) for t in CASE_TACTICS)
    profile.width.case_split_count = case_count

    # Estimate branching via case analysis
    profile.width.independent_branches = max(1, case_count)

    # Fan-in/out: approximate via tactic flow
    profile.width.max_fan_in = max(have_count, 1)
    profile.width.max_fan_out = max(case_count, 1)
    profile.width.avg_fan_in = have_count / max(profile.size.tactic_count, 1)
    profile.width.avg_fan_out = case_count / max(profile.size.tactic_count, 1)

    # ----- MODULARITY METRICS -----
    # External lemma citations
    citations = LEMMA_CITATION.findall(body_clean)
    # Filter: external if contains a dot (qualified name)
    external = [c for c in citations if '.' in c]
    profile.modularity.external_lemma_count = len(set(external))
    profile.modularity.import_count = len(imports) if imports else 0

    total_steps = max(profile.size.tactic_count, 1)
    internal_steps = total_steps - len(external)
    profile.modularity.self_contained_ratio = internal_steps / total_steps

    # Cyclomatic complexity: 1 + decision points
    profile.modularity.cyclomatic_complexity = 1 + case_count + by_count

    # Rewrite density
    rw_count = sum(tactic_hist.get(t, 0) for t in REWRITE_TACTICS)
    profile.modularity.rewrite_density = rw_count / total_steps

    # Automation ratio
    auto_count = sum(tactic_hist.get(t, 0) for t in AUTOMATION_TACTICS)
    profile.modularity.automation_ratio = auto_count / total_steps

    # ----- CRM LEVEL -----
    crm_level = CRMLevel.BISH
    markers = []

    for pattern, level in CLASSICAL_TERM_PATTERNS:
        if pattern.search(body_clean):
            crm_level = CRMLevel(max(crm_level.value, level.value))
            markers.append(pattern.pattern.replace(r'\b', ''))

    if is_noncomputable and crm_level < CRMLevel.WLPO:
        crm_level = CRMLevel.WLPO

    profile.crm_level = crm_level
    profile.crm_markers = markers

    # Archimedean detection
    for marker in ARCHIMEDEAN_MARKERS:
        if marker in body_clean:
            profile.archimedean = True
            break

    # ----- DERIVED -----
    profile.compute_derived()

    return profile


# =====================================================================
# 5. BATCH ANALYSIS FROM LEAN FILES
# =====================================================================

THEOREM_PATTERN = re.compile(
    r'^(theorem|lemma|proposition|corollary)\s+(\w[\w\'\.]*)',
    re.MULTILINE,
)
DEF_PATTERN = re.compile(
    r'^((?:noncomputable\s+)?(?:def|instance))\s+(\w[\w\'\.]*)',
    re.MULTILINE,
)
IMPORT_PATTERN = re.compile(r'^(?:public\s+)?import\s+([\w\.]+)', re.MULTILINE)


def _extract_body(content: str, start: int) -> str:
    rest = content[start:start + 5000]
    body_start = None
    for marker in [':= by', ':= fun', ':= calc', ':= show', ':=', 'where']:
        idx = rest.find(marker)
        if idx >= 0:
            body_start = idx + len(marker)
            break
    if body_start is None:
        return rest[:500]
    body_rest = rest[body_start:]
    end_match = re.search(
        r'\n(?:theorem|lemma|def|noncomputable|instance|section|namespace|end |/-|#)',
        body_rest
    )
    if end_match:
        return body_rest[:end_match.start()].strip()
    return body_rest[:2000].strip()


def _infer_domain(filename: str) -> str:
    name = filename.replace('.lean', '')
    parts = name.split('_')
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
    }
    return domain_map.get(parts[0], parts[0]) if parts else "Unknown"


def analyze_lean_file(filepath: str) -> list[ProofProfile]:
    """Analyze all declarations in a Lean 4 file."""
    with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
        content = f.read()

    filename = os.path.basename(filepath)
    domain = _infer_domain(filename)
    imports = IMPORT_PATTERN.findall(content)
    profiles = []

    # Theorems and lemmas
    for match in THEOREM_PATTERN.finditer(content):
        kind = match.group(1)
        name = match.group(2)
        line_num = content[:match.start()].count('\n') + 1
        body = _extract_body(content, match.end())

        is_nc = bool(re.search(
            r'noncomputable\s+' + re.escape(kind),
            content[max(0, match.start() - 20):match.start() + 10]
        ))

        profile = extract_proof_profile(
            name=name, kind=kind, body=body, filename=filename,
            domain=domain, line_number=line_num, imports=imports,
            is_noncomputable=is_nc,
        )
        profiles.append(profile)

    # Definitions and instances
    for match in DEF_PATTERN.finditer(content):
        full_kind = match.group(1).strip()
        name = match.group(2)
        line_num = content[:match.start()].count('\n') + 1
        body = _extract_body(content, match.end())
        is_nc = 'noncomputable' in full_kind

        profile = extract_proof_profile(
            name=name, kind=full_kind, body=body, filename=filename,
            domain=domain, line_number=line_num, imports=imports,
            is_noncomputable=is_nc,
        )
        profiles.append(profile)

    return profiles


# =====================================================================
# 6. AGGREGATE REPORTING
# =====================================================================

def format_full_report(all_profiles: list[ProofProfile]) -> str:
    """Generate the comprehensive analysis report."""
    lines = []
    lines.append("╔" + "═" * 72 + "╗")
    lines.append("║" + "  CRMlint Proof Structure & Complexity Report".center(72) + "║")
    lines.append("║" + "  Logical × Structural × Architectural Analysis".center(72) + "║")
    lines.append("╚" + "═" * 72 + "╝")
    lines.append("")

    n = len(all_profiles)
    lines.append(f"  Total declarations analyzed: {n}")
    lines.append("")

    # --- CRM Distribution ---
    crm_dist = Counter(str(p.crm_level) for p in all_profiles)
    lines.append(f"  {'─' * 68}")
    lines.append(f"  AXIS 1: CRM SIGNATURE DISTRIBUTION")
    lines.append(f"  {'─' * 68}")
    for level in CRMLevel:
        count = crm_dist.get(str(level), 0)
        pct = count / max(n, 1) * 100
        bar = "█" * int(pct / 2)
        lines.append(f"    {str(level):<8} {count:>5}  ({pct:5.1f}%)  {bar}")

    # --- Proof Type Distribution ---
    type_dist = Counter(p.proof_type for p in all_profiles)
    lines.append(f"\n  {'─' * 68}")
    lines.append(f"  PROOF TYPE DISTRIBUTION")
    lines.append(f"  {'─' * 68}")
    for ptype, count in sorted(type_dist.items(), key=lambda x: -x[1]):
        pct = count / max(n, 1) * 100
        bar = "█" * int(pct / 2)
        lines.append(f"    {ptype:<20} {count:>5}  ({pct:5.1f}%)  {bar}")

    # --- Complexity Statistics ---
    if all_profiles:
        sizes = [p.size.total_lines for p in all_profiles]
        depths = [p.depth.max_depth for p in all_profiles]
        widths = [p.width.max_active_hypotheses for p in all_profiles]
        cyclomatics = [p.modularity.cyclomatic_complexity for p in all_profiles]
        complexities = [p.overall_complexity for p in all_profiles]

        lines.append(f"\n  {'─' * 68}")
        lines.append(f"  AXIS 2: STRUCTURAL COMPLEXITY STATISTICS")
        lines.append(f"  {'─' * 68}")
        lines.append(f"    {'Metric':<30} {'Mean':>8} {'Median':>8} {'Max':>8}")
        lines.append(f"    {'─' * 54}")

        def stats(vals):
            s = sorted(vals)
            mean = sum(s) / len(s)
            median = s[len(s) // 2]
            return mean, median, max(s)

        for label, vals in [
            ("Proof lines", sizes),
            ("Dependency depth (have/let)", depths),
            ("Active hypotheses", widths),
            ("Cyclomatic complexity", cyclomatics),
            ("Overall complexity score", complexities),
        ]:
            m, med, mx = stats(vals)
            if isinstance(vals[0], float):
                lines.append(f"    {label:<30} {m:>8.3f} {med:>8.3f} {mx:>8.3f}")
            else:
                lines.append(f"    {label:<30} {m:>8.1f} {med:>8.0f} {mx:>8}")

    # --- Tactic Frequency ---
    global_tactics = Counter()
    for p in all_profiles:
        global_tactics.update(p.tactic_histogram)

    lines.append(f"\n  {'─' * 68}")
    lines.append(f"  TACTIC FREQUENCY (top 20)")
    lines.append(f"  {'─' * 68}")
    total_tactics = sum(global_tactics.values()) or 1
    for tactic, count in global_tactics.most_common(20):
        pct = count / total_tactics * 100
        bar = "█" * int(pct)
        lines.append(f"    {tactic:<20} {count:>5}  ({pct:5.1f}%)  {bar}")

    # --- Per-Domain Cross-Tabulation ---
    domains = defaultdict(list)
    for p in all_profiles:
        domains[p.domain].append(p)

    lines.append(f"\n  {'─' * 68}")
    lines.append(f"  CRM × DOMAIN CROSS-TABULATION")
    lines.append(f"  {'─' * 68}")
    lines.append(f"    {'Domain':<25} {'N':>4} {'BISH':>6} {'WKL':>6} "
                 f"{'WLPO':>6} {'CLASS':>6} {'AvgCx':>7}")
    lines.append(f"    {'─' * 62}")

    for domain in sorted(domains.keys()):
        profs = domains[domain]
        dn = len(profs)
        crm_counts = Counter(str(p.crm_level) for p in profs)
        avg_cx = sum(p.overall_complexity for p in profs) / dn

        lines.append(
            f"    {domain:<25} {dn:>4} "
            f"{crm_counts.get('BISH', 0):>6} "
            f"{crm_counts.get('WKL', 0):>6} "
            f"{crm_counts.get('WLPO', 0):>6} "
            f"{crm_counts.get('CLASS', 0):>6} "
            f"{avg_cx:>7.3f}"
        )

    # --- Most Complex Proofs ---
    lines.append(f"\n  {'─' * 68}")
    lines.append(f"  TOP 15 MOST COMPLEX PROOFS")
    lines.append(f"  {'─' * 68}")
    lines.append(f"    {'CRM':<6} {'Type':<16} {'Cx':>5} {'Ln':>4} "
                 f"{'Dp':>3} {'Wd':>3} {'Cy':>3} {'Name'}")
    lines.append(f"    {'─' * 66}")

    ranked = sorted(all_profiles, key=lambda p: p.overall_complexity, reverse=True)
    for p in ranked[:15]:
        lines.append(
            f"    {str(p.crm_level):<6} {p.proof_type:<16} "
            f"{p.overall_complexity:>5.3f} {p.size.total_lines:>4} "
            f"{p.depth.max_depth:>3} {p.width.max_active_hypotheses:>3} "
            f"{p.modularity.cyclomatic_complexity:>3} {p.kind} {p.name}"
        )

    # --- Archimedean Thesis Verification ---
    lines.append(f"\n  {'─' * 68}")
    lines.append(f"  ARCHIMEDEAN OBSTRUCTION THESIS: STRUCTURAL VERIFICATION")
    lines.append(f"  {'─' * 68}")
    lines.append(f"  Do Archimedean proofs systematically differ in structure?")
    lines.append("")

    arch_profs = [p for p in all_profiles if p.archimedean]
    non_arch_profs = [p for p in all_profiles if not p.archimedean]

    if arch_profs and non_arch_profs:
        def avg(lst): return sum(lst) / max(len(lst), 1)

        metrics = [
            ("Avg complexity score",
             avg([p.overall_complexity for p in arch_profs]),
             avg([p.overall_complexity for p in non_arch_profs])),
            ("Avg proof lines",
             avg([p.size.total_lines for p in arch_profs]),
             avg([p.size.total_lines for p in non_arch_profs])),
            ("Avg dependency depth",
             avg([p.depth.max_depth for p in arch_profs]),
             avg([p.depth.max_depth for p in non_arch_profs])),
            ("Avg active hypotheses",
             avg([p.width.max_active_hypotheses for p in arch_profs]),
             avg([p.width.max_active_hypotheses for p in non_arch_profs])),
            ("Avg external lemmas",
             avg([p.modularity.external_lemma_count for p in arch_profs]),
             avg([p.modularity.external_lemma_count for p in non_arch_profs])),
            ("Avg automation ratio",
             avg([p.modularity.automation_ratio for p in arch_profs]),
             avg([p.modularity.automation_ratio for p in non_arch_profs])),
        ]

        lines.append(f"    {'Metric':<28} {'Archimedean':>12} {'Non-Arch':>12} {'Delta':>8}")
        lines.append(f"    {'─' * 60}")
        for label, arch_val, non_val in metrics:
            delta = arch_val - non_val
            sign = "+" if delta > 0 else ""
            lines.append(
                f"    {label:<28} {arch_val:>12.2f} {non_val:>12.2f} "
                f"{sign}{delta:>7.2f}"
            )

        lines.append(f"\n    Archimedean proofs: {len(arch_profs)}  |  "
                     f"Non-Archimedean: {len(non_arch_profs)}")

        # Verdict
        cx_ratio = (avg([p.overall_complexity for p in arch_profs]) /
                    max(avg([p.overall_complexity for p in non_arch_profs]), 0.001))
        if cx_ratio > 1.3:
            lines.append(f"    VERDICT: Archimedean proofs are {cx_ratio:.1f}x more complex. "
                         f"Thesis SUPPORTED.")
        elif cx_ratio > 1.1:
            lines.append(f"    VERDICT: Archimedean proofs are moderately more complex "
                         f"({cx_ratio:.1f}x). Thesis weakly supported.")
        else:
            lines.append(f"    VERDICT: No significant structural difference detected "
                         f"({cx_ratio:.1f}x). Thesis NOT supported at this granularity.")
    else:
        lines.append("    Insufficient data for comparison.")

    lines.append("")
    lines.append("═" * 74)
    return "\n".join(lines)


# =====================================================================
# 7. MAIN
# =====================================================================

def main():
    cache_dir = "/home/claude/mathlib_cache"

    if not os.path.isdir(cache_dir):
        print(f"No files in {cache_dir}")
        return

    lean_files = sorted(f for f in os.listdir(cache_dir) if f.endswith('.lean'))
    if not lean_files:
        print("No .lean files found")
        return

    print(f"Analyzing {len(lean_files)} Lean files...\n")

    all_profiles = []
    for fname in lean_files:
        filepath = os.path.join(cache_dir, fname)
        try:
            profiles = analyze_lean_file(filepath)
            all_profiles.extend(profiles)
            print(f"  {fname}: {len(profiles)} declarations")
        except Exception as e:
            print(f"  ERROR {fname}: {e}")

    print(f"\nTotal profiles: {len(all_profiles)}\n")

    report = format_full_report(all_profiles)
    print(report)

    # Save
    outpath = "/home/claude/crmlint_structure_report.txt"
    with open(outpath, "w") as f:
        f.write(report)
    print(f"\nSaved to {outpath}")


if __name__ == "__main__":
    main()
