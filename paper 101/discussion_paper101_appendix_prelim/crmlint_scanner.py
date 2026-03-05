#!/usr/bin/env python3
"""
CRMlint Scanner v1.0
====================
Lightweight CRM signature scanner for LaTeX papers at scale.

Input:  Directory of .tex files (or single file)
Output: Per-paper bottleneck report + aggregate heatmap

No LLM. No Lean. No dependencies beyond Python 3 stdlib.
Scans thousands of papers in seconds.

Three detection layers:
  1. Keyword markers  — ~80 technique phrases mapped to CRM levels
  2. Citation markers  — ~120 landmark papers mapped to CRM levels
  3. Temporal analysis — CRM drift across publication years

Usage:
  python crmlint_scanner.py paper.tex
  python crmlint_scanner.py ./arxiv_dump/
  python crmlint_scanner.py ./arxiv_dump/ --csv output.csv
  python crmlint_scanner.py ./arxiv_dump/ --temporal
  python crmlint_scanner.py ./arxiv_dump/ --heatmap

Author: Paul Chun-Kit Lee
Date:   March 2026
Part of the CRM Programme (Papers 50-98)
"""

import os
import re
import sys
import csv
import json
import argparse
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Tuple, Optional, Set
from enum import IntEnum
from collections import Counter, defaultdict
from pathlib import Path


# ======================================================================
# CRM HIERARCHY
# ======================================================================

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


# ======================================================================
# KEYWORD DICTIONARY
# ======================================================================
# Each entry: (pattern, CRM level, short reason)
# Patterns are case-insensitive regexes applied to the LaTeX source.
# Ordered by CRM cost descending within each level.

KEYWORD_MARKERS: List[Tuple[str, CRMLevel, str]] = [

    # === CLASS (full classical logic) ===
    # Trace formula / spectral theory
    (r"trace\s+formula",                    CRMLevel.CLASS, "trace formula (spectral decomposition on adelic quotient)"),
    (r"selberg\s+trace",                    CRMLevel.CLASS, "Selberg trace formula"),
    (r"arthur[\-\s]selberg",                CRMLevel.CLASS, "Arthur-Selberg trace formula"),
    (r"arthur['']?s?\s+trace",              CRMLevel.CLASS, "Arthur trace formula"),
    (r"spectral\s+decomposition",           CRMLevel.CLASS, "spectral decomposition (L² on locally symmetric space)"),
    (r"L\^?\{?2\}?\s*[\(\[].*(?:symmetric|quotient|adel)", CRMLevel.CLASS, "L² on locally symmetric space"),
    (r"eisenstein\s+series.*(?:spectral|continuous)", CRMLevel.CLASS, "Eisenstein series (continuous spectrum)"),

    # Archimedean analysis
    (r"petersson\s+inner\s+product",        CRMLevel.CLASS, "Petersson inner product (integration on upper half-plane)"),
    (r"petersson\s+norm",                   CRMLevel.CLASS, "Petersson norm"),
    (r"analytic\s+continuation",            CRMLevel.CLASS, "analytic continuation to all of C"),
    (r"functional\s+equation.*L[\-\s](?:function|series)", CRMLevel.CLASS, "functional equation of L-function"),
    (r"(?:meromorphic|holomorphic)\s+continuation", CRMLevel.CLASS, "meromorphic/holomorphic continuation"),

    # Hodge theory / complex geometry
    (r"hodge\s+decomposition",              CRMLevel.CLASS, "Hodge decomposition (elliptic PDE on compact Kähler)"),
    (r"\\partial\\bar\{?\\partial\}?[\-\s]lemma", CRMLevel.CLASS, "∂∂̄-lemma (elliptic regularity)"),
    (r"harmonic\s+(?:forms?|representatives?)", CRMLevel.CLASS, "harmonic representatives (Hodge theorem)"),
    (r"elliptic\s+regularity",              CRMLevel.CLASS, "elliptic regularity"),
    (r"(?:hodge|lefschetz)\s+(?:standard|hard)\s+conjecture", CRMLevel.CLASS, "Hodge/Lefschetz standard conjecture"),

    # Arakelov theory
    (r"arakelov",                           CRMLevel.CLASS, "Arakelov geometry (integration on complex manifold)"),
    (r"arithmetic\s+intersection",          CRMLevel.CLASS, "arithmetic intersection theory"),
    (r"faltings\s+height",                  CRMLevel.CLASS, "Faltings height (Arakelov)"),

    # Period integrals
    (r"period\s+(?:integral|matrix|map|isomorphism)", CRMLevel.CLASS, "period integral (Betti ↔ de Rham comparison)"),
    (r"\\int_\{?\\(?:Gamma|gamma)",         CRMLevel.CLASS, "integration over modular curve"),
    (r"integration\s+over\s+(?:cycle|manifold)", CRMLevel.CLASS, "integration over topological cycle"),

    # Complex analytic
    (r"riemann\s+existence\s+theorem",      CRMLevel.CLASS, "Riemann existence theorem (GAGA)"),
    (r"GAGA",                               CRMLevel.CLASS, "GAGA (analytic ↔ algebraic)"),
    (r"heat\s+kernel",                      CRMLevel.CLASS, "heat kernel (analytic)"),
    (r"selberg\s+zeta",                     CRMLevel.CLASS, "Selberg zeta function"),
    (r"(?:laplacian|laplace)\s+(?:on|operator).*(?:manifold|symmetric)", CRMLevel.CLASS, "Laplacian on manifold"),

    # Harmonic analysis
    (r"plancherel\s+(?:formula|measure|theorem)", CRMLevel.CLASS, "Plancherel formula"),
    (r"harish[\-\s]chandra",               CRMLevel.CLASS, "Harish-Chandra (harmonic analysis on reductive groups)"),

    # Euler systems / density theorems
    (r"euler\s+system",                     CRMLevel.CLASS, "Euler system (analytic density)"),
    (r"kolyvagin",                          CRMLevel.CLASS, "Kolyvagin Euler system"),
    (r"chebotarev\s+density",              CRMLevel.CLASS, "Chebotarev density theorem"),
    (r"dirichlet\s+density",               CRMLevel.CLASS, "Dirichlet density theorem"),

    # Existence theorems (general)
    (r"(?:by|using)\s+(?:the\s+)?(?:law\s+of\s+)?excluded\s+middle", CRMLevel.CLASS, "law of excluded middle"),
    (r"by\s+contradiction",                 CRMLevel.CLASS, "proof by contradiction (possibly eliminable)"),

    # === LPO (limited principle of omniscience) ===
    (r"bounded\s+monotone\s+convergence",   CRMLevel.LPO, "BMC (bounded monotone convergence)"),
    (r"thermodynamic\s+limit",              CRMLevel.LPO, "thermodynamic limit (infinite volume)"),
    (r"supremum\s+(?:of|over)\s+(?:a|an)\s+(?:bounded|infinite)", CRMLevel.LPO, "supremum existence for bounded sequence"),
    (r"(?:least|greatest)\s+upper\s+bound\s+(?:property|axiom)", CRMLevel.LPO, "least upper bound property"),

    # Norm/filtration cutoffs — decidable ordering on ℝ (Archimedean dark matter)
    (r"\\leq?\s*[ck](?:_0)?(?:\}|\s|\\)",   CRMLevel.LPO, "norm filtration cutoff (decidable ≤ on ℝ)"),
    (r"\\[lV]ert.*\\[rV]ert.*\\leq?\s",     CRMLevel.LPO, "norm bound (decidable ≤ on ℝ)"),
    (r"(?:for|when|if)\s+[c]\s*\\geq?\s",   CRMLevel.LPO, "real parameter threshold (decidable ≥ on ℝ)"),
    (r"(?:norm|semi[\-\s]?norm).*(?:bounded|filtration|filter)", CRMLevel.LPO, "normed filtration (decidable norm comparison)"),
    (r"\$?\s*0\s*<\s*r\s*<\s*r'\s*(?:\\leq?|<)\s*1", CRMLevel.LPO, "radius ordering (decidable ordering on ℝ)"),
    (r"(?:exact|acyclic).*(?:degree|in\s+degrees?)\s*\\leq?\s", CRMLevel.LPO, "bounded exactness (norm-controlled vanishing)"),

    # === WLPO (weak LPO) ===
    (r"(?:decidab|trichotomy).*(?:real|\\mathbb\{R\})", CRMLevel.WLPO, "decidability of real equality"),
    (r"intermediate\s+value\s+theorem",     CRMLevel.WLPO, "IVT (may require WLPO/LLPO depending on formulation)"),
    (r"noncomputable\s+def",               CRMLevel.WLPO, "noncomputable definition"),

    # Normed completions — Cauchy convergence test
    (r"\\widehat\{[A-Z_]\}",               CRMLevel.WLPO, "normed completion (Cauchy convergence test)"),
    (r"(?:completion|completed)\s+(?:of|w\.?r\.?t|with\s+respect)", CRMLevel.WLPO, "normed completion"),
    (r"(?:complete|completion).*(?:normed|semi[\-\s]?normed|pseudo[\-\s]?normed)", CRMLevel.WLPO, "completion of (semi/pseudo-)normed group"),
    (r"(?:normed|semi[\-\s]?normed|pseudo[\-\s]?normed).*(?:complete|completion)", CRMLevel.WLPO, "completed normed group"),
    (r"cauchy\s+(?:sequence|net|filter|completion)", CRMLevel.WLPO, "Cauchy completion"),

    # === WKL (weak König's lemma) ===
    (r"(?:weak\s+)?k[öo]nig['']?s?\s+lemma", CRMLevel.WKL, "Weak König's Lemma"),
    (r"taylor[\-\s]wiles\s+patch",          CRMLevel.WKL, "Taylor-Wiles patching (inverse limit of finite sets)"),
    (r"(?:TW|tw)\s+patch",                  CRMLevel.WKL, "TW patching"),
    (r"inverse\s+limit.*(?:finite|compact)", CRMLevel.WKL, "inverse limit of finite objects"),
    (r"bolzano[\-\s]weierstrass",           CRMLevel.WKL, "Bolzano-Weierstrass"),
    (r"sequential\s+compactness",           CRMLevel.WKL, "sequential compactness"),
    (r"tychonoff",                          CRMLevel.WKL, "Tychonoff theorem"),

    # Berkovich / adic geometry — profinite inverse limit structure
    (r"berkovich\s+(?:spectrum|space|analytic)", CRMLevel.WKL, "Berkovich spectrum (profinite/inverse limit)"),
    (r"adic\s+space",                      CRMLevel.WKL, "adic space (inverse limit of affinoids)"),
    (r"perfectoid",                        CRMLevel.WKL, "perfectoid (inverse limit / tilting)"),
    (r"arc[\-\s]topology",                 CRMLevel.WKL, "arc-topology (profinite descent)"),

    # Condensed / solid formalism
    (r"condensed\s+(?:set|module|ring|abelian|group|math)", CRMLevel.WKL, "condensed mathematics (profinite structure)"),
    (r"solid\s+(?:module|tensor|ring)",    CRMLevel.WKL, "solid module (condensed formalism)"),

    # Motivic machinery — algebraic (BISH)
    (r"motivic\s+(?:sheaf|sheaves|cohomology|spectrum|category)", CRMLevel.BISH, "motivic sheaf/cohomology (algebraic)"),
    (r"six[\-\s]functor|6[\-\s]functor",   CRMLevel.BISH, "six-functor formalism (categorical)"),
    (r"tate\s+twist",                      CRMLevel.BISH, "Tate twist (algebraic)"),

    # === LLPO ===
    (r"(?:weak\s+)?limited\s+principle\s+of\s+omniscience", CRMLevel.LLPO, "LLPO"),

    # === MP (Markov's principle) ===
    (r"markov['']?s?\s+principle",          CRMLevel.MP, "Markov's principle"),
]


# ======================================================================
# CITATION DICTIONARY
# ======================================================================
# Maps (author-key, year) or (author-key) to CRM level.
# Author keys are lowercase substrings matched against \cite{} content
# and against the bibliography entries.

CITATION_MARKERS: List[Tuple[str, Optional[int], CRMLevel, str]] = [

    # === CLASS citations ===
    # Trace formula
    ("arthur",        2005, CRMLevel.CLASS, "Arthur trace formula (Clay 2005)"),
    ("selberg",       1956, CRMLevel.CLASS, "Selberg trace formula"),
    ("langlands",     1976, CRMLevel.CLASS, "Langlands, Eisenstein series"),
    ("langlandstunnell", None, CRMLevel.CLASS, "Langlands-Tunnell (base change, trace formula)"),
    ("moeglinwaldspurger", None, CRMLevel.CLASS, "Moeglin-Waldspurger (spectral decomposition)"),

    # Arakelov / heights
    ("faltings",      1983, CRMLevel.CLASS, "Faltings (Arakelov heights, isogeny theorem)"),
    ("arakelov",      None, CRMLevel.CLASS, "Arakelov geometry"),

    # Euler systems
    ("kolyvagin",     1990, CRMLevel.CLASS, "Kolyvagin Euler systems"),
    ("rubin",         2000, CRMLevel.CLASS, "Rubin, Euler systems"),
    ("grosszagier",   None, CRMLevel.CLASS, "Gross-Zagier (L-function derivative = height)"),
    ("gross",         1986, CRMLevel.CLASS, "Gross-Zagier"),

    # Hodge theory
    ("voisin",        2002, CRMLevel.CLASS, "Voisin, Hodge theory"),
    ("griffiths",     1969, CRMLevel.CLASS, "Griffiths, Hodge theory / periods"),
    ("deligne",       1971, CRMLevel.CLASS, "Deligne, Hodge II (Hodge decomposition)"),
    ("cattani",       None, CRMLevel.CLASS, "Cattani-Kaplan-Schmid (Hodge theory)"),

    # Analytic number theory
    ("iwaniec",       None, CRMLevel.CLASS, "Iwaniec (analytic number theory)"),
    ("harishchandra", None, CRMLevel.CLASS, "Harish-Chandra (harmonic analysis)"),

    # Condensed mathematics
    ("scholze",       2019, CRMLevel.WKL, "Scholze, Lectures on Analytic Geometry (Tychonoff gates)"),
    ("scholze",       2020, CRMLevel.WKL, "Scholze, Liquid Tensor Experiment challenge"),
    ("clausen",       None, CRMLevel.WKL, "Clausen-Scholze (condensed mathematics)"),

    # === WKL citations ===
    ("taylorwiles",   None, CRMLevel.WKL, "Taylor-Wiles patching"),
    ("taylor",        1995, CRMLevel.WKL, "Taylor-Wiles (ring-theoretic Hecke properties)"),
    ("calegari",      2012, CRMLevel.WKL, "Calegari-Geraghty (patching extension)"),
    ("khare",         2009, CRMLevel.WKL, "Khare-Wintenberger (Serre conjecture, uses patching)"),

    # === BISH citations (positive evidence for constructivity) ===
    ("mazur",         1997, CRMLevel.BISH, "Mazur, deformation theory (algebraic)"),
    ("fontaine",      1982, CRMLevel.BISH, "Fontaine-Laffaille (p-adic, algebraic)"),
    ("berger",        None, CRMLevel.BISH, "Berger (p-adic Hodge, algebraic)"),
    ("colmez",        None, CRMLevel.BISH, "Colmez-Fontaine (p-adic comparison, algebraic)"),
    ("kanirosen",     None, CRMLevel.BISH, "Kani-Rosen (Jacobian splitting, algebraic)"),
    ("ribet",         1983, CRMLevel.BISH, "Ribet (Hodge classes on abelian varieties, algebraic)"),
    ("wiles",         1995, CRMLevel.WKL,  "Wiles (FLT, uses patching = WKL)"),
    ("lafforgue",     2002, CRMLevel.BISH, "Lafforgue (function field Langlands, algebraic)"),

    # Shimura / modularity (usually CLASS due to analytic input)
    ("shimura",       None, CRMLevel.CLASS, "Shimura (automorphic forms, analytic)"),
    ("diamond",       None, CRMLevel.WKL,  "Diamond (patching refinement)"),
    ("kisin",         2009, CRMLevel.WKL,  "Kisin (modularity lifting, uses patching)"),
]


# ======================================================================
# ANTI-MARKERS (reduce false positives)
# ======================================================================
# Patterns that, when co-occurring with a keyword, suppress that keyword.

ANTI_MARKERS: List[Tuple[str, str]] = [
    # "integral" in algebraic context (ring extension, not analysis)
    (r"integral\s+(?:closure|extension|element|domain|ring|ideal|over|dependence)",
     "integral (algebraic, not analytic)"),
    # "trace" in algebraic context (trace of matrix/endomorphism)
    (r"trace\s+(?:of\s+(?:a|the)\s+)?(?:matrix|endomorphism|frobenius|operator|map)",
     "trace (algebraic, not trace formula)"),
    # "spectral" in algebraic context (spectral sequence, spectral action on Bernstein center)
    (r"spectral\s+sequence",
     "spectral sequence (algebraic, not spectral decomposition)"),
    (r"spectral\s+(?:action|Bernstein|category)",
     "spectral action (algebraic Spec, not L² spectral)"),
    # "compact" in algebraic context (compact group = profinite)
    (r"compact\s+(?:open|group|subgroup)",
     "compact (algebraic topology, not compactness argument)"),
    # "period" in algebraic context
    (r"period\s+(?:of\s+(?:a|the)\s+)?(?:group|lattice|sequence|orbit)",
     "period (algebraic, not period integral)"),
    # "L-function" without analytic continuation context
    (r"L[\-\s]function.*(?:algebraic\s+part|critical\s+value|interpolation)",
     "L-function (algebraic part only)"),
    # "by contradiction" that is actually just case analysis
    (r"(?:suppose|assume)\s+(?:for\s+)?contradiction.*(?:finite|bounded|integer)",
     "contradiction on discrete/finite object (BISH-eliminable)"),
    # "complete" in algebraic context (complete local ring, complete lattice, etc.)
    (r"complete\s+(?:local|discrete\s+valuation|noetherian|regular)\s+ring",
     "complete (ring-theoretic, not Cauchy completion)"),
    (r"complete\s+(?:lattice|poset|partial\s+order|boolean\s+algebra)",
     "complete (order-theoretic, not Cauchy completion)"),
    # "norm" in algebraic/combinatorial context (norm of integer, norm form, etc.)
    (r"(?:field|galois|reduced)\s+norm",
     "norm (algebraic, not analytic norm)"),
    # "filtration" in algebraic context (weight filtration, Hodge filtration on algebraic object)
    (r"(?:weight|hodge|monodromy)\s+filtration",
     "filtration (algebraic, not norm filtration)"),
    # ≤ c in combinatorial/degree context (degree ≤ n for polynomials)
    (r"(?:degree|dimension|rank|index)\s*\\leq?\s*\d",
     "bounded degree/dimension (combinatorial, not norm cutoff)"),
]


# ======================================================================
# SECTION PATTERN DETECTION
# ======================================================================

SECTION_PATTERN = re.compile(
    r"\\(?:section|subsection|subsubsection|paragraph)\{([^}]+)\}",
    re.IGNORECASE
)

YEAR_PATTERN = re.compile(r"\\date\{.*?(\d{4}).*?\}", re.IGNORECASE)
TITLE_PATTERN = re.compile(r"\\title\{([^}]+)\}", re.IGNORECASE)
AUTHOR_PATTERN = re.compile(r"\\author\{([^}]+)\}", re.IGNORECASE)
CITE_PATTERN = re.compile(r"\\cite[tp]?\{([^}]+)\}")

ARXIV_ID_PATTERN = re.compile(r"(\d{4}\.\d{4,5})")
MSC_PATTERN = re.compile(r"(?:MSC|Mathematics Subject Classification)[:\s]*([\d]+[A-Z]\d+)", re.IGNORECASE)


# ======================================================================
# DATA STRUCTURES
# ======================================================================

@dataclass
class Hit:
    """A single CRM marker detection."""
    level: CRMLevel
    keyword: str
    reason: str
    location: str         # section or line range
    line_num: int
    source: str           # "keyword" or "citation"
    suppressed: bool = False

@dataclass
class PaperProfile:
    """Complete CRM profile of a single paper."""
    filepath: str
    title: str = ""
    authors: str = ""
    year: int = 0
    arxiv_id: str = ""
    msc_codes: List[str] = field(default_factory=list)

    # CRM analysis
    max_level: CRMLevel = CRMLevel.BISH
    bottleneck: str = "none (entirely BISH)"
    bottleneck_location: str = ""
    hits: List[Hit] = field(default_factory=list)
    active_hits: List[Hit] = field(default_factory=list)
    suppressed_hits: List[Hit] = field(default_factory=list)

    # Aggregate counts
    level_counts: Dict[str, int] = field(default_factory=dict)
    total_keywords: int = 0
    total_citations: int = 0

    # Structural
    num_sections: int = 0
    num_theorems: int = 0
    num_lemmas: int = 0
    num_proofs: int = 0
    num_citations: int = 0
    estimated_pages: int = 0


# ======================================================================
# SCANNER ENGINE
# ======================================================================

class CRMScanner:
    """
    Scans LaTeX source for CRM markers using keyword and citation matching.
    """

    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        # Compile keyword patterns
        self.keyword_patterns = [
            (re.compile(pat, re.IGNORECASE), level, reason)
            for pat, level, reason in KEYWORD_MARKERS
        ]
        # Compile anti-marker patterns
        self.anti_patterns = [
            (re.compile(pat, re.IGNORECASE), reason)
            for pat, reason in ANTI_MARKERS
        ]
        # Build citation lookup
        self.citation_lookup = {}
        for author_key, year, level, reason in CITATION_MARKERS:
            self.citation_lookup[(author_key.lower(), year)] = (level, reason)
            if year is not None:
                # Also store without year for partial matching
                if author_key.lower() not in self.citation_lookup:
                    self.citation_lookup[(author_key.lower(), None)] = (level, reason)

    def scan_file(self, filepath: str) -> PaperProfile:
        """Scan a single .tex file and return its CRM profile."""
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            source = f.read()

        profile = PaperProfile(filepath=filepath)
        lines = source.split("\n")

        # --- Extract metadata ---
        self._extract_metadata(source, profile)

        # --- Build section map ---
        section_map = self._build_section_map(lines)

        # --- Structural counts ---
        profile.num_sections = len(re.findall(SECTION_PATTERN, source))
        profile.num_theorems = len(re.findall(r"\\begin\{theorem\}", source, re.IGNORECASE))
        profile.num_lemmas = len(re.findall(r"\\begin\{(?:lemma|proposition|corollary)\}", source, re.IGNORECASE))
        profile.num_proofs = len(re.findall(r"\\begin\{proof\}", source, re.IGNORECASE))
        profile.num_citations = len(re.findall(CITE_PATTERN, source))
        profile.estimated_pages = max(1, len(source) // 3500)  # rough estimate

        # --- Keyword scan ---
        for line_num, line in enumerate(lines, 1):
            # Skip comments
            stripped = line.split("%")[0] if "%" in line else line
            if not stripped.strip():
                continue

            for pattern, level, reason in self.keyword_patterns:
                if pattern.search(stripped):
                    section = self._get_section(line_num, section_map)
                    hit = Hit(
                        level=level,
                        keyword=pattern.pattern,
                        reason=reason,
                        location=section,
                        line_num=line_num,
                        source="keyword",
                    )
                    # Check anti-markers
                    context = self._get_context(lines, line_num, window=2)
                    for anti_pat, anti_reason in self.anti_patterns:
                        if anti_pat.search(context):
                            hit.suppressed = True
                            if self.verbose:
                                print(f"  SUPPRESSED: {reason} <- {anti_reason} (line {line_num})")
                            break

                    profile.hits.append(hit)
                    profile.total_keywords += 1

        # --- Citation scan ---
        for match in CITE_PATTERN.finditer(source):
            cite_keys = [k.strip().lower() for k in match.group(1).split(",")]
            line_num = source[:match.start()].count("\n") + 1
            section = self._get_section(line_num, section_map)

            for key in cite_keys:
                self._check_citation(key, line_num, section, profile)

        # --- Compute results ---
        profile.active_hits = [h for h in profile.hits if not h.suppressed]
        profile.suppressed_hits = [h for h in profile.hits if h.suppressed]

        if profile.active_hits:
            worst = max(profile.active_hits, key=lambda h: h.level)
            profile.max_level = worst.level
            profile.bottleneck = worst.reason
            profile.bottleneck_location = worst.location
        else:
            profile.max_level = CRMLevel.BISH
            profile.bottleneck = "none (entirely BISH)"

        # Level counts
        counts = Counter()
        for h in profile.active_hits:
            counts[str(h.level)] += 1
        profile.level_counts = dict(counts)

        return profile

    def _extract_metadata(self, source: str, profile: PaperProfile):
        """Extract title, author, year, arxiv ID, MSC codes."""
        m = TITLE_PATTERN.search(source)
        if m:
            profile.title = re.sub(r"\\[a-zA-Z]+\{?|\}|\\\\|\$", "", m.group(1)).strip()

        m = AUTHOR_PATTERN.search(source)
        if m:
            profile.authors = re.sub(r"\\[a-zA-Z]+\{?|\}|\\\\|\$", "", m.group(1)).strip()[:100]

        m = YEAR_PATTERN.search(source)
        if m:
            profile.year = int(m.group(1))

        m = ARXIV_ID_PATTERN.search(source)
        if m:
            profile.arxiv_id = m.group(1)

        for m in MSC_PATTERN.finditer(source):
            profile.msc_codes.append(m.group(1))

    def _build_section_map(self, lines: List[str]) -> List[Tuple[int, str]]:
        """Build a map of line numbers to section titles."""
        section_map = []
        for i, line in enumerate(lines, 1):
            m = SECTION_PATTERN.search(line)
            if m:
                title = re.sub(r"\\[a-zA-Z]+\{?|\}", "", m.group(1)).strip()
                section_map.append((i, title))
        return section_map

    def _get_section(self, line_num: int, section_map: List[Tuple[int, str]]) -> str:
        """Get the section name for a given line number."""
        current = "Preamble"
        for sec_line, sec_title in section_map:
            if sec_line <= line_num:
                current = sec_title
            else:
                break
        return current

    def _get_context(self, lines: List[str], line_num: int, window: int = 2) -> str:
        """Get surrounding context for anti-marker checking."""
        start = max(0, line_num - 1 - window)
        end = min(len(lines), line_num + window)
        return " ".join(lines[start:end])

    def _check_citation(self, cite_key: str, line_num: int, section: str,
                        profile: PaperProfile):
        """Check a citation key against the citation dictionary."""
        # Try exact match with known keys
        for (author_key, year), (level, reason) in self.citation_lookup.items():
            if author_key in cite_key:
                hit = Hit(
                    level=level,
                    keyword=f"\\cite{{{cite_key}}}",
                    reason=reason,
                    location=section,
                    line_num=line_num,
                    source="citation",
                )
                profile.hits.append(hit)
                profile.total_citations += 1
                return


# ======================================================================
# REPORT GENERATION
# ======================================================================

def format_paper_report(p: PaperProfile, compact: bool = False) -> str:
    """Format a single paper's CRM profile."""
    if compact:
        title = p.title[:60] if p.title else os.path.basename(p.filepath)
        return (f"{str(p.max_level):6s} | {title:60s} | "
                f"bottleneck: {p.bottleneck[:50]}")

    lines = []
    lines.append("=" * 78)
    title = p.title if p.title else os.path.basename(p.filepath)
    lines.append(f"  {title}")
    if p.authors:
        lines.append(f"  {p.authors}")
    if p.year:
        lines.append(f"  Year: {p.year}")
    lines.append("-" * 78)
    lines.append(f"  CRM Signature:  {p.max_level}")
    lines.append(f"  Bottleneck:     {p.bottleneck}")
    if p.bottleneck_location:
        lines.append(f"  Location:       {p.bottleneck_location}")
    lines.append(f"  Structure:      {p.num_theorems} thm, {p.num_lemmas} lem, "
                 f"{p.num_proofs} proof, {p.num_sections} sec, "
                 f"~{p.estimated_pages} pp, {p.num_citations} cites")

    if p.active_hits:
        lines.append("")
        lines.append("  Active markers (by CRM cost descending):")
        seen = set()
        for h in sorted(p.active_hits, key=lambda x: -x.level):
            sig = (h.reason, h.location)
            if sig in seen:
                continue
            seen.add(sig)
            lines.append(f"    [{h.level:6s}]  {h.reason}")
            lines.append(f"              in: {h.location}  (line {h.line_num})")
            if len(seen) >= 15:
                remaining = len(p.active_hits) - len(seen)
                if remaining > 0:
                    lines.append(f"    ... and {remaining} more markers")
                break

    if p.suppressed_hits:
        lines.append("")
        lines.append(f"  Suppressed (false positive candidates): {len(p.suppressed_hits)}")

    lines.append("=" * 78)
    return "\n".join(lines)


def format_aggregate_report(profiles: List[PaperProfile]) -> str:
    """Format aggregate statistics across all scanned papers."""
    lines = []
    lines.append("")
    lines.append("=" * 78)
    lines.append("  CRMlint Scanner — Aggregate Report")
    lines.append(f"  Papers scanned: {len(profiles)}")
    lines.append("=" * 78)

    # CRM distribution
    level_counts = Counter()
    for p in profiles:
        level_counts[str(p.max_level)] += 1

    lines.append("")
    lines.append("  CRM DISTRIBUTION")
    lines.append("  " + "-" * 40)
    for level in CRMLevel:
        count = level_counts.get(str(level), 0)
        pct = 100.0 * count / len(profiles) if profiles else 0
        bar = "#" * int(pct / 2)
        lines.append(f"  {str(level):6s}  {count:4d}  ({pct:5.1f}%)  {bar}")

    # Top bottlenecks
    bottleneck_counts = Counter()
    for p in profiles:
        if p.max_level > CRMLevel.BISH:
            bottleneck_counts[p.bottleneck] += 1

    if bottleneck_counts:
        lines.append("")
        lines.append("  TOP CLASSICAL BOTTLENECKS")
        lines.append("  " + "-" * 40)
        for reason, count in bottleneck_counts.most_common(15):
            lines.append(f"    {count:3d}x  {reason[:65]}")

    # Domain heatmap (by MSC code prefix)
    msc_levels = defaultdict(list)
    for p in profiles:
        for code in p.msc_codes:
            prefix = code[:2]
            msc_levels[prefix].append(p.max_level)

    if msc_levels:
        lines.append("")
        lines.append("  MSC DOMAIN HEATMAP")
        lines.append("  " + "-" * 40)
        for prefix in sorted(msc_levels.keys()):
            levels = msc_levels[prefix]
            avg = sum(l.value for l in levels) / len(levels)
            max_l = max(levels)
            lines.append(f"    MSC {prefix}xx  n={len(levels):3d}  "
                         f"avg={avg:.2f}  max={max_l}")

    lines.append("")
    lines.append("=" * 78)
    return "\n".join(lines)


def format_temporal_report(profiles: List[PaperProfile]) -> str:
    """Format temporal CRM drift analysis."""
    lines = []
    year_data = defaultdict(list)
    for p in profiles:
        if p.year > 0:
            year_data[p.year].append(p.max_level)

    if not year_data:
        return "  No year data available for temporal analysis."

    lines.append("")
    lines.append("=" * 78)
    lines.append("  CRMlint Scanner — Temporal Drift Analysis")
    lines.append("=" * 78)
    lines.append("")
    lines.append(f"  {'Year':6s}  {'N':4s}  {'Avg CRM':8s}  {'% BISH':7s}  "
                 f"{'% CLASS':8s}  Distribution")
    lines.append("  " + "-" * 65)

    for year in sorted(year_data.keys()):
        levels = year_data[year]
        n = len(levels)
        avg = sum(l.value for l in levels) / n
        pct_bish = 100.0 * sum(1 for l in levels if l == CRMLevel.BISH) / n
        pct_class = 100.0 * sum(1 for l in levels if l == CRMLevel.CLASS) / n

        # Mini histogram
        hist = Counter(str(l) for l in levels)
        dist = " ".join(f"{k}:{v}" for k, v in sorted(hist.items()))

        lines.append(f"  {year:6d}  {n:4d}  {avg:8.2f}  {pct_bish:6.1f}%  "
                     f"{pct_class:7.1f}%  {dist}")

    lines.append("")
    lines.append("=" * 78)
    return "\n".join(lines)


# ======================================================================
# CSV / JSON EXPORT
# ======================================================================

def export_csv(profiles: List[PaperProfile], filepath: str):
    """Export profiles to CSV."""
    with open(filepath, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow([
            "filepath", "title", "authors", "year", "arxiv_id",
            "max_crm_level", "bottleneck", "bottleneck_location",
            "num_active_hits", "num_suppressed",
            "num_theorems", "num_lemmas", "num_proofs",
            "num_sections", "num_citations", "estimated_pages",
        ])
        for p in profiles:
            writer.writerow([
                p.filepath, p.title, p.authors, p.year, p.arxiv_id,
                str(p.max_level), p.bottleneck, p.bottleneck_location,
                len(p.active_hits), len(p.suppressed_hits),
                p.num_theorems, p.num_lemmas, p.num_proofs,
                p.num_sections, p.num_citations, p.estimated_pages,
            ])


def export_json(profiles: List[PaperProfile], filepath: str):
    """Export profiles to JSON."""
    data = []
    for p in profiles:
        d = {
            "filepath": p.filepath,
            "title": p.title,
            "authors": p.authors,
            "year": p.year,
            "arxiv_id": p.arxiv_id,
            "msc_codes": p.msc_codes,
            "max_crm_level": str(p.max_level),
            "max_crm_value": p.max_level.value,
            "bottleneck": p.bottleneck,
            "bottleneck_location": p.bottleneck_location,
            "num_active_hits": len(p.active_hits),
            "num_suppressed": len(p.suppressed_hits),
            "level_counts": p.level_counts,
            "structure": {
                "theorems": p.num_theorems,
                "lemmas": p.num_lemmas,
                "proofs": p.num_proofs,
                "sections": p.num_sections,
                "citations": p.num_citations,
                "estimated_pages": p.estimated_pages,
            },
            "active_hits": [
                {"level": str(h.level), "reason": h.reason,
                 "location": h.location, "line": h.line_num, "source": h.source}
                for h in p.active_hits
            ],
        }
        data.append(d)

    with open(filepath, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


# ======================================================================
# MAIN
# ======================================================================

def collect_tex_files(path: str) -> List[str]:
    """Collect all .tex files from a path (file or directory)."""
    p = Path(path)
    if p.is_file() and p.suffix == ".tex":
        return [str(p)]
    elif p.is_dir():
        return sorted(str(f) for f in p.rglob("*.tex"))
    else:
        print(f"Error: {path} is not a .tex file or directory.")
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser(
        description="CRMlint Scanner: lightweight CRM classifier for LaTeX papers",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python crmlint_scanner.py paper.tex
  python crmlint_scanner.py ./papers/ --compact
  python crmlint_scanner.py ./papers/ --csv results.csv
  python crmlint_scanner.py ./papers/ --json results.json
  python crmlint_scanner.py ./papers/ --temporal
  python crmlint_scanner.py ./papers/ --heatmap
        """,
    )
    parser.add_argument("path", help="Path to .tex file or directory of .tex files")
    parser.add_argument("--compact", action="store_true",
                        help="One-line-per-paper output")
    parser.add_argument("--csv", metavar="FILE",
                        help="Export results to CSV")
    parser.add_argument("--json", metavar="FILE",
                        help="Export results to JSON")
    parser.add_argument("--temporal", action="store_true",
                        help="Show temporal CRM drift analysis")
    parser.add_argument("--heatmap", action="store_true",
                        help="Show MSC domain heatmap only")
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Show suppression details")
    parser.add_argument("--sort", choices=["level", "name", "year", "hits"],
                        default="level",
                        help="Sort order for results (default: level descending)")
    parser.add_argument("--min-level", choices=["BISH", "MP", "LLPO", "WKL", "WLPO", "LPO", "CLASS"],
                        default=None,
                        help="Only show papers at or above this CRM level")

    args = parser.parse_args()

    # Collect files
    tex_files = collect_tex_files(args.path)
    if not tex_files:
        print("No .tex files found.")
        sys.exit(1)

    print(f"CRMlint Scanner v1.0 — scanning {len(tex_files)} file(s)...", file=sys.stderr)

    # Scan
    scanner = CRMScanner(verbose=args.verbose)
    profiles = []
    for filepath in tex_files:
        try:
            p = scanner.scan_file(filepath)
            profiles.append(p)
        except Exception as e:
            print(f"  ERROR scanning {filepath}: {e}", file=sys.stderr)

    # Filter by min level
    if args.min_level:
        min_val = CRMLevel[args.min_level].value
        profiles = [p for p in profiles if p.max_level.value >= min_val]

    # Sort
    if args.sort == "level":
        profiles.sort(key=lambda p: (-p.max_level.value, p.title))
    elif args.sort == "name":
        profiles.sort(key=lambda p: p.title)
    elif args.sort == "year":
        profiles.sort(key=lambda p: (p.year, p.title))
    elif args.sort == "hits":
        profiles.sort(key=lambda p: (-len(p.active_hits), p.title))

    # Output
    if args.compact:
        for p in profiles:
            print(format_paper_report(p, compact=True))
    elif args.temporal:
        print(format_temporal_report(profiles))
    elif args.heatmap:
        print(format_aggregate_report(profiles))
    else:
        for p in profiles:
            print(format_paper_report(p))
        if len(profiles) > 1:
            print(format_aggregate_report(profiles))

    # Export
    if args.csv:
        export_csv(profiles, args.csv)
        print(f"CSV exported to {args.csv}", file=sys.stderr)
    if args.json:
        export_json(profiles, args.json)
        print(f"JSON exported to {args.json}", file=sys.stderr)

    print(f"Done. {len(profiles)} paper(s) profiled.", file=sys.stderr)


if __name__ == "__main__":
    main()
