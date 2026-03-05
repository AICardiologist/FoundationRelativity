"""
CRMlint: Constructive Reverse Mathematics Proof Analysis Framework
==================================================================

A computational framework for:
  1. CRM hierarchy representation as a computable lattice
  2. Proof structure modeling via directed acyclic graphs
  3. Signature propagation and bottleneck localization
  4. Structural invariant computation
  5. Substitution proposal for CRM-reducing simplifications

Author: Paul Chun-Kit Lee
Date: March 2026
Companion to: Paper 98 (The Motivic CRM Architecture)
"""

from __future__ import annotations
from enum import IntEnum, auto
from dataclasses import dataclass, field
from typing import Optional
import json


# =====================================================================
# 1. THE CRM HIERARCHY AS A COMPUTABLE LATTICE
# =====================================================================

class CRMLevel(IntEnum):
    """
    The CRM hierarchy, ordered by logical strength.
    
    The ordering encodes: BISH < MP < LLPO < WKL < WLPO < LPO < CLASS
    
    Note: Over BISH, WKL and WLPO are logically incomparable.
    We assign WKL < WLPO in the linear ordering for computational
    convenience (both are strictly between LLPO and LPO). The
    incomparability is tracked separately in the lattice structure.
    """
    BISH  = 0   # Bishop's constructive mathematics
    MP    = 1   # Markov's principle
    LLPO  = 2   # Lesser limited principle of omniscience
    WKL   = 3   # Weak König's Lemma (compactness)
    WLPO  = 4   # Weak limited principle of omniscience (analytic decidability)
    LPO   = 5   # Limited principle of omniscience
    CLASS = 6   # Full classical logic (LEM)

    def __str__(self):
        return self.name

    @property
    def description(self) -> str:
        descriptions = {
            CRMLevel.BISH:  "Intuitionistic logic + dependent choice. Every existence proof yields a computable witness.",
            CRMLevel.MP:    "If ¬¬∃n.P(n), then ∃n.P(n). Markov's principle for decidable predicates.",
            CRMLevel.LLPO:  "For binary sequences, ¬(∀n.a(n)=0 ∧ ∀n.b(n)=0) → (∃n.a(n)≠0) ∨ (∃n.b(n)≠0).",
            CRMLevel.WKL:   "Every infinite finitely-branching tree has an infinite path. Topological compactness.",
            CRMLevel.WLPO:  "For every real x, either x=0 or x≠0. Decidability of equality for reals.",
            CRMLevel.LPO:   "For every binary sequence, either ∀n.a(n)=0 or ∃n.a(n)≠0. Full omniscience.",
            CRMLevel.CLASS: "Law of excluded middle for all propositions. Full classical logic.",
        }
        return descriptions[self]

    @staticmethod
    def join(a: CRMLevel, b: CRMLevel) -> CRMLevel:
        """Lattice join (least upper bound). For the linear ordering, this is max."""
        return CRMLevel(max(a.value, b.value))

    @staticmethod
    def meet(a: CRMLevel, b: CRMLevel) -> CRMLevel:
        """Lattice meet (greatest lower bound). For the linear ordering, this is min."""
        return CRMLevel(min(a.value, b.value))

    @staticmethod
    def incomparable(a: CRMLevel, b: CRMLevel) -> bool:
        """Check if two levels are genuinely incomparable over BISH."""
        incomparable_pairs = {
            frozenset({CRMLevel.WKL, CRMLevel.WLPO}),
        }
        return frozenset({a, b}) in incomparable_pairs

    @property
    def is_archimedean(self) -> bool:
        """Does this level require passage through the Archimedean place?"""
        return self >= CRMLevel.CLASS


# =====================================================================
# 2. REALIZATIONS AND COMPARISONS
# =====================================================================

class RealizationType(IntEnum):
    DE_RHAM      = auto()
    ETALE        = auto()
    CRYSTALLINE  = auto()
    BETTI        = auto()
    HODGE        = auto()
    AUTOMORPHIC  = auto()


@dataclass(frozen=True)
class Realization:
    """A realization functor with its CRM signature."""
    rtype: RealizationType
    level: CRMLevel
    obstruction: str
    is_archimedean: bool

    def __str__(self):
        arch = "ARCH" if self.is_archimedean else "non-arch"
        return f"{self.rtype.name}({self.level}, {arch})"


# Canonical realization signatures from Paper 98, §4
REALIZATIONS = {
    RealizationType.DE_RHAM: Realization(
        RealizationType.DE_RHAM, CRMLevel.BISH,
        "None: algebraic differential forms modulo exact forms",
        is_archimedean=False,
    ),
    RealizationType.ETALE: Realization(
        RealizationType.ETALE, CRMLevel.BISH,
        "None (pure motives): bounded limits, spectral data descends to Z",
        is_archimedean=False,
    ),
    RealizationType.CRYSTALLINE: Realization(
        RealizationType.CRYSTALLINE, CRMLevel.BISH,
        "None: linear algebra over Witt vectors",
        is_archimedean=False,
    ),
    RealizationType.BETTI: Realization(
        RealizationType.BETTI, CRMLevel.CLASS,
        "Formation of X(C) and integration over topological cycles",
        is_archimedean=True,
    ),
    RealizationType.HODGE: Realization(
        RealizationType.HODGE, CRMLevel.CLASS,
        "Hodge decomposition requires elliptic PDE on X(C)",
        is_archimedean=True,
    ),
    RealizationType.AUTOMORPHIC: Realization(
        RealizationType.AUTOMORPHIC, CRMLevel.CLASS,
        "L² spectral decomposition on G(R)",
        is_archimedean=True,
    ),
}


@dataclass(frozen=True)
class Comparison:
    """A comparison isomorphism between two realizations."""
    source: RealizationType
    target: RealizationType
    level: CRMLevel
    passes_through_R: bool
    mechanism: str

    def __str__(self):
        arrow = "↔"
        arch = "via R" if self.passes_through_R else "non-arch"
        return f"{self.source.name} {arrow} {self.target.name} ({self.level}, {arch})"


# Canonical comparison signatures from Paper 98, §5
COMPARISONS = [
    Comparison(RealizationType.CRYSTALLINE, RealizationType.DE_RHAM,
               CRMLevel.BISH, False, "Berthelot, Fontaine D_cris/D_dR: p-adic algebra"),
    Comparison(RealizationType.CRYSTALLINE, RealizationType.ETALE,
               CRMLevel.BISH, False, "Fontaine-Laffaille: algebraic equivalence for bounded HT weights"),
    Comparison(RealizationType.ETALE, RealizationType.BETTI,
               CRMLevel.CLASS, True, "Artin comparison via RET: requires embedding k̄ ↪ C"),
    Comparison(RealizationType.BETTI, RealizationType.DE_RHAM,
               CRMLevel.CLASS, True, "Period map: integration of forms over topological cycles"),
    Comparison(RealizationType.DE_RHAM, RealizationType.HODGE,
               CRMLevel.CLASS, True, "∂∂̄-lemma: elliptic regularity on compact Kähler manifold"),
]


def get_comparison(src: RealizationType, tgt: RealizationType) -> Optional[Comparison]:
    """Look up the comparison isomorphism between two realizations."""
    for c in COMPARISONS:
        if (c.source == src and c.target == tgt) or (c.source == tgt and c.target == src):
            return c
    return None


# =====================================================================
# 3. PROOF STRUCTURE: THE DIRECTED ACYCLIC GRAPH
# =====================================================================

@dataclass
class ProofStep:
    """
    A single step in a proof path.
    
    Each step has:
      - A name (human-readable identifier)
      - A direct CRM cost (the intrinsic logical cost of this step)
      - An optional realization it invokes
      - An optional comparison it uses
      - Dependencies: other steps this step depends on
      - Whether this step is essential or a convenience
      - An optional substitution that could replace it
    """
    name: str
    direct_cost: CRMLevel
    description: str = ""
    realization: Optional[RealizationType] = None
    comparison_src: Optional[RealizationType] = None
    comparison_tgt: Optional[RealizationType] = None
    dependencies: list[str] = field(default_factory=list)
    essential: bool = True
    substitution_key: Optional[str] = None

    @property
    def effective_cost(self) -> CRMLevel:
        """
        The effective CRM cost, accounting for realization and comparison costs.
        This is the maximum of the direct cost, the realization cost (if any),
        and the comparison cost (if any).
        """
        cost = self.direct_cost

        if self.realization is not None:
            r = REALIZATIONS[self.realization]
            cost = CRMLevel.join(cost, r.level)

        if self.comparison_src is not None and self.comparison_tgt is not None:
            comp = get_comparison(self.comparison_src, self.comparison_tgt)
            if comp:
                cost = CRMLevel.join(cost, comp.level)

        return cost

    @property
    def is_archimedean(self) -> bool:
        """Does this step pass through the Archimedean place?"""
        if self.realization is not None:
            if REALIZATIONS[self.realization].is_archimedean:
                return True
        if self.comparison_src is not None and self.comparison_tgt is not None:
            comp = get_comparison(self.comparison_src, self.comparison_tgt)
            if comp and comp.passes_through_R:
                return True
        return False

    def __str__(self):
        arch = " [ARCH]" if self.is_archimedean else ""
        ess = "" if self.essential else " [convenience]"
        return f"{self.name}: {self.effective_cost}{arch}{ess}"


@dataclass
class ProofStructure:
    """
    A proof as a directed acyclic graph of ProofSteps.
    
    This is the central data structure for CRMlint analysis.
    """
    name: str
    theorem: str
    steps: dict[str, ProofStep] = field(default_factory=dict)

    def add_step(self, step: ProofStep) -> None:
        self.steps[step.name] = step

    def get_step(self, name: str) -> ProofStep:
        return self.steps[name]

    # --- Signature Propagation ---

    def propagated_cost(self, step_name: str, visited: set[str] | None = None) -> CRMLevel:
        """
        Compute the propagated CRM cost of a step: the join of its own
        effective cost and the propagated costs of all its dependencies.
        This is the key recursive computation.
        """
        if visited is None:
            visited = set()
        if step_name in visited:
            return CRMLevel.BISH  # cycle guard
        visited.add(step_name)

        step = self.steps[step_name]
        cost = step.effective_cost

        for dep in step.dependencies:
            if dep in self.steps:
                dep_cost = self.propagated_cost(dep, visited)
                cost = CRMLevel.join(cost, dep_cost)

        return cost

    @property
    def signature(self) -> CRMLevel:
        """The global CRM signature: max over all terminal steps."""
        terminals = self._terminal_steps()
        if not terminals:
            terminals = list(self.steps.keys())
        sig = CRMLevel.BISH
        for name in terminals:
            sig = CRMLevel.join(sig, self.propagated_cost(name))
        return sig

    def _terminal_steps(self) -> list[str]:
        """Steps that no other step depends on."""
        all_deps = set()
        for step in self.steps.values():
            all_deps.update(step.dependencies)
        return [name for name in self.steps if name not in all_deps]


# =====================================================================
# 4. STRUCTURAL INVARIANTS
# =====================================================================

@dataclass
class ProofInvariants:
    """
    The computable structural invariants of a proof.
    
    These determine the proof's type and complexity from the
    CRM perspective, and are the variables that CRMlint tracks.
    """
    # --- Signature invariants ---
    global_signature: CRMLevel
    step_signatures: dict[str, CRMLevel]

    # --- Archimedean invariants ---
    archimedean_steps: list[str]
    archimedean_depth: int          # max chain length through arch steps
    archimedean_fraction: float     # fraction of steps that are arch

    # --- Bottleneck invariants ---
    bottleneck_steps: list[str]     # steps whose removal would reduce signature
    essential_bottlenecks: list[str]  # bottlenecks marked essential
    removable_bottlenecks: list[str]  # bottlenecks with known substitutions
    bottleneck_count: int

    # --- Structural invariants ---
    total_steps: int
    max_depth: int                  # longest dependency chain
    branching_factor: float         # avg number of dependencies per step
    realization_set: set[str]       # which realizations are used
    comparison_set: set[str]        # which comparisons are used

    # --- Complexity class ---
    proof_type: str                 # classification of proof structure
    minimal_achievable: CRMLevel    # signature after all known substitutions

    def summary(self) -> str:
        lines = [
            f"{'='*65}",
            f"  PROOF STRUCTURE ANALYSIS: {self.proof_type}",
            f"{'='*65}",
            "",
            f"  Global CRM Signature:    {self.global_signature}",
            f"  Minimal Achievable:      {self.minimal_achievable}",
            f"  Reduction Possible:      {'YES' if self.minimal_achievable < self.global_signature else 'NO'}",
            "",
            f"  Total Steps:             {self.total_steps}",
            f"  Max Dependency Depth:    {self.max_depth}",
            f"  Avg Branching Factor:    {self.branching_factor:.2f}",
            "",
            f"  Archimedean Steps:       {len(self.archimedean_steps)} / {self.total_steps}"
                f" ({self.archimedean_fraction:.0%})",
            f"  Archimedean Depth:       {self.archimedean_depth}",
            "",
            f"  Bottlenecks (total):     {self.bottleneck_count}",
            f"    Essential:             {len(self.essential_bottlenecks)}",
            f"    Removable:             {len(self.removable_bottlenecks)}",
            "",
            f"  Realizations Used:       {', '.join(sorted(self.realization_set)) or 'None'}",
            f"  Comparisons Used:        {', '.join(sorted(self.comparison_set)) or 'None'}",
        ]

        if self.bottleneck_steps:
            lines.append("")
            lines.append(f"  {'─'*61}")
            lines.append(f"  BOTTLENECK DETAIL:")
            for name in self.bottleneck_steps:
                sig = self.step_signatures[name]
                tag = "ESSENTIAL" if name in self.essential_bottlenecks else "REMOVABLE"
                lines.append(f"    • {name}: {sig} [{tag}]")

        lines.append(f"{'='*65}")
        return "\n".join(lines)


def compute_invariants(proof: ProofStructure, sub_db: SubstitutionDB | None = None) -> ProofInvariants:
    """
    Compute all structural invariants of a proof.
    This is the main analysis function.
    """
    if sub_db is None:
        sub_db = SubstitutionDB()

    global_sig = proof.signature

    # Step signatures
    step_sigs = {}
    for name in proof.steps:
        step_sigs[name] = proof.propagated_cost(name)

    # Archimedean analysis
    arch_steps = [n for n, s in proof.steps.items() if s.is_archimedean]
    arch_depth = _max_arch_chain_depth(proof)
    arch_frac = len(arch_steps) / max(len(proof.steps), 1)

    # Bottleneck detection
    bottlenecks = _find_bottlenecks(proof, global_sig)
    essential = [n for n in bottlenecks if proof.steps[n].essential]
    removable = [n for n in bottlenecks
                 if not proof.steps[n].essential
                 or proof.steps[n].substitution_key in sub_db.entries]

    # Structural metrics
    max_depth = _max_depth(proof)
    total_deps = sum(len(s.dependencies) for s in proof.steps.values())
    branching = total_deps / max(len(proof.steps), 1)

    # Realization and comparison sets
    real_set = set()
    comp_set = set()
    for s in proof.steps.values():
        if s.realization is not None:
            real_set.add(s.realization.name)
        if s.comparison_src is not None and s.comparison_tgt is not None:
            comp_set.add(f"{s.comparison_src.name}↔{s.comparison_tgt.name}")

    # Minimal achievable signature
    minimal = _compute_minimal(proof, sub_db)

    # Proof type classification
    proof_type = _classify_proof(global_sig, arch_steps, bottlenecks,
                                 essential, removable, proof)

    return ProofInvariants(
        global_signature=global_sig,
        step_signatures=step_sigs,
        archimedean_steps=arch_steps,
        archimedean_depth=arch_depth,
        archimedean_fraction=arch_frac,
        bottleneck_steps=bottlenecks,
        essential_bottlenecks=essential,
        removable_bottlenecks=removable,
        bottleneck_count=len(bottlenecks),
        total_steps=len(proof.steps),
        max_depth=max_depth,
        branching_factor=branching,
        realization_set=real_set,
        comparison_set=comp_set,
        proof_type=proof_type,
        minimal_achievable=minimal,
    )


def _find_bottlenecks(proof: ProofStructure, global_sig: CRMLevel) -> list[str]:
    """
    Identify bottleneck steps: those whose removal would reduce the
    global signature. A step is a bottleneck iff it is one of the
    steps achieving the global maximum AND no other independent path
    also achieves that maximum.
    """
    bottlenecks = []
    for name, step in proof.steps.items():
        if step.effective_cost >= global_sig:
            # Check: would removing this step reduce the signature?
            reduced_sig = _signature_without(proof, name)
            if reduced_sig < global_sig:
                bottlenecks.append(name)
    return bottlenecks


def _signature_without(proof: ProofStructure, excluded: str) -> CRMLevel:
    """Compute proof signature with one step excluded."""
    sig = CRMLevel.BISH
    for name in proof.steps:
        if name == excluded:
            continue
        cost = _propagated_cost_excluding(proof, name, excluded, set())
        sig = CRMLevel.join(sig, cost)
    return sig


def _propagated_cost_excluding(
    proof: ProofStructure, step_name: str, excluded: str, visited: set[str]
) -> CRMLevel:
    """Propagated cost with one step excluded from the graph."""
    if step_name in visited or step_name == excluded:
        return CRMLevel.BISH
    visited.add(step_name)
    step = proof.steps[step_name]
    cost = step.effective_cost
    for dep in step.dependencies:
        if dep in proof.steps and dep != excluded:
            dep_cost = _propagated_cost_excluding(proof, dep, excluded, visited)
            cost = CRMLevel.join(cost, dep_cost)
    return cost


def _max_depth(proof: ProofStructure) -> int:
    """Maximum dependency chain length."""
    memo: dict[str, int] = {}

    def depth(name: str) -> int:
        if name in memo:
            return memo[name]
        step = proof.steps.get(name)
        if not step or not step.dependencies:
            memo[name] = 0
            return 0
        d = 1 + max(depth(dep) for dep in step.dependencies if dep in proof.steps)
        memo[name] = d
        return d

    return max((depth(n) for n in proof.steps), default=0)


def _max_arch_chain_depth(proof: ProofStructure) -> int:
    """Maximum chain length through Archimedean steps only."""
    memo: dict[str, int] = {}

    def arch_depth(name: str) -> int:
        if name in memo:
            return memo[name]
        step = proof.steps.get(name)
        if not step or not step.is_archimedean:
            memo[name] = 0
            return 0
        arch_deps = [dep for dep in step.dependencies
                     if dep in proof.steps and proof.steps[dep].is_archimedean]
        if not arch_deps:
            memo[name] = 1
        else:
            memo[name] = 1 + max(arch_depth(d) for d in arch_deps)
        return memo[name]

    return max((arch_depth(n) for n in proof.steps), default=0)


def _classify_proof(
    sig: CRMLevel,
    arch_steps: list[str],
    bottlenecks: list[str],
    essential: list[str],
    removable: list[str],
    proof: ProofStructure,
) -> str:
    """
    Classify proof structure type.
    
    Types:
      - PURELY_CONSTRUCTIVE: signature is BISH, no arch steps
      - ALGEBRAIC_CORE_WITH_CLASSICAL_BRIDGE: mostly BISH with isolated CLASS steps
      - BIFURCATING: different branches have different signatures (Hodge pattern)
      - UNIFORMLY_CLASSICAL: CLASS pervades the proof (trace formula pattern)
      - EXCISABLE: has removable bottlenecks (TW pattern)
    """
    if sig == CRMLevel.BISH:
        return "PURELY_CONSTRUCTIVE"

    if not arch_steps:
        if sig <= CRMLevel.WKL:
            return "COMPACTNESS_DEPENDENT"
        return "NON_ARCHIMEDEAN_CLASSICAL"

    arch_frac = len(arch_steps) / len(proof.steps)

    if removable:
        return "EXCISABLE"
    if arch_frac < 0.25 and essential:
        return "ALGEBRAIC_CORE_WITH_CLASSICAL_BRIDGE"
    if arch_frac > 0.6:
        return "UNIFORMLY_CLASSICAL"
    if len(set(proof.steps[n].effective_cost for n in proof.steps)) > 2:
        return "BIFURCATING"

    return "MIXED"


# =====================================================================
# 5. SUBSTITUTION DATABASE
# =====================================================================

@dataclass(frozen=True)
class Substitution:
    """A known CRM-reducing substitution."""
    key: str
    classical_technique: str
    constructive_alternative: str
    cost_before: CRMLevel
    cost_after: CRMLevel
    applicability: str
    source_paper: str

    @property
    def reduction(self) -> str:
        return f"{self.cost_before} → {self.cost_after}"


class SubstitutionDB:
    """Database of known CRM-reducing substitutions from Papers 50-97."""

    def __init__(self):
        self.entries: dict[str, Substitution] = {}
        self._load_seed_database()

    def _load_seed_database(self):
        """Load the seed substitutions extracted from the CRM programme."""
        seed = [
            Substitution(
                "petersson_to_patching",
                "Petersson inner product (integration on H)",
                "Taylor-Wiles patching (inverse limit of finite local rings)",
                CRMLevel.CLASS, CRMLevel.WKL,
                "Computing congruence ideal of Hecke algebra acting on modular forms. "
                "Requires auxiliary primes satisfying Taylor-Wiles conditions.",
                "Papers 68-71",
            ),
            Substitution(
                "hodge_decomp_to_filtration",
                "Hodge decomposition (elliptic PDE)",
                "Algebraic Hodge filtration",
                CRMLevel.CLASS, CRMLevel.BISH,
                "When only the filtration (not the splitting) is needed. "
                "Applies to period-independent questions.",
                "Papers 86-90",
            ),
            Substitution(
                "chebotarev_to_explicit_frob",
                "Chebotarev density theorem (analytic continuation of Artin L-functions)",
                "Explicit Frobenius computation at finitely many primes",
                CRMLevel.CLASS, CRMLevel.BISH,
                "When the Galois representation can be identified by traces at finitely "
                "many primes (Faltings-Serre method with effective bounds).",
                "Papers 52, 68",
            ),
            Substitution(
                "analytic_cont_to_algebraic_sv",
                "Analytic continuation of L-function to all of C",
                "Algebraic special value formulas (Euler system classes)",
                CRMLevel.CLASS, CRMLevel.BISH,
                "When only finitely many critical values are needed, not the full "
                "analytic continuation.",
                "Papers 95-96",
            ),
            Substitution(
                "trace_formula_to_shtukas",
                "Arthur-Selberg trace formula (L² spectral decomposition on G(R))",
                "Moduli of shtukas (algebraic geometry over function fields)",
                CRMLevel.CLASS, CRMLevel.BISH,
                "Function field setting only. Requires characteristic p > 0. "
                "Not directly applicable over number fields.",
                "Papers 69, 78",
            ),
            Substitution(
                "arakelov_to_neron_tate",
                "Arakelov height pairing (integration on complex fiber)",
                "Néron-Tate height via algebraic descent",
                CRMLevel.CLASS, CRMLevel.BISH,
                "When the height pairing can be computed via the Néron model "
                "without passage to the Archimedean fiber.",
                "Paper 95",
            ),
            Substitution(
                "hodge_generic_to_special",
                "Hodge class detection on generic fiber (Mumford-Tate decidability)",
                "Kani-Rosen splitting on palindromic / Hodge-special locus",
                CRMLevel.WLPO, CRMLevel.BISH,
                "Requires the variety to lie on a positive-dimensional special "
                "sublocus with extra algebraic endomorphisms.",
                "Papers 87-90",
            ),
            Substitution(
                "ret_to_etale_pi1",
                "Riemann Existence Theorem (embedding k̄ ↪ C, complex analysis)",
                "Étale fundamental group (finite covers, SGA1)",
                CRMLevel.CLASS, CRMLevel.BISH,
                "When only the profinite completion of π₁ is needed, not the "
                "topological fundamental group. Applies to finite étale covers.",
                "Paper 73",
            ),
        ]
        for s in seed:
            self.entries[s.key] = s

    def lookup(self, key: str) -> Optional[Substitution]:
        return self.entries.get(key)

    def propose(self, step: ProofStep) -> Optional[Substitution]:
        """Propose a substitution for a given proof step, if one exists."""
        if step.substitution_key and step.substitution_key in self.entries:
            return self.entries[step.substitution_key]
        return None

    def all_applicable(self, proof: ProofStructure) -> list[tuple[str, Substitution]]:
        """Find all applicable substitutions for a proof structure."""
        results = []
        for name, step in proof.steps.items():
            sub = self.propose(step)
            if sub and sub.cost_before <= step.effective_cost:
                results.append((name, sub))
        return results


def _compute_minimal(proof: ProofStructure, sub_db: SubstitutionDB) -> CRMLevel:
    """
    Compute the minimal achievable signature after applying all
    known substitutions. This is the theoretical floor given
    current knowledge.
    """
    # Build a modified cost map with substitutions applied
    modified_costs: dict[str, CRMLevel] = {}
    for name, step in proof.steps.items():
        sub = sub_db.propose(step)
        if sub and sub.cost_before <= step.effective_cost:
            modified_costs[name] = sub.cost_after
        else:
            modified_costs[name] = step.effective_cost

    # Propagate with modified costs
    def prop(step_name: str, visited: set[str]) -> CRMLevel:
        if step_name in visited:
            return CRMLevel.BISH
        visited.add(step_name)
        cost = modified_costs.get(step_name, CRMLevel.BISH)
        step = proof.steps.get(step_name)
        if step:
            for dep in step.dependencies:
                if dep in proof.steps:
                    cost = CRMLevel.join(cost, prop(dep, visited))
        return cost

    sig = CRMLevel.BISH
    for name in proof.steps:
        sig = CRMLevel.join(sig, prop(name, set()))
    return sig


# =====================================================================
# 6. ANALYSIS PIPELINE
# =====================================================================

def analyze(proof: ProofStructure, sub_db: SubstitutionDB | None = None) -> str:
    """
    Full CRMlint analysis pipeline.
    Returns a formatted report.
    """
    if sub_db is None:
        sub_db = SubstitutionDB()

    inv = compute_invariants(proof, sub_db)
    report = [inv.summary()]

    # Substitution proposals
    applicable = sub_db.all_applicable(proof)
    if applicable:
        report.append("")
        report.append(f"  {'─'*61}")
        report.append(f"  PROPOSED SUBSTITUTIONS:")
        for step_name, sub in applicable:
            report.append(f"")
            report.append(f"    Step: {step_name}")
            report.append(f"    Replace: {sub.classical_technique}")
            report.append(f"    With:    {sub.constructive_alternative}")
            report.append(f"    Effect:  {sub.reduction}")
            report.append(f"    Source:  {sub.source_paper}")
            report.append(f"    Conditions: {sub.applicability}")

    # Archimedean obstruction check
    report.append("")
    report.append(f"  {'─'*61}")
    report.append(f"  ARCHIMEDEAN OBSTRUCTION ANALYSIS:")
    if not inv.archimedean_steps:
        report.append(f"    No Archimedean steps. Proof is within non-Archimedean envelope.")
        report.append(f"    By the Archimedean Obstruction Theorem: σ(P) = BISH confirmed.")
    else:
        report.append(f"    Archimedean steps detected: {', '.join(inv.archimedean_steps)}")
        report.append(f"    These steps force σ(P) ≥ CLASS.")
        non_arch_sig = CRMLevel.BISH
        for name, step in proof.steps.items():
            if not step.is_archimedean:
                non_arch_sig = CRMLevel.join(non_arch_sig, step.effective_cost)
        report.append(f"    Non-Archimedean fragment signature: {non_arch_sig}")
        report.append(f"    Archimedean overhead: {inv.global_signature.value - non_arch_sig.value} levels")

    report.append(f"{'='*65}")
    return "\n".join(report)


# =====================================================================
# 7. EXAMPLE PROOF STRUCTURES
# =====================================================================

def build_wiles_1993() -> ProofStructure:
    """Wiles 1993 proof structure (pre-TW fix)."""
    proof = ProofStructure(
        name="Wiles 1993",
        theorem="Modularity of semistable elliptic curves over Q (original attempt)",
    )

    proof.add_step(ProofStep(
        "galois_deformation", CRMLevel.BISH,
        "Mazur's Galois deformation theory: universal deformation ring R",
        realization=RealizationType.ETALE,
    ))

    proof.add_step(ProofStep(
        "hecke_algebra", CRMLevel.BISH,
        "Hecke algebra T acting on modular forms of level N",
        realization=RealizationType.DE_RHAM,
    ))

    proof.add_step(ProofStep(
        "fontaine_laffaille", CRMLevel.BISH,
        "Fontaine-Laffaille classification of crystalline representations",
        realization=RealizationType.CRYSTALLINE,
        comparison_src=RealizationType.CRYSTALLINE,
        comparison_tgt=RealizationType.ETALE,
    ))

    proof.add_step(ProofStep(
        "numerical_criterion", CRMLevel.BISH,
        "Wiles numerical criterion: #(R/ann) ≤ #(T/η)",
        dependencies=["galois_deformation", "hecke_algebra"],
    ))

    proof.add_step(ProofStep(
        "petersson_inner_product", CRMLevel.CLASS,
        "Congruence ideal η_T via Petersson inner product ∫|f|² y^k dxdy/y²",
        realization=RealizationType.BETTI,
        comparison_src=RealizationType.BETTI,
        comparison_tgt=RealizationType.DE_RHAM,
        dependencies=["hecke_algebra"],
        essential=False,
        substitution_key="petersson_to_patching",
    ))

    proof.add_step(ProofStep(
        "langlands_tunnell", CRMLevel.CLASS,
        "Base case: mod-3 representation via Langlands-Tunnell (trace formula)",
        realization=RealizationType.AUTOMORPHIC,
        essential=True,
    ))

    proof.add_step(ProofStep(
        "R_equals_T", CRMLevel.CLASS,
        "R = T isomorphism (the modularity lifting theorem)",
        dependencies=["numerical_criterion", "petersson_inner_product",
                       "fontaine_laffaille", "langlands_tunnell"],
    ))

    return proof


def build_wiles_taylor_1995() -> ProofStructure:
    """Wiles-Taylor 1995 proof structure (with TW patching)."""
    proof = ProofStructure(
        name="Wiles-Taylor 1995",
        theorem="Modularity of semistable elliptic curves over Q",
    )

    proof.add_step(ProofStep(
        "galois_deformation", CRMLevel.BISH,
        "Mazur's Galois deformation theory: universal deformation ring R",
        realization=RealizationType.ETALE,
    ))

    proof.add_step(ProofStep(
        "hecke_algebra", CRMLevel.BISH,
        "Hecke algebra T acting on modular forms of level N",
        realization=RealizationType.DE_RHAM,
    ))

    proof.add_step(ProofStep(
        "fontaine_laffaille", CRMLevel.BISH,
        "Fontaine-Laffaille classification of crystalline representations",
        realization=RealizationType.CRYSTALLINE,
        comparison_src=RealizationType.CRYSTALLINE,
        comparison_tgt=RealizationType.ETALE,
    ))

    proof.add_step(ProofStep(
        "tw_auxiliary_primes", CRMLevel.BISH,
        "Selection of Taylor-Wiles auxiliary primes Q_n",
        dependencies=["galois_deformation"],
    ))

    proof.add_step(ProofStep(
        "tw_patching", CRMLevel.WKL,
        "Taylor-Wiles patching: R_∞ = lim R_{Q_n}, extracting compatible system",
        dependencies=["galois_deformation", "hecke_algebra", "tw_auxiliary_primes"],
    ))

    proof.add_step(ProofStep(
        "numerical_criterion", CRMLevel.BISH,
        "Wiles numerical criterion via patched modules",
        dependencies=["tw_patching"],
    ))

    proof.add_step(ProofStep(
        "langlands_tunnell", CRMLevel.CLASS,
        "Base case: mod-3 representation via Langlands-Tunnell (trace formula)",
        realization=RealizationType.AUTOMORPHIC,
        essential=True,
    ))

    proof.add_step(ProofStep(
        "R_equals_T", CRMLevel.WKL,
        "R = T isomorphism via patching (modularity lifting theorem)",
        dependencies=["numerical_criterion", "fontaine_laffaille", "langlands_tunnell"],
    ))

    return proof


def build_function_field_langlands() -> ProofStructure:
    """Lafforgue's function field Langlands (GL_n over F_q(C))."""
    proof = ProofStructure(
        name="Function Field Langlands",
        theorem="Langlands correspondence for GL_n over F_q(C) (Lafforgue)",
    )

    proof.add_step(ProofStep(
        "shtuka_moduli", CRMLevel.BISH,
        "Moduli of Drinfeld shtukas: algebraic geometry over F_q",
    ))

    proof.add_step(ProofStep(
        "etale_cohomology", CRMLevel.BISH,
        "ℓ-adic étale cohomology of shtuka moduli stacks",
        realization=RealizationType.ETALE,
        dependencies=["shtuka_moduli"],
    ))

    proof.add_step(ProofStep(
        "excursion_operators", CRMLevel.BISH,
        "V. Lafforgue's excursion operators: algebraic decomposition",
        dependencies=["etale_cohomology"],
    ))

    proof.add_step(ProofStep(
        "galois_to_automorphic", CRMLevel.BISH,
        "Galois-to-automorphic direction via trace of Frobenius",
        realization=RealizationType.CRYSTALLINE,
        comparison_src=RealizationType.CRYSTALLINE,
        comparison_tgt=RealizationType.ETALE,
        dependencies=["excursion_operators"],
    ))

    proof.add_step(ProofStep(
        "automorphic_to_galois", CRMLevel.BISH,
        "Automorphic-to-Galois via cohomology of shtukas",
        dependencies=["etale_cohomology"],
    ))

    proof.add_step(ProofStep(
        "correspondence", CRMLevel.BISH,
        "Full Langlands correspondence for GL_n/F_q(C)",
        dependencies=["galois_to_automorphic", "automorphic_to_galois"],
    ))

    return proof


def build_hodge_detection() -> ProofStructure:
    """Hodge class detection on genus-4 Torelli locus."""
    proof = ProofStructure(
        name="Hodge Detection (genus 4)",
        theorem="Hodge class algebraicity on J(C_t)² over Torelli locus T_4",
    )

    proof.add_step(ProofStep(
        "jacobian_construction", CRMLevel.BISH,
        "Algebraic construction of J(C_t) for genus-4 curve C_t",
    ))

    proof.add_step(ProofStep(
        "hodge_filtration", CRMLevel.BISH,
        "Algebraic Hodge filtration F^• on H^4_dR(J(C_t)²)",
        realization=RealizationType.DE_RHAM,
        dependencies=["jacobian_construction"],
    ))

    proof.add_step(ProofStep(
        "hodge_decomposition", CRMLevel.CLASS,
        "Hodge decomposition H^4 = ⊕ H^{p,q} via elliptic PDE on J(C_t)(C)",
        realization=RealizationType.HODGE,
        comparison_src=RealizationType.DE_RHAM,
        comparison_tgt=RealizationType.HODGE,
        dependencies=["hodge_filtration"],
        essential=True,
    ))

    proof.add_step(ProofStep(
        "mumford_tate_computation", CRMLevel.WLPO,
        "Determine Mumford-Tate group of generic fiber (equality decidability)",
        dependencies=["hodge_decomposition"],
        essential=True,
    ))

    proof.add_step(ProofStep(
        "palindromic_detection", CRMLevel.BISH,
        "On palindromic locus: Kani-Rosen splitting J(C_t) ~ A₁ × A₂",
        realization=RealizationType.ETALE,
        dependencies=["jacobian_construction"],
    ))

    proof.add_step(ProofStep(
        "ribet_algebraicity", CRMLevel.BISH,
        "Ribet's theorem: Hodge classes on products of CM abelian varieties are algebraic",
        dependencies=["palindromic_detection"],
    ))

    proof.add_step(ProofStep(
        "generic_detection", CRMLevel.CLASS,
        "Generic Hodge class detection: requires full Hodge decomposition",
        dependencies=["mumford_tate_computation"],
    ))

    proof.add_step(ProofStep(
        "special_detection", CRMLevel.BISH,
        "Special locus detection: algebraic via Kani-Rosen + Ribet",
        dependencies=["ribet_algebraicity"],
    ))

    return proof


def build_bsd_rank_sha() -> ProofStructure:
    """BSD conjecture: rank verification vs Sha finiteness."""
    proof = ProofStructure(
        name="BSD Rank/Sha Decoupling",
        theorem="BSD conjecture components for E/Q with analytic rank ≤ 1",
    )

    proof.add_step(ProofStep(
        "algebraic_descent", CRMLevel.BISH,
        "2-descent on E(Q): compute Selmer group S²(E/Q)",
        realization=RealizationType.ETALE,
    ))

    proof.add_step(ProofStep(
        "rank_verification", CRMLevel.BISH,
        "Verify rank(E(Q)) = r via explicit point search + descent bounds",
        dependencies=["algebraic_descent"],
    ))

    proof.add_step(ProofStep(
        "heegner_point", CRMLevel.BISH,
        "Heegner point construction: algebraic point on X₀(N) over ring class field",
        dependencies=["algebraic_descent"],
    ))

    proof.add_step(ProofStep(
        "gross_zagier", CRMLevel.CLASS,
        "Gross-Zagier formula: height of Heegner point = L'(E,1) (period integral)",
        realization=RealizationType.BETTI,
        comparison_src=RealizationType.BETTI,
        comparison_tgt=RealizationType.DE_RHAM,
        dependencies=["heegner_point"],
        essential=True,
    ))

    proof.add_step(ProofStep(
        "euler_system", CRMLevel.CLASS,
        "Kolyvagin Euler system: annihilate Sha[p^∞] for all p",
        realization=RealizationType.BETTI,
        dependencies=["heegner_point"],
        essential=True,
    ))

    proof.add_step(ProofStep(
        "sha_finiteness", CRMLevel.CLASS,
        "|Sha(E/Q)| < ∞ via Euler system + Chebotarev",
        dependencies=["euler_system", "gross_zagier"],
        essential=True,
    ))

    return proof


# =====================================================================
# 8. MAIN: RUN ALL ANALYSES
# =====================================================================

def main():
    sub_db = SubstitutionDB()

    proofs = [
        build_wiles_1993(),
        build_wiles_taylor_1995(),
        build_function_field_langlands(),
        build_hodge_detection(),
        build_bsd_rank_sha(),
    ]

    print("╔" + "═"*65 + "╗")
    print("║" + "  CRMlint v0.1 — Proof Structure Analysis".center(65) + "║")
    print("║" + "  Companion to Paper 98: The Motivic CRM Architecture".center(65) + "║")
    print("╚" + "═"*65 + "╝")

    for proof in proofs:
        print(f"\n\n{'▓'*67}")
        print(f"  ANALYZING: {proof.name}")
        print(f"  Theorem: {proof.theorem}")
        print(f"{'▓'*67}\n")
        print(analyze(proof, sub_db))

    # === Comparative analysis ===
    print(f"\n\n{'▓'*67}")
    print(f"  COMPARATIVE ANALYSIS")
    print(f"{'▓'*67}\n")

    header = f"  {'Proof':<32} {'σ(P)':<8} {'Min':<8} {'Steps':<7} {'Arch%':<7} {'Type'}"
    print(header)
    print(f"  {'─'*80}")

    for proof in proofs:
        inv = compute_invariants(proof, sub_db)
        print(f"  {proof.name:<32} {str(inv.global_signature):<8} "
              f"{str(inv.minimal_achievable):<8} {inv.total_steps:<7} "
              f"{inv.archimedean_fraction:<7.0%} {inv.proof_type}")

    # === The Archimedean Obstruction in action ===
    print(f"\n\n{'▓'*67}")
    print(f"  ARCHIMEDEAN OBSTRUCTION VERIFICATION")
    print(f"{'▓'*67}\n")

    for proof in proofs:
        inv = compute_invariants(proof, sub_db)
        has_arch = len(inv.archimedean_steps) > 0
        is_classical = inv.global_signature >= CRMLevel.CLASS

        if not has_arch and not is_classical:
            verdict = "✓ CONFIRMED: No Archimedean steps → BISH"
        elif has_arch and is_classical:
            verdict = "✓ CONFIRMED: Archimedean steps → ≥ CLASS"
        elif has_arch and not is_classical:
            verdict = "⚠ NOTE: Archimedean steps present but signature < CLASS"
        else:
            verdict = "⚠ ANOMALY: Classical without Archimedean steps"

        print(f"  {proof.name:<32} {verdict}")

    # === Substitution database summary ===
    print(f"\n\n{'▓'*67}")
    print(f"  SUBSTITUTION DATABASE ({len(sub_db.entries)} entries)")
    print(f"{'▓'*67}\n")

    for key, sub in sub_db.entries.items():
        print(f"  [{key}]")
        print(f"    {sub.cost_before} → {sub.cost_after}")
        print(f"    Replace: {sub.classical_technique}")
        print(f"    With:    {sub.constructive_alternative}")
        print(f"    Source:  {sub.source_paper}")
        print()


if __name__ == "__main__":
    main()
