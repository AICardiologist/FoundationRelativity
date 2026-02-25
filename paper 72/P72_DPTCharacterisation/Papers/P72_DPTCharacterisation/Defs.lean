/-
  Paper 72: The DPT Characterisation Theorem — Definitions
  Extends Paper 70 infrastructure with axiomatised height-pairing costs.

  Key distinction (missed in v1):
  - Rep_ℚ(G) is trivially BISH-decidable for ANY G (morphisms are ℚ-matrices).
  - The motivic question is cycle-SEARCH decidability: can you bound the
    search for algebraic cycles using the height pairing?
  - Positive-definite height → Northcott → bounded search → BISH.
  - Indefinite height → no Northcott → unbounded search → LPO.

  Design (v3): Each mathematical component is axiomatised (Paper 69 pattern).
  The assembly function `cycle_search_cost` maps HeightType to opaque values,
  forcing proofs to invoke the axioms rather than unfolding definitions.

  References: Paper 50 (DPT axioms), Paper 51 (BSD Archimedean rescue),
    Paper 61 (Lang's conjecture as MP→BISH gate), Paper 70.
-/
import Mathlib.Order.Defs.PartialOrder

-- ============================================================
-- CRM Hierarchy (from Paper 70)
-- ============================================================

inductive CRMLevel : Type where
  | BISH    : CRMLevel
  | BISH_MP : CRMLevel
  | LLPO    : CRMLevel
  | WLPO    : CRMLevel
  | LPO     : CRMLevel
  | CLASS   : CRMLevel
  deriving DecidableEq, Repr

open CRMLevel

/-- Explicit ordinal for the CRM hierarchy (avoids internal .ctorIdx). -/
def CRMLevel.toNat : CRMLevel → Nat
  | BISH    => 0
  | BISH_MP => 1
  | LLPO    => 2
  | WLPO    => 3
  | LPO     => 4
  | CLASS   => 5

instance : LE CRMLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT CRMLevel where
  lt a b := a.toNat < b.toNat

instance (a b : CRMLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance (a b : CRMLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

def CRMLevel.join (a b : CRMLevel) : CRMLevel :=
  if a.toNat ≥ b.toNat then a else b

-- ============================================================
-- DPT Axioms (from Paper 50)
-- ============================================================

structure DPTAxioms where
  decidable_morphisms : Prop      -- A1: Standard Conjecture D
  algebraic_spectrum : Prop       -- A2: eigenvalues in Q̄
  archimedean_polarisation : Prop -- A3: positive-definite over ℝ

-- ============================================================
-- Height Pairing Classification
-- ============================================================

/-- Height pairing type on a lattice of algebraic cycles.
    Positive-definite: ⟨Z,Z⟩ > 0 for non-torsion Z.
    Indefinite: ∃ non-torsion Z with ⟨Z,Z⟩ = 0.
    Reference: Néron-Tate (Paper 48/51), Hodge-Riemann (Paper 49),
    Rosati involution (Paper 50). -/
inductive HeightType : Type where
  | positive_definite : HeightType  -- Axiom 3 holds
  | indefinite        : HeightType  -- Axiom 3 fails (e.g., p-adic)
  deriving DecidableEq, Repr

open HeightType

/-- Northcott property: {Z : h(Z,Z) ≤ B} is finite for any bound B.
    This is the bridge between positive-definiteness and decidability.
    Reference: Northcott (1950); Lang, Fundamentals of Diophantine
    Geometry (1983), Ch. 3. -/
def has_northcott : HeightType → Bool
  | positive_definite => true
  | indefinite        => false

-- ============================================================
-- Axiomatised Cycle-Search Costs (Paper 69 pattern)
-- ============================================================

/-- CRM cost of cycle-search with positive-definite height pairing.
    Northcott's theorem (1950): {P ∈ Λ : h(P) ≤ B} is finite.
    Consequence: enumerate candidates up to height B, test each,
    halt in bounded time. Pure BISH — no omniscience, no unbounded search.
    This is the mechanism in Paper 51 (BSD via Silverman bound)
    and Paper 61 (Lang's conjecture as MP→BISH gate).
    Reference: Northcott (1950), Silverman AEC VIII.9.3,
    Paper 51 §3 (searchGrid construction). -/
axiom northcott_search_cost : CRMLevel
axiom northcott_search_cost_eq : northcott_search_cost = BISH

/-- CRM cost of cycle-search with indefinite height pairing.
    Northcott fails: the null cone {P : h(P) = 0} is infinite, and
    non-torsion points accumulate with zero height.

    Two LPO entry points (both established in earlier papers):
    (1) L-function zero-test: deciding L(E,1) = 0 is a real number
        equality test, which costs LPO (Paper 48, Theorem B1).
    (2) Unbounded generator search: without Northcott, the finiteness
        of {P : h(P) ≤ B} fails, so no finite grid contains all
        candidates. The search for Mordell-Weil generators becomes
        unbounded (Paper 51 §3, padic_failure_vacuous).

    Topological strengthening: even if a p-adic height pairing is
    anisotropic (rank ≤ 4, below Meyer threshold), Northcott still
    fails because ℤ is dense in ℚ_p (p^n → 0). Bounded p-adic balls
    intersect ℤ infinitely. ℝ is the unique completion where ℤ is
    discrete, making Northcott possible.
    Reference: Lang (1983) Ch. 3, Paper 48 Thm B1, Paper 51 §3,
    Bridges-Richman (1987) Ch. 3. -/
axiom no_northcott_search_cost : CRMLevel
axiom no_northcott_search_cost_eq : no_northcott_search_cost = LPO

/-- CRM cost of cycle-search, assembled from axiomatised components.
    Each case delegates to an axiomatised value; proofs must rewrite
    through the corresponding axiom. -/
noncomputable def cycle_search_cost : HeightType → CRMLevel
  | positive_definite => northcott_search_cost
  | indefinite        => no_northcott_search_cost

-- ============================================================
-- u-Invariant (from Paper 70)
-- ============================================================

/-- u-invariant determines which height type is available.
    u(ℝ) = ∞: positive-definite forms in every dimension → Axiom 3.
    u(ℚ_p) = 4: no positive-definite form in dim ≥ 5 → Axiom 3 fails.
    Reference: Serre, A Course in Arithmetic (1973), Ch. IV. -/
structure CompletionProfile where
  is_archimedean : Bool
  u_invariant_finite : Bool  -- true if u < ∞ (p-adic)

def real_completion : CompletionProfile := ⟨true, false⟩   -- u = ∞
def padic_completion : CompletionProfile := ⟨false, true⟩   -- u = 4

/-- Height type available at a given completion for the motivic category.
    Archimedean (u = ∞): positive-definite available in every dimension.
    Non-Archimedean (u = 4): indefinite forced in dim ≥ 5 (Meyer).

    Low-rank qualification: anisotropic p-adic forms exist in dim ≤ 4.
    However, Northcott still fails over ℚ_p even for anisotropic forms,
    because ℤ is dense (not discrete) in the p-adic topology: p^n → 0,
    so {x ∈ ℤ : |x|_p ≤ B} is infinite for any B ≥ 1.
    The classification `indefinite` is correct for the cycle-search
    problem across the whole motivic category (arbitrarily high rank)
    and remains correct even for individual low-rank motives
    (topological failure of Northcott).
    Reference: Lang (1983) Ch. 3; Serre (1973) Ch. IV Thm 6. -/
def available_height (c : CompletionProfile) : HeightType :=
  if c.is_archimedean then positive_definite else indefinite
