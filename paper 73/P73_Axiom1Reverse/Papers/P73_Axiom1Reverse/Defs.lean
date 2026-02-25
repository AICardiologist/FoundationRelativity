/-
  Paper 73: Axiom 1 Reverse Characterisation — Definitions
  Standard Conjecture D Is Necessary for BISH Morphism Decidability

  Parallels Paper 72 (Axiom 3 reverse). Paper 72 proved:
    positive-definite height ↔ BISH cycle-search.
  Paper 73 proves:
    Standard Conjecture D ↔ BISH morphism decidability.

  The mathematical content:
  - Homological equivalence: cl(Z₁) = cl(Z₂) in H*(X, ℚ_ℓ) — costs LPO
    (zero-testing in ℚ_ℓ; Paper 46 Theorem T4a).
  - Numerical equivalence: ∀W, Z₁·W = Z₂·W — costs BISH
    (finitely many integer comparisons; Paper 46 Theorem T2).
  - Conjecture D: these coincide. Without it, the radical of the
    intersection pairing is non-detachable.

  The radical obstruction: if Conjecture D fails, cycles exist that
  are numerically trivial but homologically nontrivial. Detecting them
  requires ℚ_ℓ zero-testing → LPO. The gap between rad(⟨·,·⟩) and
  ker(cl) is the non-constructive content.

  Jannsen's theorem (1992): numerical motives form a semisimple abelian
  category without Conjecture D — but without faithful ℓ-adic realization.
  CRM reading: numerical motives are the BISH-accessible part; homological
  motives are the realization-faithful part; Conjecture D asserts these coincide.

  Design: Paper 69/72 axiom pattern. Each mathematical component gets
  an opaque + axiom _eq pair. Proofs require rewriting through axioms.

  References: Paper 46 (Tate CRM), Paper 50 (DPT axioms),
    Jannsen (1992), Grothendieck (Standard Conjectures, 1969).
-/
import Mathlib.Order.Defs.PartialOrder

-- ============================================================
-- CRM Hierarchy (shared with Paper 72)
-- ============================================================

inductive CRMLevel : Type where
  | BISH    : CRMLevel
  | BISH_MP : CRMLevel
  | LLPO    : CRMLevel
  | WLPO    : CRMLevel
  | LPO     : CRMLevel
  | CLASS   : CRMLevel
  deriving DecidableEq, Repr, Inhabited

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

-- ============================================================
-- Radical Status (Paper 73 specific)
-- ============================================================

/-- Status of the intersection pairing's radical on algebraic cycles.

    The radical rad(⟨·,·⟩) = {Z : ∀W, ⟨Z,W⟩ = 0} is the kernel of
    numerical equivalence. Standard Conjecture D asserts this equals
    the kernel of the cycle class map (homological equivalence).

    - Detachable: rad is decidable. Membership reduces to finitely many
      integer intersection tests. This holds iff Conjecture D: hom = num.
      Reference: Paper 46 Theorem T2 (num_equiv_fin_decidable).

    - Non-detachable: rad is NOT decidable. The gap ker(cl) \ rad(⟨·,·⟩)
      contains cycles whose radical membership requires ℚ_ℓ zero-testing.
      This fails precisely when hom ≠ num (Conjecture D fails).
      Reference: Paper 46 Theorem T4a (hom_equiv_requires_LPO). -/
inductive RadicalStatus : Type where
  | detachable     : RadicalStatus  -- Conjecture D holds
  | non_detachable : RadicalStatus  -- Conjecture D fails
  deriving DecidableEq, Repr

open RadicalStatus

/-- Whether Conjecture D holds, i.e., hom = num. -/
def conjD_holds : RadicalStatus → Bool
  | detachable     => true
  | non_detachable => false

-- ============================================================
-- Axiomatized Morphism Costs (Paper 69/72 pattern)
-- ============================================================

/-- CRM cost of morphism decidability when Conjecture D holds.
    Conjecture D: hom ≡ num. Morphism equality reduces to numerical
    equivalence, which is BISH-decidable via finitely many integer
    intersection tests.

    Mechanism (Paper 46 T4b + Paper 50 ConjD):
    Given Z₁, Z₂ ∈ CH^r(X), and a complementary basis {W₁,...,Wₘ}:
      Z₁ ~_hom Z₂  ↔  Z₁ ~_num Z₂         (Conjecture D)
                    ↔  ∀j, Z₁·Wⱼ = Z₂·Wⱼ   (basis spans)
    The latter is a finite conjunction of integer comparisons → BISH.
    Reference: Paper 46 Theorem T2, Paper 50 §6. -/
opaque conjD_morphism_cost : CRMLevel
axiom conjD_morphism_cost_eq : conjD_morphism_cost = BISH

/-- CRM cost of morphism decidability when Conjecture D fails.
    Without Conjecture D, hom ≠ num: the gap
      ker(cl) ∖ rad(⟨·,·⟩)
    is nonempty. Elements in this gap are numerically trivial
    but homologically nontrivial.

    Two LPO entry points (both established in Paper 46):
    (1) Encoding: for any a ∈ ℚ_ℓ, there exist cycles Z_a, Z_0
        with cl(Z_a) = cl(Z_0) iff a = 0 (Paper 46, encode axiom).
        A homological-equality oracle would decide a = 0 for all a → LPO.
    (2) Realization compatibility: a faithful motivic category
        requires detecting homological equivalence (not just numerical).
        But homological equivalence requires ℚ_ℓ zero-testing → LPO.

    Jannsen's theorem (1992): numerical motives are semisimple and
    abelian WITHOUT Conjecture D. So you can build a nice BISH-decidable
    category — but it lacks faithful ℓ-adic realization. The trade-off:
    BISH-decidable OR realization-compatible, not both, unless Conj D.
    Reference: Paper 46 Theorem T4a, Jannsen (1992). -/
opaque no_conjD_morphism_cost : CRMLevel
axiom no_conjD_morphism_cost_eq : no_conjD_morphism_cost = LPO

/-- CRM cost of morphism decidability in a realization-compatible
    motivic category, as a function of the radical status.
    Delegates to axiomatized components. -/
def morphism_cost : RadicalStatus → CRMLevel
  | detachable     => conjD_morphism_cost
  | non_detachable => no_conjD_morphism_cost

-- ============================================================
-- Realization Compatibility
-- ============================================================

/-- A motivic category is realization-compatible if its equivalence
    relation ~ is at least as fine as homological equivalence:
      Z₁ ~ Z₂  ⟹  cl(Z₁) = cl(Z₂).
    Equivalently: ker(~) ⊆ ker(cl).

    This is required for the ℓ-adic realization functor to be faithful.
    Without it, the category identifies motives with different cohomology.

    When the radical is detachable (Conj D): numerical = homological,
    so numerical motives are automatically realization-compatible.
    When the radical is non-detachable (no Conj D): only homological
    motives are realization-compatible, but these cost LPO. -/
structure MotivicCategory where
  radical : RadicalStatus
  realization_compatible : Bool

def standard_with_conjD : MotivicCategory :=
  ⟨detachable, true⟩

def standard_without_conjD : MotivicCategory :=
  ⟨non_detachable, true⟩

def numerical_without_conjD : MotivicCategory :=
  ⟨detachable, false⟩  -- BISH-decidable but unfaithful
