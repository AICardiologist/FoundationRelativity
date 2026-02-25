/-
  Paper 75: Conservation Test — Definitions
  CRM Calibration of the Genestier-Lafforgue Semisimple LLC

  This paper tests the DPT framework (Papers 72–74) as an external
  diagnostic on a major result from the condensed/perfectoid programme.

  Target: the Genestier-Lafforgue semisimple local Langlands
  parametrization for arbitrary reductive G over a local field.

  Statement: ∀G ∀π ∈ Irrep(G(F)), ∃φ ∈ Φ_ss(G),
             trace(π) = trace(φ).
  (Semisimple L-parameters matching irreducible representations.)

  Three-layer stratification of the Fargues-Scholze proof:
  - Algebraic (solidification): BISH. Mittag-Leffler holds trivially —
    transition maps of finite sets are split epimorphisms, lim¹ = 0
    constructively, no Dependent Choice needed.
    Reference: Clausen-Scholze (2019, Lecture 3).
  - Homological (K-injective resolutions): CLASS (Zorn's lemma).
    Čech bypass fails — v-site has infinite cohomological dimension
    (Scholze 2017, Prop 14.12). Animation resolves sources only;
    Rf_! requires injective envelopes in target category.
    Reference: Fargues-Scholze (2021, §VII), Scholze (2017).
  - Geometric (v-topology): CLASS (Boolean Prime Ideal theorem).
    BunG is an Artin v-stack, not pro-étale. G-torsors on the
    Fargues-Fontaine curve require v-covers to trivialize.
    Reference: Fargues-Scholze (2021, §III), Scholze (2017, §14).

  Statement cost: BISH + WLPO. The ∃φ is NOT a search — by Schur's
  lemma, Z(G) acts on irreducible admissible π by scalars (finite-
  dimensional invariants under compact open subgroups), giving a
  character χ_π : Z(G) → Q̄_ℓ that deterministically extracts φ via
  Spec(Z(G)) = coarse moduli of semisimple parameters. The only
  residual logical cost is the trace equality test: WLPO by Paper 74.
  Reference: Bernstein (1984), Paper 74 Theorem C.

  Conservation hypothesis (OPEN CONJECTURE): the CLASS scaffolding
  (homological + geometric) is eliminable. The arithmetic content
  (trace matching) does not require it. The contribution of this
  paper is proving the gap exists and identifying where CLASS enters,
  not proving the gap is eliminable.

  References: Genestier-Lafforgue (2018), Fargues-Scholze (2021),
    Scholze (2017), Clausen-Scholze (2019), Bernstein (1984),
    Paper 45, Paper 50, Paper 72, Paper 73, Paper 74.
-/
import Mathlib.Order.Defs.PartialOrder

-- ============================================================
-- CRM Hierarchy (shared with Papers 72–74)
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

/-- Join (maximum) of two CRM levels. -/
def CRMLevel.join (a b : CRMLevel) : CRMLevel :=
  if a.toNat ≤ b.toNat then b else a

-- ============================================================
-- Proof Layer Classification
-- ============================================================

/-- The three layers of the Fargues-Scholze proof architecture.
    Each layer has an independent CRM cost that can be separately
    calibrated.

    - algebraic: solidification functor, condensed abelian groups,
      inverse limits of finite sets.
    - homological: derived categories, K-injective resolutions,
      injective envelopes, six-functor formalism.
    - geometric: v-topology on perfectoid spaces, v-stacks,
      BunG, Fargues-Fontaine curve. -/
inductive ProofLayer : Type where
  | algebraic   : ProofLayer
  | homological  : ProofLayer
  | geometric    : ProofLayer
  deriving DecidableEq, Repr

open ProofLayer

-- ============================================================
-- Axiomatized Layer Costs (4 opaque + axiom pairs)
-- ============================================================

/-- CRM cost of the algebraic layer (solidification functor).
    Solidification of light condensed abelian groups requires
    computing inverse limits of diagrams indexed by the category
    of finite sets.

    Key fact: transition maps of finite sets are split epimorphisms
    (every surjection of finite sets splits). Therefore:
    (1) Mittag-Leffler condition holds trivially.
    (2) lim¹ = 0 without Dependent Choice.
    (3) The inverse limit is constructively computable.

    No omniscience principle is needed. Cost: BISH.
    Reference: Clausen-Scholze (2019), Lecture 3. -/
opaque algebraic_layer_cost : CRMLevel
axiom algebraic_layer_cost_eq : algebraic_layer_cost = BISH

/-- CRM cost of the homological layer (K-injective resolutions).
    The derived category D(Solid) requires K-injective resolutions
    for unbounded complexes. Existence of enough K-injectives in
    a general Grothendieck abelian category requires:
    (1) Enough injective objects (Zorn's lemma = CLASS).
    (2) Transfinite composition indexed by ordinals.

    Čech bypass fails: the v-site has infinite cohomological
    dimension (Scholze 2017, Prop 14.12), so Čech complexes
    cannot substitute for injective resolutions. Animation
    (Lurie) resolves sources by free presentations, but the
    target (Rf_!) requires injective envelopes.

    Cost: CLASS (via Zorn's lemma).
    Reference: Fargues-Scholze (2021, §VII), Scholze (2017). -/
opaque homological_layer_cost : CRMLevel
axiom homological_layer_cost_eq : homological_layer_cost = CLASS

/-- CRM cost of the geometric layer (v-topology).
    BunG (the stack of G-bundles on the Fargues-Fontaine curve)
    is an Artin v-stack. The v-topology is strictly finer than
    the pro-étale topology and requires:
    (1) Existence of v-covers: for every perfectoid space S and
        G-torsor P on X_S, there exists a v-cover S' → S
        trivializing P. Constructing such covers requires the
        Boolean Prime Ideal theorem (BPI), a consequence of the
        Axiom of Choice.
    (2) Sheaf condition for v-covers: verifying the sheaf axiom
        for BunG requires enough points of the v-topos, which
        again invokes BPI.

    Cost: CLASS (via BPI).
    Reference: Fargues-Scholze (2021, §III), Scholze (2017, §14). -/
opaque geometric_layer_cost : CRMLevel
axiom geometric_layer_cost_eq : geometric_layer_cost = CLASS

/-- CRM cost of the GL LLC statement (not proof).
    The Genestier-Lafforgue semisimple parametrization:
      ∀G ∀π ∈ Irrep(G(F)), ∃φ ∈ Φ_ss(G), trace(π) = trace(φ).

    The ∃φ is NOT an existential search. By Schur's lemma, the
    Bernstein center Z(G) acts on irreducible admissible π by
    scalars (the space of K-fixed vectors is finite-dimensional
    for any compact open K). This gives a character
      χ_π : Z(G) → Q̄_ℓ.
    The geometric structure of Spec(Z(G)) is the coarse moduli
    space of semisimple L-parameters. So φ = the point in
    Spec(Z(G)) corresponding to χ_π — deterministically extracted,
    not searched for.

    The only residual logical cost is the trace equality test:
      trace(π)(f) = trace(φ)(f) for all test functions f.
    This is an equality test on algebraic/continuous values,
    which costs WLPO (Paper 74, Theorem C).

    NOT LPO: there is no existential search. The Bernstein center
    hands you φ; you only need to verify the trace identity.
    Cf. Paper 74's WLPO-vs-LPO distinction: equality test (WLPO)
    vs existential search (LPO).

    Cost: WLPO (BISH + WLPO in the hierarchy).
    Reference: Bernstein (1984), Paper 74 Theorem C,
      Genestier-Lafforgue (2018). -/
opaque gl_statement_cost : CRMLevel
axiom gl_statement_cost_eq : gl_statement_cost = WLPO
