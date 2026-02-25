/-
  Paper 72: Height Search — The Core Theorem

  The correct formulation of WHY Axiom 3 is necessary for motives.

  NOT about abstract Tannakian categories (Rep_ℚ(G) is always decidable).
  ABOUT the cycle-search problem: given a lattice of algebraic cycles
  with a height pairing, can you decide torsion membership and find
  generators?

  The bridge: positive-definite height ↔ Northcott property ↔ bounded
  search ↔ BISH. Each ↔ is an equivalence.

  How LPO enters without Northcott (two mechanisms from Papers 48, 51):
  (1) L-function zero-test: L(E,1) ∈ ℝ, deciding L(E,1) = 0 costs LPO.
  (2) Unbounded generator search: without the Northcott finiteness
      guarantee, the search grid for Mordell-Weil generators is infinite.
      Paper 51's searchGrid construction (Silverman bound → exp → Finset.Icc)
      is exactly the BISH mechanism that fails when the height is indefinite.

  References: Paper 48 (L(E,1) = 0 ↔ LPO), Paper 51 (BSD rescue via
    Silverman bound), Paper 61 (Lang gate), Northcott (1950).
-/
import Papers.P72_DPTCharacterisation.Defs

open CRMLevel HeightType

-- ============================================================
-- The Height-Decidability Bridge
-- ============================================================

/-- **Forward:** Positive-definite height gives Northcott, which gives
    bounded cycle-search, which gives BISH.
    This is the content of Papers 48, 51, 61 (specific cases).
    The mechanism (Paper 51): canonical height bound C → naive height
    bound 2C+2μ via Silverman → coordinates in [-exp(H), exp(H)] ∩ ℤ
    → finite searchGrid → decidable exhaustion. -/
theorem positive_definite_gives_BISH :
    cycle_search_cost positive_definite = BISH := by
  unfold cycle_search_cost
  exact northcott_search_cost_eq

/-- **Reverse:** Indefinite height → Northcott fails → LPO.
    The null cone {P : h(P) = 0} is infinite. Non-torsion points
    accumulate at zero height. Deciding "is this null-cone point
    torsion?" encodes a real-number equality test (Paper 48: is
    L(E,1) = 0?) which costs LPO. Even after resolving the L-function
    question via Axiom 2 (algebraic L-values), finding explicit
    generators requires unbounded search (Paper 51 §3:
    padic_failure_vacuous shows the p-adic search bound collapses). -/
theorem indefinite_gives_LPO :
    cycle_search_cost indefinite = LPO := by
  unfold cycle_search_cost
  exact no_northcott_search_cost_eq

-- ============================================================
-- The Northcott Bridge (structural equivalence)
-- ============================================================

/-- Northcott ↔ positive-definite (structural, not axiomatised).
    Forward: positive-definite → Northcott. Standard (Northcott 1950).
    Reverse: indefinite → Northcott fails (null vectors accumulate). -/
theorem northcott_iff_positive_definite (ht : HeightType) :
    has_northcott ht = true ↔ ht = positive_definite := by
  cases ht <;> simp [has_northcott]

-- ============================================================
-- The Main Equivalence
-- ============================================================

/-- **THEOREM B (Height-Search Equivalence):**
    cycle_search_cost ht = BISH ↔ ht = positive_definite.

    Forward: positive-definite → BISH (Northcott bounds the search).
    Reverse: indefinite → LPO ≠ BISH (contrapositive).

    This is the correct version of the "reverse direction" that v1
    got wrong. It says: for the CYCLE-SEARCH problem (not the abstract
    category), positive-definiteness is necessary and sufficient for
    BISH-decidability. -/
theorem height_search_equivalence (ht : HeightType) :
    cycle_search_cost ht = BISH ↔ ht = positive_definite := by
  constructor
  · intro h
    cases ht
    · rfl
    · -- indefinite: derive contradiction from axioms
      unfold cycle_search_cost at h
      rw [no_northcott_search_cost_eq] at h
      -- h : LPO = BISH — contradiction
      contradiction
  · intro h
    rw [h]
    unfold cycle_search_cost
    exact northcott_search_cost_eq

-- ============================================================
-- Archimedean Necessity for Cycle-Search
-- ============================================================

/-- **COROLLARY:** The Archimedean place is necessary for BISH
    cycle-search.
    At ℝ: available height = positive-definite → BISH.
    At ℚ_p: available height = indefinite → LPO. -/
theorem archimedean_necessary_for_search :
    cycle_search_cost (available_height real_completion) = BISH ∧
    cycle_search_cost (available_height padic_completion) = LPO := by
  constructor
  · -- real: available_height gives positive_definite
    show cycle_search_cost positive_definite = BISH
    exact positive_definite_gives_BISH
  · -- p-adic: available_height gives indefinite
    show cycle_search_cost indefinite = LPO
    exact indefinite_gives_LPO
