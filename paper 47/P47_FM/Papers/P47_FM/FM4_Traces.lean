/-
  Paper 47: Fontaine-Mazur Conjecture — Lean 4 Formalization
  FM4_Traces.lean: Theorem FM4 — Trace Descent to ℚ̄ (BISH)

  Main result:
    Under geometric origin, Frobenius traces descend to ℚ ⊂ ℚ_p,
    where equality is decidable. Without geometric origin,
    trace zero-testing requires LPO.

  Pattern: Direct parallel to Paper 45 C4.
  Custom axiom: trace_algebraic (from Defs.lean).
  No sorry.
-/

import Papers.P47_FM.Defs

noncomputable section

namespace Papers.P47

-- ============================================================
-- §1. Geometric Traces are Decidable
-- ============================================================

/-- **Theorem FM4: Frobenius trace is decidably zero under geometric origin.**

    By trace_algebraic, the Frobenius trace at ℓ descends to ℚ:
      trace(Frob_ℓ) = algebraMap ℚ ℚ_p α for some α ∈ ℚ.
    Testing α = 0 is decidable (ℚ has decidable equality in BISH).
    Testing trace = 0 reduces to testing α = 0 via injectivity.

    Returns Or (Prop) rather than Decidable (Type) to stay in Prop universe.
    The constructive content is identical. -/
theorem trace_decidable_geometric (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    LinearMap.trace Q_p W (frob_action ℓ) = 0 ∨
    LinearMap.trace Q_p W (frob_action ℓ) ≠ 0 := by
  -- trace_algebraic: ∃ α ∈ range(algebraMap ℚ Q_p), trace = α
  obtain ⟨α, ⟨q, hq⟩, hα⟩ := trace_algebraic ℓ
  -- α = algebraMap ℚ Q_p q, and trace(Frob_ℓ) = α
  rw [hα, ← hq]
  -- Now decide: is algebraMap ℚ Q_p q = 0?
  -- by_cases on q : ℚ uses ℚ's DecidableEq (constructive, not classical)
  by_cases hq0 : q = 0
  · left; rw [hq0, map_zero]
  · right
    intro h_contra
    exact hq0 (algebraMap_Q_p_injective (by rwa [map_zero]))

-- ============================================================
-- §2. Abstract Traces Require LPO (Contrast)
-- ============================================================

/-- **The trace encoding.**
    For x ∈ ℚ_p, construct a linear map on (ℚ_p)² with trace = x.
    The map sends (a, b) ↦ (x·a, 0), which has matrix
    [[x, 0], [0, 0]] and thus trace = x + 0 = x. -/
def encodingTrace (x : Q_p) :
    (Fin 2 → Q_p) →ₗ[Q_p] (Fin 2 → Q_p) where
  toFun v := fun i =>
    match i with
    | 0 => x * v 0
    | 1 => 0
  map_add' u v := by
    ext i; fin_cases i
    · simp; ring
    · simp
  map_smul' c v := by
    ext i; fin_cases i
    · simp [smul_eq_mul]; ring
    · simp [smul_eq_mul]

/-- The trace of encodingTrace x is x.
    encodingTrace x has matrix [[x, 0], [0, 0]], so trace = x + 0 = x.

    Proof: Convert to matrix trace via Pi.basisFun, then compute
    using Matrix.trace_fin_two and toMatrix' entry evaluation. -/
theorem encodingTrace_trace (x : Q_p) :
    LinearMap.trace Q_p (Fin 2 → Q_p) (encodingTrace x) = x := by
  have h := LinearMap.trace_eq_matrix_trace Q_p
    (b := Pi.basisFun Q_p (Fin 2)) (encodingTrace x)
  rw [h, Matrix.trace_fin_two]
  simp only [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  simp [encodingTrace, Pi.single]

/-- **Abstract trace zero-testing requires LPO.**
    For an abstract ℚ_p-linear endomorphism, testing whether its
    trace is zero requires testing elements of ℚ_p for zero.

    Proof: Given x ∈ ℚ_p, the encodingTrace x has trace x.
    An oracle for trace-zero-testing decides x = 0 ∨ x ≠ 0. -/
theorem trace_abstract_requires_LPO :
    (∀ (f : (Fin 2 → Q_p) →ₗ[Q_p] (Fin 2 → Q_p)),
      LinearMap.trace Q_p (Fin 2 → Q_p) f = 0 ∨
      LinearMap.trace Q_p (Fin 2 → Q_p) f ≠ 0) →
    LPO_Q_p := by
  intro oracle x
  -- Apply the oracle to encodingTrace x
  have hdec := oracle (encodingTrace x)
  -- trace(encodingTrace x) = x, so the oracle's decision transfers
  rwa [encodingTrace_trace] at hdec

-- ============================================================
-- §3. FM4 Summary
-- ============================================================

/-- **Theorem FM4 (Trace Descent Summary).**
    Abstract traces require LPO. Geometric traces are decidable in BISH.

    This parallels Paper 45 C4: geometric origin descends coefficients
    from undecidable ℚ_p to decidable ℚ (via Weil conjectures). -/
theorem FM4_trace_summary :
    -- Geometric traces are decidable
    (∀ (ℓ : ℕ) [Fact (Nat.Prime ℓ)],
      LinearMap.trace Q_p W (frob_action ℓ) = 0 ∨
      LinearMap.trace Q_p W (frob_action ℓ) ≠ 0) ∧
    -- Abstract traces require LPO
    ((∀ (f : (Fin 2 → Q_p) →ₗ[Q_p] (Fin 2 → Q_p)),
      LinearMap.trace Q_p (Fin 2 → Q_p) f = 0 ∨
      LinearMap.trace Q_p (Fin 2 → Q_p) f ≠ 0) →
      LPO_Q_p) :=
  ⟨fun ℓ _ => trace_decidable_geometric ℓ, trace_abstract_requires_LPO⟩

end Papers.P47
