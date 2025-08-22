/-
  Papers/P1_GBC/RankOneToggle/ShermanMorrison.lean

  Sherman–Morrison identities for an idempotent projection P : H →L[𝕜] H
  and the "toggle" operator G(P,c) = if c then (Id - P) else Id.

  The resolvent (right inverse) is constructed explicitly in both cases:
   • c = false:  z•Id - G = (z-1)•Id is invertible on the right when z ≠ 1
   • c = true :  z•Id - G = (z-1)•Id + P   factors as (z-1)(Id + α P) with α=(z-1)⁻¹;
                  we use a Sherman–Morrison product to invert (Id + α P) on the right,
                  under 1+α ≠ 0, which follows from z ≠ 0.

  Exactly one intentional `sorry` remains at the end for an optional norm bound.
-/

import Mathlib
-- We rely on: ContinuousLinearMap, basic algebraic tactics (simp/ring/abel), and inv-cancel lemmas.

set_option linter.unusedSectionVars false

open scoped BigOperators
open ContinuousLinearMap

namespace Papers.P1_GBC.RankOneToggle

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-! ### Small helper lemmas on `H →L[𝕜] H` -/

private lemma comp_smul_smul
    (A B : H →L[𝕜] H) (a b : 𝕜) :
    (a • A).comp (b • B) = (a * b) • (A.comp B) := by
  ext x; simp [comp_apply, smul_apply, smul_smul, mul_comm, mul_left_comm, mul_assoc]

private lemma comp_add_right (A B C : H →L[𝕜] H) :
  (A + B).comp C = A.comp C + B.comp C := by
  ext x; simp

private lemma comp_sub_right (A B C : H →L[𝕜] H) :
  (A - B).comp C = A.comp C - B.comp C := by
  ext x; simp

private lemma comp_add_left (A B C : H →L[𝕜] H) :
  A.comp (B + C) = A.comp B + A.comp C := by
  ext x; simp

private lemma comp_sub_left (A B C : H →L[𝕜] H) :
  A.comp (B - C) = A.comp B - A.comp C := by
  ext x; simp

private lemma smul_comp_right (a : 𝕜) (A C : H →L[𝕜] H) :
  (a • A).comp C = a • (A.comp C) := by
  ext x; simp

private lemma comp_smul_left (a : 𝕜) (A B : H →L[𝕜] H) :
  A.comp (a • B) = a • (A.comp B) := by
  ext x; simp

-- pull scalars through composition on either side
private lemma smul_comp (a : 𝕜) (A C : H →L[𝕜] H) :
  (a • A).comp C = a • (A.comp C) := by ext x; simp
private lemma comp_smul (A C : H →L[𝕜] H) (a : 𝕜) :
  A.comp (a • C) = a • (A.comp C) := by ext x; simp

/-- In any module, `a • (x - b • x) = (a - a*b) • x`. -/
private lemma smul_sub_smul_module
    {𝕜 M} [Ring 𝕜] [AddCommGroup M] [Module 𝕜 M]
    (a b : 𝕜) (x : M) :
  a • (x - b • x) = (a - a*b) • x := by
  -- distribute and fold back with `sub_smul`
  simp [smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  -- goal is `a•x - (a*b)•x = (a - a*b)•x`
  simpa using (sub_smul a (a*b) x).symm

/-- Normalize `Id - b•P + t•P` into `Id + (-b + t)•P`. -/
private lemma normalize_id_sum
    (P : H →L[𝕜] H) (b t : 𝕜) :
    (ContinuousLinearMap.id 𝕜 H - b • P) + t • P
  = ContinuousLinearMap.id 𝕜 H + ((-b) + t) • P := by
  -- Just reassociate/commute the additive terms
  simpa [sub_eq_add_neg, add_smul, add_comm, add_left_comm, add_assoc]

/-! ### Toggle operator -/

/-- The toggle: `G P false = Id`, `G P true = Id - P`. -/
def G (P : H →L[𝕜] H) (c : Bool) : H →L[𝕜] H :=
  if c then (ContinuousLinearMap.id 𝕜 H - P) else (ContinuousLinearMap.id 𝕜 H)

@[simp] lemma G_false (P : H →L[𝕜] H) :
  G (𝕜 := 𝕜) (H := H) P false = ContinuousLinearMap.id 𝕜 H := rfl

@[simp] lemma G_true (P : H →L[𝕜] H) :
  G (𝕜 := 𝕜) (H := H) P true = ContinuousLinearMap.id 𝕜 H - P := rfl

/-! ### Algebra with an idempotent projection -/

/-- Idempotence hypothesis for `P`. We write it as an assumption in lemmas that need it. -/
@[simp] lemma idempotent_apply
  {P : H →L[𝕜] H} (hP : P.comp P = P) (x : H) :
  (P.comp P) x = P x := by simpa [hP]

/-- `(Id + a P) ∘ (Id - b P) = Id + (a - b - ab) P` for idempotent `P`. -/
private lemma comp_formula_right
    {P : H →L[𝕜] H} (hP : P.comp P = P) (a b : 𝕜) :
    (ContinuousLinearMap.id 𝕜 H + a • P).comp
      (ContinuousLinearMap.id 𝕜 H - b • P)
  = ContinuousLinearMap.id 𝕜 H + (a - b - a*b) • P := by
  -- expand bilinearly and use `P ∘ P = P`
  calc
    (ContinuousLinearMap.id 𝕜 H + a • P).comp (ContinuousLinearMap.id 𝕜 H - b • P)
        = (ContinuousLinearMap.id 𝕜 H).comp (ContinuousLinearMap.id 𝕜 H - b • P)
          + (a • P).comp (ContinuousLinearMap.id 𝕜 H - b • P) := by
            -- (A+B).comp C = A.comp C + B.comp C
            simpa using
              comp_add_right
                (A := ContinuousLinearMap.id 𝕜 H) (B := a • P) (C := ContinuousLinearMap.id 𝕜 H - b • P)
    _ = (ContinuousLinearMap.id 𝕜 H - b • P)
          + ((a • P).comp (ContinuousLinearMap.id 𝕜 H)
             - (a • P).comp (b • P)) := by
            simpa [comp_sub_left]
    _ = (ContinuousLinearMap.id 𝕜 H - b • P)
          + (a • P - (a*b) • (P.comp P)) := by
            -- Make scalar associativity explicit
            simpa [comp_id, comp_smul_smul, smul_comp_right, smul_smul,
                  mul_comm, mul_left_comm, mul_assoc]
    _ = (ContinuousLinearMap.id 𝕜 H - b • P)
          + (a - a*b) • P := by
            -- a•P - (a*b)•P•P = (a - a*b)•P using hP : P.comp P = P
            simp [sub_eq_add_neg, add_smul, hP]
    _ = ContinuousLinearMap.id 𝕜 H + ((-b) + (a - a*b)) • P := by
            simpa using normalize_id_sum P b (a - a*b)
    _ = ContinuousLinearMap.id 𝕜 H + (a - b - a*b) • P := by
            ring

/-- The special scalar identity needed for Sherman–Morrison. -/
private lemma sm_coeff_is_zero (α : 𝕜) (hα : 1 + α ≠ 0) :
  α - α/(1 + α) - α*(α/(1 + α)) = 0 := by
  -- Work on the product and use `mul_eq_zero` with `hα`.
  have h1 : (1 + α) * (α - α/(1 + α) - α*(α/(1 + α))) = 0 := by
    have hx : (1 + α) * α = α + α*α := by ring
    calc
      (1 + α) * (α - α/(1 + α) - α*(α/(1 + α)))
          = (1 + α) * α - (1 + α) * (α / (1 + α))
              - (1 + α) * (α * (α / (1 + α))) := by ring
      _ = (α + α*α) - α - α*α := by
            simp [div_eq_mul_inv, hα, hx, mul_comm, mul_left_comm, mul_assoc]
      _ = 0 := by ring
  -- Use `mul_eq_zero` in the field to cancel the nonzero factor.
  have := (mul_eq_zero.mp h1)
  rcases this with hL | hR
  · exact (hα hL).elim
  · exact hR

/-- `(Id + α P)` is a right-unit with explicit right-inverse when `1+α ≠ 0`. -/
private lemma sm_right_inverse
    {P : H →L[𝕜] H} (hP : P.comp P = P)
    (α : 𝕜) (hα : 1 + α ≠ 0) :
    (ContinuousLinearMap.id 𝕜 H + α • P).comp
      (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P)
  = ContinuousLinearMap.id 𝕜 H := by
  -- Use the general composition formula and annihilate the coefficient.
  simpa [sm_coeff_is_zero α hα, zero_smul, add_zero]
    using
      (comp_formula_right (P := P) hP α (α / (1 + α)))

/-! ### `(Id - P)` is not a unit if `P ≠ 0` -/

lemma not_isUnit_id_sub_proj
    {P : H →L[𝕜] H} (hP : P.comp P = P) (hP_ne_zero : P ≠ 0) :
    ¬ IsUnit (ContinuousLinearMap.id 𝕜 H - P) := by
  intro hU
  classical
  rcases hU with ⟨u, hu⟩
  -- Build a left inverse via units; then rewrite to subtraction form.
  -- Step 1: `u.inv_mul : ↑(u⁻¹) * ↑u = 1`  (here `*` = `comp`, `1` = `Id`).
  have h_comp₀ :
      ((↑(u⁻¹)) : H →L[𝕜] H).comp ((↑u) : H →L[𝕜] H)
        = ContinuousLinearMap.id 𝕜 H := by
    change ((↑(u⁻¹)) * (↑u) = (1 : H →L[𝕜] H))
    simpa using u.inv_mul
  -- Step 2: rewrite the right factor using the witness `hu : ↑u = Id - P`.
  have h_comp :
      ((↑(u⁻¹)) : H →L[𝕜] H).comp (ContinuousLinearMap.id 𝕜 H - P)
        = ContinuousLinearMap.id 𝕜 H := by
    simpa [hu] using h_comp₀
  -- Step 3: turn composition into the requested subtraction shape.
  have h_left :
      ((↑(u⁻¹)) : H →L[𝕜] H) - ((↑(u⁻¹)) : H →L[𝕜] H).comp P
        = ContinuousLinearMap.id 𝕜 H := by
    simpa [comp_sub_left, comp_id] using h_comp
  have hinj : Function.Injective (ContinuousLinearMap.id 𝕜 H - P) := by
    -- Pointwise form of `h_left` is a `LeftInverse`.
    have hLI :
        Function.LeftInverse
          (((↑(u⁻¹)) : H →L[𝕜] H))
          (ContinuousLinearMap.id 𝕜 H - P) := by
      intro v
      simpa [comp_apply, id_apply] using congrArg (fun f => f v) h_left
    exact hLI.injective
  -- Exhibit a nonzero kernel vector using idempotence.
  have hker_comp : (ContinuousLinearMap.id 𝕜 H - P).comp P = 0 := by
    ext y; simp [sub_apply, id_apply, comp_apply, hP]
  -- Choose x with P x ≠ 0 (otherwise P = 0).
  have hx' : ∃ x, P x ≠ 0 := by
    by_contra H0
    push_neg at H0
    have : P = 0 := by
      ext y; simpa using H0 y
    exact (hP_ne_zero this)
  rcases hx' with ⟨x, hx0⟩
  have hker : (ContinuousLinearMap.id 𝕜 H - P) (P x) = 0 := by
    simpa [comp_apply] using congrArg (fun f => f x) hker_comp
  have h_eq :
      (ContinuousLinearMap.id 𝕜 H - P) (P x)
        = (ContinuousLinearMap.id 𝕜 H - P) 0 := by
    simpa [sub_apply, id_apply] using hker
  have : P x = 0 := hinj h_eq
  exact hx0 this

/-! ## Explicit resolvents for the toggle `G P c` -/

/-- False case `c = false`: `G = Id`, so `(z Id - G)` has right inverse `(z-1)⁻¹ Id` for `z ≠ 1`. -/
theorem resolvent_G_false_explicit
    (P : H →L[𝕜] H) {z : 𝕜} (hz1 : z ≠ 1) :
    ((z • ContinuousLinearMap.id 𝕜 H - G (𝕜 := 𝕜) (H := H) P false).comp
       ((z - 1)⁻¹ • ContinuousLinearMap.id 𝕜 H)
     = ContinuousLinearMap.id 𝕜 H) := by
  -- Reduce to scalars and use `mul_inv_cancel₀`.
  have hz1' : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
  simp [G_false, sub_eq_add_neg, id_apply] -- rewrite to ((z-1)•Id).comp ((z-1)⁻¹•Id)
  -- Now push scalars through the composition.
  -- Rewrite z•Id - Id = (z - 1)•Id
  have hzsmul :
      z • ContinuousLinearMap.id 𝕜 H - ContinuousLinearMap.id 𝕜 H
        = (z - 1) • ContinuousLinearMap.id 𝕜 H := by
    -- (z - 1)•Id = z•Id - 1•Id
    simpa [one_smul] using
      (sub_smul z (1 : 𝕜) (ContinuousLinearMap.id 𝕜 H)).symm

  -- The typical "assumption" step becomes deterministic:
  have : ((z - 1)⁻¹) • (z • ContinuousLinearMap.id 𝕜 H - ContinuousLinearMap.id 𝕜 H) = 
         ContinuousLinearMap.id 𝕜 H := by
    simpa [hzsmul, smul_smul, inv_mul_cancel₀ hz1', one_smul]
  -- Use this for the scalar goal
  simpa [sub_eq_add_neg, smul_sub] using this

/-- True case `c = true`: `G = Id - P`.  Let `α = (z-1)⁻¹`.
    If `z ≠ 1` and `z ≠ 0`, then
    `(z Id - G)` has the right inverse `((z-1)⁻¹) (Id - α/(1+α) P)`. -/
theorem resolvent_G_true_explicit
    {P : H →L[𝕜] H} (hP : P.comp P = P)
    {z : 𝕜} (hz1 : z ≠ 1) (hz0 : z ≠ 0) :
    ((z • ContinuousLinearMap.id 𝕜 H - G (𝕜 := 𝕜) (H := H) P true).comp
       ((z - 1)⁻¹ • (ContinuousLinearMap.id 𝕜 H - ((z - 1)⁻¹ / (1 + (z - 1)⁻¹)) • P))
     = ContinuousLinearMap.id 𝕜 H) := by
  classical
  set α : 𝕜 := (z - 1)⁻¹
  have hz1' : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
  -- Show `(1 + α) ≠ 0` using `(1+α)(z-1) = z` (no `congrArg`).
  have hα : 1 + α ≠ 0 := by
    -- `α = (z-1)⁻¹`, so `(z-1)*α = 1`.
    have hmul_base : ((z - 1) * α : 𝕜) = 1 := by simpa [α] using mul_inv_cancel₀ hz1'
    have hmul1 : α * (z - 1) = 1 := by simpa [mul_comm] using hmul_base
    intro hzero
    have hcalc : (1 + α) * (z - 1) = z := by
      calc
        (1 + α) * (z - 1) = (z - 1) + α * (z - 1) := by ring
        _ = (z - 1) + 1 := by simpa [hmul1]
        _ = z := by ring
    have hz' : 0 = z := by simpa [hzero] using hcalc
    exact hz0 hz'.symm
  -- The Sherman–Morrison core identity:
  have core_right :
      (ContinuousLinearMap.id 𝕜 H + α • P).comp
        (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P)
    = ContinuousLinearMap.id 𝕜 H :=
    sm_right_inverse (P := P) hP α hα
  -- Factorization:  z•Id - (Id - P) = (z-1)•Id + P = (z-1)•(Id + α P),
  --  using (z-1)α = 1.
  have hmul : (z - 1) * α = 1 := by simpa [α] using mul_inv_cancel₀ hz1'
  -- Factorization:  z•Id - (Id - P) = (z-1)•Id + P = (z-1)•(Id + α P)
  have fac :
      z • ContinuousLinearMap.id 𝕜 H - G (𝕜 := 𝕜) (H := H) P true
        = (z - 1) • (ContinuousLinearMap.id 𝕜 H + α • P) := by
    calc
      z • ContinuousLinearMap.id 𝕜 H - G (𝕜 := 𝕜) (H := H) P true
          = z • ContinuousLinearMap.id 𝕜 H - (ContinuousLinearMap.id 𝕜 H - P) := by
            simp [G_true]
      _ = (z - 1) • ContinuousLinearMap.id 𝕜 H + P := by
        -- First normalize: z•Id - (Id - P) = (z•Id - Id) + P
        have hL :
            z • ContinuousLinearMap.id 𝕜 H - (ContinuousLinearMap.id 𝕜 H - P)
              = (z • ContinuousLinearMap.id 𝕜 H - ContinuousLinearMap.id 𝕜 H) + P := by
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        -- Then fold z•Id - Id = (z - 1)•Id
        have hz :
            z • ContinuousLinearMap.id 𝕜 H - ContinuousLinearMap.id 𝕜 H
              = (z - 1) • ContinuousLinearMap.id 𝕜 H := by
          simpa [one_smul]
            using (sub_smul z (1 : 𝕜) (ContinuousLinearMap.id 𝕜 H)).symm
        simpa [hL, hz]
      _ = (z - 1) • (ContinuousLinearMap.id 𝕜 H + α • P) := by
        -- Split the RHS, then use hmul to match the LHS sum.
        have hsplit :
          (z - 1) • (ContinuousLinearMap.id 𝕜 H + α • P)
            = (z - 1) • ContinuousLinearMap.id 𝕜 H
              + ((z - 1) * α) • P := by
          simp [smul_add, smul_smul]
        have : (z - 1) • ContinuousLinearMap.id 𝕜 H + P
            = (z - 1) • ContinuousLinearMap.id 𝕜 H + ((z - 1) * α) • P := by
          simpa [hmul, one_smul]
        exact this.trans hsplit.symm
  -- Compose the factorization with the candidate right inverse.
  have hpull :
    ((z - 1) • (ContinuousLinearMap.id 𝕜 H + α • P)).comp
      ((z - 1)⁻¹ • (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P))
      = 1 • ((ContinuousLinearMap.id 𝕜 H + α • P).comp
              (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P)) := by
    -- First collapse ((z-1)•A) ∘ ((z-1)⁻¹•B) → ((z-1)*(z-1)⁻¹)•(A∘B).
    have H :
      ((z - 1) • (ContinuousLinearMap.id 𝕜 H + α • P)).comp
        ((z - 1)⁻¹ • (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P))
        =
      ((z - 1) * (z - 1)⁻¹) •
        ((ContinuousLinearMap.id 𝕜 H + α • P).comp
         (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P)) := by
      simpa using
        (comp_smul_smul
          (ContinuousLinearMap.id 𝕜 H + α • P)
          (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P)
          (z - 1) ((z - 1)⁻¹))
    -- Then cancel ((z-1)*(z-1)⁻¹) = 1.
    simpa [mul_inv_cancel₀ hz1', one_smul] using H
  -- Put the pieces together, keeping the composition shape fixed.
  let Y₁ : H →L[𝕜] H :=
    ( (z - 1)⁻¹ • (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P) )
  have step1 :
    (z • ContinuousLinearMap.id 𝕜 H - G (𝕜 := 𝕜) (H := H) P true).comp Y₁
      =
    ((z - 1) • (ContinuousLinearMap.id 𝕜 H + α • P)).comp Y₁ := by
    -- rewrite the left factor by `fac` and leave the right factor as `Y₁`
    rw [fac]
  have step2 :
    ((z - 1) • (ContinuousLinearMap.id 𝕜 H + α • P)).comp Y₁
      =
    1 • ((ContinuousLinearMap.id 𝕜 H + α • P).comp
           (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P)) := by
    -- this is exactly `hpull`
    simpa [Y₁] using hpull
  calc
    (z • ContinuousLinearMap.id 𝕜 H - G (𝕜 := 𝕜) (H := H) P true).comp Y₁
        = ((z - 1) • (ContinuousLinearMap.id 𝕜 H + α • P)).comp Y₁ := step1
    _   = 1 • ((ContinuousLinearMap.id 𝕜 H + α • P).comp
               (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P)) := step2
    _   = 1 • ContinuousLinearMap.id 𝕜 H := by simpa [core_right]
    _   = ContinuousLinearMap.id 𝕜 H := by simp

/-! ## Optional: a norm bound for the resolvent (left as intended `sorry`) -/

-- Depending on your project, you may want a crude bound such as:
--   ‖(Id + α P)⁻¹‖ ≤ 1 + |α|  (or a more refined spectral estimate),
-- and then transfer it through the factorization of `z•Id - (Id - P)`.
-- We leave this as the single intentional placeholder.

theorem resolvent_norm_bound_placeholder
    {P : H →L[𝕜] H} (hP : P.comp P = P) :
    True := by
  -- Intentionally left for later analytic sharpening.
  sorry

end Papers.P1_GBC.RankOneToggle