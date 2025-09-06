/-
Paper 6: Heisenberg Uncertainty Principle AxCal Analysis
Complex Number Axioms (Prop-only, no instances to avoid codegen)
Based on technical guidance for mathlib-free implementation
-/

-- Basic real number operations (signature only)
axiom ℝ : Type
axiom real_add : ℝ → ℝ → ℝ
axiom real_mul : ℝ → ℝ → ℝ
axiom real_zero : ℝ
axiom real_one : ℝ
axiom real_neg : ℝ → ℝ
-- Prop-only order on ℝ
axiom real_le : ℝ → ℝ → Prop
infix:50 " ≤ᵣ " => real_le

-- Basic properties of ≤ᵣ used in inequality chaining
axiom real_le_refl  : ∀ a : ℝ, a ≤ᵣ a
axiom real_le_trans : ∀ {a b c : ℝ}, a ≤ᵣ b → b ≤ᵣ c → a ≤ᵣ c
axiom real_le_of_eq : ∀ {a b : ℝ}, a = b → a ≤ᵣ b

-- Monotonicity under left-multiplication by 4 (specialized; no general order theory needed)
axiom real_mul_mono_left_four :
  ∀ {x y : ℝ}, x ≤ᵣ y → real_mul real_four x ≤ᵣ real_mul real_four y

-- Small named constants (no division needed)
noncomputable def real_two  : ℝ := real_add real_one real_one
noncomputable def real_four : ℝ := real_add real_two real_two

-- Complex number type and operations (signature only)
axiom ℂ : Type
axiom complex_add : ℂ → ℂ → ℂ
axiom complex_mul : ℂ → ℂ → ℂ
axiom complex_zero : ℂ
axiom complex_one : ℂ
axiom complex_conj : ℂ → ℂ
axiom complex_norm_sq : ℂ → ℝ

-- Real embedding
axiom real_to_complex : ℝ → ℂ

-- Imaginary unit
axiom complex_i : ℂ

-- Key algebraic properties (Prop-only statements)
axiom complex_add_assoc : ∀ a b c : ℂ, 
  complex_add (complex_add a b) c = complex_add a (complex_add b c)

axiom complex_add_comm : ∀ a b : ℂ, 
  complex_add a b = complex_add b a

axiom complex_add_zero : ∀ a : ℂ, 
  complex_add a complex_zero = a

axiom complex_mul_assoc : ∀ a b c : ℂ, 
  complex_mul (complex_mul a b) c = complex_mul a (complex_mul b c)

axiom complex_mul_comm : ∀ a b : ℂ, 
  complex_mul a b = complex_mul b a

axiom complex_mul_one : ∀ a : ℂ, 
  complex_mul a complex_one = a

axiom complex_distrib : ∀ a b c : ℂ, 
  complex_mul a (complex_add b c) = complex_add (complex_mul a b) (complex_mul a c)

-- Conjugation properties
axiom complex_conj_add : ∀ a b : ℂ, 
  complex_conj (complex_add a b) = complex_add (complex_conj a) (complex_conj b)

axiom complex_conj_mul : ∀ a b : ℂ, 
  complex_conj (complex_mul a b) = complex_mul (complex_conj a) (complex_conj b)

axiom complex_conj_conj : ∀ a : ℂ, 
  complex_conj (complex_conj a) = a

-- Norm properties
axiom complex_norm_sq_nonneg : ∀ a : ℂ, 
  ∃ r : ℝ, complex_norm_sq a = r ∧ (r = real_zero ∨ ∃ s : ℝ, real_mul s s = r)

axiom complex_norm_sq_conj : ∀ a : ℂ, 
  real_to_complex (complex_norm_sq a) = complex_mul a (complex_conj a)

-- Complex negation
axiom complex_neg : ℂ → ℂ

-- Imaginary unit properties  
axiom complex_i_sq : complex_mul complex_i complex_i = complex_neg complex_one

-- Negation definition
axiom complex_neg_def : ∀ z : ℂ, 
  complex_neg z = complex_mul (real_to_complex (real_neg real_one)) z

-- Real embedding properties
axiom real_embed_add : ∀ a b : ℝ, 
  real_to_complex (real_add a b) = complex_add (real_to_complex a) (real_to_complex b)

axiom real_embed_mul : ∀ a b : ℝ, 
  real_to_complex (real_mul a b) = complex_mul (real_to_complex a) (real_to_complex b)

axiom real_embed_zero : real_to_complex real_zero = complex_zero
axiom real_embed_one : real_to_complex real_one = complex_one

-- Universal complex bound: |z - conj z|^2 ≤ 4 |z|^2 (in squared-norm form)
axiom norm_sq_sub_conj_le_4_norm_sq :
  ∀ z : ℂ,
    complex_norm_sq (complex_add z (complex_neg (complex_conj z)))
      ≤ᵣ real_mul real_four (complex_norm_sq z)

-- Congruence for real_mul to avoid transport issues
axiom real_mul_congr_right :
  ∀ {a a' b b' : ℝ}, a = a' → b = b' → real_mul a b = real_mul a' b'

/-! Additional small helpers for Phase-3+ -/

/-- Congruence for real addition. -/
axiom real_add_congr :
  ∀ {a a' b b' : ℝ}, a = a' → b = b' → real_add a b = real_add a' b'

/-- Exact identity: ‖z - conj z‖² + ‖z + conj z‖² = 4‖z‖². -/
axiom norm_sq_skew_sym_sum_eq_4_norm_sq :
  ∀ z : ℂ,
    real_add
      (complex_norm_sq (complex_add z (complex_neg (complex_conj z))))
      (complex_norm_sq (complex_add z (complex_conj z)))
    = real_mul real_four (complex_norm_sq z)