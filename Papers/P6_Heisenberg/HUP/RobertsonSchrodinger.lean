/-
Paper 6: Robertson-Schrödinger inequality shell
Predicate structure for Height 0 constructive proof
Based on technical guidance for mathlib-free implementation
-/

import Papers.P6_Heisenberg.HUP.HilbertSig
import Papers.P6_Heisenberg.HUP.AxCalCore

namespace Papers.P6_Heisenberg.HUP

-- RS_Ineq is defined in HilbertSig.lean

/-- Phase-3: Constructive RS proof from bridge axioms. -/
theorem RS_from_bridges (S : HilbertSig) (O : OperatorSig S) :
    RS_Ineq S O :=
by
  intro A B ψ hA hB hnorm
  -- notation shorthands for centered vectors
  let ΔA := center S O A ψ
  let ΔB := center S O B ψ
  let z  := S.inner ΔA ΔB
  -- Step 1:  |⟨[A,B]⟩|^2 ≤ 4 |z|^2
  have hsk : O.cexpect (O.comm A B) ψ
              = complex_add z (complex_neg (complex_conj z)) :=
    comm_expect_as_skew_centered S O A B ψ hA hB hnorm
  have h1 :
    complex_norm_sq (O.cexpect (O.comm A B) ψ)
      ≤ᵣ real_mul real_four (complex_norm_sq z) :=
  by
    have hx :
      complex_norm_sq (O.cexpect (O.comm A B) ψ)
        = complex_norm_sq (complex_add z (complex_neg (complex_conj z))) :=
      congrArg complex_norm_sq hsk
    exact real_le_trans
      (real_le_of_eq hx)
      (norm_sq_sub_conj_le_4_norm_sq z)
  -- Step 2:  |z|^2 ≤ Var(A)·Var(B)  (Cauchy–Schwarz + variance=‖Δ‖²)
  have hcs :
    complex_norm_sq z
      ≤ᵣ real_mul
            (complex_norm_sq (S.inner ΔA ΔA))
            (complex_norm_sq (S.inner ΔB ΔB)) :=
    cauchy_schwarz_sq S ΔA ΔB
  have hvarA :
    O.variance A ψ
      = complex_norm_sq (S.inner ΔA ΔA) :=
    variance_centered S O A ψ
  have hvarB :
    O.variance B ψ
      = complex_norm_sq (S.inner ΔB ΔB) :=
    variance_centered S O B ψ
  have h2 :
    complex_norm_sq z
      ≤ᵣ real_mul (O.variance A ψ) (O.variance B ψ) :=
  by
    -- rewrite RHS of hcs using variance_centered equalities
    have : real_mul
             (complex_norm_sq (S.inner ΔA ΔA))
             (complex_norm_sq (S.inner ΔB ΔB))
           = real_mul (O.variance A ψ) (O.variance B ψ) :=
      real_mul_congr_right (by symm; exact hvarA) (by symm; exact hvarB)
    exact real_le_trans hcs (real_le_of_eq this)
  -- Step 3: multiply h2 by 4 (monotonicity) and chain with h1
  have h2' :
    real_mul real_four (complex_norm_sq z)
      ≤ᵣ real_mul real_four (real_mul (O.variance A ψ) (O.variance B ψ)) :=
    real_mul_mono_left_four h2
  exact real_le_trans h1 h2'

/-- Schrödinger inequality (squared, division-free).
    |⟨[A,B]⟩|² + |⟨{ΔA,ΔB}⟩|² ≤ 4·Var(A)·Var(B). -/
theorem Schrodinger_from_bridges
  (S : HilbertSig) (O : OperatorSig S) :
  ∀ (A B : O.Operator) (ψ : S.ψ),
    O.selfAdj A → O.selfAdj B → S.norm ψ = real_one →
    real_add
      (complex_norm_sq (O.cexpect (O.comm  A B) ψ))
      (complex_norm_sq (O.cexpect (O.acomm A B) ψ))
    ≤ᵣ real_mul real_four (real_mul (O.variance A ψ) (O.variance B ψ)) :=
by
  intro A B ψ hA hB hnorm
  -- Centered vectors and their inner product
  let ΔA := center S O A ψ
  let ΔB := center S O B ψ
  let z  := S.inner ΔA ΔB

  -- Step 1: rewrite expectations via centered skew/sym identities
  have h_comm :
    O.cexpect (O.comm A B) ψ
      = complex_add z (complex_neg (complex_conj z)) :=
    comm_expect_as_skew_centered S O A B ψ hA hB hnorm
  have h_acomm :
    O.cexpect (O.acomm A B) ψ
      = complex_add z (complex_conj z) :=
    acomm_expect_as_sym_centered S O A B ψ hA hB hnorm

  have hx1 :
    complex_norm_sq (O.cexpect (O.comm A B)  ψ)
      = complex_norm_sq (complex_add z (complex_neg (complex_conj z))) :=
    congrArg complex_norm_sq h_comm
  have hx2 :
    complex_norm_sq (O.cexpect (O.acomm A B) ψ)
      = complex_norm_sq (complex_add z (complex_conj z)) :=
    congrArg complex_norm_sq h_acomm

  -- Turn the sum on the LHS into the canonical sum of skew/sym norms
  have hsum_rewrite :
    real_add
      (complex_norm_sq (O.cexpect (O.comm  A B) ψ))
      (complex_norm_sq (O.cexpect (O.acomm A B) ψ))
      =
    real_add
      (complex_norm_sq (complex_add z (complex_neg (complex_conj z))))
      (complex_norm_sq (complex_add z (complex_conj z))) :=
    real_add_congr hx1 hx2

  -- Exact identity: sum of skew/sym squares = 4 |z|^2
  have hsum_eq :
    real_add
      (complex_norm_sq (complex_add z (complex_neg (complex_conj z))))
      (complex_norm_sq (complex_add z (complex_conj z)))
      = real_mul real_four (complex_norm_sq z) :=
    norm_sq_skew_sym_sum_eq_4_norm_sq z

  -- So LHS ≤ 4 |z|^2 by chaining equalities as ≤
  have hsum_le_4z :
    real_add
      (complex_norm_sq (O.cexpect (O.comm  A B) ψ))
      (complex_norm_sq (O.cexpect (O.acomm A B) ψ))
    ≤ᵣ real_mul real_four (complex_norm_sq z) :=
    real_le_trans (real_le_of_eq hsum_rewrite) (real_le_of_eq hsum_eq)

  -- Step 2: |z|^2 ≤ Var(A) Var(B) by Cauchy–Schwarz + variance=‖Δ‖²
  have hcs :
    complex_norm_sq z
      ≤ᵣ real_mul
            (complex_norm_sq (S.inner ΔA ΔA))
            (complex_norm_sq (S.inner ΔB ΔB)) :=
    cauchy_schwarz_sq S ΔA ΔB

  have hvarA :
    O.variance A ψ = complex_norm_sq (S.inner ΔA ΔA) :=
    variance_centered S O A ψ
  have hvarB :
    O.variance B ψ = complex_norm_sq (S.inner ΔB ΔB) :=
    variance_centered S O B ψ

  have hprod_eq :
    real_mul
      (complex_norm_sq (S.inner ΔA ΔA))
      (complex_norm_sq (S.inner ΔB ΔB))
      = real_mul (O.variance A ψ) (O.variance B ψ) :=
    real_mul_congr_right (by symm; exact hvarA) (by symm; exact hvarB)

  have h_z_le_var :
    complex_norm_sq z ≤ᵣ real_mul (O.variance A ψ) (O.variance B ψ) :=
    real_le_trans hcs (real_le_of_eq hprod_eq)

  -- Step 3: multiply by 4 and chain
  have h_4z_le_4var :
    real_mul real_four (complex_norm_sq z)
      ≤ᵣ real_mul real_four (real_mul (O.variance A ψ) (O.variance B ψ)) :=
    real_mul_mono_left_four h_z_le_var

  exact real_le_trans hsum_le_4z h_4z_le_4var

/-- RS witness family now uses the proved theorem instead of a ledger axiom. -/
def HUP_RS_W (S : HilbertSig) (O : OperatorSig S) : WitnessFamily Unit :=
{ property := fun _ => RS_Ineq S O,
  witness_exists := ⟨(), RS_from_bridges S O⟩ }

/-- Height 0 certificate for RS (constructive proof target) -/  
def HUP_RS_ProfileUpper (_S : HilbertSig) (_O : OperatorSig _S) :
  ProfileUpper height_zero_profile := {
  wlpo_cert := fun _ => True.intro,
  ft_cert   := fun _ => True.intro,
  dc_cert   := True.intro
}

end Papers.P6_Heisenberg.HUP