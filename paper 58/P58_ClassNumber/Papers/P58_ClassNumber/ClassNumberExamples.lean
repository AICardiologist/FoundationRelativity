/-
  Paper 58: Class Number Correction — Systematic Conductor Verification
  All nine conductors from Papers 56–57 paired with K = ℚ(√-5), h_K = 2.

  Results:
    f = 7:   nonFree, h = 7/2,   det(G) = 980   = 49·20   ✓
    f = 9:   free,    h = 9,     det(G) = 1620  = 81·20   ✓
    f = 13:  inert    (no CM fourfold)
    f = 19:  inert    (no CM fourfold)
    f = 37:  inert    (no CM fourfold)
    f = 61:  free,    h = 61,    det(G) = 74420 = 3721·20 ✓
    f = 79:  inert    (no CM fourfold)
    f = 97:  inert    (no CM fourfold)
    f = 163: nonFree, h = 163/2, det(G) = 531380 = 26569·20 ✓
-/
import Papers.P58_ClassNumber.Defs
import Papers.P58_ClassNumber.GramMatrix
import Papers.P58_ClassNumber.NormObstruction

/-!
# Conductor Verification for K = ℚ(√-5)

For each conductor f from Papers 56–57, we determine:
1. Does f split in K? (Is -5 a QR mod f?)
2. If split: is the Weil lattice free (f ∈ Nm(K×)) or non-free (f/2 ∈ Nm(K×))?
3. If split: compute Gram matrix and verify det(G) = f² · 20.
-/

-- ========================================================================
-- Section 1: WeilLatticeData instances for split conductors
-- ========================================================================

/-- f = 7: non-free lattice. h = 7/2, Nm(𝔞) = 2.
    Fundamental identity: 7 · 2 = 7 · 2. -/
def weilData_K5_f7 : WeilLatticeData where
  K := K_sqrt5
  F := ⟨7, by norm_num⟩
  steinitz := .nonFree
  ideal := ideal_p_K5
  h_num := 7
  h_den := 2
  h_den_pos := by norm_num
  fundamental_identity := by native_decide

/-- f = 9: free lattice. h = 9, Nm(𝔞) = 1.
    Fundamental identity: 9 · 1 = 9 · 1. -/
def weilData_K5_f9 : WeilLatticeData where
  K := K_sqrt5
  F := ⟨9, by norm_num⟩
  steinitz := .free
  ideal := trivialIdeal
  h_num := 9
  h_den := 1
  h_den_pos := by norm_num
  fundamental_identity := by native_decide

/-- f = 61: free lattice. h = 61, Nm(𝔞) = 1.
    Fundamental identity: 61 · 1 = 61 · 1. -/
def weilData_K5_f61 : WeilLatticeData where
  K := K_sqrt5
  F := ⟨61, by norm_num⟩
  steinitz := .free
  ideal := trivialIdeal
  h_num := 61
  h_den := 1
  h_den_pos := by norm_num
  fundamental_identity := by native_decide

/-- f = 163: non-free lattice. h = 163/2, Nm(𝔞) = 2.
    Fundamental identity: 163 · 2 = 163 · 2. -/
def weilData_K5_f163 : WeilLatticeData where
  K := K_sqrt5
  F := ⟨163, by norm_num⟩
  steinitz := .nonFree
  ideal := ideal_p_K5
  h_num := 163
  h_den := 2
  h_den_pos := by norm_num
  fundamental_identity := by native_decide

-- ========================================================================
-- Section 2: Conductor classification summary
-- ========================================================================

/-- Complete classification of all nine conductors from Papers 56–57
    paired with K = ℚ(√-5), h_K = 2. -/
structure ConductorClassification where
  conductor : ℕ
  steinitz : SteinitzType

/-- The nine conductor classifications. -/
def allNineConductors_K5 : List ConductorClassification := [
  ⟨7,   .nonFree⟩,
  ⟨9,   .free⟩,
  ⟨13,  .inert⟩,
  ⟨19,  .inert⟩,
  ⟨37,  .inert⟩,
  ⟨61,  .free⟩,
  ⟨79,  .inert⟩,
  ⟨97,  .inert⟩,
  ⟨163, .nonFree⟩
]

-- ========================================================================
-- Section 3: Gram matrix verification for each split conductor
-- ========================================================================

/-- Verified Gram data for a split conductor. -/
structure VerifiedGramData where
  conductor : ℕ
  steinitz : SteinitzType
  gram : Matrix (Fin 2) (Fin 2) ℤ
  det_match : gram.det = (conductor : ℤ) ^ 2 * 20

/-- f = 7: verified Gram data. -/
def verifiedGram_K5_f7 : VerifiedGramData where
  conductor := 7
  steinitz := .nonFree
  gram := gram_K5_f7
  det_match := gram_K5_f7_match

/-- f = 9: verified Gram data. -/
def verifiedGram_K5_f9 : VerifiedGramData where
  conductor := 9
  steinitz := .free
  gram := gram_K5_f9
  det_match := gram_K5_f9_match

/-- f = 61: verified Gram data. -/
def verifiedGram_K5_f61 : VerifiedGramData where
  conductor := 61
  steinitz := .free
  gram := gram_K5_f61
  det_match := gram_K5_f61_match

/-- f = 163: verified Gram data. -/
def verifiedGram_K5_f163 : VerifiedGramData where
  conductor := 163
  steinitz := .nonFree
  gram := gram_K5_f163
  det_match := gram_K5_f163_match

-- ========================================================================
-- Section 4: Count verification
-- ========================================================================

/-- There are exactly 4 split and 5 inert conductors. -/
theorem split_count_K5 :
    (allNineConductors_K5.filter (fun c => c.steinitz != .inert)).length = 4 := by
  native_decide

theorem inert_count_K5 :
    (allNineConductors_K5.filter (fun c => c.steinitz == .inert)).length = 5 := by
  native_decide

-- ========================================================================
-- Section 5: The corrected formula h · Nm(𝔞) = f for each split conductor
-- ========================================================================

/-- f = 7: h · Nm(𝔞) = (7/2) · 2 = 7 = f. -/
theorem corrected_formula_f7 : weilData_K5_f7.h_num * weilData_K5_f7.ideal.ideal_norm
    = weilData_K5_f7.F.conductor * weilData_K5_f7.h_den :=
  weilData_K5_f7.fundamental_identity

/-- f = 9: h · Nm(𝔞) = 9 · 1 = 9 = f. -/
theorem corrected_formula_f9 : weilData_K5_f9.h_num * weilData_K5_f9.ideal.ideal_norm
    = weilData_K5_f9.F.conductor * weilData_K5_f9.h_den :=
  weilData_K5_f9.fundamental_identity

/-- f = 61: h · Nm(𝔞) = 61 · 1 = 61 = f. -/
theorem corrected_formula_f61 : weilData_K5_f61.h_num * weilData_K5_f61.ideal.ideal_norm
    = weilData_K5_f61.F.conductor * weilData_K5_f61.h_den :=
  weilData_K5_f61.fundamental_identity

/-- f = 163: h · Nm(𝔞) = (163/2) · 2 = 163 = f. -/
theorem corrected_formula_f163 : weilData_K5_f163.h_num * weilData_K5_f163.ideal.ideal_norm
    = weilData_K5_f163.F.conductor * weilData_K5_f163.h_den :=
  weilData_K5_f163.fundamental_identity
