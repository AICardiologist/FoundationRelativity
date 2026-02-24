/-
  Paper 58: Class Number Correction — Gram Matrix Computations
  Gram matrices for the Weil lattice on integral bases of O_K-ideals.

  For K = ℚ(√-5), h_K = 2, |Δ_K| = 20:
    Free case (basis {1, √-5}):   G = !![2f, 0; 0, 10f],    det = 20f²
    NonFree case (basis {2, 1+√-5}): G = !![4f, 2f; 2f, 6f], det = 20f²
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Gram Matrix Templates

The Gram matrix of the real intersection pairing B(x,y) = Tr_{K/ℚ} H(x,y)
on an integral ℤ-basis {α·w₀, β·w₀} of W_int = 𝔞·w₀ is:

    G = [[2h·Nm(α), h·Tr(αβ̄)], [h·Tr(αβ̄), 2h·Nm(β)]]

For K = ℚ(√-5):
  Free (𝔞 = O_K, basis {1, √-5}, Nm(𝔞) = 1, h = f):
    Nm(1) = 1, Nm(√-5) = 5, Tr(1·(-√-5)) = 0
    G = [[2f, 0], [0, 10f]], det = 20f²

  NonFree (𝔞 = 𝔭 = (2, 1+√-5), basis {2, 1+√-5}, Nm(𝔞) = 2, h = f/2):
    Nm(2) = 4, Nm(1+√-5) = 6, Tr(2·(1-√-5)) = 4
    G = [[4f, 2f], [2f, 6f]], det = 20f²
-/

-- ========================================================================
-- Section 1: Template Gram matrices
-- ========================================================================

/-- Gram matrix for the free case: basis {1, √-5}, h = f. -/
def gramFree (f : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2 * f, 0; 0, 10 * f]

/-- Gram matrix for the non-free case: basis {2, 1+√-5}, h = f/2. -/
def gramNonFree (f : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![4 * f, 2 * f; 2 * f, 6 * f]

/-- Template determinant: free case gives det = 20f². -/
theorem gramFree_det (f : ℤ) : (gramFree f).det = 20 * f ^ 2 := by
  simp [gramFree, Matrix.det_fin_two]
  ring

/-- Template determinant: non-free case gives det = 20f². -/
theorem gramNonFree_det (f : ℤ) : (gramNonFree f).det = 20 * f ^ 2 := by
  simp [gramNonFree, Matrix.det_fin_two]
  ring

-- ========================================================================
-- Section 2: Per-conductor Gram matrices for K = ℚ(√-5)
-- ========================================================================

/-- f = 7 (non-free): G = [[28, 14], [14, 42]], det = 980 = 49 · 20. -/
def gram_K5_f7 : Matrix (Fin 2) (Fin 2) ℤ := !![28, 14; 14, 42]

theorem gram_K5_f7_eq : gram_K5_f7 = gramNonFree 7 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gram_K5_f7, gramNonFree]

theorem gram_K5_f7_det : gram_K5_f7.det = 980 := by native_decide

theorem gram_K5_f7_volume : (7 : ℤ) ^ 2 * 20 = 980 := by norm_num

theorem gram_K5_f7_match : gram_K5_f7.det = (7 : ℤ) ^ 2 * 20 := by
  rw [gram_K5_f7_det]; norm_num

/-- f = 9 (free): G = [[18, 0], [0, 90]], det = 1620 = 81 · 20. -/
def gram_K5_f9 : Matrix (Fin 2) (Fin 2) ℤ := !![18, 0; 0, 90]

theorem gram_K5_f9_eq : gram_K5_f9 = gramFree 9 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gram_K5_f9, gramFree]

theorem gram_K5_f9_det : gram_K5_f9.det = 1620 := by native_decide

theorem gram_K5_f9_volume : (9 : ℤ) ^ 2 * 20 = 1620 := by norm_num

theorem gram_K5_f9_match : gram_K5_f9.det = (9 : ℤ) ^ 2 * 20 := by
  rw [gram_K5_f9_det]; norm_num

/-- f = 61 (free): G = [[122, 0], [0, 610]], det = 74420 = 3721 · 20. -/
def gram_K5_f61 : Matrix (Fin 2) (Fin 2) ℤ := !![122, 0; 0, 610]

theorem gram_K5_f61_eq : gram_K5_f61 = gramFree 61 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gram_K5_f61, gramFree]

theorem gram_K5_f61_det : gram_K5_f61.det = 74420 := by native_decide

theorem gram_K5_f61_volume : (61 : ℤ) ^ 2 * 20 = 74420 := by norm_num

theorem gram_K5_f61_match : gram_K5_f61.det = (61 : ℤ) ^ 2 * 20 := by
  rw [gram_K5_f61_det]; norm_num

/-- f = 163 (non-free): G = [[652, 326], [326, 978]], det = 531380 = 26569 · 20. -/
def gram_K5_f163 : Matrix (Fin 2) (Fin 2) ℤ := !![652, 326; 326, 978]

theorem gram_K5_f163_eq : gram_K5_f163 = gramNonFree 163 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gram_K5_f163, gramNonFree]

theorem gram_K5_f163_det : gram_K5_f163.det = 531380 := by native_decide

theorem gram_K5_f163_volume : (163 : ℤ) ^ 2 * 20 = 531380 := by norm_num

theorem gram_K5_f163_match : gram_K5_f163.det = (163 : ℤ) ^ 2 * 20 := by
  rw [gram_K5_f163_det]; norm_num

-- ========================================================================
-- Section 3: Universal identity
-- ========================================================================

/-- The topological volume det(G) = f² · |Δ_K| is an absolute invariant.
    Both template Gram matrices yield det = 20f². -/
theorem gram_volume_invariant (f : ℤ) :
    (gramFree f).det = (gramNonFree f).det := by
  rw [gramFree_det, gramNonFree_det]
