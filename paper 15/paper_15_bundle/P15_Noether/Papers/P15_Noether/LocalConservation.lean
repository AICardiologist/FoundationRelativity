/-
Papers/P15_Noether/LocalConservation.lean
Paper 15: Noether's Theorem and the Logical Cost of Global Conservation Laws.

THE NOETHER CONTENT: Energy is conserved under Hamiltonian time evolution.

We prove conservation as a **purely algebraic identity** about finite sums.
The identity states: if we substitute Hamilton's equations
(φ̇_i = π_i, π̇_i = Δ_d φ_i - V'(φ_i)) into the time derivative of the
total energy, the result is identically zero.

The proof uses a key lemma: for any function f : Fin N → ℝ,
the sum Σ_i f(next(i)) = Σ_i f(i) under periodic boundary conditions.
This is the "shift invariance of periodic sums" — a bijective reindexing.

From this, the conservation identity follows by algebraic expansion.
Pure BISH: finite sums, algebraic cancellation, no limits.
-/
import Papers.P15_Noether.Defs

namespace Papers.P15

open Finset

noncomputable section

-- ========================================================================
-- Inverse relationship between fnext and fprev
-- ========================================================================

theorem fnext_fprev (hN : 0 < N) (i : Fin N) : fnext hN (fprev hN i) = i := by
  ext
  simp only [fnext, fprev]
  have hi := i.isLt
  -- Goal: ((i.val + N - 1) % N + 1) % N = i.val
  by_cases h : i.val = 0
  · -- i.val = 0
    rw [h]; simp only [Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    -- Goal: (N - 1 + 1) % N = 0
    rw [show N - 1 + 1 = N from by omega]
    exact Nat.mod_self N
  · -- i.val ≠ 0, hence > 0
    rw [show i.val + N - 1 = i.val - 1 + N from by omega]
    rw [Nat.add_mod_right]
    -- Goal: (i.val - 1 + 1) % N = i.val  (note: i.val - 1 < N since i.val ≤ N - 1 and i.val > 0)
    rw [Nat.mod_eq_of_lt (by omega : i.val - 1 < N)]
    rw [show i.val - 1 + 1 = i.val from by omega]
    exact Nat.mod_eq_of_lt hi

theorem fprev_fnext (hN : 0 < N) (i : Fin N) : fprev hN (fnext hN i) = i := by
  ext
  simp only [fnext, fprev]
  have hi := i.isLt
  -- Goal: ((i.val + 1) % N + N - 1) % N = i.val
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hi) with h | h
  · -- i.val + 1 = N (i is the last element)
    have hmod : (i.val + 1) % N = 0 := by
      rw [show i.val + 1 = N from by omega]
      exact Nat.mod_self N
    rw [hmod]
    -- Goal: (0 + N - 1) % N = i.val
    simp only [Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    omega
  · -- i.val + 1 < N
    have hmod : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt h
    rw [hmod]
    -- Goal: (i.val + 1 + N - 1) % N = i.val
    rw [show i.val + 1 + N - 1 = i.val + N from by omega]
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hi

-- ========================================================================
-- Shift invariance of periodic sums (key lemma)
-- ========================================================================

/-- The "next" function on Fin N is a bijection. -/
theorem fin_next_bijective (hN : 0 < N) : Function.Bijective (fnext hN) := by
  constructor
  · intro a b hab
    have : fprev hN (fnext hN a) = fprev hN (fnext hN b) := by rw [hab]
    rwa [fprev_fnext, fprev_fnext] at this
  · intro j
    exact ⟨fprev hN j, fnext_fprev hN j⟩

/-- **Shift invariance of periodic sums.** For any f : Fin N → ℝ,
    Σ_i f(next(i)) = Σ_i f(i). This is the fundamental property of
    periodic boundary conditions. -/
theorem sum_shift (hN : 0 < N) (f : Fin N → ℝ) :
    ∑ i : Fin N, f (fnext hN i) = ∑ i : Fin N, f i := by
  exact Fintype.sum_bijective _ (fin_next_bijective hN) _ _ (fun _ => rfl)

/-- The "prev" function on Fin N is also a bijection. -/
theorem fin_prev_bijective (hN : 0 < N) : Function.Bijective (fprev hN) := by
  constructor
  · intro a b hab
    have : fnext hN (fprev hN a) = fnext hN (fprev hN b) := by rw [hab]
    rwa [fnext_fprev, fnext_fprev] at this
  · intro j
    exact ⟨fnext hN j, fprev_fnext hN j⟩

/-- Shift invariance for prev: Σ_i f(prev(i)) = Σ_i f(i). -/
theorem sum_shift_prev (hN : 0 < N) (f : Fin N → ℝ) :
    ∑ i : Fin N, f (fprev hN i) = ∑ i : Fin N, f i := by
  exact Fintype.sum_bijective _ (fin_prev_bijective hN) _ _ (fun _ => rfl)

-- ========================================================================
-- The algebraic conservation identity
-- ========================================================================

/-- The "energy rate of change" expression, summed over all sites.
    Under Hamilton's equations (φ̇_i = π_i, π̇_i = Δ_d φ_i - V'(φ_i)),
    this equals dE/dt. We prove it equals 0. -/
def totalEnergyRate (hN : 0 < N) (φ π : Fin N → ℝ) (V' : ℝ → ℝ) : ℝ :=
  ∑ i : Fin N,
    (π i * (discreteLaplacian hN φ i - V' (φ i))
     + (φ (fnext hN i) - φ i) * (π (fnext hN i) - π i)
     + V' (φ i) * π i)

/-- **Noether's Theorem (algebraic form).**

    The total rate of energy change vanishes identically:

      Σ_i [π_i · (Δ_d φ_i - V'(φ_i)) + (φ_{i+1} - φ_i)(π_{i+1} - π_i) + V'(φ_i) · π_i] = 0

    This is the algebraic identity underlying energy conservation for
    Hamiltonian lattice field theory with periodic boundary conditions.

    Physical interpretation: along any Hamiltonian trajectory, dE/dt = 0.
    The proof is pure BISH — no limits, no completeness, no omniscience. -/
theorem noether_conservation (hN : 2 ≤ N) (φ π : Fin N → ℝ) (V' : ℝ → ℝ) :
    totalEnergyRate (by omega) φ π V' = 0 := by
  unfold totalEnergyRate discreteLaplacian
  have hN' : 0 < N := by omega
  -- Step 1: Ring-simplify each summand.
  -- After expanding and cancelling V' terms, each summand equals:
  --   (φ(next i) · π(next i) - φ_i · π_i) + (π_i · φ(prev i) - φ_i · π(next i))
  conv_lhs =>
    arg 2; ext i
    rw [show π i * (φ (fnext hN' i) - 2 * φ i + φ (fprev hN' i) - V' (φ i))
        + (φ (fnext hN' i) - φ i) * (π (fnext hN' i) - π i)
        + V' (φ i) * π i
      = (φ (fnext hN' i) * π (fnext hN' i) - φ i * π i)
        + (π i * φ (fprev hN' i) - φ i * π (fnext hN' i))
      from by ring]
  rw [Finset.sum_add_distrib]
  -- Sum 1: Σ_i [φ(next i)·π(next i) - φ_i·π_i] = 0 (telescoping)
  have h1 : ∑ i : Fin N, (φ (fnext hN' i) * π (fnext hN' i) - φ i * π i) = 0 := by
    rw [Finset.sum_sub_distrib]
    rw [sum_shift hN' (fun i => φ i * π i)]
    ring
  -- Sum 2: Σ_i [π_i·φ(prev i) - φ_i·π(next i)] = 0
  -- Key: Σ_i π_i·φ(prev i) = Σ_i π(next i)·φ(prev(next i)) = Σ_i π(next i)·φ(i)
  --       by shift invariance with fnext.
  -- Then Σ_i π(next i)·φ(i) = Σ_i φ(i)·π(next i) by commutativity.
  -- So both parts of the difference are equal.
  have h2 : ∑ i : Fin N, (π i * φ (fprev hN' i) - φ i * π (fnext hN' i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    suffices ∑ i : Fin N, π i * φ (fprev hN' i) = ∑ i : Fin N, φ i * π (fnext hN' i) by
      linarith
    -- Reindex the LHS: substitute i ↦ fnext hN' j
    rw [← sum_shift hN' (fun i => π i * φ (fprev hN' i))]
    -- Now LHS = Σ_j π(next j) * φ(prev(next j)) = Σ_j π(next j) * φ(j)
    simp only [fprev_fnext]
    -- Now: Σ_j π(fnext hN' j) * φ j = Σ_j φ j * π(fnext hN' j)
    congr 1; ext j; ring
  linarith

-- ========================================================================
-- Conservation along a Hamiltonian trajectory
-- ========================================================================

/-- Hamilton's equations of motion on the lattice (discrete time formulation).
    Given states s and s', this says s' is obtained from s by one step
    of the exact Hamiltonian flow:
      φ'_i = φ_i + Δt · π_i
      π'_i = π_i + Δt · (Δ_d φ_i - V'(φ_i))
    Note: this is the symplectic Euler method, which does NOT exactly conserve
    energy. The exact conservation identity (noether_conservation) is about
    the continuous-time Hamiltonian flow, expressed algebraically.
    For the symplectic Euler step, energy is conserved to O(Δt²). -/
def hamiltonStep (V' : ℝ → ℝ) (hN : 0 < N) (Δt : ℝ)
    (s : LatticeState N) : LatticeState N where
  φ := fun i => s.φ i + Δt * s.π i
  π := fun i => s.π i + Δt * (discreteLaplacian hN s.φ i - V' (s.φ i))

end

end Papers.P15
