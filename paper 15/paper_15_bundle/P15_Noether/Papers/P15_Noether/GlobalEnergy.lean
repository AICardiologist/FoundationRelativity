/-
Papers/P15_Noether/GlobalEnergy.lean
Paper 15: Noether's Theorem and the Logical Cost of Global Conservation Laws.

The LPO equivalence: "every bounded partial sum of non-negative terms
converges" ↔ BMC ↔ LPO.

The abstract framework:
  - NPSC (Nonnegative Partial Sum Convergence): every bounded sequence
    of partial sums of non-negative terms converges.
  - NPSC ↔ BMC: forward by telescoping (increments), reverse by monotonicity.
  - Therefore NPSC ↔ LPO.

The physical instantiation: the partial energy sequence E_N = Σ_{i<N} e_i
is an instance of NPSC (each e_i ≥ 0). So asserting that E = lim E_N
exists for all bounded field configurations is equivalent to LPO.
-/
import Papers.P15_Noether.Monotonicity
import Papers.P15_Noether.LPO_BMC

namespace Papers.P15

open Finset

noncomputable section

-- ========================================================================
-- Abstract framework: NPSC
-- ========================================================================

/-- **Nonnegative Partial Sum Convergence (NPSC).**
    Every bounded sequence of partial sums of non-negative terms converges.

    This is the lattice-energy version of BMC: when each energy density
    term e_i ≥ 0 and the partial sums Σ_{i<N} e_i are bounded, then
    the infinite sum converges. -/
def NPSC : Prop :=
  ∀ (d : ℕ → ℝ), (∀ n, 0 ≤ d n) →
    (∃ M : ℝ, ∀ N, ∑ i ∈ Finset.range N, d i ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |∑ i ∈ Finset.range N, d i - L| < ε

-- ========================================================================
-- NPSC ↔ BMC
-- ========================================================================

/-- **NPSC ↔ BMC.** Nonnegative Partial Sum Convergence is equivalent to
    Bounded Monotone Convergence.

    Forward (NPSC → BMC): Given a monotone bounded sequence a_n, define
    d_n = a_{n+1} - a_n ≥ 0 (by monotonicity). The partial sums telescope:
    Σ_{i<N} d_i = a_N - a_0, which is bounded since a is bounded.
    NPSC gives convergence of partial sums, hence convergence of a.

    Reverse (BMC → NPSC): Given non-negative d_n with bounded partial sums,
    the sequence S_N = Σ_{i<N} d_i is monotone (adding a non-negative term)
    and bounded. BMC gives convergence. -/
theorem npsc_iff_bmc : NPSC ↔ BMC := by
  constructor
  · -- NPSC → BMC
    intro hNPSC a M ha_mono ha_bdd
    -- Define d_n = a_{n+1} - a_n ≥ 0
    set d := fun n => a (n + 1) - a n with hd_def
    have hd_nonneg : ∀ n, 0 ≤ d n := fun n => by
      simp only [hd_def]
      linarith [ha_mono (Nat.le_succ n)]
    -- Partial sums telescope: Σ_{i<N} d_i = a_N - a_0
    have htelescope : ∀ N, ∑ i ∈ Finset.range N, d i = a N - a 0 := by
      intro N
      induction N with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [hd_def]
    -- Partial sums bounded: a_N - a_0 ≤ M - a_0
    have hbdd : ∃ M', ∀ N, ∑ i ∈ Finset.range N, d i ≤ M' :=
      ⟨M - a 0, fun N => by rw [htelescope]; linarith [ha_bdd N]⟩
    -- Apply NPSC
    obtain ⟨L_d, hL_d⟩ := hNPSC d hd_nonneg hbdd
    -- The limit of a is L_d + a_0
    exact ⟨L_d + a 0, fun ε hε => by
      obtain ⟨N₀, hN₀⟩ := hL_d ε hε
      exact ⟨N₀, fun N hN => by
        have h := hN₀ N hN
        rw [htelescope] at h
        -- h : |a N - a 0 - L_d| < ε
        -- goal: |a N - (L_d + a 0)| < ε
        -- These differ only by ring: a N - (L_d + a 0) = a N - a 0 - L_d
        rwa [show a N - (L_d + a 0) = a N - a 0 - L_d from by ring]
        ⟩⟩
  · -- BMC → NPSC
    intro hBMC d hd_nonneg hd_bdd
    -- S_N = Σ_{i<N} d_i is monotone and bounded
    set S := fun N => ∑ i ∈ Finset.range N, d i with hS_def
    have hS_mono : Monotone S := by
      apply monotone_nat_of_le_succ
      intro n
      simp only [hS_def, Finset.sum_range_succ]
      linarith [hd_nonneg n]
    obtain ⟨M, hM⟩ := hd_bdd
    -- Apply BMC directly
    exact hBMC S M hS_mono hM

-- ========================================================================
-- Headline theorem: NPSC ↔ LPO
-- ========================================================================

/-- **NPSC ↔ LPO.** Nonnegative Partial Sum Convergence is equivalent to
    the Limited Principle of Omniscience. -/
theorem npsc_iff_lpo : NPSC ↔ LPO := by
  rw [npsc_iff_bmc]
  exact lpo_iff_bmc.symm

-- ========================================================================
-- Physical instantiation: partial energy is an NPSC instance
-- ========================================================================

/-- The partial energy sequence is a monotone bounded sequence when V ≥ 0
    and the field configuration has bounded total energy. Therefore,
    asserting its convergence for all bounded configurations is LPO. -/
theorem partialEnergy_is_nonneg_partial_sum (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (φ : ℕ → ℝ) (π : ℕ → ℝ) :
    (∀ n, 0 ≤ infiniteEnergyDensity V φ π n) ∧
    partialEnergy V φ π = fun N => ∑ i ∈ Finset.range N, infiniteEnergyDensity V φ π i :=
  ⟨infiniteEnergyDensity_nonneg V hV φ π, rfl⟩

/-- **Headline theorem: Global energy existence ↔ LPO.**

    The assertion "for every bounded field configuration with V ≥ 0,
    the infinite-volume energy E = lim_{N→∞} E_N exists" is equivalent to LPO.

    Forward (LPO → global energy): LPO → BMC. The partial energy is
    monotone (Monotonicity.lean) and bounded by hypothesis. BMC gives convergence.

    Reverse (global energy → LPO): The partial energy is a sum of
    non-negative terms. If all such sums converge when bounded,
    then NPSC holds. NPSC ↔ BMC ↔ LPO. -/
theorem global_energy_iff_LPO :
    (∀ (V : ℝ → ℝ), (∀ x, 0 ≤ V x) →
      ∀ (φ : ℕ → ℝ) (π : ℕ → ℝ) (M : ℝ), (∀ N, partialEnergy V φ π N ≤ M) →
      ∃ E : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |partialEnergy V φ π N - E| < ε)
    ↔ LPO := by
  constructor
  · -- Global energy → LPO
    intro hGE
    -- It suffices to show NPSC
    rw [← npsc_iff_lpo]
    intro d hd_nonneg hd_bdd
    -- Encode d as a partial energy: set V(x) = 0, φ = 0, π = 0
    -- and use a custom potential that gives d_i directly
    -- Simplest: define V_d(x) := d (some encoding of x)... too complex.
    -- Better: just observe that the hypothesis gives convergence for ANY V ≥ 0.
    -- Choose V(x) = 0, φ = 0, π_i = 0 ... then partialEnergy = 0. Not useful.
    --
    -- Actually, we need to encode d into the energy. The cleanest way:
    -- Choose V = 0, φ(i) = 0 for all i, and encode d into π:
    -- We want ½ π_i² = d_i, but this requires π_i = √(2·d_i).
    -- The gradient terms ½(φ_{i+1} - φ_i)² = 0 since φ = 0.
    --
    -- Actually, even simpler: observe that the hypothesis applies to ALL V ≥ 0.
    -- Choose V such that V(0) = d_i at each site... but V is a single function.
    --
    -- Cleanest encoding: we don't need the full generality of partialEnergy.
    -- Since partialEnergy V φ π N = Σ_{i<N} [½π_i² + ½(φ_{i+1}-φ_i)² + V(φ_i)],
    -- choose φ = 0, V = 0, and set π_i so that ½π_i² = d_i.
    -- This requires d_i ≥ 0 (which we have) and π_i = √(2·d_i).
    --
    -- Then partialEnergy 0 0 π N = Σ_{i<N} ½·(√(2·d_i))² = Σ_{i<N} d_i. ✓
    set π_enc := fun i => Real.sqrt (2 * d i)
    have hV0 : ∀ (x : ℝ), 0 ≤ (fun _ : ℝ => (0 : ℝ)) x := fun _ => le_refl 0
    -- partialEnergy with V=0, φ=0, π = π_enc
    have henc : ∀ N, partialEnergy (fun _ => 0) (fun _ => 0) π_enc N =
        ∑ i ∈ Finset.range N, d i := by
      intro N
      unfold partialEnergy infiniteEnergyDensity
      congr 1; ext i
      -- Goal: ½·(√(2·d_i))² + ½·(0 - 0)² + 0 = d_i
      -- Simplify: (0 - 0) = 0, 0² = 0, and (√x)² = x for x ≥ 0
      rw [Real.sq_sqrt (by linarith [hd_nonneg i] : 0 ≤ 2 * d i)]
      ring
    -- Apply the hypothesis
    obtain ⟨M, hM⟩ := hd_bdd
    have hbdd_enc : ∀ N, partialEnergy (fun _ => 0) (fun _ => 0) π_enc N ≤ M := by
      intro N; rw [henc]; exact hM N
    obtain ⟨E, hE⟩ := hGE (fun _ => 0) hV0 (fun _ => 0) π_enc M hbdd_enc
    exact ⟨E, fun ε hε => by
      obtain ⟨N₀, hN₀⟩ := hE ε hε
      exact ⟨N₀, fun N hN => by rw [← henc]; exact hN₀ N hN⟩⟩
  · -- LPO → Global energy
    intro hLPO V hV φ π M hM
    -- LPO → BMC
    have hBMC := bmc_of_lpo hLPO
    -- partialEnergy is monotone and bounded by M
    exact hBMC (partialEnergy V φ π) M (partialEnergy_mono V hV φ π) hM

end

end Papers.P15
