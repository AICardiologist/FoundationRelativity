# Senior Professor's Final Guidance - Pristine Codebase Achieved

**Date:** September 28, 2025
**Re:** Outstanding Achievement and Path to Completion
**Status:** Zero Other Errors, Excellent Budget Compliance

## Outstanding Achievement

This is an outstanding achievement. The stabilization efforts and the "Exterior Domain Refactor" have been highly successful, resulting in a pristine codebase with zero "Other Errors" (OEs) and excellent budget compliance (18 UGs remaining).

The path forward is clear: systematically eliminate the remaining mechanical UGs by leveraging the robust infrastructure you have established, and then implement the necessary strategic prerequisites for the activation of the Riemann tensor calculation pipeline.

## Strategy: Systematic Completion by Dependency

The remaining UGs are mechanical proofs within the ExteriorDomainProofs section. We must address them in the correct order of mathematical dependency:

1. **Prerequisites:** Inverse Metric (gInv) Infrastructure
2. **Phase 1:** Christoffel Symbol Values (9 UGs)
3. **Phase 2:** Compatibility Lemmas (9 UGs)
4. **Phase 3:** Infrastructure Proofs (Clairaut, nabla_g)
5. **Phase 4:** Strategic Implementation (Fintype sums and Local Automation)

## The Robust Exterior Proof Pattern

All remaining mechanical proofs should utilize this standardized tactical pattern, which leverages the h_ext hypothesis to ensure safety from singularities, followed by algebraic normalization using field_simp and ring.

```lean
lemma example_lemma_ext : ... = ... := by
  classical -- Required for division/field_simp on real numbers

  -- 1. Extract Non-Zero Hypotheses (Crucial Step)
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext
  -- have hsin_ne := Exterior.sin_theta_ne_zero h_ext (if θ is involved)

  -- 2. Unfold Definitions and Apply Calculus
  -- Use 'simp only' with a strict list of relevant definitions and calculus rules
  simp only [...]

  -- (Optional: If derivatives are complex, apply specific derivative lemmas here)

  -- 3. Normalize Algebraically
  -- 'field_simp' uses the extracted hypotheses to safely handle division
  field_simp [hr_ne, hf_ne, pow_two] -- Add hsin_ne if needed

  -- 4. Close the Goal
  ring
```

## Execution Plan

### Prerequisites: Inverse Metric (gInv)

The calculation of Christoffel symbols depends on the inverse metric.

**Action:** Ensure the following are completed inside the ExteriorDomainProofs section:
- The definition of gInv is active
- The component lemmas (e.g., gInv_tt_ext, gInv_rr_ext) are proven using the Robust Exterior Proof Pattern

### Phase 1: Christoffel Symbol Values (9 UGs, Lines 338-423)

**Goal:** Prove the explicit values of the Christoffel symbols (e.g., Γ_trt_ext).

**Tactic Application:**
- In Step 2 (simp only), include the definition of Γtot, the relevant gInv_ext lemmas (from Prerequisites), and the necessary derivative facts (e.g., f_derivative)

**Action:** Systematically apply the pattern to the 9 UGs from Γ_trt_ext through Γ_φθφ_ext.

### Phase 2: Compatibility Lemmas (9 UGs, Lines 250-323)

**Goal:** Prove the metric compatibility equations (e.g., compat_r_tt_ext).

**Tactic Application:**
- In Step 2 (simp only), include the coordinate derivative definitions (dCoord_r, etc.), metric component definitions (g_tt, etc.), and crucially, the explicit Christoffel values proven in Phase 1 (Γ_trt_ext, etc.)

**Example: compat_r_tt_ext (Line 250)**

```lean
lemma compat_r_tt_ext :
  dCoord Idx.r (fun r' θ' => g M Idx.t Idx.t r' θ') r θ
    = 2 * Γtot M r θ Idx.t Idx.r Idx.t * g M Idx.t Idx.t r θ := by
  classical
  -- 1. Extract Hypotheses
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext

  -- 2. Unfold Definitions and Apply Calculus
  -- Use the explicit value of Γ proven in Phase 1
  simp only [dCoord_r, g_tt, Γ_trt_ext]

  -- Handle specific derivatives (Derivative of g_tt = -f M r)
  -- (This step requires specific derivative lemmas from Schwarzschild.lean)
  -- Example assuming 'f_derivative' proves the value of the derivative of f:
  -- have hf' := f_derivative M r hr_ne
  -- have h_deriv : deriv (fun s => -f M s) r = -(2 * M / r^2) := by ...
  -- rw [h_deriv]

  -- 3. Normalize & 4. Close
  -- The goal is now an algebraic identity: -(2M/r²) = 2 * (M/(r²*f)) * (-f)
  field_simp [hr_ne, hf_ne, pow_two]
  ring
```

**Action:** Apply this pattern to the 9 UGs from compat_r_tt_ext through compat_φ_θφ_ext.

### Phase 3: Infrastructure Proofs (2 UGs)

- **local_Clairaut (Line 190):** Apply the Robust Exterior Proof Pattern. This involves direct calculation by applying derivative rules twice and normalizing.

- **nabla_g (Line 223):** Address this based on the specific goal state; it likely requires unfolding the definition and potentially applying the compatibility lemmas from Phase 2.

### Phase 4: Strategic Implementation (Pre-Activation)

Once the mechanical UGs are closed (reducing the error count to the 2 architectural sorries), the following strategic steps are crucial before activation.

#### 1. Implement Fintype Sums (Option B)

Transition sumIdx from definitional expansion to Finset.sum. This is critical for managing the complexity of the upcoming Stage 1/2 assembly and Ricci contraction.

**Action:** Ensure Idx has Fintype and DecidableEq instances. Refactor the definition of sumIdx:

```lean
noncomputable def sumIdx {α : Type*} [AddCommMonoid α] (f : Idx → α) : α :=
  Finset.sum Finset.univ f
```

#### 2. Implement Local Simp Attributes (Crucial)

To enable the necessary automation for the Stage 1/2 proofs, all the newly proven _ext lemmas must be added to the local simp set within the ExteriorDomainProofs section.

**Action:** Insert the attribute [local simp] block immediately after the definitions of the _ext lemmas and before the Stage 1 infrastructure.

```lean
section ExteriorDomainProofs
-- ... (Definitions of _ext lemmas) ...

/-! ### Local Simp Attributes for Exterior Domain -/
attribute [local simp]
  -- Inverse Metric Components (gInv_tt_ext, gInv_rr_ext, ...)
  -- Christoffel Symbol Values (Γ_trt_ext, Γ_rtt_ext, ...)
  -- Compatibility Lemmas (compat_r_tt_ext, compat_r_rr_ext, ...)
  dCoord_g_via_compat_ext
  nabla_g_zero_ext
```

## Conclusion

With these phases completed, the project is ready to execute the activation plan detailed in ACTIVATION_TRACKING.md. The pristine state of the codebase positions us perfectly for systematic completion of the Schwarzschild vacuum proof.