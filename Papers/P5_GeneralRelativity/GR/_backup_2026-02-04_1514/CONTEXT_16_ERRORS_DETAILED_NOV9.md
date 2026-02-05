# DETAILED CONTEXT FOR ALL 16 ERRORS - November 9, 2025

**Purpose**: Provide Paul with complete context to create revised patchset  
**Branch**: `rescue/riemann-16err-nov9` (commit abd50e2)  
**Build Log**: `build_current_state_nov9.txt`  
**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

---

## Error Distribution Summary

**Cluster 1** (Lines 8751-8937): 5 errors  
**Cluster 2** (Lines 8966-9151): 5 errors  
**Cluster 3** (Lines 9192-9824): 6 errors  

**Total**: 16 errors

---

## ERROR AT LINE 8751

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8751:65: unsolved goals
case calc.step
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
```

### Code Context (Lines 8736 to 8766):
```lean
  8736→    (sumIdx B_b) - Cμa + Cνa
  8737→      = sumIdx (fun ρ =>
  8738→          B_b ρ
  8739→        - (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
  8740→        + (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b)) := by
  8741→    -- (ΣB_b − ΣX) + ΣY = Σ (B_b − X) + ΣY = Σ ((B_b − X) + Y)
  8742→    rw [hCμa, hCνa]
  8743→    rw [← sumIdx_map_sub B_b (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))]
  8744→    rw [← sumIdx_add_distrib]
  8745→
  8746→  have hb :
  8747→    (sumIdx B_b)
  8748→    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  8749→    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  8750→  =
  8751→    - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by
  8752→    classical
  8753→
  8754→    -- 0) Open only the outer shells; keep sums atomic.
  8755→    simp only [nabla_g, RiemannUp, sub_eq_add_neg]
  8756→
  8757→    /- 1) Cancel the Γ·∂g payload at Σ_ρ level.
  8758→          Keep it at Σ_ρ and use a tiny scalar `ring` under `sumIdx_congr`. -/
  8759→    have payload_cancel :
  8760→      sumIdx (fun ρ =>
  8761→        (-(Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ
  8762→          + (Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ)
  8763→        - ((Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ
  8764→           - (Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ)
  8765→      ) = 0 := by
  8766→      have h : ∀ ρ,
```

---

## ERROR AT LINE 8901

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8901:6: failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information

```

### Code Context (Lines 8886 to 8916):
```lean
  8886→      =
  8887→      sumIdx (fun ρ =>
  8888→        - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  8889→            - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  8890→            + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8891→            - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ) * g M ρ b r θ)
  8892→        * (if ρ = b then 1 else 0)) := by
  8893→      classical
  8894→      -- Put the minus inside to match the helper F·g shape, then insert δ in one shot.
  8895→      have := insert_delta_right_diag M r θ b (fun ρ =>
  8896→        - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  8897→            - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  8898→            + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8899→            - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ))
  8900→      -- `-(E * g) = (-E) * g` on both sides.
  8901→      simpa [neg_mul_right₀] using this
  8902→
  8903→    /- 3) Final scalar packaging -/
  8904→    have scalar_finish :
  8905→      ∀ ρ,
  8906→        ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
  8907→          +  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ )
  8908→        +  ( g M ρ b r θ *
  8909→              ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8910→               -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ) )
  8911→        =
  8912→          - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  8913→               - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  8914→               + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8915→               - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
  8916→              * g M ρ b r θ ) := by
```

---

## ERROR AT LINE 8916

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8916:33: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
```

### Code Context (Lines 8901 to 8931):
```lean
  8901→      simpa [neg_mul_right₀] using this
  8902→
  8903→    /- 3) Final scalar packaging -/
  8904→    have scalar_finish :
  8905→      ∀ ρ,
  8906→        ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
  8907→          +  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ )
  8908→        +  ( g M ρ b r θ *
  8909→              ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8910→               -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ) )
  8911→        =
  8912→          - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  8913→               - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  8914→               + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8915→               - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
  8916→              * g M ρ b r θ ) := by
  8917→      intro ρ
  8918→      ring
  8919→
  8920→    /- 4) Assemble to get hb_partial with rho_core_b -/
  8921→    calc
  8922→      (sumIdx B_b)
  8923→    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  8924→    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  8925→        = sumIdx (fun ρ =>
  8926→              - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  8927→                 - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  8928→                 + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8929→                 - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
  8930→               * g M ρ b r θ) := by
  8931→        simp only [nabla_g, RiemannUp, sub_eq_add_neg]
```

---

## ERROR AT LINE 8933

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8933:8: Type mismatch
  H
has type
  (sumIdx fun i =>
      -dCoord μ (fun r θ => Γtot M r θ i ν a) r θ * g M i b r θ +
          dCoord ν (fun r θ => Γtot M r θ i μ a) r θ * g M i b r θ +
        g M i b r θ *
          ((sumIdx fun e => Γtot M r θ i μ e * Γtot M r θ e ν a) -
            sumIdx fun e => Γtot M r θ i ν e * Γtot M r θ e μ a)) =
    sumIdx fun i =>
      -(((dCoord μ (fun r θ => Γtot M r θ i ν a) r θ - dCoord ν (fun r θ => Γtot M r θ i μ a) r θ +
              sumIdx fun e => Γtot M r θ i μ e * Γtot M r θ e ν a) -
            sumIdx fun e => Γtot M r θ i ν e * Γtot M r θ e μ a) *
          g M i b r θ)
but is expected to have type
  ((sumIdx B_b +
        -sumIdx fun ρ =>
            Γtot M r θ ρ μ a *
              ((dCoord ν (fun r θ => g M ρ b r θ) r θ + -sumIdx fun e => Γtot M r θ e ν ρ * g M e b r θ) +
                -sumIdx fun e => Γtot M r θ e ν b * g M ρ e r θ)) +
```

### Code Context (Lines 8918 to 8948):
```lean
  8918→      ring
  8919→
  8920→    /- 4) Assemble to get hb_partial with rho_core_b -/
  8921→    calc
  8922→      (sumIdx B_b)
  8923→    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  8924→    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  8925→        = sumIdx (fun ρ =>
  8926→              - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  8927→                 - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  8928→                 + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8929→                 - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
  8930→               * g M ρ b r θ) := by
  8931→        simp only [nabla_g, RiemannUp, sub_eq_add_neg]
  8932→        have H := sumIdx_congr scalar_finish
  8933→        exact H
  8934→      _   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
  8935→          + rho_core_b := by
  8936→        simp only [h_rho_core_b]
  8937→        rw [h_insert_delta_for_b, ← sumIdx_add_distrib]
  8938→        apply sumIdx_congr; intro ρ
  8939→        simp only [RiemannUp]
  8940→        split_ifs with h_rho_eq_b
  8941→        · -- ρ = b case
  8942→          subst h_rho_eq_b
  8943→          simp only [h_bb_core]
  8944→          rw [← scalar_finish_bb]
  8945→          ring
  8946→        · -- ρ ≠ b case: Kronecker δ = 0
  8947→          simp
  8948→          ring
```

---

## ERROR AT LINE 8937

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8937:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun ρ =>
    -(((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
            sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
          sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) *
        g M ρ b r θ)
in the target expression
  (sumIdx fun ρ =>
      -((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
              sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
            sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) *
        g M ρ b r θ) =
    (-sumIdx fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)

```

### Code Context (Lines 8922 to 8952):
```lean
  8922→      (sumIdx B_b)
  8923→    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  8924→    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  8925→        = sumIdx (fun ρ =>
  8926→              - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  8927→                 - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  8928→                 + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  8929→                 - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
  8930→               * g M ρ b r θ) := by
  8931→        simp only [nabla_g, RiemannUp, sub_eq_add_neg]
  8932→        have H := sumIdx_congr scalar_finish
  8933→        exact H
  8934→      _   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
  8935→          + rho_core_b := by
  8936→        simp only [h_rho_core_b]
  8937→        rw [h_insert_delta_for_b, ← sumIdx_add_distrib]
  8938→        apply sumIdx_congr; intro ρ
  8939→        simp only [RiemannUp]
  8940→        split_ifs with h_rho_eq_b
  8941→        · -- ρ = b case
  8942→          subst h_rho_eq_b
  8943→          simp only [h_bb_core]
  8944→          rw [← scalar_finish_bb]
  8945→          ring
  8946→        · -- ρ ≠ b case: Kronecker δ = 0
  8947→          simp
  8948→          ring
  8949→
  8950→  -- 7) **a-branch**: identical pattern with (a,b) swapped appropriately.
  8951→  have ha_pack :
  8952→    (sumIdx B_a) - Cμb + Cνb
```

---

## ERROR AT LINE 8966

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8966:65: unsolved goals
case calc.step
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
```

### Code Context (Lines 8951 to 8981):
```lean
  8951→  have ha_pack :
  8952→    (sumIdx B_a) - Cμb + Cνb
  8953→      = sumIdx (fun ρ =>
  8954→          B_a ρ
  8955→        - (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ)
  8956→        + (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ)) := by
  8957→    rw [hCμb, hCνb]
  8958→    rw [← sumIdx_map_sub B_a (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))]
  8959→    rw [← sumIdx_add_distrib]
  8960→
  8961→  have ha :
  8962→    (sumIdx B_a)
  8963→    - sumIdx (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
  8964→    + sumIdx (fun ρ => (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
  8965→  =
  8966→    - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) := by
  8967→    classical
  8968→
  8969→    -- 0) Open only the outer shells; keep sums atomic.
  8970→    simp only [nabla_g, RiemannUp, sub_eq_add_neg]
  8971→
  8972→    /- 1) Cancel the Γ·∂g payload at Σ_ρ level. -/
  8973→    have payload_cancel :
  8974→      sumIdx (fun ρ =>
  8975→        (-(Γtot M r θ ρ ν b) * dCoord μ (fun r θ => g M a ρ r θ) r θ
  8976→          + (Γtot M r θ ρ μ b) * dCoord ν (fun r θ => g M a ρ r θ) r θ)
  8977→        - ((Γtot M r θ ρ μ b) * dCoord ν (fun r θ => g M a ρ r θ) r θ
  8978→           - (Γtot M r θ ρ ν b) * dCoord μ (fun r θ => g M a ρ r θ) r θ)
  8979→      ) = 0 := by
  8980→      have h : ∀ ρ,
  8981→        (-(Γtot M r θ ρ ν b) * dCoord μ (fun r θ => g M a ρ r θ) r θ
```

---

## ERROR AT LINE 9114

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9114:6: failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information

```

### Code Context (Lines 9099 to 9129):
```lean
  9099→            + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9100→            - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) ) * g M a ρ r θ))
  9101→      =
  9102→      sumIdx (fun ρ =>
  9103→        - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
  9104→            - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
  9105→            + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9106→            - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) ) * g M a ρ r θ)
  9107→        * (if ρ = a then 1 else 0)) := by
  9108→      classical
  9109→      have := insert_delta_left_diag M r θ a (fun ρ =>
  9110→        - ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
  9111→            - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
  9112→            + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9113→            - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) ))
  9114→      simpa [neg_mul_left₀] using this
  9115→
  9116→    /- 3) Final scalar packaging -/
  9117→    have scalar_finish :
  9118→      ∀ ρ,
  9119→        ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ) * g M a ρ r θ
  9120→          +  (dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ) * g M a ρ r θ )
  9121→        +  ( g M a ρ r θ *
  9122→              ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9123→               -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) ) )
  9124→        =
  9125→          - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
  9126→               - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
  9127→               + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9128→               - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) )
  9129→              * g M a ρ r θ ) := by
```

---

## ERROR AT LINE 9129

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9129:33: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
```

### Code Context (Lines 9114 to 9144):
```lean
  9114→      simpa [neg_mul_left₀] using this
  9115→
  9116→    /- 3) Final scalar packaging -/
  9117→    have scalar_finish :
  9118→      ∀ ρ,
  9119→        ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ) * g M a ρ r θ
  9120→          +  (dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ) * g M a ρ r θ )
  9121→        +  ( g M a ρ r θ *
  9122→              ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9123→               -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) ) )
  9124→        =
  9125→          - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
  9126→               - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
  9127→               + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9128→               - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) )
  9129→              * g M a ρ r θ ) := by
  9130→      intro ρ
  9131→      ring
  9132→
  9133→    /- 4) Assemble to get ha_partial with rho_core_a -/
  9134→    calc
  9135→      (sumIdx B_a)
  9136→    - sumIdx (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
  9137→    + sumIdx (fun ρ => (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
  9138→        = sumIdx (fun ρ =>
  9139→              - ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
  9140→                 - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
  9141→                 + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9142→                 - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) )
  9143→               * g M a ρ r θ) := by
  9144→        simp only [nabla_g, RiemannUp, sub_eq_add_neg]
```

---

## ERROR AT LINE 9147

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9147:8: Type mismatch
  H
has type
  (sumIdx fun i =>
      -dCoord μ (fun r θ => Γtot M r θ i ν b) r θ * g M a i r θ +
          dCoord ν (fun r θ => Γtot M r θ i μ b) r θ * g M a i r θ +
        g M a i r θ *
          ((sumIdx fun e => Γtot M r θ i μ e * Γtot M r θ e ν b) -
            sumIdx fun e => Γtot M r θ i ν e * Γtot M r θ e μ b)) =
    sumIdx fun i =>
      -(((dCoord μ (fun r θ => Γtot M r θ i ν b) r θ - dCoord ν (fun r θ => Γtot M r θ i μ b) r θ +
              sumIdx fun e => Γtot M r θ i μ e * Γtot M r θ e ν b) -
            sumIdx fun e => Γtot M r θ i ν e * Γtot M r θ e μ b) *
          g M a i r θ)
but is expected to have type
  ((sumIdx B_a +
        -sumIdx fun ρ =>
            Γtot M r θ ρ μ b *
              ((dCoord ν (fun r θ => g M a ρ r θ) r θ + -sumIdx fun e => Γtot M r θ e ν a * g M e ρ r θ) +
                -sumIdx fun e => Γtot M r θ e ν ρ * g M a e r θ)) +
```

### Code Context (Lines 9132 to 9162):
```lean
  9132→
  9133→    /- 4) Assemble to get ha_partial with rho_core_a -/
  9134→    calc
  9135→      (sumIdx B_a)
  9136→    - sumIdx (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
  9137→    + sumIdx (fun ρ => (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
  9138→        = sumIdx (fun ρ =>
  9139→              - ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
  9140→                 - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
  9141→                 + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9142→                 - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) )
  9143→               * g M a ρ r θ) := by
  9144→        simp only [nabla_g, RiemannUp, sub_eq_add_neg]
  9145→        have H := sumIdx_congr scalar_finish
  9146→        -- deterministically normalize the scalar shell; no binder algebra
  9147→        exact H
  9148→      _   = - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ)
  9149→          + rho_core_a := by
  9150→        simp only [h_rho_core_a]
  9151→        rw [h_insert_delta_for_a, ← sumIdx_add_distrib]
  9152→        apply sumIdx_congr; intro ρ
  9153→        simp only [RiemannUp]
  9154→        split_ifs with h_rho_eq_a
  9155→        · -- ρ = a case
  9156→          subst h_rho_eq_a
  9157→          simp only [h_aa_core]
  9158→          rw [← scalar_finish_aa]
  9159→          ring
  9160→        · -- ρ ≠ a case: Kronecker δ = 0
  9161→          simp
  9162→          ring
```

---

## ERROR AT LINE 9151

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9151:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun ρ =>
    -(((dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ +
            sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b) -
          sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) *
        g M a ρ r θ)
in the target expression
  (sumIdx fun ρ =>
      -((dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ +
              sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b) -
            sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) *
        g M a ρ r θ) =
    (-sumIdx fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)

```

### Code Context (Lines 9136 to 9166):
```lean
  9136→    - sumIdx (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
  9137→    + sumIdx (fun ρ => (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
  9138→        = sumIdx (fun ρ =>
  9139→              - ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
  9140→                 - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
  9141→                 + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
  9142→                 - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) )
  9143→               * g M a ρ r θ) := by
  9144→        simp only [nabla_g, RiemannUp, sub_eq_add_neg]
  9145→        have H := sumIdx_congr scalar_finish
  9146→        -- deterministically normalize the scalar shell; no binder algebra
  9147→        exact H
  9148→      _   = - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ)
  9149→          + rho_core_a := by
  9150→        simp only [h_rho_core_a]
  9151→        rw [h_insert_delta_for_a, ← sumIdx_add_distrib]
  9152→        apply sumIdx_congr; intro ρ
  9153→        simp only [RiemannUp]
  9154→        split_ifs with h_rho_eq_a
  9155→        · -- ρ = a case
  9156→          subst h_rho_eq_a
  9157→          simp only [h_aa_core]
  9158→          rw [← scalar_finish_aa]
  9159→          ring
  9160→        · -- ρ ≠ a case: Kronecker δ = 0
  9161→          simp
  9162→          ring
  9163→
  9164→  -- The two ρρ-cores cancel by commutativity
  9165→  have diag_cancel : rho_core_b + rho_core_a = 0 := by
  9166→    simp only [h_rho_core_b, h_rho_core_a]
```

---

## ERROR AT LINE 9192

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9192:88: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
```

### Code Context (Lines 9177 to 9207):
```lean
  9177→    simpa [h] using sumIdx_zero
  9178→
  9179→  -- Combine the two branches, canceling the ρρ-cores
  9180→  have branches_sum :
  9181→      (sumIdx B_b)
  9182→    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  9183→    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  9184→    + (sumIdx B_a)
  9185→    - sumIdx (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
  9186→    + sumIdx (fun ρ => (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
  9187→    =
  9188→      - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
  9189→    - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) := by
  9190→    calc
  9191→      _ = ( - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) + rho_core_b )
  9192→        + ( - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) + rho_core_a ) := by
  9193→        rw [← hb, ← ha]
  9194→      _ = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
  9195→        - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ)
  9196→        + (rho_core_b + rho_core_a) := by
  9197→        ring
  9198→      _ = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
  9199→        - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) := by
  9200→        rw [diag_cancel]; ring
  9201→
  9202→  -- 8) Assemble: two scalar rings, no heavy rewriting.
  9203→  calc
  9204→    ((dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - Gamma_mu_nabla_nu M r θ μ ν a b)
  9205→     - (dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ - Gamma_nu_nabla_mu M r θ μ ν a b))
  9206→        = (sumIdx B_b + sumIdx B_a) - (Cμa + Cμb) + (Cνa + Cνb) := LHS_small
  9207→    _ = ((sumIdx B_b) - Cμa + Cνa) + ((sumIdx B_a) - Cμb + Cνb) := regroup
```

---

## ERROR AT LINE 9429

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9429:15: Type mismatch
  h_cancel
has type
  ((((sumIdx fun ρ =>
            -Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ +
              Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ) +
          sumIdx fun ρ =>
            -Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ +
              Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) +
        sumIdx fun ρ =>
          -Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ +
            Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ) +
      sumIdx fun ρ =>
        -Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ +
          Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ) =
    0
but is expected to have type
  ((sumIdx fun e =>
        Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
          Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ) +
```

### Code Context (Lines 9414 to 9444):
```lean
  9414→     -  (dCoord μ (fun r θ => g M a e r θ) r θ) * Γtot M r θ e ν b
  9415→     +  (dCoord ν (fun r θ => g M a e r θ) r θ) * Γtot M r θ e μ b)
  9416→        = sumIdx (fun e =>
  9417→            ( Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
  9418→            - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ )
  9419→          + ( Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
  9420→            - Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ )) := by simpa using hunflip
  9421→    _   =
  9422→          (sumIdx (fun e =>
  9423→            Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
  9424→          - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ))
  9425→        +
  9426→          (sumIdx (fun e =>
  9427→            Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
  9428→          - Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ)) := hsplit
  9429→    _   = 0 := h_cancel
  9430→
  9431→/-! ### Block C: Main to Commutator -/
  9432→
  9433→/-- Block C: C'_main equals the ΓΓ commutator part of RHS.
  9434→    Uses: sum swapping, index relabeling, metric symmetry, and commutativity. -/
  9435→lemma main_to_commutator (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  9436→  -- LHS: main from expand_Ca and expand_Cb (Formula A with e as upper index)
  9437→  ( sumIdx (fun ρ => sumIdx (fun e =>
  9438→      Γtot M r θ ρ μ a * Γtot M r θ e ν ρ * g M e b r θ
  9439→    - Γtot M r θ ρ ν a * Γtot M r θ e μ ρ * g M e b r θ)) )
  9440→+ ( sumIdx (fun ρ => sumIdx (fun e =>
  9441→      Γtot M r θ ρ μ b * Γtot M r θ e ν ρ * g M e a r θ
  9442→    - Γtot M r θ ρ ν b * Γtot M r θ e μ ρ * g M e a r θ)) )
  9443→  =
  9444→  -- RHS: ΓΓ part with g factored outside (corrected form per JP)
```

---

## ERROR AT LINE 9630

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9630:4: Type mismatch
  payload_cancel_all_flipped M r θ h_ext μ ν a b
has type
  (sumIdx fun e =>
      -dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a +
            dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a -
          dCoord μ (fun r θ => g M a e r θ) r θ * Γtot M r θ e ν b +
        dCoord ν (fun r θ => g M a e r θ) r θ * Γtot M r θ e μ b) =
    0
but is expected to have type
  A + B + C + D = 0
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9644:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun e =>
    -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ -
          Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
        Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ +
      Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
in the target expression
  ((sumIdx fun e =>
            -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
```

### Code Context (Lines 9615 to 9645):
```lean
  9615→    simpa [hshape] using (payload_split_and_flip M r θ μ ν a b)
  9616→
  9617→  -- A2: Name the four Σ blocks to stabilize the outer algebra and align with `payload_cancel_all`.
  9618→  set A :=
  9619→    sumIdx (fun e => -(dCoord μ (fun r θ => g M e b r θ) r θ) * Γtot M r θ e ν a)
  9620→  set B :=
  9621→    sumIdx (fun e =>  (dCoord ν (fun r θ => g M e b r θ) r θ) * Γtot M r θ e μ a)
  9622→  set C :=
  9623→    sumIdx (fun e => -(dCoord μ (fun r θ => g M a e r θ) r θ) * Γtot M r θ e ν b)
  9624→  set D :=
  9625→    sumIdx (fun e =>  (dCoord ν (fun r θ => g M a e r θ) r θ) * Γtot M r θ e μ b)
  9626→
  9627→  have hP0 : A + B + C + D = 0 := by
  9628→    -- FIX (Option 2): Use the flipped variant.
  9629→    -- Since the definitions of A, B, C, D match the lemma exactly, `exact` should work.
  9630→    exact payload_cancel_all_flipped M r θ h_ext μ ν a b
  9631→
  9632→  -- A3: Collapse the four-sum payload in one shot:
  9633→  have h_payload_zero :
  9634→    sumIdx (fun e =>
  9635→        - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
  9636→      - Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
  9637→      + Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
  9638→      + Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ)
  9639→    = 0 := by
  9640→    -- Use A1 then A2, no extra simplification.
  9641→    simpa [A, B, C, D] using h_payload_flip.trans hP0
  9642→
  9643→  -- Use the equality; avoid recursive simp loops
  9644→  rw [h_payload_zero]
  9645→  simp only [zero_add, add_zero, sub_zero]  -- stable cleanup only
```

---

## ERROR AT LINE 9644

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9644:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun e =>
    -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ -
          Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
        Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ +
      Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
in the target expression
  ((sumIdx fun e =>
            -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
                  dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
                dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
          sumIdx fun e =>
            -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
                  Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
                Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
              Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) +
        (((sumIdx fun ρ =>
              -Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ +
                Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) +
```

### Code Context (Lines 9629 to 9659):
```lean
  9629→    -- Since the definitions of A, B, C, D match the lemma exactly, `exact` should work.
  9630→    exact payload_cancel_all_flipped M r θ h_ext μ ν a b
  9631→
  9632→  -- A3: Collapse the four-sum payload in one shot:
  9633→  have h_payload_zero :
  9634→    sumIdx (fun e =>
  9635→        - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
  9636→      - Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
  9637→      + Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
  9638→      + Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ)
  9639→    = 0 := by
  9640→    -- Use A1 then A2, no extra simplification.
  9641→    simpa [A, B, C, D] using h_payload_flip.trans hP0
  9642→
  9643→  -- Use the equality; avoid recursive simp loops
  9644→  rw [h_payload_zero]
  9645→  simp only [zero_add, add_zero, sub_zero]  -- stable cleanup only
  9646→
  9647→  -- Steps 6-8: Apply remaining blocks to simplify the rest of the goal.
  9648→  -- A2: normalize the ∂Γ–metric cluster inside the binder so `dGamma_match` matches syntactically.
  9649→  have hΓshape :
  9650→    sumIdx (fun e =>
  9651→        - dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ
  9652→      +   dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ
  9653→      -   dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ
  9654→      +   dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ)
  9655→    =
  9656→    sumIdx (fun e =>
  9657→        - (dCoord μ (fun r θ => Γtot M r θ e ν a) r θ) * g M e b r θ
  9658→      +   (dCoord ν (fun r θ => Γtot M r θ e μ a) r θ) * g M e b r θ
  9659→      -   (dCoord μ (fun r θ => Γtot M r θ e ν b) r θ) * g M a e r θ
```

---

## ERROR AT LINE 9713

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9713:65: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
h_θ : sin θ ≠ 0
a b : Idx
H :
  dCoord Idx.r (fun r θ => nabla_g M r θ Idx.θ a b) r θ - Gamma_mu_nabla_nu M r θ Idx.r Idx.θ a b -
      (dCoord Idx.θ (fun r θ => nabla_g M r θ Idx.r a b) r θ - Gamma_nu_nabla_mu M r θ Idx.r Idx.θ a b) =
    -Riemann M r θ b a Idx.r Idx.θ - Riemann M r θ a b Idx.r Idx.θ
h_r : nabla_g M r θ Idx.r a b = 0
h_θ' : nabla_g M r θ Idx.θ a b = 0
⊢ deriv
        (fun s =>
          deriv (fun t => g M a b s t) θ + (-(g M b b s θ * Γtot M s θ b Idx.θ a) - g M a a s θ * Γtot M s θ a Idx.θ b))
        r -
      deriv
        (fun t =>
          deriv (fun s => g M a b s t) r + (-(g M b b r t * Γtot M r t b Idx.r a) - g M a a r t * Γtot M r t a Idx.r b))
        θ =
    0
```

### Code Context (Lines 9698 to 9728):
```lean
  9698→lemma ricci_identity_on_g_rθ_ext
  9699→    (M r θ : ℝ) (h_ext : Exterior M r θ) (h_θ : Real.sin θ ≠ 0) (a b : Idx) :
  9700→  nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
  9701→  - nabla (fun M r θ a b => nabla_g M r θ Idx.r a b) M r θ Idx.θ a b
  9702→  =
  9703→  - Riemann M r θ b a Idx.r Idx.θ - Riemann M r θ a b Idx.r Idx.θ := by
  9704→  classical
  9705→  -- General Ricci identity at (μ,ν) = (r,θ)
  9706→  have H := ricci_identity_on_g_general M r θ h_ext h_θ Idx.r Idx.θ a b
  9707→
  9708→  -- Kill the commutator LHS by metric compatibility (∇g = 0)
  9709→  have h_r : nabla_g M r θ Idx.r a b = 0 := nabla_g_zero_ext M r θ h_ext Idx.r a b
  9710→  have h_θ' : nabla_g M r θ Idx.θ a b = 0 := nabla_g_zero_ext M r θ h_ext Idx.θ a b
  9711→  have LHS0 :
  9712→    dCoord Idx.r (fun r θ => nabla_g M r θ Idx.θ a b) r θ
  9713→  - dCoord Idx.θ (fun r θ => nabla_g M r θ Idx.r a b) r θ = 0 := by
  9714→    -- both dCoord terms are derivatives of the constant 0
  9715→    simp [h_r, h_θ', dCoord]
  9716→    ring
  9717→
  9718→  -- Convert both Σ(RUp⋅g) terms to lowered Riemann
  9719→  have S₁ :
  9720→    sumIdx (fun ρ => RiemannUp M r θ ρ a Idx.r Idx.θ * g M ρ b r θ)
  9721→      = Riemann M r θ b a Idx.r Idx.θ :=
  9722→    sum_RUp_g_to_Riemann_ba M r θ a b Idx.r Idx.θ
  9723→  have S₂ :
  9724→    sumIdx (fun ρ => RiemannUp M r θ ρ b Idx.r Idx.θ * g M a ρ r θ)
  9725→      = Riemann M r θ a b Idx.r Idx.θ :=
  9726→    sum_RUp_g_to_Riemann_ab M r θ a b Idx.r Idx.θ
  9727→
  9728→  -- Kill Gamma terms by metric compatibility
```

---

## ERROR AT LINE 9824

### Error Message:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9824:57: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
a b μ ν : Idx
H :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - Gamma_mu_nabla_nu M r θ μ ν a b -
      (dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ - Gamma_nu_nabla_mu M r θ μ ν a b) =
    -Riemann M r θ b a μ ν - Riemann M r θ a b μ ν
hμ : nabla_g M r θ μ a b = 0
hν : nabla_g M r θ ν a b = 0
⊢ ((match μ with
      | Idx.r =>
        deriv
          (fun s =>
            (match ν with
              | Idx.r =>
                deriv
                  (fun s =>
                    (match (motive := Idx → Idx → ℝ → ℝ → ℝ) a, b with
```

### Code Context (Lines 9809 to 9839):
```lean
  9809→
  9810→    Proven using ricci_identity_on_g_general + metric compatibility (∇g = 0).
  9811→    This is the standard textbook derivation.
  9812→-/
  9813→lemma Riemann_swap_a_b_ext
  9814→  (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0)
  9815→  (a b μ ν : Idx) :
  9816→  Riemann M r θ a b μ ν = - Riemann M r θ b a μ ν := by
  9817→  classical
  9818→  have H := ricci_identity_on_g_general M r θ h_ext hθ μ ν a b
  9819→  -- ∇g = 0 on Exterior
  9820→  have hμ : nabla_g M r θ μ a b = 0 := nabla_g_zero_ext M r θ h_ext μ a b
  9821→  have hν : nabla_g M r θ ν a b = 0 := nabla_g_zero_ext M r θ h_ext ν a b
  9822→  have LHS0 :
  9823→    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
  9824→  - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ = 0 := by
  9825→    simp [hμ, hν, dCoord]
  9826→    ring
  9827→
  9828→  -- Convert the two Σ(RUp⋅g) to Riemann
  9829→  have S₁ := sum_RUp_g_to_Riemann_ba M r θ a b μ ν
  9830→  have S₂ := sum_RUp_g_to_Riemann_ab M r θ a b μ ν
  9831→
  9832→  -- Kill Gamma terms by metric compatibility
  9833→  have hμν :
  9834→    Gamma_mu_nabla_nu M r θ μ ν a b = 0 := by
  9835→    unfold Gamma_mu_nabla_nu
  9836→    calc
  9837→      sumIdx (fun ρ =>
  9838→        (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b) +
  9839→        (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
```

---

