# Part 3 Code Block Reference Guide

**Purpose:** Detailed listing of code blocks to document in Part 3 of the restructured Paper 5

**Format:** Each block follows the triple-discussion template:
1. Mathematical Statement (LaTeX)
2. Lean Code (verbatim)
3. Proof Narrative (tactics → English)
4. Triple Discussion: (a) Physical, (b) Mathematical, (c) Lean Technical

---

## 3.2 AxCal Framework Code (12-15 pages, ~15-20 blocks)

### AxCalCore/Axis.lean Blocks

**Block 3.2.1:** Height Inductive Type
- **File:** Papers/P5_GeneralRelativity/AxCalCore/Axis.lean
- **Lines:** ~15-20
- **Content:** `inductive Height | zero | one | omega`
- **Key Points:** Three-level hierarchy, ordering

**Block 3.2.2:** AxisProfile Structure
- **Lines:** ~30-35
- **Content:** `structure AxisProfile where hChoice hComp hLogic : Height`
- **Key Points:** Product of three axes

**Block 3.2.3:** Height Ordering
- **Lines:** ~40-50
- **Content:** `instance : LE Height`, `le_def`
- **Key Points:** zero ≤ one ≤ omega

**Block 3.2.4:** Profile Composition (Product Law)
- **Lines:** ~60-80
- **Content:** `def compose : AxisProfile → AxisProfile → AxisProfile`
- **Key Points:** Componentwise maximum

**Block 3.2.5:** WitnessFamily Type
- **Lines:** ~90-100
- **Content:** `def WitnessFamily := Foundation → Prop`
- **Key Points:** Parametric over foundations

---

### GR/Portals.lean Blocks

**Block 3.2.6:** PortalFlag Inductive
- **File:** Papers/P5_GeneralRelativity/GR/Portals.lean
- **Lines:** ~15-25
- **Content:** `inductive PortalFlag | uses_zorn | uses_limit_curve | uses_serial_chain | uses_reductio`

**Block 3.2.7:** Zorn Portal Axiom
- **Lines:** ~30-35
- **Content:** `axiom Zorn_portal : ∀ {F}, Uses uses_zorn → HasAC F`
- **Key Points:** AC equivalence

**Block 3.2.8:** LimitCurve Portal Axiom
- **Lines:** ~40-45
- **Content:** `axiom LimitCurve_portal : ∀ {F}, Uses uses_limit_curve → (HasFT F ∨ HasWKL0 F)`
- **Key Points:** Compactness disjunction

**Block 3.2.9:** SerialChain Portal Axiom
- **Lines:** ~50-55
- **Content:** `axiom SerialChain_portal : ∀ {F}, Uses uses_serial_chain → HasDCw F`

**Block 3.2.10:** Reductio Portal Axiom
- **Lines:** ~60-65
- **Content:** `axiom Reductio_portal : ∀ {F}, Uses uses_reductio → HasLEM F`

**Block 3.2.11:** route_to_profile Function
- **Lines:** ~70-100
- **Content:** `def route_to_profile (flags : List PortalFlag) : AxisProfile`
- **Key Points:** Maps flags to heights

---

### GR/Witnesses.lean Blocks

**Block 3.2.12:** G1_Vacuum_W
- **File:** Papers/P5_GeneralRelativity/GR/Witnesses.lean
- **Lines:** ~20-30
- **Content:** `def G1_Vacuum_W : WitnessFamily := fun F => ∀ S, IsPinnedSchwarzschild S → VacuumEFE S`

**Block 3.2.13:** G2_MGHD_W
- **Lines:** ~40-50
- **Content:** `def G2_MGHD_W : WitnessFamily := fun F => ∀ ID, Uses uses_zorn → MGHD_Exists ID`

**Block 3.2.14:** G3_Penrose_W
- **Lines:** ~60-75
- **Content:** `def G3_Penrose_W : WitnessFamily := fun F => ...`
- **Key Points:** Trapped surface + energy conditions

---

### GR/Certificates.lean Blocks

**Block 3.2.15:** HeightCertificate Structure
- **File:** Papers/P5_GeneralRelativity/GR/Certificates.lean
- **Lines:** ~15-25
- **Content:** `structure HeightCertificate where name W profile flags upper cites`

**Block 3.2.16:** G1_Vacuum_Cert
- **Lines:** ~30-40
- **Content:** Full certificate with profile (0,0,0), flags = []

**Block 3.2.17:** G2_MGHD_Cert
- **Lines:** ~50-60
- **Content:** Profile (1,0,0), flags = [uses_zorn]

**Block 3.2.18:** G3_Penrose_Cert
- **Lines:** ~65-75
- **Content:** Profile (0,1,1), flags = [uses_limit_curve, uses_reductio]

**Block 3.2.19:** Certificate Registry
- **Lines:** ~100-110
- **Content:** `def all_certificates : List HeightCertificate`

---

## 3.3 Schwarzschild Engine Code (20-25 pages, ~25-30 blocks)

### Foundational Definitions

**Block 3.3.1:** SchwarzschildCoords Structure
- **File:** Papers/P5_GeneralRelativity/GR/Schwarzschild.lean
- **Lines:** 32-37
- **Content:**
```lean
structure SchwarzschildCoords where
  t : ℝ  -- time coordinate
  r : ℝ  -- radial coordinate (r > 2M)
  θ : ℝ  -- polar angle (0 < θ < π)
  φ : ℝ  -- azimuthal angle (0 ≤ φ < 2π)
```

**Block 3.3.2:** Schwarzschild Factor f(r)
- **Lines:** 42
- **Content:** `noncomputable def f (M r : ℝ) : ℝ := 1 - 2*M/r`

---

### Positivity and Sign Properties

**Block 3.3.3:** f_pos_of_hr Theorem
- **Lines:** 45-52
- **Full theorem with proof** (see outline for details)
- **Key tactic:** `simpa [f] using (sub_pos.mpr hdiv)`

**Block 3.3.4:** f_pos_iff_r_gt_2M
- **Lines:** 85-95
- **Iff characterization of exterior**

**Block 3.3.5:** f_eq_zero_iff_r_eq_2M
- **Lines:** 98-110
- **Horizon characterization**

**Block 3.3.6:** f_at_horizon
- **Lines:** 121-125
- **Simp lemma for f(M, 2M) = 0**

---

### Derivative Calculations

**Block 3.3.7:** f_hasDerivAt Theorem
- **Lines:** 55-76
- **Full proof chain** (see outline Part 3.3.3 Block 6)
- **Key tactics:** `convert`, `simpa`

**Block 3.3.8:** f_derivative
- **Lines:** 80-82
- **Deriv form:** `deriv (fun r' => f M r') r = 2*M / r^2`

**Block 3.3.9:** g_tt_derivative
- **Lines:** ~234-240
- **Content:** `deriv (fun r' => g M Idx.t Idx.t r' θ) r = 2*M / r^2`

**Block 3.3.10:** g_rr_derivative
- **Lines:** ~289-295
- **Content:** `deriv (fun r' => g M Idx.r Idx.r r' θ) r = -2*M*f M r / r^2`

**Block 3.3.11:** g_inv_tt_derivative_exterior
- **Lines:** ~274-280
- **Content:** `deriv (fun r' => gInv M Idx.t Idx.t r' θ) r = -2*M / (r^2 * (f M r)^2)`

**Block 3.3.12:** g_inv_rr_derivative
- **Lines:** ~254-258
- **Content:** `deriv (fun r' => gInv M Idx.r Idx.r r' θ) r = 2*M / r^2`

---

### Metric Components

**Block 3.3.13:** g Definition (Diagonal Metric)
- **Lines:** ~400-420
- **Content:**
```lean
noncomputable def g (M : ℝ) (μ ν : Idx) (r θ : ℝ) : ℝ :=
  match μ, ν with
  | Idx.t, Idx.t => -(f M r)
  | Idx.r, Idx.r => (f M r)⁻¹
  | Idx.θ, Idx.θ => r^2
  | Idx.φ, Idx.φ => r^2 * (Real.sin θ)^2
  | _, _ => 0
```

**Block 3.3.14:** gInv Definition (Inverse Metric)
- **Lines:** ~440-460
- **Content:** Similar match structure with inverses

**Block 3.3.15:** g_offdiag Lemmas
- **Lines:** ~480-520
- **Content:** Simp lemmas proving g M Idx.t Idx.r r θ = 0, etc.

**Block 3.3.16:** gInv_offdiag Lemmas
- **Lines:** ~540-580
- **Content:** Similar for inverse metric

---

### Christoffel Symbols

**Block 3.3.17:** Γ_t_tr Definition
- **Lines:** ~800-810
- **Content:** `noncomputable def Γ_t_tr (M r : ℝ) : ℝ := M / (r * (r - 2*M))`

**Block 3.3.18:** Γ_r_rr Definition
- **Lines:** ~820-830
- **Content:** `noncomputable def Γ_r_rr (M r : ℝ) : ℝ := -M / (r * (r - 2*M))`

**Block 3.3.19:** Γ_r_θθ Definition
- **Lines:** ~840-850
- **Content:** `noncomputable def Γ_r_θθ (M r : ℝ) : ℝ := -(r - 2*M)`

**Block 3.3.20:** Γ_θ_rθ Definition
- **Lines:** ~860-870
- **Content:** `noncomputable def Γ_θ_rθ (M r : ℝ) : ℝ := 1 / r`

**Block 3.3.21:** Γ_θ_φφ Definition
- **Lines:** ~880-890
- **Content:** `noncomputable def Γ_θ_φφ (θ : ℝ) : ℝ := -Real.sin θ * Real.cos θ`

**Block 3.3.22:** Remaining Christoffel Symbols (4 more)
- Γ_r_φφ, Γ_φ_rφ, Γ_φ_θφ, Γ_t_tφ (all explicit formulas)

**Block 3.3.23:** Γtot Unified Lookup
- **Lines:** ~1100-1200
- **Content:**
```lean
noncomputable def Γtot (M r θ : ℝ) (α μ ν : Idx) : ℝ :=
  match α, μ, ν with
  | Idx.t, Idx.t, Idx.r => Γ_t_tr M r
  | Idx.t, Idx.r, Idx.t => Γ_t_tr M r
  | Idx.r, Idx.r, Idx.r => Γ_r_rr M r
  | Idx.r, Idx.θ, Idx.θ => Γ_r_θθ M r
  ... (40 cases total, most are 0)
```

**Block 3.3.24:** Γtot Zero Lemmas (Selection)
- **Lines:** ~1300-1400
- **Content:** Simp lemmas like `Γtot M r θ Idx.t Idx.t Idx.t = 0`
- **Purpose:** Enable simp to eliminate vanishing terms

---

### Index Infrastructure

**Block 3.3.25:** Idx Inductive
- **Lines:** ~100-110
- **Content:** `inductive Idx | t | r | θ | φ`

**Block 3.3.26:** sumIdx Definition
- **Lines:** ~150-160
- **Content:**
```lean
def sumIdx (f : Idx → ℝ) : ℝ :=
  f Idx.t + f Idx.r + f Idx.θ + f Idx.φ
```

**Block 3.3.27:** sumIdx_expand Lemma
- **Lines:** ~170-180
- **Content:** Unfold sumIdx to explicit 4-term sum

**Block 3.3.28:** sumIdx2 Definition
- **Lines:** ~190-200
- **Content:** `def sumIdx2 (f : Idx → Idx → ℝ) : ℝ := sumIdx (fun i => sumIdx (fun j => f i j))`

---

### Ricci Tensor Infrastructure

**Block 3.3.29:** Ricci Definition (Stub/Import)
- **Lines:** ~2100-2110
- **Content:** `def Ricci (M r θ : ℝ) (μ ν : Idx) : ℝ := ...` (actual def in Riemann.lean)

**Block 3.3.30:** RicciScalar Definition
- **Lines:** ~2120-2130
- **Content:** `def RicciScalar (M r θ : ℝ) : ℝ := sumIdx2 (fun μ ν => gInv M μ ν r θ * Ricci M r θ μ ν)`

---

## 3.4 Riemann Tensor Code (25-30 pages, ~35-40 blocks)

**THIS IS THE LARGEST SECTION**

### Exterior Domain and Smoothness

**Block 3.4.1:** Exterior Structure
- **File:** Papers/P5_GeneralRelativity/GR/Riemann.lean
- **Lines:** 27-30
- **Content:**
```lean
structure Exterior (M r θ : ℝ) : Prop where
  hM : 0 < M
  hr_ex : 2 * M < r
```

**Block 3.4.2:** Exterior.r_ne_zero Lemma
- **Lines:** 33-34
- **Content:** `lemma r_ne_zero {M r θ : ℝ} (h : Exterior M r θ) : r ≠ 0`

**Block 3.4.3:** Exterior.f_ne_zero Lemma
- **Lines:** 36-37
- **Content:** `lemma f_ne_zero {M r θ : ℝ} (h : Exterior M r θ) : f M r ≠ 0`

**Block 3.4.4:** isOpen_exterior_set Theorem
- **Lines:** 52-60
- **Content:** Proof that {(r,θ) | r > 2M} is open
- **Key tactic:** `rw [this]; exact IsOpen.preimage continuous_fst isOpen_Ioi`

**Block 3.4.5:** deriv_zero_of_locally_zero Lemma
- **Lines:** 75-92
- **Content:** If f = 0 on open set U, then deriv f x = 0 for x ∈ U
- **Key tactic:** Filter.EventuallyEq techniques
- **Purpose:** Level 3 de-axiomatization infrastructure

---

### Directional Derivative (dCoord)

**Block 3.4.6:** dCoord Definition
- **Lines:** ~250-260
- **Content:**
```lean
def dCoord (μ : Idx) (F : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ :=
  match μ with
  | Idx.t => 0
  | Idx.r => deriv (fun r' => F r' θ) r
  | Idx.θ => deriv (fun θ' => F r θ') θ
  | Idx.φ => 0
```

**Block 3.4.7:** dCoord_r Simp Lemma
- **Lines:** ~270-275
- **Content:** `@[simp] lemma dCoord_r : dCoord Idx.r F r θ = deriv (fun r' => F r' θ) r`

**Block 3.4.8:** dCoord_θ Simp Lemma
- **Lines:** ~280-285
- **Content:** `@[simp] lemma dCoord_θ : dCoord Idx.θ F r θ = deriv (fun θ' => F r θ') θ`

**Block 3.4.9:** dCoord_t and dCoord_φ Lemmas
- **Lines:** ~290-300
- **Content:** Both are 0 by definition (static, spherically symmetric)

---

### Christoffel Derivative Calculators

**Block 3.4.10:** deriv_Γ_t_tr Theorem
- **Lines:** ~918-960
- **FULL CALC-CHAIN PROOF** (see outline Part 3.4.3 Block 9)
- **Result:** `-2*M / (r^2 * (r - 2*M))`

**Block 3.4.11:** deriv_Γ_r_rr Theorem
- **Lines:** ~966-1000
- **Content:**
```lean
theorem deriv_Γ_r_rr (M r : ℝ) (hr : r ≠ 0) (hr2M : r - 2*M ≠ 0) :
    deriv (fun r' => Γ_r_rr M r') r = 2*M / (r^2 * (r - 2*M)) := by
  calc
    deriv (fun r' => Γ_r_rr M r') r
        = deriv (fun r' => -M / (r' * (r' - 2*M))) r := by rw [Γ_r_rr]
    _   = ... := by rw [deriv_div ...]
    _   = 2*M / (r^2 * (r - 2*M)) := by field_simp [hr, hr2M]; ring
```

**Block 3.4.12:** deriv_Γ_θ_φφ Theorem
- **Lines:** ~1074-1120
- **Content:**
```lean
theorem deriv_Γ_θ_φφ (θ : ℝ) :
    deriv (fun θ' => Γ_θ_φφ θ') θ = -(Real.cos θ)^2 + (Real.sin θ)^2 := by
  calc
    deriv (fun θ' => Γ_θ_φφ θ') θ
        = deriv (fun θ' => -Real.sin θ' * Real.cos θ') θ := by rw [Γ_θ_φφ]
    _   = ... := by rw [deriv_mul ...]
    _   = -(Real.cos θ)^2 + (Real.sin θ)^2 := by simp [Real.deriv_sin, Real.deriv_cos]; ring
```

**Block 3.4.13:** deriv_Γ_r_θθ Theorem
- **Lines:** ~1030-1050
- **Content:** `deriv (fun r' => Γ_r_θθ M r') r = -1`

**Block 3.4.14:** deriv_Γ_r_φφ Theorem
- **Lines:** ~1055-1070
- **Content:** `deriv (fun r' => Γ_r_φφ M r' θ) r = -1 + 2*M/r`

---

### Riemann Tensor Definition and Helpers

**Block 3.4.15:** Riemann Definition
- **Lines:** ~1400-1410
- **Content:**
```lean
noncomputable def Riemann (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (fun r' θ' => Γtot M r' θ' a b d) r θ
- dCoord d (fun r' θ' => Γtot M r' θ' a b c) r θ
+ sumIdx (fun k => Γtot M r θ a c k * Γtot M r θ k b d)
- sumIdx (fun k => Γtot M r θ a d k * Γtot M r θ k b c)
```

**Block 3.4.16:** RiemannUp Definition (Raised Indices)
- **Lines:** ~1450-1460
- **Content:** `def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ := gInv M a a r θ * Riemann M r θ a b c d`

**Block 3.4.17:** Riemann_last_equal_zero Lemma
- **Lines:** ~1500-1510
- **Content:** `Riemann M r θ a b d d = 0` (first Bianchi consequence)

**Block 3.4.18:** Riemann_swap_a_b Lemma
- **Lines:** ~1550-1600
- **Content:** `Riemann M r θ a b c d = -Riemann M r θ b a c d` (antisymmetry)

---

### Six Component Reduction Lemmas (THE CORE)

**Block 3.4.19:** Riemann_trtr_reduce Theorem
- **Lines:** ~1800-1850
- **FULL REDUCTION PROOF** (see outline Part 3.4.5 Block 16)
- **Content:**
```lean
theorem Riemann_trtr_reduce (M r θ : ℝ) :
    Riemann M r θ Idx.t Idx.r Idx.t Idx.r
      = dCoord_r (fun r' _ => Γtot M r' θ Idx.t Idx.t Idx.r) r θ
      - dCoord_r (fun r' _ => Γtot M r' θ Idx.t Idx.r Idx.t) r θ
      + sumIdx (fun k => Γtot M r θ Idx.t Idx.t k * Γtot M r θ k Idx.r Idx.r)
      - sumIdx (fun k => Γtot M r θ Idx.t Idx.r k * Γtot M r θ k Idx.r Idx.t) := by
  unfold Riemann dCoord
  simp [sumIdx_expand]
  rfl
```

**Block 3.4.20:** Riemann_tθtθ_reduce Theorem
- **Lines:** ~1860-1910
- **Similar structure to Block 19**

**Block 3.4.21:** Riemann_tφtφ_reduce Theorem
- **Lines:** ~1920-1970

**Block 3.4.22:** Riemann_rθrθ_reduce Theorem
- **Lines:** ~1980-2030

**Block 3.4.23:** Riemann_rφrφ_reduce Theorem
- **Lines:** ~2040-2090

**Block 3.4.24:** Riemann_θφθφ_reduce Theorem
- **Lines:** ~2100-2150

---

### Component Value Lemmas (THE RESULTS)

**Block 3.4.25:** Riemann_trtr_value Theorem
- **Lines:** ~2200-2250
- **FULL PROOF** (see outline Part 3.4.6 Block 22)
- **Result:** `2*M / r^3`

**Block 3.4.26:** Riemann_tθtθ_value Theorem
- **Lines:** ~2260-2300
- **Result:** `M / r`

**Block 3.4.27:** Riemann_tφtφ_value Theorem
- **Lines:** ~2310-2350
- **Result:** `M / r`

**Block 3.4.28:** Riemann_rθrθ_value Theorem
- **Lines:** ~2360-2400
- **Result:** `M / r`

**Block 3.4.29:** Riemann_rφrφ_value Theorem
- **Lines:** ~2410-2450
- **Result:** `M / r`

**Block 3.4.30:** Riemann_θφθφ_value Theorem
- **Lines:** ~2460-2500
- **Result:** `2*M*r^2*(Real.sin θ)^2`

---

### Ricci Tensor Contraction

**Block 3.4.31:** Ricci Definition (Contraction)
- **Lines:** ~2600-2610
- **Content:** `def Ricci (M r θ : ℝ) (μ ν : Idx) : ℝ := sumIdx (fun ρ => RiemannUp M r θ ρ μ ρ ν)`

**Block 3.4.32:** Ricci_tt_vanishes Theorem
- **Lines:** ~2650-2700
- **Content:**
```lean
theorem Ricci_tt_vanishes (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) :
    Ricci M r θ Idx.t Idx.t = 0 := by
  classical
  unfold Ricci
  simp [sumIdx_expand, RiemannUp]
  -- Expand to: g^tt R_trtt + g^rr R_rtrt + g^θθ R_θtθt + g^φφ R_φtφt
  -- Each term computed, cancellation shown algebraically
  ... (detailed proof showing cancellation)
```

**Block 3.4.33:** Ricci_rr_vanishes Theorem
- **Lines:** ~2710-2760
- **Similar cancellation proof**

**Block 3.4.34:** Ricci_θθ_vanishes Theorem
- **Lines:** ~2770-2820

**Block 3.4.35:** Ricci_φφ_vanishes Theorem
- **Lines:** ~2830-2880

**Block 3.4.36:** Ricci_offdiag_vanishes Lemmas
- **Lines:** ~2890-2950
- **Content:** All off-diagonal components are 0

---

### Supporting Infrastructure

**Block 3.4.37:** sumIdx_mul_g_right Lemma
- **Lines:** ~1241-1250
- **Content:** `sumIdx (fun k => F k * g M k b r θ) = F b * g M b b r θ` (diagonal collapse)

**Block 3.4.38:** sumIdx_mul_g_left Lemma
- **Lines:** ~1251-1257

**Block 3.4.39:** sumIdx_Γ_g_left Lemma
- **Lines:** ~1224-1233
- **Content:** Christoffel-metric collapse

**Block 3.4.40:** sumIdx_Γ_g_right Lemma
- **Lines:** ~1234-1239

**Block 3.4.41:** dCoord_g_via_compat_ext Lemma
- **Lines:** ~1300-1350
- **Content:** Metric compatibility: ∂_μ g_νρ = Γ_μνσ g_σρ + Γ_μρσ g_νσ

---

## 3.5 Kretschmann Invariant Code (10-12 pages, ~12-15 blocks)

### Kretschmann Definition and Infrastructure

**Block 3.5.1:** Kretschmann Definition
- **File:** Papers/P5_GeneralRelativity/GR/Invariants.lean
- **Lines:** 33-43
- **Content:**
```lean
noncomputable def Kretschmann (M r θ : ℝ) : ℝ :=
  sumIdx2 (fun a b =>
    sumIdx2 (fun c d =>
      let Rabcd := Riemann M r θ a b c d
      let R_raised :=
        sumIdx2 (fun α β =>
          sumIdx2 (fun γ δ =>
            gInv M a α r θ * gInv M b β r θ
          * gInv M c γ r θ * gInv M d δ r θ
          * Riemann M r θ α β γ δ))
      Rabcd * R_raised))
```

**Block 3.5.2:** raise4_R Helper Lemma
- **Lines:** ~60-80
- **Content:** Simplification of 4-index raising with diagonal metric

**Block 3.5.3:** Kretschmann_after_raise_sq Lemma
- **Lines:** 73-84
- **Content:**
```lean
lemma Kretschmann_after_raise_sq (M r θ : ℝ) :
  Kretschmann M r θ
    = sumIdx2 (fun a b => sumIdx2 (fun c d =>
        (gInv M a a r θ * gInv M b b r θ * gInv M c c r θ * gInv M d d r θ)
      * (Riemann M r θ a b c d)^2)) := by
  classical
  unfold Kretschmann
  congr; ext a b; congr; ext c d
  rw [raise4_R]
  simp only [pow_two]
  ring
```

---

### Six-Block Structure

**Block 3.5.4:** sixBlock Definition
- **Lines:** 57-58
- **Content:**
```lean
noncomputable def sixBlock (M r θ : ℝ) (a b : Idx) : ℝ :=
  (gInv M a a r θ * gInv M b b r θ)^2 * (Riemann M r θ a b a b)^2
```

**Block 3.5.5:** sumSixBlocks Definition
- **Lines:** 61-67
- **Content:**
```lean
noncomputable def sumSixBlocks (M r θ : ℝ) : ℝ :=
  sixBlock M r θ Idx.t Idx.r +
  sixBlock M r θ Idx.t Idx.θ +
  sixBlock M r θ Idx.t Idx.φ +
  sixBlock M r θ Idx.r Idx.θ +
  sixBlock M r θ Idx.r Idx.φ +
  sixBlock M r θ Idx.θ Idx.φ
```

**Block 3.5.6:** Kretschmann_six_blocks Theorem
- **Lines:** 91-111
- **Content:** `Kretschmann M r θ = 4 * sumSixBlocks M r θ` (with sorry)
- **Status:** Structural lemma, off-block vanishing complete but proof deferred

---

### Block Value Calculations

**Block 3.5.7:** sixBlock_tr_value Lemma
- **Lines:** 173-191
- **FULL PROOF** (see outline Part 3.5.3 Block 7)
- **Result:** `4 * M^2 / r^6`

**Block 3.5.8:** sixBlock_tθ_value Lemma
- **Lines:** 194-208
- **Result:** `M^2 / r^6`

**Block 3.5.9:** sixBlock_tφ_value Lemma
- **Lines:** 210-224
- **Result:** `M^2 / r^6`

**Block 3.5.10:** sixBlock_rθ_value Lemma
- **Lines:** 227-244
- **Result:** `M^2 / r^6`

**Block 3.5.11:** sixBlock_rφ_value Lemma
- **Lines:** 247-264
- **Result:** `M^2 / r^6`

**Block 3.5.12:** sixBlock_θφ_value Lemma
- **Lines:** 267-288
- **Result:** `4 * M^2 / r^6`

---

### Final Result

**Block 3.5.13:** Kretschmann_exterior_value Theorem
- **Lines:** 291-302
- **FULL PROOF** (see outline Part 3.5.4 Block 13)
- **Result:** `48 * M^2 / r^6`
- **Content:**
```lean
theorem Kretschmann_exterior_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  Kretschmann M r θ = 48 * M^2 / r^6 := by
  classical
  rw [Kretschmann_six_blocks]
  unfold sumSixBlocks
  rw [sixBlock_tr_value M r θ hM hr hθ, sixBlock_tθ_value M r θ hM hr hθ, sixBlock_tφ_value M r θ hM hr hθ]
  rw [sixBlock_rθ_value M r θ hM hr hθ, sixBlock_rφ_value M r θ hM hr hθ, sixBlock_θφ_value M r θ hM hr hθ]
  ring
```

---

### Supporting Infrastructure

**Block 3.5.14:** gInv_mul_g_diag Lemma
- **Lines:** 125-164
- **Content:** `gInv M i i r θ * g M i i r θ = 1` (inverse property)
- **Cases for all 4 indices**

**Block 3.5.15:** RicciScalar_exterior_zero Theorem
- **Lines:** 19-25
- **Content:** Ricci scalar vanishes in exterior (follows from Ricci_vanishes)

---

## 3.6 EPS Framework Code (8-10 pages, ~8-10 blocks)

**Block 3.6.1:** LightRay Structure
- **File:** Papers/P5_GeneralRelativity/GR/EPSCore.lean
- **Lines:** 21-25

**Block 3.6.2:** FreeFall Structure
- **Lines:** 28-32

**Block 3.6.3:** EPS_Light_Conformal Axiom
- **Lines:** 34-38

**Block 3.6.4:** EPS_FreeFall_Projective Axiom
- **Lines:** 40-44

**Block 3.6.5:** EPS_Compatibility Axiom
- **Lines:** 46-50

**Block 3.6.6:** EPS_Integrability Axiom
- **Lines:** ~55-60

**Block 3.6.7:** EPS_Height_Zero Theorem
- **Lines:** ~70-80
- **Content:** Statement that EPS reconstruction is portal-free

**Block 3.6.8:** EPS_Kinematics_Height0 Lemma
- **Lines:** ~85-95
- **Content:** Height certificate construction

---

## 3.7 Build System Verification (5-6 pages, ~5-6 blocks)

**Block 3.7.1:** lakefile.lean Configuration
- **File:** Papers/P5_GeneralRelativity/lakefile.lean (or root)
- **Lines:** N/A (external file)
- **Content:** Package definition, dependencies

**Block 3.7.2:** Smoke Test
- **File:** Papers/P5_GeneralRelativity/Smoke.lean
- **Lines:** ~10-30
- **Content:** `def Paper5_Smoke_Success : True := trivial` (aggregates all imports)

**Block 3.7.3:** No-Sorry Guard
- **Lines:** N/A (shell script)
- **Content:** `grep -r "sorry" ... | wc -l` should output 0

**Block 3.7.4:** SchematicAudit.sh Script
- **Lines:** N/A (bash)
- **Content:** Checks that schematic modules use axioms, deep-dives don't

**Block 3.7.5:** AxiomDeclAudit.sh Script
- **Lines:** N/A (bash)
- **Content:** Verifies portal axioms are declared correctly

**Block 3.7.6:** CI Workflow (GitHub Actions)
- **File:** .github/workflows/build.yml (or similar)
- **Lines:** N/A
- **Content:** Build, test, audit steps

---

## BLOCK STATISTICS SUMMARY

| Section | Blocks | Pages | Avg Pages/Block |
|---------|--------|-------|-----------------|
| 3.2 AxCal | 19 | 12-15 | 0.7 |
| 3.3 Schwarzschild | 30 | 20-25 | 0.75 |
| 3.4 Riemann | 41 | 25-30 | 0.65 |
| 3.5 Kretschmann | 15 | 10-12 | 0.75 |
| 3.6 EPS | 8 | 8-10 | 1.1 |
| 3.7 Build | 6 | 5-6 | 0.9 |
| **Total** | **119** | **80-98** | **0.75** |

**Note:** "Blocks" are major code segments requiring full triple discussion. Supporting lemmas and infrastructure may be grouped or summarized.

---

## WRITING WORKFLOW FOR PART 3

### Step 1: Extract Code
For each block:
1. Open the source file (e.g., Schwarzschild.lean)
2. Navigate to the line numbers
3. Copy the exact Lean code (no modifications)
4. Include file path and line numbers as reference

### Step 2: Write Mathematical Statement
- Convert Lean types to LaTeX notation
- Use standard symbols (∀, ∃, ⟹, etc.)
- Keep it concise (1-2 lines for most blocks)

### Step 3: Write Proof Narrative
For each tactic:
- `unfold` → "We expand the definition of..."
- `simp` → "Simplifying using lemmas X, Y, Z..."
- `rw [lemma]` → "Rewriting with lemma, we obtain..."
- `field_simp` → "Clearing denominators using field arithmetic..."
- `ring` → "Polynomial normalization completes the identity"
- `calc` → "We compute step-by-step:"

### Step 4: Triple Discussion (Most Time-Consuming)

**(a) Physical Implications** (2-3 sentences):
- What physical quantity is this?
- What does the result mean for spacetime geometry?
- Any connection to observable phenomena?

**(b) Mathematical Implications** (2-3 sentences):
- What general mathematical principle is illustrated?
- How does this fit into the larger theoretical structure?
- Any surprising or non-obvious aspects?

**(c) Lean Technical Discussion** (3-4 sentences):
- Which tactics were used and why?
- Any dependencies on other lemmas?
- Proof strategy (direct, calc-chain, case split)?
- Any technical challenges or gotchas?

### Example Time Estimate per Block:
- Extract code: 2 min
- Math statement: 5 min
- Proof narrative: 10 min
- Physical discussion: 10 min
- Mathematical discussion: 8 min
- Lean discussion: 12 min
- Formatting: 3 min
- **Total: ~50 min per block**

**For 119 blocks: ~100 hours**

This matches the outline estimate of 115-145 hours for Part 3 (including integration and polish).

---

## CONCLUSION

This reference guide provides:
1. ✅ **Complete block listing** for all subsections of Part 3
2. ✅ **File paths and line numbers** for each block
3. ✅ **Content descriptions** (what the block contains)
4. ✅ **Example structures** for complex proofs
5. ✅ **Writing workflow** with time estimates

**Usage:**
- Use this as a checklist while writing Part 3
- Check off blocks as they are completed
- Adjust groupings if certain blocks are too small/large
- Add additional blocks if important lemmas are discovered

**Next Steps:**
1. Begin with Section 3.1 (File Organization) - no code blocks, easier start
2. Move to Section 3.2 (AxCal) - conceptual blocks, shorter proofs
3. Tackle Section 3.3 (Schwarzschild) - moderate complexity
4. Deep dive into Section 3.4 (Riemann) - most detailed, allow extra time
5. Complete Sections 3.5-3.7 - wrap up with results and verification

**Estimated Completion:**
At 4 hours/day writing pace, Part 3 alone: ~30-40 working days (~6-8 weeks)

---

**Prepared:** October 2025
**For:** Paper 5 Restructuring Project - Part 3 Code Documentation
