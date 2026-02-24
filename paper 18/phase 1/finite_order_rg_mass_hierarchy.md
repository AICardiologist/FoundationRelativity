# Finite-Order RG Quasi-Fixed-Point Structure and the Fermion Mass Hierarchy

## A Numerical Investigation

**Author:** Paul Chun-Kit Lee  
**Date:** February 2026  
**Status:** Exploratory computation — not a paper draft

---

## 1. Motivation

The Constructive Reverse Mathematics (CRM) programme has established that empirical predictions in physics calibrate at BISH (Bishop's constructive mathematics), while non-constructive principles (LPO, WLPO) enter only through idealizations — completed limits, infinite-dimensional spaces, exact symmetries — that are dispensable for extracting numbers that match experiment.

Applied to the fermion mass problem: every existing approach to explaining the mass hierarchy (flavor symmetries, extra dimensions, Sumino's mechanism for Koide) operates within BISH *except* when it invokes exact all-orders statements about perturbation theory or exact continuous symmetries. The CRM insight suggests that the demand for exact relations may be artificially constraining the search space. If we relax "exact" to "accurate to observed precision at finite loop order," new mechanisms become visible.

**Core hypothesis:** The Standard Model's own perturbative structure, evaluated as a *discrete finite-step map* rather than a continuous flow, may contain quasi-fixed-point structure that produces the observed fermion mass hierarchy from non-hierarchical initial conditions.

**Known precedent:** The top quark Yukawa coupling has a well-known infrared quasi-fixed-point (Pendleton-Ross 1981, Hill 1981). At one loop, the top Yukawa is driven toward y_t ~ 1 by the large QCD correction, regardless of its initial value at high scales (provided it starts large enough). This is visible at *finite* loop order — it's a property of the one-loop beta function as a discrete map, not of the continuous RG flow.

**Question:** Does the coupled Yukawa-gauge system at two-loop and three-loop order exhibit additional quasi-fixed-point structure that determines the lighter fermion masses?

---

## 2. The Computation

### 2.1 Standard Model Beta Functions

The one-loop beta functions for the Yukawa couplings in the SM are well-known. For the third generation (which dominates due to the top mass):

```
16π² dy_t/dt = y_t [9/2 y_t² + 3/2 y_b² + y_τ² - 8g₃² - 9/4 g₂² - 17/12 g₁²]

16π² dy_b/dt = y_b [9/2 y_b² + 3/2 y_t² + y_τ² - 8g₃² - 9/4 g₂² - 5/12 g₁²]

16π² dy_τ/dt = y_τ [5/2 y_τ² + 3y_b² + 3y_t² - 9/4 g₂² - 15/4 g₁²]
```

where t = ln(μ/μ₀) and g₁, g₂, g₃ are the U(1), SU(2), SU(3) gauge couplings.

The gauge coupling beta functions at one loop:

```
16π² dg₁/dt = 41/6 g₁³
16π² dg₂/dt = -19/6 g₂³  
16π² dg₃/dt = -7 g₃³
```

### 2.2 What to Compute

**Phase 1: Reproduce the known top quasi-fixed-point.**

1. Implement the one-loop RG equations for (y_t, y_b, y_τ, g₁, g₂, g₃) as a discrete map.
2. Run from the Planck scale (μ = 10¹⁹ GeV) to the electroweak scale (μ = 246 GeV) in N discrete steps (try N = 100, 1000, 10000).
3. Scan over initial conditions: y_t(Planck) ∈ [0.1, 10], y_b(Planck) ∈ [0.001, 1], y_τ(Planck) ∈ [0.001, 1].
4. Verify that y_t at the EW scale converges to ≈ 1 (the quasi-fixed-point) for a wide range of initial y_t values.
5. Plot y_t(EW) vs y_t(Planck) to visualize the fixed-point attraction basin.

**Phase 2: Look for additional structure in the coupled system.**

1. For each scan point, record all six couplings at the EW scale.
2. Compute the fermion mass ratios: m_t/m_b = y_t/y_b, m_t/m_τ = y_t/y_τ (at tree level).
3. Plot these ratios as functions of initial conditions.
4. Look for *correlations* — are there regions of initial-condition space where the mass ratios m_t/m_b and m_t/m_τ simultaneously match the observed values (~40 and ~100 respectively)?
5. If so, how large is this region? If it's an attractor (many initial conditions lead to the same ratios), that's a quasi-fixed-point for the mass hierarchy.

**Phase 3: Two-loop effects.**

The two-loop beta functions for Yukawa couplings are known (Machacek & Vaughn 1984; Luo, Wang & Xiao 2003). They are more complex but still finite algebra.

1. Implement the two-loop beta functions.
2. Repeat the scan from Phase 2.
3. Compare one-loop and two-loop results: does the two-loop structure change the fixed-point structure qualitatively? Are there new quasi-fixed-points visible at two loops that are absent at one loop?

**Phase 4: The Koide test.**

1. At each scan point, compute the Koide ratio Q = (m_e + m_μ + m_τ)/(√m_e + √m_μ + √m_τ)² using the RG-evolved Yukawa couplings.
2. For this to work, need to include the first and second generation Yukawa couplings (y_c, y_s, y_u, y_d, y_μ, y_e). These are perturbatively decoupled from the third generation at one loop but contribute at two loops.
3. Check whether there exist initial conditions where Q ≈ 2/3 emerges from the RG evolution without being put in by hand.

---

## 3. Implementation Notes

### 3.1 Physical Constants (at the EW scale, μ = M_Z = 91.1876 GeV)

```python
# Gauge couplings at M_Z (MSbar scheme)
g1_MZ = 0.3574    # U(1)_Y, GUT normalized: g1 = sqrt(5/3) g'
g2_MZ = 0.6518    # SU(2)_L
g3_MZ = 1.221     # SU(3)_C (at M_Z)

# Yukawa couplings at M_Z (approximate, from pole masses)
# y_f = sqrt(2) m_f / v, where v = 246.22 GeV
v = 246.22  # Higgs VEV in GeV

# Pole masses (PDG 2024)
m_t = 172.57   # GeV (top)
m_b = 4.18     # GeV (bottom, MSbar at m_b)
m_tau = 1.777  # GeV (tau)
m_c = 1.27     # GeV (charm, MSbar at m_c)
m_s = 0.0934   # GeV (strange, MSbar at 2 GeV)
m_mu = 0.10566 # GeV (muon)
m_u = 0.00216  # GeV (up, MSbar at 2 GeV)
m_d = 0.00467  # GeV (down, MSbar at 2 GeV)
m_e = 0.000511 # GeV (electron)

# Tree-level Yukawa couplings
# y_f = sqrt(2) * m_f / v
```

### 3.2 The Discrete Map

The key CRM-motivated choice: treat the RG evolution as a **discrete map**, not a continuous ODE. At each step:

```python
def rg_step(y, g, dt):
    """
    One step of the discrete RG map.
    y = dict of Yukawa couplings
    g = (g1, g2, g3) gauge couplings
    dt = step size in t = ln(mu/mu0)
    
    Returns updated (y, g) after one step.
    This is BISH: finite arithmetic, no limits.
    """
    # Compute beta functions (finite algebra)
    beta_y = compute_yukawa_betas(y, g)  # one-loop or two-loop
    beta_g = compute_gauge_betas(g)
    
    # Euler step (simplest discrete map)
    y_new = {f: y[f] + beta_y[f] * dt for f in y}
    g_new = tuple(g[i] + beta_g[i] * dt for i in range(3))
    
    return y_new, g_new
```

For better accuracy, use RK4 (still BISH — it's a finite composition of arithmetic operations):

```python
def rg_step_rk4(y, g, dt):
    """Fourth-order Runge-Kutta step. Still BISH."""
    k1_y, k1_g = compute_betas(y, g)
    
    y2 = {f: y[f] + 0.5*dt*k1_y[f] for f in y}
    g2 = tuple(g[i] + 0.5*dt*k1_g[i] for i in range(3))
    k2_y, k2_g = compute_betas(y2, g2)
    
    y3 = {f: y[f] + 0.5*dt*k2_y[f] for f in y}
    g3 = tuple(g[i] + 0.5*dt*k2_g[i] for i in range(3))
    k3_y, k3_g = compute_betas(y3, g3)
    
    y4 = {f: y[f] + dt*k3_y[f] for f in y}
    g4 = tuple(g[i] + dt*k3_g[i] for i in range(3))
    k4_y, k4_g = compute_betas(y4, g4)
    
    y_new = {f: y[f] + dt/6*(k1_y[f] + 2*k2_y[f] + 2*k3_y[f] + k4_y[f]) for f in y}
    g_new = tuple(g[i] + dt/6*(k1_g[i] + 2*k2_g[i] + 2*k3_g[i] + k4_g[i]) for i in range(3))
    
    return y_new, g_new
```

### 3.3 Scale Range

```python
import numpy as np

mu_EW = 91.1876      # GeV (M_Z)
mu_Planck = 1.22e19  # GeV (Planck mass)

t_range = np.log(mu_Planck / mu_EW)  # ≈ 39.4

# For N steps:
N = 1000
dt = t_range / N  # ≈ 0.0394

# Run DOWNWARD from Planck to EW:
# t goes from t_range to 0
# dt is negative for downward running
```

---

## 4. Specific Questions to Answer

### Q1: Top Quasi-Fixed-Point (Validation)

Run the one-loop system with y_t(Planck) scanned over [0.1, 10] and fixed y_b = 0.01, y_τ = 0.01, and gauge couplings at their Planck-scale values (evolved upward from M_Z values).

**Expected result:** y_t(EW) ≈ 1.0 ± 0.1 for y_t(Planck) > 0.5 or so. This is the Pendleton-Ross fixed point.

**Plot:** y_t(EW) vs y_t(Planck). Should show convergence/flattening.

### Q2: Bottom and Tau Quasi-Fixed-Points

For the coupled (y_t, y_b, y_τ) system, scan over initial conditions at the Planck scale:
- y_t(Planck) ∈ [0.5, 5.0] (50 points)
- y_b(Planck) ∈ [0.001, 1.0] (50 points, log scale)
- y_τ(Planck) ∈ [0.001, 1.0] (50 points, log scale)

Compute y_b(EW)/y_τ(EW) for each point.

**Key question:** Is there a region where y_b(EW)/y_τ(EW) ≈ m_b/m_τ ≈ 2.35 regardless of the specific initial conditions? If so, this is a quasi-fixed-point for the b/τ mass ratio.

**Known result to check against:** In GUT models, bottom-tau unification (y_b = y_τ at the GUT scale) is a well-known prediction of SU(5). The RG running from the GUT scale to M_Z with the SM beta functions produces m_b/m_τ ≈ 3, which is close to the observed ratio. Does this show up as a quasi-fixed-point in the discrete map?

### Q3: Mass Hierarchy Attractor

The big question: treating the full system (all 9 Yukawa couplings + 3 gauge couplings) as a discrete map from the Planck scale to the EW scale, does the map have attractor structure that produces the observed mass hierarchy?

Specifically, define the "mass hierarchy vector":
```
H = (y_t/y_b, y_t/y_τ, y_t/y_c, y_t/y_s, y_t/y_μ, y_t/y_u, y_t/y_d, y_t/y_e)
```

Observed values (approximate):
```
H_obs ≈ (41, 97, 136, 1850, 1635, 80000, 37000, 338000)
```

Scan random initial conditions at the Planck scale (all Yukawa couplings drawn from a log-uniform distribution on [0.01, 10]) and compute H at the EW scale.

**If H(EW) clusters near H_obs for many initial conditions:** the mass hierarchy is an attractor of the finite-order RG map. This would be a genuine discovery — the hierarchy emerges from SM dynamics without new physics.

**If H(EW) is sensitive to initial conditions:** the mass hierarchy is not determined by the SM RG and requires UV input (new physics at the Planck scale or a selection mechanism).

### Q4: The Koide Ratio Under RG Flow

For initial conditions that produce approximately correct third-generation masses:

1. Include the charged lepton Yukawa couplings (y_e, y_μ, y_τ).
2. Evolve from Planck to EW.
3. Compute Q = (m_e + m_μ + m_τ) / (√m_e + √m_μ + √m_τ)² at the EW scale.
4. Is Q ≈ 2/3 a generic output of the RG evolution, or does it require fine-tuned initial conditions?

### Q5: Discrete Map vs Continuous Flow

Compare the output of:
- (a) N = 10 discrete Euler steps (very coarse BISH computation)
- (b) N = 100 discrete RK4 steps (moderate BISH computation)
- (c) N = 10000 discrete RK4 steps (fine BISH computation, approximates continuous flow)

**Question:** At what coarseness N does the quasi-fixed-point structure become visible? If it's visible at N = 10, the structure is robust and truly finite. If it requires N → ∞ to see, it's an LPO artifact.

---

## 5. Two-Loop Beta Functions

The full two-loop Yukawa beta functions for the SM are given in Luo, Wang & Xiao (2003), Phys. Rev. D 67, 065019. They are lengthy but entirely algebraic. The key additions at two loops:

- Yukawa-gauge mixing terms (y²g², y²g⁴)
- Yukawa self-coupling terms (y⁶)
- Inter-generation Yukawa mixing (small but present via CKM)

For the initial exploration, it is sufficient to implement:
1. One-loop for all couplings (Phase 1-2)
2. Two-loop for gauge couplings, one-loop for Yukawa (Phase 3 intermediate)
3. Full two-loop for everything (Phase 3 complete)

**Reference for two-loop beta functions:**
- M.-x. Luo, H.-w. Wang, Y. Xiao, "Two-loop renormalization group equations in the Standard Model," Phys. Rev. D 67, 065019 (2003). arXiv:hep-ph/0211440.

The coefficients can be found in Table I of that paper or obtained from the PyR@TE package (Python tool for automatic computation of RG equations).

---

## 6. Success Criteria

This investigation succeeds if ANY of the following are found:

1. **Quasi-fixed-point for mass ratios:** The ratio y_b/y_τ or y_c/y_s at the EW scale is approximately independent of initial conditions at the Planck scale. (Partially known: b-τ unification is a one-loop result.)

2. **Attractor structure for the hierarchy:** The full mass hierarchy vector H clusters near its observed value for a non-trivial region of initial-condition space.

3. **Koide from RG:** The Koide ratio Q ≈ 2/3 emerges at the EW scale from generic initial conditions at the Planck scale, without being inserted by hand.

4. **Discrete-map novelty:** The quasi-fixed-point structure at finite N (coarse discrete map) differs qualitatively from the continuous-flow result, suggesting genuinely new structure visible only in the BISH formulation.

5. **New quasi-fixed-points at two loops:** Two-loop beta functions reveal quasi-fixed-point structure not present at one loop, suggesting the mass hierarchy is a perturbative phenomenon that becomes visible at the right loop order.

This investigation fails cleanly (and informatively) if:

- The mass ratios are highly sensitive to initial conditions, showing no attractor structure. This means the hierarchy requires UV physics that the SM RG cannot determine.
- The results at finite N and large N are qualitatively identical, meaning the discrete-map formulation adds nothing over the standard continuous-flow analysis.

Either outcome is worth knowing.

---

## 7. Dependencies

```
numpy
scipy (for scipy.integrate.solve_ivp as comparison to discrete map)
matplotlib (for plots)
```

No specialized physics packages required. The beta functions are polynomials in the couplings — pure arithmetic.

---

## 8. Philosophical Context

This investigation is motivated by the CRM programme's central finding: physics computes at BISH, and LPO enters only through dispensable idealizations. The standard treatment of the RG as a continuous flow (an ODE integrated to a limit) is an LPO idealization. The BISH content is the discrete map at finite step count. If the mass hierarchy is determined by the discrete map, then the hierarchy is a BISH phenomenon — computable by finite arithmetic from the SM's algebraic structure. If it requires the continuous limit, the hierarchy has genuinely non-constructive content and the CRM programme would need to account for this.

The investigation is not a CRM formalization (no Lean, no proof certificates). It is a numerical experiment to determine whether the question is worth formalizing. If affirmative results are found, a formal treatment could follow as a future paper in the CRM series.
