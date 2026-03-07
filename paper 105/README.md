# Paper 105: The Dynamical Penumbra — CRM of Cardiac Electrophysiology

**Clinical Sub-Series Paper C** of the Constructive Reverse Mathematics Series

Paul Chun-Kit Lee (NYU Grossman School of Medicine, Brooklyn)

## Main Results

The logical cost of cardiac electrophysiology tracks mathematical idealisation
(finite → infinite dimensions), not biological complexity.

| # | Component | CRM Level |
|---|-----------|-----------|
| 1 | ODE existence (Picard-Lindelöf) | BISH |
| 2 | Trapping region (inward flow) | BISH |
| 3 | SOS barrier verification | BISH |
| 4 | Topological charge conservation | BISH |
| 5 | Eigenvalue sign (fixed params) | BISH |
| 6 | Hopf bifurcation (generic params) | BISH+WLPO |
| 7 | Sustained chaotic fibrillation | BISH+WKL |
| 8 | Defibrillation optimality | BISH+LPO |

**Decomposition:** 5 BISH + 1 WLPO + 1 WKL + 1 LPO = 8 components
**BISH fraction:** 62.5%
**Overall CRM level:** BISH+LPO

### Theorems

- **Theorem A (BISH):** Local existence and uniqueness of FHN solutions via
  constructive Picard-Lindelöf. Explicit Lipschitz constant L = 202/25 on
  trapping box [-3,3] × [-5,5].
- **Theorem B (BISH):** Bounded safety verification via SOS barrier certificates.
  Certificate verification requires only polynomial ring arithmetic.
- **Theorem B' (BISH/WLPO):** Hopf bifurcation detection. Fixed rational
  parameters: BISH (norm_num). Generic parameters: WLPO (deciding Re(λ)=0).
- **Theorem C (WKL):** Three-level idealisation ladder. Cell (BISH) →
  Network (BISH) → Tissue (BISH + WKL). Short-time mild solutions are BISH
  (heat semigroup + Duhamel). WKL enters through Cantor Intersection Theorem
  on nested compact surviving-state sets in the chaotic regime.
- **Theorem D (LPO):** Defibrillation threshold optimality. Minimax over
  uncountable fibrillation attractor requires real trichotomy.

## Lean 4 Bundle

**Location:** `P105_DynamicalPenumbra/`
**Toolchain:** `leanprover/lean4:v4.29.0-rc2`
**Lines:** 1,246
**Sorry count:** 0
**Files:** 9

### Build

```bash
cd P105_DynamicalPenumbra
lake build
```

### File Structure

| File | Lines | Content |
|------|-------|---------|
| OmnisciencePrinciples.lean | 189 | LPO, WLPO, LLPO, WKL, MP, CRMLevel hierarchy |
| FHNSystem.lean | 123 | FHN parameters, vector field, Jacobian, nullclines |
| LipschitzBound.lean | 135 | Theorem A: Lipschitz constant, trapping region, Picard convergence |
| SOSBarrier.lean | 144 | Theorem B: SOS barrier certificates, Lie derivative verification |
| HopfBifurcation.lean | 137 | Theorem B': Hopf condition, eigenvalue sign, WLPO boundary |
| ThreeLevelDecomposition.lean | 137 | Theorem C: Cell/Network/Tissue idealisation ladder |
| DefibrillationOptimality.lean | 142 | Theorem D: VEP computation (BISH), defibrillation threshold (LPO) |
| TopologicalCharge.lean | 128 | Spiral wave charges, pair annihilation, teleportation |
| Paper105_Assembly.lean | 111 | Master CRM decomposition, audit, clinical sub-series comparison |

### Axiom Inventory

**Documentary axioms** (model CRM boundaries, not mathematical truth):
1. `hopf_detection_requires_WLPO` — Hopf bifurcation detection is WLPO
2. `chaotic_termination_is_WKL` — Cantor Intersection Theorem (Weihrauch-equivalent to WKL)
3. `defibrillation_threshold_requires_LPO` — minimax over attractor
4. `below_threshold_failure` — converse direction of Theorem D
5. `min_defib_pos` — minimum defibrillation energy is positive

**Infrastructure axioms** (universal):
- `propext`, `Quot.sound`, `Classical.choice` (Mathlib imports only)

**Zero sorry. Zero Classical.choice on constructive path.**

## Python CAS

`solve_fhn.py` computes:
- Lipschitz bound L = 202/25 for R=3 trapping box
- Rectangular trapping box [-3,3] × [-5,5] face conditions
- Equilibrium coordinates and Jacobian eigenvalues
- Hopf bifurcation threshold I*_Hopf

## Dependencies

- Lean 4 v4.29.0-rc2
- Mathlib (via lakefile.lean)
- Python 3 + SymPy (for CAS script only)

## Clinical Sub-Series Context

| Paper | Title | BISH% | Overall |
|-------|-------|-------|---------|
| 103 | Asymptotic Penumbra | 70% | BISH+LPO |
| 104 | Algorithmic Penumbra | 50% | BISH+MP |
| **105** | **Dynamical Penumbra** | **62.5%** | **BISH+LPO** |

Paper 105 introduces dynamical systems (FHN, spiral waves, defibrillation)
and spans the widest CRM range in the clinical sub-series: BISH through LPO,
with WLPO and WKL intermediate levels.
