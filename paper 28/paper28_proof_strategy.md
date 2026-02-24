# Paper 28: Newton vs. Lagrange — Constructive Stratification of Classical Mechanics

## Proof Strategy Document for Lean 4 Agent

**Series:** Constructive Reverse Mathematics and Physics
**Depends on:** Paper 23 (FT ↔ CompactOptimization)
**Target:** ~400–600 lines Lean 4, zero sorries
**Date:** 2026-02-11

---

## 1. THEOREM STATEMENT (ENGLISH)

**Main Theorem (Stratification).** Over BISH, for a classical mechanical system with compact configuration space M ⊆ ℝⁿ and regular Lagrangian L(q, q̇, t):

1. **(BISH)** The discrete Euler-Lagrange equations ∂Sₙ/∂qᵢ = 0 are solvable without FT.
2. **(FT)** The assertion that the discrete action functional Sₙ attains its minimum on the space of admissible discrete paths requires FT.

Therefore the Newtonian (ODE/algebraic) formulation and the Lagrangian (variational/optimization) formulation are constructively stratified: BISH versus FT.

**Corollary.** The variational interpretation of classical mechanics is logically dispensable — the equations are the physical content; the optimization is a framing whose existence claim costs FT.

---

## 2. ARCHITECTURE OVERVIEW

```
Paper23.FT_iff_CompactOpt          -- imported, already proved
    │
    ├── DiscreteAction.lean         -- §3: define Sₙ, prove continuity
    │       │
    │       ├── Minimizer requires FT (invoke P23)
    │       │
    │       └── EulerLagrange.lean  -- §4: derive ∂Sₙ/∂qᵢ = 0, solve in BISH
    │
    ├── HarmonicOscillator.lean     -- §5: concrete instantiation
    │       │
    │       ├── QuadraticAction (explicit formula)
    │       ├── TridiagonalSystem (EL equations)
    │       ├── GaussianElimination (BISH solver)
    │       └── MinimizerFT (invoke P23 on quadratic)
    │
    └── Stratification.lean         -- §6: package the separation theorem
            │
            ├── bish_solves_EL : BISH ⊢ ∃ solution to EL system
            ├── ft_needed_for_min : (∃ minimizer of Sₙ) → FT
            └── stratification : ¬(BISH ⊢ ∃ minimizer) ∧ (BISH ⊢ ∃ EL solution)
```

---

## 3. KEY DEFINITIONS

### 3.1 Discrete Path Space

```
-- A discrete path on [0,T] with N+1 time steps, endpoints fixed
structure DiscretePath (N : ℕ) (M : Set ℝ) (A B : ℝ) where
  nodes : Fin (N + 1) → ℝ         -- q₀, q₁, ..., qₙ
  in_config : ∀ i, nodes i ∈ M     -- all nodes in configuration space
  left_bc : nodes 0 = A             -- q₀ = A
  right_bc : nodes ⟨N, Nat.lt_succ_of_le le_rfl⟩ = B  -- qₙ = B
```

**Agent note:** The free variables are (q₁, ..., qₙ₋₁). The boundary conditions fix q₀ and qₙ. The interior nodes form a point in M^(N-1). When M = [0,1], this is [0,1]^(N-1), which is compact.

### 3.2 Discrete Action Functional

```
-- Discrete Lagrangian action
-- S_N(q₁,...,qₙ₋₁) = Σᵢ L(qᵢ, (qᵢ₊₁ - qᵢ)/Δt, tᵢ) · Δt
noncomputable def discreteAction
    (L : ℝ → ℝ → ℝ → ℝ)  -- L(q, qdot, t)
    (T : ℝ) (N : ℕ) (hN : 0 < N)
    (path : Fin (N + 1) → ℝ) : ℝ :=
  let Δt := T / N
  ∑ i : Fin N,
    L (path i) ((path (i + 1) - path i) / Δt) (i * Δt) * Δt
```

### 3.3 Harmonic Oscillator Specialization

```
-- L(q, qdot, t) = ½m·qdot² - ½k·q²
def harmonicLagrangian (m k : ℝ) (hm : 0 < m) (hk : 0 < k) :
    ℝ → ℝ → ℝ → ℝ :=
  fun q qdot _t => (m * qdot^2 - k * q^2) / 2
```

**Agent note:** For the harmonic oscillator, the discrete action is a *quadratic form* in the free variables (q₁,...,qₙ₋₁). This makes both halves of the theorem concrete and clean. The EL equations become a tridiagonal linear system. The quadratic form is continuous on a compact domain.

---

## 4. PROOF STRATEGIES

### 4.1 FT Half: Minimizer Existence Requires FT

**Strategy:** Direct reduction to Paper 23's `ft_iff_compact_opt`.

**Proof sketch:**
1. The domain of Sₙ (interior nodes) is [0,1]^(N-1) when M = [0,1]. This is compact.
2. Sₙ is continuous on this domain (composition of continuous functions: addition, multiplication, division by fixed Δt > 0).
3. "Sₙ attains its minimum" is an instance of "continuous function on compact set attains its minimum" = EVT = CompactOptimization.
4. By Paper 23, CompactOptimization ↔ FT.
5. Therefore minimizer existence requires FT. ∎

**Lean outline:**
```
theorem minimizer_requires_ft
    (L : ℝ → ℝ → ℝ → ℝ) (hL_cont : Continuous (fun p => L p.1 p.2.1 p.2.2))
    (M : Set ℝ) (hM : IsCompact M)
    (N : ℕ) (hN : 2 ≤ N) :
    (∀ S : (Fin (N-1) → M) → ℝ, Continuous S →
      ∃ x, ∀ y, S x ≤ S y) ↔ FanTheorem :=
  Paper23.ft_iff_compact_opt _ _
```

**Technical warnings:**
- You need `IsCompact` on M^(N-1). Use `IsCompact.pi` or `isCompact_Icc.pi` from Mathlib.
- The continuity of Sₙ follows from `Continuous.sum`, `Continuous.mul`, `Continuous.sub`, `Continuous.div_const`. These are all in Mathlib.
- The key import is Paper 23's equivalence. Match its type signature exactly.

**Risk:** LOW. This is a direct application of Paper 23. The only real work is showing Sₙ is continuous, which is routine.

### 4.2 BISH Half: Euler-Lagrange Equations Solvable

**Strategy:** For the harmonic oscillator, the discrete EL equations form a tridiagonal linear system. Solve by Gaussian elimination (constructive, BISH).

**Proof sketch (harmonic oscillator):**

1. Compute ∂Sₙ/∂qᵢ for the harmonic Lagrangian. Result:

   m(qᵢ₊₁ - 2qᵢ + qᵢ₋₁)/Δt² + k·qᵢ = 0

   for i = 1, ..., N-1.

2. This is the linear system **A**·**q** = **b** where:
   - **A** is (N-1)×(N-1) tridiagonal with diagonal entries -(2m/Δt² + k) and off-diagonal entries m/Δt².
   - **b** encodes the boundary terms from q₀ = A, qₙ = B.

3. **A** is strictly diagonally dominant (for appropriate Δt, i.e., Δt² < 2m/k). Strictly diagonally dominant matrices are invertible constructively.

4. Gaussian elimination on a tridiagonal system is O(N) operations, all computable. Solution exists in BISH. ∎

**Lean outline:**
```
-- The tridiagonal matrix for harmonic oscillator EL equations
def tridiagonalMatrix (m k : ℝ) (Δt : ℝ) (N : ℕ) :
    Matrix (Fin (N-1)) (Fin (N-1)) ℝ := ...

-- Strict diagonal dominance implies invertibility (constructive)
theorem diag_dominant_invertible
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : StrictDiagDominant A) : IsUnit A.det := ...

-- The EL system has a unique solution in BISH
theorem el_solution_bish
    (m k T : ℝ) (hm : 0 < m) (hk : 0 < k) (hT : 0 < T)
    (N : ℕ) (hN : 2 ≤ N)
    (hΔt : (T/N)^2 < 2*m/k)  -- CFL-like stability condition
    (A B : ℝ) :
    ∃! q : Fin (N-1) → ℝ,
      tridiagonalMatrix m k (T/N) N *ᵥ q = boundaryVector m (T/N) A B := ...
```

**Technical warnings:**
- Diagonal dominance → invertibility is in Mathlib as `Matrix.det_ne_zero_of_strictDiagDominant` or similar. CHECK MATHLIB. If not present, it's ~50 lines to prove from the Gershgorin circle theorem or direct induction on the tridiagonal structure.
- The stability condition hΔt is physically the CFL condition. Without it, the discrete system can be ill-conditioned. Include it as a hypothesis — it's a standard requirement.
- You do NOT need `Classical.choice` or `Classical.em` anywhere in the BISH half. If the axiom audit shows classical axioms, something is wrong.

**Risk:** MEDIUM. The main risk is whether Mathlib has the tridiagonal solver infrastructure. If not, you'll need to build it (~100 lines). The diagonal dominance result may also need construction.

### 4.3 Stratification Assembly

**Strategy:** Package both halves into the separation theorem.

```
theorem stratification
    (m k T : ℝ) (hm : 0 < m) (hk : 0 < k) (hT : 0 < T)
    (N : ℕ) (hN : 2 ≤ N)
    (hΔt : (T/N)^2 < 2*m/k)
    (A B : ℝ) (hA : A ∈ Set.Icc 0 1) (hB : B ∈ Set.Icc 0 1) :
    -- BISH: EL equations solvable without FT
    (∃! q : Fin (N-1) → ℝ,
      tridiagonalMatrix m k (T/N) N *ᵥ q = boundaryVector m (T/N) A B)
    ∧
    -- FT: minimizer existence equivalent to FT
    ((∃ q : Fin (N-1) → Set.Icc (0:ℝ) 1,
      ∀ q', discreteAction (harmonicLagrangian m k hm hk) T N _ (pathFromInterior q A B) ≤
             discreteAction (harmonicLagrangian m k hm hk) T N _ (pathFromInterior q' A B))
      ↔ FanTheorem) := by
  exact ⟨el_solution_bish m k T hm hk hT N hN hΔt A B,
         minimizer_requires_ft (harmonicLagrangian m k hm hk) hL_cont (Set.Icc 0 1) isCompact_Icc N hN⟩
```

---

## 5. AXIOM AUDIT SPECIFICATION

This is the central deliverable. The agent MUST verify:

| Result | Allowed Axioms | Forbidden Axioms |
|--------|---------------|-----------------|
| `el_solution_bish` | propext, Quot.sound, funext | Classical.choice, Classical.em, FanTheorem |
| `minimizer_requires_ft` | propext, Quot.sound, funext, FanTheorem (as hypothesis/equivalence) | Classical.choice should appear ONLY through FT |
| `stratification` | union of above | nothing beyond the union |

**How to audit:**
```lean
#print axioms el_solution_bish
-- Expected: [propext, Quot.sound, funext] only

#print axioms minimizer_requires_ft
-- Expected: [propext, Quot.sound, funext] + possibly FanTheorem-related
```

**CRITICAL:** If `Classical.choice` appears in `el_solution_bish`, the BISH claim is INVALID. Debug immediately. Common culprits:
- `Finset.sum` sometimes pulls in classical axioms through `Decidable` instances. Use `DecidableEq` instances explicitly.
- `Matrix.det` in Mathlib may use classical decidability. If so, provide constructive `DecidableEq` for `Fin n`.
- `∃!` (exists unique) is fine constructively, but the proof must not use `Classical.choice` to extract the witness.

---

## 6. DETAILED COMPONENT SPECIFICATIONS

### 6.1 DiscreteAction.lean (~80–120 lines)

**Definitions needed:**
- `DiscretePath` structure (§3.1 above)
- `discreteAction` function (§3.2 above)
- `pathFromInterior`: given free nodes (q₁,...,qₙ₋₁) and boundary values A, B, assemble full path

**Theorems needed:**
- `discreteAction_continuous`: Sₙ is continuous as a function of interior nodes
  - Proof: `Continuous.sum` of `Continuous.mul` of compositions. Straightforward.
- `domain_compact`: [0,1]^(N-1) is compact
  - Proof: `isCompact_Icc.pi` or `IsCompact.pi_of_finite`

**Mathlib dependencies:** `Topology.Order.Basic`, `Topology.Algebra.InfiniteSum.Basic`, `MeasureTheory.Function.ContinuousMapDense` (maybe), `Topology.CompactOpen`

### 6.2 EulerLagrange.lean (~100–150 lines)

**Definitions needed:**
- `discreteEL`: the system ∂Sₙ/∂qᵢ = 0 expressed as a matrix equation
- `tridiagonalMatrix`: the specific (N-1)×(N-1) matrix for the harmonic oscillator
- `boundaryVector`: the RHS vector encoding boundary conditions

**Theorems needed:**
- `el_eq_matrix_system`: the discrete EL equations equal **A**·**q** = **b**
  - Proof: Direct computation. Expand ∂Sₙ/∂qᵢ for harmonic Lagrangian, collect terms.
- `tridiag_diag_dominant`: the matrix **A** is strictly diagonally dominant (under the CFL condition)
  - Proof: Direct computation. |diagonal entry| = 2m/Δt² + k. Sum of |off-diagonal| = 2m/Δt² (for interior rows) or m/Δt² (for boundary rows). The condition Δt² < 2m/k ensures |diag| > |off-diag sum|.
- `diag_dominant_det_ne_zero`: strictly diagonally dominant → det ≠ 0
  - Check Mathlib first. If absent, prove by Gershgorin or by LU factorization with positive pivots.
- `el_solution_bish`: combine above to get ∃! solution

**Technical note on constructive linear algebra:** Cramer's rule gives an explicit formula for the solution of **A**·**q** = **b** when det(**A**) ≠ 0. Cramer's rule is fully constructive — it's a finite sum of finite products. This is the cleanest path if diagonal dominance → det ≠ 0 is hard to get without classical axioms. In Mathlib: `Matrix.cramer`, `Matrix.mulVec_cramer`.

### 6.3 HarmonicOscillator.lean (~80–120 lines)

**Definitions:**
- `harmonicLagrangian` (§3.3 above)
- Explicit quadratic form for Sₙ with this Lagrangian

**Theorems:**
- `harmonic_action_quadratic`: Sₙ for harmonic oscillator equals ½ **q**ᵀ **H** **q** + **c**ᵀ **q** + d for explicit **H**, **c**, d
  - Proof: Expand the sum. Standard algebra.
- `harmonic_action_continuous`: immediate from quadratic = polynomial = continuous
- `harmonic_minimizer_iff_ft`: invoke Paper 23

### 6.4 Stratification.lean (~50–80 lines)

Package everything. State and prove `stratification`. Run axiom audits. Add docstrings explaining the physical interpretation.

---

## 7. CONVEXITY AND THE STATIONARY-VS-MINIMUM SUBTLETY

**Important conceptual point the agent should encode in comments/docstrings:**

Hamilton's principle says δS = 0 (stationarity), not min S. Our FT claim is about minimizers, not stationary points. For the harmonic oscillator:

- The Hessian matrix **H** of Sₙ is the tridiagonal matrix **A** itself (up to sign and scaling).
- Under the CFL condition, **A** is strictly diagonally dominant with negative diagonal entries → **A** is negative definite → Sₙ is concave... 

**WAIT.** Check the sign convention carefully.

- L = T - V = ½mq̇² - ½kq². The kinetic term ½m(qᵢ₊₁-qᵢ)²/Δt² contributes POSITIVE curvature to Sₙ. The potential term -½kqᵢ² contributes NEGATIVE curvature.
- For the action to be bounded below on the compact domain [0,1]^(N-1), we need the domain compactness (which we have), not convexity.
- The action may NOT be convex for all parameter choices. But EVT doesn't require convexity — it only requires continuity + compactness.

**Resolution:** The FT claim does NOT depend on convexity. It depends only on: (1) Sₙ continuous, (2) domain compact, (3) EVT = FT. Convexity would give us stationary ⟹ minimizer, which is a bonus but not needed for the theorem.

**What the agent should prove:** The minimizer exists ↔ FT. Period. The relationship between stationary points and minimizers is a remark in the docstring, not a formal theorem for this paper.

---

## 8. MATHLIB DEPENDENCY CHECKLIST

Before writing any code, the agent should verify these exist in the current Mathlib:

| Item | Expected Location | Fallback if Missing |
|------|------------------|-------------------|
| `IsCompact.pi` or equivalent | `Topology.Compactness.Compact` | Build from `isCompact_Icc` + finite product |
| `Continuous.sum` (finite) | `Topology.Algebra.InfiniteSum` | Use `Finset.sum` continuity |
| `Matrix.mulVec` | `LinearAlgebra.Matrix.NonsingularInverse` | Definitely present |
| `Matrix.cramer` | `LinearAlgebra.Matrix.Adjugate` | Definitely present |
| `Matrix.det_ne_zero_of_sum_...` (diag dominance) | Unknown | Build ~40 lines |
| Paper 23 `ft_iff_compact_opt` | Local project | MUST be importable |

**Agent instruction:** Run `#check @IsCompact.pi` etc. at the start. Report missing items before proceeding.

---

## 9. PROOF ORDER (RECOMMENDED)

1. **Start with HarmonicOscillator.lean** — define the Lagrangian, compute the explicit quadratic action. This is concrete and testable.
2. **Build EulerLagrange.lean** — derive the tridiagonal system, prove diagonal dominance, prove solvability. This is the BISH half.
3. **Build DiscreteAction.lean** — prove continuity and domain compactness. Invoke Paper 23 for the FT half.
4. **Assemble Stratification.lean** — combine both halves, run axiom audit.
5. **Axiom audit LAST** — after everything compiles, verify the separation.

**Rationale:** Start with the concrete (harmonic oscillator) before the abstract (general framework). The concrete example is the paper's primary evidence; the general framework is scaffolding.

---

## 10. POTENTIAL PITFALLS AND MITIGATIONS

### 10.1 Classical Leakage in Finite Sums
**Problem:** `Finset.sum` in Mathlib sometimes depends on `Decidable` instances that pull in `Classical.decidable`.
**Mitigation:** Provide explicit `DecidableEq (Fin n)` instances. Use `Fin.decidableEq` which is constructive.

### 10.2 Matrix Determinant Computability
**Problem:** `Matrix.det` uses `Finset.sum` over permutations. The `DecidableEq` on `Equiv.Perm` might be classical.
**Mitigation:** For the tridiagonal case, compute det by the recurrence relation det(Aₙ) = aₙ·det(Aₙ₋₁) - bₙ²·det(Aₙ₋₂) directly. This avoids the general `Matrix.det` and stays constructive. ~30 lines.

### 10.3 Division by Δt
**Problem:** Δt = T/N involves division. Division by zero is a lurking issue if N = 0.
**Mitigation:** Carry `hN : 0 < N` as hypothesis everywhere. Derive `hΔt_pos : 0 < Δt` early and reuse.

### 10.4 Paper 23 Interface Mismatch
**Problem:** Paper 23's `ft_iff_compact_opt` may have a type signature that doesn't directly match our setup (e.g., it might be stated for `ℝ` not `ℝⁿ`, or for a specific compact set).
**Mitigation:** Read Paper 23's exact statement FIRST. If it's for [0,1] → ℝ, generalize to [0,1]ⁿ → ℝ via the standard product compact argument. If it's already general, use directly.

### 10.5 The ∃ vs ∃! Issue
**Problem:** The BISH half claims ∃! (existence AND uniqueness) via Cramer's rule. The FT half claims ∃ (existence only) of a minimizer.
**Mitigation:** These are different claims and that's fine. Uniqueness of the minimizer is NOT claimed (and may fail for non-convex actions). Uniqueness of the EL solution IS claimed (and follows from det ≠ 0).

---

## 11. EXPECTED LINE COUNTS

| File | Lines | Confidence |
|------|-------|-----------|
| DiscreteAction.lean | 80–120 | HIGH |
| EulerLagrange.lean | 100–150 | MEDIUM (depends on Mathlib coverage) |
| HarmonicOscillator.lean | 80–120 | HIGH |
| Stratification.lean | 50–80 | HIGH |
| **Total** | **310–470** | Within 400–600 target |

---

## 12. SUCCESS CRITERIA

The paper is complete when:

1. ✅ `el_solution_bish` compiles with `#print axioms` showing BISH only
2. ✅ `minimizer_requires_ft` compiles showing FT dependence
3. ✅ `stratification` compiles packaging both
4. ✅ Zero `sorry`s in all files
5. ✅ The harmonic oscillator instantiation is fully explicit (no abstract nonsense)
6. ✅ Docstrings explain the physical interpretation at each theorem

---

## 13. SUMMARY FOR AGENT

**You are proving:** The same physical system (harmonic oscillator on [0,1]) has two mathematically equivalent formulations that are constructively inequivalent. Solving the equations of motion is BISH. Asserting the existence of an action-minimizing path is FT. This is the cleanest possible demonstration that variational principles carry logical overhead beyond their equation-of-motion content.

**Your main tool is Paper 23.** The FT half is a one-line invocation of Paper 23 after you establish continuity + compactness. The BISH half is independent: tridiagonal linear algebra, no choice principles, no excluded middle.

**The axiom audit is the theorem.** If the audit doesn't show clean separation, the paper has no content. Prioritize clean axioms over generality.
