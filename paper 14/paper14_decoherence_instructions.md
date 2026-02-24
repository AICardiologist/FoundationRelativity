# Paper 14: The Measurement Problem as a Logical Artefact
## Coding Agent Instructions — Lean 4 Formalization

**Author:** P.C.K. Lee
**Date:** February 2026
**Status:** Exploratory — let the Lean code decide whether this paper exists

---

## 0. Executive Summary

**Thesis:** "Wave function collapse" is the measurement problem's singularity — an LPO-level assertion that a bounded monotone process (decoherence) reaches its limit. The physical content (a system becomes effectively classical to any finite-precision observation) is BISH. The metaphysical puzzle (does the wave function *really* collapse?) is a question about a completed infinite object that no experiment can distinguish.

**Goal:** Formalize finite-dimensional decoherence in Lean 4 and calibrate the logical cost of exact vs approximate decoherence. If the exact-decoherence limit produces a clean LPO equivalence (via BMC), this is the strongest paper in the series — domain invariance across a third physical domain (after statistical mechanics and general relativity). If the equivalence is messy or involves different principles, we have a technical result but not a head-turner. Let the axiom certificates decide.

**What makes this different from the abandoned Paper 14:** The previous Paper 14 (LPO Elimination Theorem) was abandoned because its core content was folklore. This paper has concrete, novel Lean-verifiable content: the logical cost of decoherence has never been calibrated in constructive reverse mathematics.

---

## 1. The Physics

### 1.1 Setup: Qubit + N-Qubit Environment

A quantum system (single qubit) interacts with an environment (N qubits). The composite system lives in ℂ² ⊗ (ℂ²)^⊗N ≅ ℂ^(2^(N+1)).

Initial state: |ψ⟩_S ⊗ |0⟩_E where |ψ⟩_S = α|0⟩ + β|1⟩ is an arbitrary qubit state and |0⟩_E is the environment ground state.

After interaction (a controlled-NOT or similar entangling gate applied sequentially), the composite state becomes entangled. The reduced density matrix of the system (obtained by partial trace over the environment) has off-diagonal elements that decay as N grows.

### 1.2 The Decoherence Sequence

Define the **coherence** of the system after interacting with N environment qubits:

  c(N) = |ρ_S^(N)_{01}| = |Tr_E(ρ_{SE}^(N))_{01}|

where ρ_S^(N) is the reduced density matrix of the system after tracing out N environment qubits.

Key properties (to be proven in Lean):
- c(0) = |αβ*| (initial coherence, determined by the state)
- c(N) is monotonically decreasing: c(N+1) ≤ c(N)
- c(N) is bounded below by 0
- c(N) = |αβ*| · ∏_{k=1}^{N} |cos θ_k| for interaction angles θ_k

For uniform interactions (all θ_k = θ with 0 < θ < π/2):
  c(N) = |αβ*| · (cos θ)^N

This is a bounded monotone decreasing sequence.

### 1.3 The Logical Split

**BISH content (finite decoherence):** For any ε > 0 and any finite N, we can compute c(N) and verify whether c(N) < ε. The explicit formula c(N) = |αβ*| · (cos θ)^N gives a computable Cauchy modulus: N > log(ε/|αβ*|) / log(cos θ) suffices. This is finite arithmetic — BISH.

**LPO content (exact decoherence):** The assertion "c(N) → 0 as N → ∞" — i.e., the off-diagonal elements vanish *exactly* in the limit — is the assertion that a bounded monotone sequence converges to its infimum. This is BMC, which is equivalent to LPO (proven in Papers 3 and 8).

**The measurement problem lives in the gap:** "Collapse" = the assertion that ρ_S becomes *exactly* diagonal. This is the completed limit. The physical content — that ρ_S is *ε-close* to diagonal for any desired ε, given enough environmental interactions — is BISH.

---

## 2. Formalization Architecture

### 2.1 Module Structure

```
Paper14_Decoherence/
├── Defs.lean                  -- Core definitions
│                                 (coherence, decoherence map, interaction model)
├── FiniteDecoherence.lean     -- BISH content: c(N) computation,
│                                 explicit formula, ε-approximation
├── MonotoneDecay.lean         -- c(N+1) ≤ c(N), bounded below by 0
├── CauchyModulus.lean         -- Explicit modulus for geometric decay
├── ExactDecoherence.lean      -- The LPO equivalence:
│                                 "c(N) → 0 exactly" ↔ BMC ↔ LPO
├── PartialTraceN.lean         -- Partial trace over N qubits
│                                 (extends Paper 11 infrastructure)
├── Main.lean                  -- Assembly, #print axioms, documentation
└── Papers.lean                -- Module imports
```

Estimated total: 600–1000 lines.

### 2.2 Dependencies on Existing Infrastructure

**From Paper 11 (Entanglement):**
- `partialTraceB` — partial trace over a single qubit (ℂ⁴ → ℂ²)
- `bellDensityMatrix`, `bellState_partialTrace` — Bell state computations
- `binaryEntropy` — entropy definitions
- Matrix-first approach (concrete Fin n matrices, not abstract tensor products)

**From Paper 8 (Ising/BMC ↔ LPO):**
- `BMC_iff_LPO` — the equivalence between bounded monotone convergence and LPO
- This is the key theorem we'll invoke for the reverse direction

**From Paper 13 (Schwarzschild):**
- Pattern: bounded monotone sequence from physics → LPO equivalence
- The Cauchy modulus extraction pattern

### 2.3 Key Design Decision: Matrix Size

The composite system ℂ² ⊗ (ℂ²)^⊗N has dimension 2^(N+1). We CANNOT work with concrete `Fin (2^(N+1))` matrices for arbitrary N — the dimension is parametric.

**Two approaches:**

**Approach A (Recommended): Work with N as parameter, use inductive structure.**

Define the decoherence map inductively:
```lean
/-- The reduced density matrix after interacting with k environment qubits.
    Defined inductively: ρ_S^(0) = initial state,
    ρ_S^(k+1) = Tr_E_k(U_k · (ρ_S^(k) ⊗ |0⟩⟨0|) · U_k†) -/
noncomputable def decoherenceStep (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  -- Apply one CNOT-like interaction with angle θ, then trace out the environment qubit
  -- Result: a 2×2 matrix (the system's reduced state)
  sorry
```

Each step takes a 2×2 matrix → 2×2 matrix. We never need to represent the full 2^(N+1)-dimensional space. The decoherence map is a completely positive trace-preserving (CPTP) map on 2×2 matrices.

This is the right approach because:
1. It matches how decoherence actually works (sequential interactions)
2. It keeps all matrices at 2×2 or 4×4 (manageable in Lean)
3. It makes the monotonicity proof inductive
4. It matches the existing Paper 11 infrastructure (4×4 matrices)

**Approach B (Fallback): Work with concrete small N.**

Formalize for N = 1, 2, 3 explicitly using `Fin 4`, `Fin 8`, `Fin 16` matrices. Extract the pattern. State the general theorem with the inductive structure as a conjecture verified for small cases.

Less elegant but guaranteed to compile.

---

## 3. Detailed Proof Plan

### Part A: The BISH Content (Finite Decoherence)

#### 3.1 The Single-Step Decoherence Map

Model: system qubit interacts with one environment qubit via a controlled rotation.

The interaction unitary on ℂ² ⊗ ℂ² ≅ ℂ⁴:
```
U(θ) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ R_y(θ)
```
where R_y(θ) = [[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]].

This is a controlled rotation: if the system is |0⟩, the environment is unchanged; if |1⟩, the environment rotates by θ.

As a 4×4 matrix:
```
U(θ) = [[1, 0, 0, 0],
         [0, 1, 0, 0],
         [0, 0, cos(θ/2), -sin(θ/2)],
         [0, 0, sin(θ/2), cos(θ/2)]]
```

Initial composite state: ρ_S ⊗ |0⟩⟨0|.

After interaction: U(θ) · (ρ_S ⊗ |0⟩⟨0|) · U(θ)†.

Partial trace over environment: Tr_E[...].

**Theorem (decoherence_step):** If ρ_S = [[a, b], [b*, d]] then after one decoherence step with angle θ:
```
ρ_S' = [[a, b·cos(θ/2)], [b*·cos(θ/2), d]]
```

The diagonal entries are preserved. The off-diagonal entries are multiplied by cos(θ/2).

**This is the key calculation.** It's 4×4 matrix arithmetic — same infrastructure as Paper 11.

```lean
/-- One decoherence step multiplies off-diagonal elements by cos(θ/2) -/
theorem decoherence_step_offdiag (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (θ : ℝ) :
    (decoherenceMap θ ρ) 0 1 = ρ 0 1 * (Real.cos (θ / 2) : ℂ) := by
  sorry -- 4×4 matrix computation via fin_cases and norm_num
```

#### 3.2 N-Step Iteration

By induction:

```lean
/-- After N decoherence steps, off-diagonal coherence is multiplied by cos(θ/2)^N -/
theorem decoherence_N_offdiag (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (θ : ℝ) (N : ℕ) :
    ((decoherenceMap θ)^[N] ρ) 0 1 = ρ 0 1 * ((Real.cos (θ / 2) : ℂ))^N := by
  induction N with
  | zero => simp [Function.iterate_zero]
  | succ n ih => simp [Function.iterate_succ', decoherence_step_offdiag, ih, pow_succ]; ring
```

#### 3.3 The Coherence Sequence

Define:
```lean
/-- The coherence after N interactions -/
noncomputable def coherence (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (N : ℕ) : ℝ :=
  Complex.abs (((decoherenceMap θ)^[N] ρ₀) 0 1)
```

**Theorem (coherence_geometric):**
```lean
theorem coherence_eq_geometric (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (N : ℕ) :
    coherence ρ₀ θ N = Complex.abs (ρ₀ 0 1) * |Real.cos (θ / 2)|^N := by
  sorry
```

#### 3.4 Explicit ε-Approximation (BISH)

**Theorem (decoherence_epsilon):** For any ε > 0, if 0 < θ < π (so |cos(θ/2)| < 1), then:
  N ≥ ⌈log(ε / c₀) / log(|cos(θ/2)|)⌉ implies coherence(ρ₀, θ, N) < ε

where c₀ = Complex.abs (ρ₀ 0 1).

```lean
/-- Explicit N making coherence < ε. This is BISH: computable bound. -/
theorem decoherence_epsilon_bound (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ)
    (hθ : 0 < θ ∧ θ < Real.pi)
    (hc : Complex.abs (ρ₀ 0 1) > 0)
    (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ N, N ≥ N₀ → coherence ρ₀ θ N < ε := by
  sorry
```

**This theorem has a computable witness** — N₀ is explicitly constructed from θ and ε. The proof uses only the geometric decay formula and log arithmetic. No limits, no completeness, no LPO. Pure BISH.

### Part B: The LPO Content (Exact Decoherence)

#### 3.5 Monotonicity and Boundedness

```lean
/-- Coherence is monotonically decreasing -/
theorem coherence_antitone (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ)
    (hθ : |Real.cos (θ / 2)| ≤ 1) :
    Antitone (coherence ρ₀ θ) := by
  sorry

/-- Coherence is bounded below by 0 -/
theorem coherence_nonneg (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (N : ℕ) :
    0 ≤ coherence ρ₀ θ N := by
  exact Complex.abs.nonneg _
```

So `coherence ρ₀ θ` is a bounded monotone (decreasing) sequence. Define `c'(N) = -coherence(ρ₀, θ, N)` to get a bounded monotone increasing sequence, or work with antitone sequences directly.

#### 3.6 The LPO Equivalence

**Central Theorem:** The assertion "coherence converges to exactly 0" is equivalent to BMC, hence to LPO.

More precisely:

**Forward direction (BMC → exact decoherence):**
If every bounded monotone sequence converges, then the coherence sequence converges to some limit L ≥ 0. But for geometric decay with ratio r < 1, the only possible limit is 0. So BMC gives coherence → 0 exactly.

**Reverse direction (exact decoherence → LPO):**
Given an arbitrary bounded monotone increasing sequence {a_n} with a_n ≤ M, we need to show it converges using only the assumption that geometric decoherence sequences converge exactly to 0.

**THIS IS THE CRITICAL STEP.** There are two possible outcomes:

**Outcome 1 (Clean equivalence):** We can encode an arbitrary bounded monotone sequence into a decoherence-like sequence, proving that exact decoherence for all initial states and all angles implies BMC, hence LPO. This would give:

```lean
theorem exact_decoherence_iff_LPO :
    (∀ ρ₀ θ, [conditions] → ∃ L, Filter.Tendsto (coherence ρ₀ θ) Filter.atTop (nhds L))
    ↔ LPO := by
  sorry
```

This is the head-turning result. Domain invariance: decoherence joins the Ising thermodynamic limit and Schwarzschild geodesic incompleteness as a third independent physical manifestation of BMC ↔ LPO.

**Outcome 2 (Geometric decay is too special):** The geometric decay c(N) = c₀ · r^N converges constructively (the Cauchy modulus is explicit). So the specific decoherence sequence in this model doesn't need LPO at all — it converges at BISH with an explicit rate. The LPO content enters only if we consider the *general* statement "every decoherence process converges" for arbitrary (non-geometric) decay patterns.

**IMPORTANT:** Outcome 2 is actually the more likely result for this specific model. Geometric sequences converge constructively. The LPO content would need to come from a more general decoherence model where the decay rate is not explicitly computable — e.g., when the interaction angles θ_k vary and the product ∏ cos(θ_k/2) is a bounded monotone sequence with no closed-form expression.

#### 3.7 The Generalized Model (If Needed for LPO)

If the uniform-angle model is too constructive, generalize:

**Variable-angle decoherence:** System interacts with environment qubits at angles θ₁, θ₂, θ₃, ... The coherence after N steps is:

  c(N) = c₀ · ∏_{k=1}^{N} |cos(θ_k/2)|

This is a bounded monotone decreasing sequence (each factor ≤ 1). Whether it converges to 0 depends on whether ∑ -log|cos(θ_k/2)| diverges — which is a statement about an infinite series.

**Encoding BMC into variable-angle decoherence:**

Given a bounded monotone increasing sequence {a_n} with 0 ≤ a_n ≤ 1, define:
  θ_n = 2·arccos(1 - (a_{n+1} - a_n))  (or similar encoding)

such that the product ∏ cos(θ_k/2) converges iff {a_n} converges. This encoding would give the LPO equivalence.

```lean
/-- The general decoherence convergence principle is equivalent to LPO -/
theorem general_decoherence_convergence_iff_LPO :
    (∀ (θ : ℕ → ℝ), (∀ k, 0 < θ k ∧ θ k ≤ π) →
      ∃ L, Filter.Tendsto (fun N => c₀ * ∏ k in Finset.range N, |Real.cos (θ k / 2)|)
        Filter.atTop (nhds L))
    ↔ LPO := by
  sorry
```

**This is the theorem to aim for.** The general principle that "every decoherence process converges" is LPO. Specific processes (uniform angle) converge at BISH with explicit rates. Same pattern as Ising and Schwarzschild.

---

## 4. Axiom Certificate Requirements

Every theorem must satisfy `#print axioms` showing:

**BISH content (Part A):**
- NO `Classical.choice`, `Classical.em`, `Classical.byContradiction`, `Decidable` instances beyond finite types
- Permitted: `propext`, `Quot.sound`, `funext`

**LPO equivalence (Part B):**
- The forward direction (LPO → exact decoherence) will use `Classical.em` or an explicit `LPO` hypothesis
- The reverse direction (exact decoherence → LPO) must be BISH — no classical axioms
- The equivalence theorem itself states the biconditional

**Certification levels (same as Paper 13):**
- Level 0 (Structurally verified BISH): finite decoherence computation, ε-bounds, monotonicity
- Level 1 (Intentional classical): the LPO equivalence statement and forward direction

---

## 5. Proof Strategy: Step by Step

### Step 1: Decoherence Map (200–300 lines)

1. Define the controlled-rotation unitary U(θ) as a 4×4 matrix over ℂ
2. Define the decoherence map: ρ ↦ Tr_E[U(θ) · (ρ ⊗ |0⟩⟨0|) · U(θ)†]
3. Prove the off-diagonal multiplication theorem: ρ'_{01} = ρ_{01} · cos(θ/2)
4. Prove diagonal preservation: ρ'_{00} = ρ_{00}, ρ'_{11} = ρ_{11}
5. Prove trace preservation: Tr(ρ') = Tr(ρ)
6. Prove positivity preservation: ρ ≥ 0 → ρ' ≥ 0

All proofs by `fin_cases` and `norm_num` on 4×4 matrices. Same infrastructure as Paper 11.

### Step 2: N-Step Iteration (100–150 lines)

7. Define coherence(N) via Function.iterate
8. Prove geometric decay formula by induction
9. Prove monotonicity (antitone) of coherence
10. Prove boundedness (≥ 0)

### Step 3: BISH ε-Approximation (100–150 lines)

11. Construct explicit N₀ from ε, θ, c₀ using log arithmetic
12. Prove coherence(N) < ε for N ≥ N₀
13. This is the "finite decoherence is BISH" theorem
14. Verify `#print axioms` — must be clean

### Step 4: The LPO Equivalence (200–300 lines)

15. Import BMC ↔ LPO from Paper 8
16. Prove: BMC → coherence sequence converges (forward direction)
17. Define the encoding: arbitrary bounded monotone sequence → variable-angle decoherence
18. Prove: if all variable-angle decoherence processes converge, then BMC holds
19. Close the cycle: general decoherence convergence ↔ BMC ↔ LPO

### Step 5: Assembly and Audit (50–100 lines)

20. Main.lean with all imports
21. `#print axioms` for every exported theorem
22. Documentation of certification levels

---

## 6. What Could Go Wrong

### 6.1 The encoding might not work cleanly

The reverse direction (decoherence → LPO) requires encoding an arbitrary bounded monotone sequence into a decoherence problem. The product structure ∏ cos(θ_k/2) might not encode arbitrary monotone sequences cleanly. The encoding needs:
- Given {a_n} monotone increasing, bounded by M
- Construct {θ_k} such that ∏_{k≤N} cos(θ_k/2) is related to a_N
- The relationship must be tight enough that convergence of the product ↔ convergence of {a_n}

**Fallback:** If the direct encoding fails, try encoding through the logarithm. The series ∑ -log cos(θ_k/2) diverges iff the product → 0. Encoding a divergent/convergent series into the θ_k values might be easier than encoding the product directly. Alternatively, use the partial sums of the series as the monotone sequence.

### 6.2 Geometric decay is too constructive

If the specific model (uniform angles) is the only one formalized, the paper shows decoherence is BISH — which is correct and interesting but doesn't give the LPO equivalence. The paper would then be: "Finite decoherence is BISH; the question of whether it reaches exact zero is LPO by analogy with BMC, but we prove only the forward direction formally."

That's still a publishable result. Just less dramatic.

### 6.3 The partial trace infrastructure is insufficient

Paper 11's partial trace works for ℂ² ⊗ ℂ² → ℂ². The decoherence step is the same: trace out one qubit from a two-qubit system. So the existing infrastructure should suffice for the single-step computation. The iteration handles the N-qubit environment without ever forming the full 2^(N+1)-dimensional space.

---

## 7. The Punchline (If It Works)

**Three independent physical domains. Same logical structure.**

| Domain | Bounded Monotone Sequence | BISH Content | LPO Content |
|--------|--------------------------|--------------|-------------|
| Stat. Mech. (Paper 8) | Free energy per particle f_N | f_N computed, ε-bounds | f_∞ exists exactly |
| Gen. Relativity (Paper 13) | Radial coordinate r(τ) | r(τ) computed along geodesic | r → 0 exactly (singularity) |
| **Quantum Measurement (Paper 14)** | **Coherence c(N)** | **c(N) computed, ε-bounds** | **c → 0 exactly (collapse)** |

All three: finite physics at BISH, completed limit at LPO, connected via BMC.

The measurement problem dissolves: "collapse" is the assertion that a bounded monotone process reaches its limit. Copenhagen, many-worlds, and decoherence interpretations all agree at BISH (the system is ε-close to classical for any ε). They disagree only about LPO-level assertions regarding the completed limit of an infinite-dimensional process. The programme doesn't adjudicate between interpretations. It shows the disagreement is about the formalism, not about nature.

---

## 8. References

- H. D. Zeh, "On the interpretation of measurement in quantum theory," *Found. Phys.* 1 (1970), 69–76.
- W. H. Zurek, "Decoherence and the transition from quantum to classical," *Physics Today* 44 (1991), 36–44.
- E. Joos and H. D. Zeh, "The emergence of classical properties through interaction with the environment," *Z. Phys. B* 59 (1985), 223–243.
- M. Schlosshauer, *Decoherence and the Quantum-to-Classical Transition*, Springer, 2007.
- E. Bishop, *Foundations of Constructive Analysis*, McGraw-Hill, 1967.
- H. Ishihara, "Reverse mathematics in Bishop's constructive mathematics," *Philosophia Scientiae* (2006).
- P. C.-K. Lee, Papers 8, 11, 13 in the Constructive Calibration Programme (Zenodo, 2026).

---

## 9. Instructions for the Coding Agent

### Priority Order

1. **First:** Implement the decoherence map (Section 5, Step 1). This is the foundation. Get the 4×4 matrix computation working. Reuse Paper 11's partial trace.

2. **Second:** Prove the geometric decay formula (Step 2). This is the N-step induction. Should be straightforward once Step 1 compiles.

3. **Third:** Prove the ε-approximation (Step 3). This is the BISH content. Run `#print axioms` — it must be clean. This is the minimum publishable result.

4. **Fourth:** Attempt the LPO equivalence (Step 4). This is the hard part. Start with the forward direction (BMC → convergence), which is easier. Then attempt the encoding for the reverse direction. If the encoding doesn't work after reasonable effort, stop and report what the obstacle is.

### Lean Style

- Use `Matrix (Fin 4) (Fin 4) ℂ` for composite systems (same as Paper 11)
- Use `Matrix (Fin 2) (Fin 2) ℂ` for single-qubit density matrices
- Use `fin_cases` and `norm_num` for matrix computations
- Use `Function.iterate` for N-step iteration
- Use `Real.cos`, `Real.log` from Mathlib
- Import BMC ↔ LPO from Paper 8 (do not re-prove)

### Mathlib Dependencies

- `Mathlib.Analysis.InnerProductSpace.Basic`
- `Mathlib.LinearAlgebra.Matrix.Hermitian`
- `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Mathlib.Data.Matrix.Kronecker`
- `Mathlib.LinearAlgebra.Matrix.Trace`
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- `Mathlib.Data.Complex.Basic`
- `Mathlib.Order.Filter.Basic` (for Tendsto)

### What to Report Back

After each step, report:
1. Lines of code written
2. `#print axioms` output for all theorems
3. Any obstacles encountered
4. Whether the next step seems feasible

**Critical checkpoint:** After Step 3, we decide whether to proceed to Step 4 based on what the axiom certificates show and whether the encoding looks tractable.

---

## 10. Success Criteria

**Minimum publishable result (Steps 1–3 only):**
- Finite decoherence is BISH (clean axiom certificates)
- Geometric decay formula proven
- Explicit ε-approximation with computable bound
- Paper title: "Decoherence at BISH: The Constructive Content of Quantum-to-Classical Transition"

**Full result (Steps 1–4):**
- Everything above, plus:
- General decoherence convergence ↔ LPO equivalence
- Domain invariance: third physical domain producing BMC ↔ LPO
- Paper title: "The Measurement Problem as a Logical Artefact: Constructive Calibration of Quantum Decoherence"

Let the Lean code decide which paper we write.
