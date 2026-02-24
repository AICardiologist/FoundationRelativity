# Proof Strategy Document: P27 — The LLPO-Bell Correspondence

## Paper Working Title
**The LLPO-Bell Correspondence: Σ⁰₁ Disjunction Structure Inside Bell Nonlocality**
**Subtitle: A Lean 4 Formalization**

## Series Context

Paper 26 established the Gödel-Gap correspondence: the Lindenbaum algebra of Π⁰₁ sentences order-embeds into ℓ∞/c₀, calibrated at WLPO. This paper attempts the analogous construction for LLPO and Bell nonlocality.

**Critical honesty warning**: The LLPO/Bell connection is less clean than the WLPO/Gödel-Gap connection. This document flags exactly where the mathematics is established, where it's speculative, and where the Lean formalization might fail. The proof agent should treat this document as a research exploration with fallback positions, not a guaranteed proof path.

## Background: Why LLPO and Bell?

### What LLPO Is

LLPO (Lesser Limited Principle of Omniscience): For any binary sequence α, 
if α has at most one 1, then either all odd-indexed entries are 0, or all even-indexed entries are 0.

Equivalently: given two binary sequences, at most one of which is nonzero, you can decide which one is identically zero.

Equivalently: for a continuous function f: [a,b] → ℝ with f(a) ≤ 0 ≤ f(b), there exists c with f(c) = 0. (IVT — Intermediate Value Theorem.)

LLPO is strictly between BISH and WLPO. WLPO implies LLPO but not conversely. LLPO is incomparable with MP.

### What Bell's Theorem Says (Constructively)

**The naive claim that "Bell = LLPO" is WRONG.** We discussed this extensively (see Paper 19 planning notes). Bell's theorem says:

1. Assume a local hidden variable (LHV) model: probability space (Λ, μ) with functions A(a,λ), B(b,λ) ∈ {−1, +1}.
2. Derive CHSH: |⟨S⟩| ≤ 2 (finite linear algebra — BISH).
3. Quantum mechanics gives |⟨S⟩| = 2√2 for Bell state (finite computation — BISH).
4. Contradiction. Therefore ¬(LHV).

This is a negation, not a disjunction. Constructively valid at BISH. No omniscience needed.

The desire to say "either locality fails or realism fails" (which sounds like LLPO) is a classical inference: ¬(L ∧ R) → ¬L ∨ ¬R requires De Morgan's law, which requires LEM. Constructive Bell simply says the conjunction fails, period.

### Where LLPO Actually Enters

LLPO enters Bell-adjacent physics through three genuine routes:

**Route 1: Optimal measurement angles (IVT).** For a general entangled state ρ, the maximum CHSH violation S*(ρ) = max_{a,a',b,b'} |⟨S⟩|. The correlation function C(θ) = Tr(ρ · σ_A(θ) ⊗ σ_B(θ')) is continuous in measurement angles. Finding the angles that saturate the bound involves the intermediate value theorem (or more precisely, the extreme value theorem for optimization). For *specific* states (Bell state), the optimal angles are computable (π/4, etc.). For *general* states, finding optimal angles requires IVT, which is LLPO.

**Route 2: Critical detection efficiency (IVT).** In real Bell experiments, the critical detection efficiency η* above which no LHV model survives is determined by solving an equation. For a general state/measurement setup, finding η* requires root-finding of a continuous function, which is IVT, hence LLPO.

**Route 3: Decomposition of correlations.** Given a quantum correlation matrix P that violates CHSH, decomposing the violation into "which classical constraint fails" requires a disjunction. The correlation polytope has facets corresponding to different Bell inequalities. Determining which facet is violated by a general correlation involves linear programming feasibility, which for continuous parameters involves IVT-type arguments.

**This paper focuses on Route 1** (optimal angles) because it's the most mathematically natural and connects directly to IVT ↔ LLPO. Route 2 is a potential extension. Route 3 requires more infrastructure.

## Central Theorem (Target)

### Main Result

**LLPO-Bell Correspondence**: The set of "angle-finding problems" for Bell correlations embeds into the set of IVT instances, and vice versa, with the LLPO principle governing decidability of both.

More precisely, we aim to prove a calibration chain analogous to P26:

```
LLPO ↔ "optimal Bell angle findable for all states" 
     ↔ "IVT for continuous functions on [0, 2π]"
```

### Correspondence Structure (Parallel to P26)

**P26 structure**: Π⁰₁ sentence → Gödel sequence → element of ℓ∞/c₀ → zero iff refutable.

**P27 structure**: IVT instance (continuous function with sign change) → Bell correlation function → optimal angle existence → angle findable iff LLPO.

**The "logical algebra" on the LLPO side**: IVT instances modulo constructive equivalence. An IVT instance is a continuous function f: [0,1] → ℝ with f(0) ≤ 0 ≤ f(1). Two instances are equivalent if they have the same zero set structure. The "zero element" is an instance where the root is computable (trivial IVT). The "nonzero elements" are instances where the root exists classically but is not computable.

**The "physical space" on the Bell side**: The space of entangled states with their optimal measurement angles. For each state ρ, the optimal CHSH violation requires specific angles. The question "what are the optimal angles?" is the physical analogue of "where is the root?"

## Architecture Overview

```
P27_LLPOBell/
├── Basic.lean               -- LLPO definition, IVT connection
├── BellCorrelation.lean     -- CHSH, correlation functions, quantum bound
├── AngleFinding.lean        -- Optimal angle as IVT instance
├── IVTInstances.lean        -- IVT instances, equivalence, algebra structure
├── Encoding.lean            -- Map from IVT instances to Bell angle problems
├── Calibration.lean         -- LLPO ↔ optimal angle findable ↔ IVT
├── Correspondence.lean      -- Main embedding theorem
├── Main.lean                -- Aggregator, axiom audit
```

---

## Phase 1: LLPO and IVT (`Basic.lean`)

### LLPO Definition

```lean
/-- LLPO: Lesser Limited Principle of Omniscience.
    If a binary sequence has at most one 1, then either all even-indexed
    entries are 0, or all odd-indexed entries are 0. -/
def LLPO : Prop :=
  ∀ (α : ℕ → Bool),
    (∀ m n, α m = true → α n = true → m = n) →  -- at most one 1
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)
```

**Alternative equivalent formulation** (more useful for IVT connection):

```lean
/-- LLPO equivalent: for two binary sequences, at most one nonzero,
    we can decide which is identically zero. -/
def LLPO' : Prop :=
  ∀ (α β : ℕ → Bool),
    (¬ (∃ n, α n = true) ∨ ¬ (∃ n, β n = true)) →  -- at most one nonzero
    (∀ n, α n = false) ∨ (∀ n, β n = false)

/-- Proof that LLPO ↔ LLPO' -/
theorem llpo_iff_llpo' : LLPO ↔ LLPO' := by sorry -- standard, see Bridges-Richman
```

### IVT ↔ LLPO (Established Result)

The equivalence IVT ↔ LLPO is a known result in constructive analysis (Bridges and Richman, "Varieties of Constructive Mathematics", 1987; Ishihara 2006).

```lean
/-- Constructive IVT: if f is continuous on [a,b] with f(a) ≤ 0 ≤ f(b),
    then there exists c ∈ [a,b] with f(c) = 0.
    This is equivalent to LLPO over BISH. -/
def ConstructiveIVT : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f →
    ∀ (a b : ℝ), a < b → f a ≤ 0 → 0 ≤ f b →
      ∃ c, a ≤ c ∧ c ≤ b ∧ f c = 0

/-- IVT implies LLPO -/
theorem ivt_implies_llpo : ConstructiveIVT → LLPO := by sorry

/-- LLPO implies IVT -/  
theorem llpo_implies_ivt : LLPO → ConstructiveIVT := by sorry
```

**Proof strategy for ivt_implies_llpo**: Given a binary sequence α with at most one 1, construct a continuous piecewise-linear function f: [0,1] → ℝ that encodes α. The function starts positive, and at each stage n where α(n) could be 1, the function is deflected toward a sign change at either even or odd position. If the root is found, reading off its position tells you whether the even or odd subsequence is all-zero.

**This is the hardest proof in the paper.** The encoding of binary sequences into continuous functions is delicate. Multiple constructions exist in the literature (Bridges-Richman §3.3, Ishihara 2006 §4). The Lean formalization requires careful management of piecewise linear functions and their continuity proofs.

**Proof strategy for llpo_implies_ivt**: Given LLPO and f continuous with f(a) ≤ 0 ≤ f(b), perform bisection: let c = (a+b)/2, evaluate f(c). If we could decide f(c) ≤ 0 or f(c) ≥ 0, we'd recurse. We can't decide this in general — but we can use LLPO to resolve the ambiguity when f(c) is close to zero. Specifically, LLPO gives us: either f(c) ≤ ε or f(c) ≥ -ε for appropriate ε. This is enough to make bisection converge.

**Proof agent note**: The IVT ↔ LLPO equivalence is the mathematical foundation of the paper. If these two proofs don't compile, nothing else works. **Prioritize these above everything else.** Allow up to 400 lines for this phase alone.

**Fallback**: If the full IVT ↔ LLPO proof is too hard to formalize, axiomatize it:
```lean
axiom ivt_iff_llpo : ConstructiveIVT ↔ LLPO
```
This is justified by the established literature. Document it as an axiomatized known result. But try the proofs first — formalizing IVT ↔ LLPO would be a genuine contribution independent of the Bell connection.

---

## Phase 2: Bell Correlation Functions (`BellCorrelation.lean`)

### CHSH Setup

```lean
/-- A Bell measurement setup: two parties, two settings each,
    outcomes ±1. We work in ℝ for simplicity. -/
structure BellSetup where
  /-- Correlation function: E(a,b) = expected value of product of outcomes
      when Alice measures setting a, Bob measures setting b -/
  correlation : ℝ → ℝ → ℝ
  /-- Correlations are bounded by 1 -/
  corr_bound : ∀ a b, |correlation a b| ≤ 1

/-- CHSH combination for settings a, a' (Alice) and b, b' (Bob) -/
def chshValue (B : BellSetup) (a a' b b' : ℝ) : ℝ :=
  B.correlation a b + B.correlation a b' + B.correlation a' b - B.correlation a' b'

/-- Classical CHSH bound: any LHV model satisfies |S| ≤ 2 -/
-- This is BISH (finite algebra). Paper 11 proved this already.
-- We can import or re-prove.
```

### Quantum Correlation Function

For a quantum state, the correlation function has a specific form:

```lean
/-- For a two-qubit quantum state, the correlation when Alice measures
    along angle θ_A and Bob along θ_B is:
    E(θ_A, θ_B) = -cos(θ_A - θ_B) for the Bell singlet state -/
def singletCorrelation (θ_A θ_B : ℝ) : ℝ :=
  -Real.cos (θ_A - θ_B)

/-- The singlet correlation function is continuous -/
theorem singletCorrelation_continuous :
    Continuous (fun p : ℝ × ℝ => singletCorrelation p.1 p.2) := by
  unfold singletCorrelation
  exact continuous_neg.comp (Real.continuous_cos.comp (continuous_fst.sub continuous_snd))
```

### The CHSH Violation as a Function of Angles

```lean
/-- CHSH value for singlet state as a function of measurement angles -/
def singletCHSH (a a' b b' : ℝ) : ℝ :=
  singletCorrelation a b + singletCorrelation a b' +
  singletCorrelation a' b - singletCorrelation a' b'

/-- For specific angles (0, π/4, π/8, 3π/8), the violation is 2√2 -/
theorem singlet_tsirelson : singletCHSH 0 (π/4) (π/8) (3*π/8) = 2 * Real.sqrt 2 := by
  sorry -- trigonometric computation, similar to Paper 11

/-- The CHSH value is continuous in all four angles -/
theorem singletCHSH_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ => singletCHSH p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  sorry -- composition of continuous functions
```

---

## Phase 3: The Angle-Finding Problem (`AngleFinding.lean`)

### Key Insight: Optimal Angles as an IVT Problem

For the singlet state, the optimal angles are known: (0, π/4, π/8, 3π/8). But for a GENERAL two-qubit state ρ, the optimal measurement angles are NOT known in closed form. Finding them requires optimizing a continuous function over a compact set, which in general requires root-finding (setting the gradient to zero), which is IVT.

```lean
/-- A general two-qubit state determines a correlation function -/
structure QuantumCorrelation where
  /-- Correlation as a function of measurement angles -/
  E : ℝ → ℝ → ℝ
  /-- Continuity -/
  E_continuous : Continuous (fun p : ℝ × ℝ => E p.1 p.2)
  /-- Bounded -/
  E_bound : ∀ θ₁ θ₂, |E θ₁ θ₂| ≤ 1

/-- The CHSH value for a general quantum correlation -/
def generalCHSH (Q : QuantumCorrelation) (a a' b b' : ℝ) : ℝ :=
  Q.E a b + Q.E a b' + Q.E a' b - Q.E a' b'

/-- The maximum CHSH violation for a quantum correlation -/
noncomputable def maxCHSH (Q : QuantumCorrelation) : ℝ :=
  sSup { s | ∃ a a' b b', generalCHSH Q a a' b b' = s }

/-- The angle-finding problem: given Q with maxCHSH Q > 2,
    find specific angles (a, a', b, b') achieving the violation -/
def AngleFindable (Q : QuantumCorrelation) : Prop :=
  maxCHSH Q > 2 →
    ∃ a a' b b', generalCHSH Q a a' b b' > 2
```

**Note**: `AngleFindable` as stated is trivially true classically (the supremum is attained on a compact set by the extreme value theorem). The constructive content is: *can you compute the witnessing angles?*

### The Root-Finding Reduction

The CHSH value S(a, a', b, b') is a smooth function of four angles. At the maximum, the gradient vanishes:

∂S/∂a = 0, ∂S/∂a' = 0, ∂S/∂b = 0, ∂S/∂b' = 0

This is a system of equations. For a general correlation function E, solving this system requires root-finding for continuous functions, which is IVT.

```lean
/-- The gradient of CHSH with respect to Alice's first angle -/
noncomputable def chsh_gradient_a (Q : QuantumCorrelation) (a a' b b' : ℝ) : ℝ :=
  deriv (fun θ => generalCHSH Q θ a' b b') a

/-- Finding critical points of CHSH requires solving:
    gradient = 0, which is an IVT instance -/
def CriticalAngleExists (Q : QuantumCorrelation) : Prop :=
  ∃ a a' b b',
    chsh_gradient_a Q a a' b b' = 0 ∧
    -- (and similar for other partial derivatives)
    generalCHSH Q a a' b b' > 2
```

**The IVT connection**: For a single-parameter family (fixing three angles, varying one), the gradient is a continuous function that changes sign (it's positive on one side of the maximum, negative on the other). Finding the root of the gradient is an IVT instance. Hence, finding optimal angles costs LLPO per angle.

---

## Phase 4: The Encoding (`Encoding.lean`)

### IVT Instances

```lean
/-- An IVT instance: a continuous function on [0,1] with a sign change -/
structure IVTInstance where
  f : ℝ → ℝ
  f_continuous : Continuous f
  f_neg_at_zero : f 0 ≤ 0
  f_pos_at_one : 0 ≤ f 1

/-- An IVT instance is "trivial" if the root is computable -/
def IVTInstance.isTrivial (I : IVTInstance) : Prop :=
  ∃ c, 0 ≤ c ∧ c ≤ 1 ∧ I.f c = 0 ∧ 
    -- c is computable (there exists a Cauchy sequence converging to c
    -- with known modulus of convergence)
    True -- placeholder for computability condition

/-- The "IVT algebra": IVT instances modulo equivalence -/
-- Two instances are equivalent if they have the same root-finding difficulty
-- This is less clean than the Lindenbaum algebra. See discussion below.
```

### From Bell Angles to IVT Instances

```lean
/-- Given a quantum correlation Q and three fixed angles,
    the CHSH gradient as a function of the fourth angle
    is an IVT instance (when the gradient changes sign) -/
noncomputable def bellToIVT (Q : QuantumCorrelation)
    (a' b b' : ℝ) (h_sign_change : ∃ θ₁ θ₂,
      chsh_gradient_a Q θ₁ a' b b' < 0 ∧
      0 < chsh_gradient_a Q θ₂ a' b b') : IVTInstance where
  f := fun θ => chsh_gradient_a Q θ a' b b'
  f_continuous := sorry -- derivative of continuous function
  f_neg_at_zero := sorry -- use θ₁ from hypothesis
  f_pos_at_one := sorry -- use θ₂ from hypothesis
```

### From IVT Instances to Bell Angles

This is the reverse direction and the harder one. Given an arbitrary IVT instance (continuous function with sign change), can we construct a quantum correlation whose optimal angle-finding problem encodes that IVT instance?

```lean
/-- Given an IVT instance, construct a quantum correlation whose
    optimal angle-finding problem is equivalent to finding the root -/
noncomputable def ivtToBell (I : IVTInstance) : QuantumCorrelation where
  E := fun θ₁ θ₂ =>
    -- Encode I.f into a correlation function
    -- The correlation should be such that the optimal θ₁ 
    -- corresponds to the root of I.f
    sorry
  E_continuous := sorry
  E_bound := sorry
```

**THIS IS THE CRITICAL CONSTRUCTION AND THE MAIN RISK.**

Unlike P26 where the encoding was natural (proof search → binary sequence → ℓ∞), encoding an arbitrary continuous function into a quantum correlation is not obviously possible. Quantum correlations have specific structure — they arise from quantum states and measurements, not from arbitrary continuous functions.

**Possible approach**: Use the Horodecki criterion. For a two-qubit state ρ, the maximal CHSH violation is S_max = 2√(λ₁ + λ₂) where λ₁ ≥ λ₂ are the two largest eigenvalues of T^T · T (T being the correlation matrix). The optimal angles depend on the eigenvectors of T^T · T. By constructing a family of states ρ(t) parameterized by a continuous parameter t, where the eigenvectors of T(t)^T · T(t) rotate continuously with t, the optimal angle becomes a continuous function of t. If this function has a sign change (relative to some reference), finding where the angle crosses a threshold is an IVT instance.

**Alternative approach (simpler)**: Forget about encoding arbitrary IVT instances into Bell. Instead, prove only the forward direction: Bell angle-finding costs LLPO. This gives a calibration upper bound (angle-finding ≤ LLPO) rather than a full equivalence. Combined with the known IVT ↔ LLPO, this places angle-finding in the LLPO complexity class.

**Proof agent recommendation**: Attempt the forward direction first (Bell → IVT). If it works cleanly, attempt the reverse (IVT → Bell). If the reverse fails, settle for a one-directional calibration.

---

## Phase 5: The Calibration Chain (`Calibration.lean`)

### Target

```lean
/-- Forward: LLPO implies optimal angles are findable for all states -/
theorem llpo_implies_angle_findable :
    LLPO → ∀ Q : QuantumCorrelation, maxCHSH Q > 2 →
      ∃ a a' b b', generalCHSH Q a a' b b' > 2 := by
  intro hllpo Q hmax
  -- Use LLPO → IVT to find roots of the gradient
  -- IVT gives the critical points
  -- Among critical points, the maximum exists (by compactness + IVT again)
  sorry

/-- Reverse: if optimal angles are always findable, then LLPO -/
theorem angle_findable_implies_llpo :
    (∀ Q : QuantumCorrelation, maxCHSH Q > 2 →
      ∃ a a' b b', generalCHSH Q a a' b b' > 2) → LLPO := by
  -- Need: given a binary sequence with at most one 1,
  -- construct a quantum correlation whose angle-finding encodes the sequence
  sorry

/-- Calibration chain -/
theorem llpo_iff_bell_angle_finding :
    LLPO ↔ ∀ Q : QuantumCorrelation, maxCHSH Q > 2 →
      ∃ a a' b b', generalCHSH Q a a' b b' > 2 := by
  exact ⟨llpo_implies_angle_findable, angle_findable_implies_llpo⟩
```

---

## Phase 6: The Correspondence (`Correspondence.lean`)

### Parallel to P26

If both directions of the calibration work, we can state:

```lean
/-- The LLPO-Bell correspondence: the map from IVT instances
    to Bell angle-finding problems preserves the LLPO structure -/
theorem llpo_bell_correspondence :
    -- IVT instances with computable roots ↔ Bell problems with computable angles
    -- IVT instances with non-computable roots ↔ Bell problems with non-computable angles
    -- The LLPO principle decides both simultaneously
    LLPO ↔ ConstructiveIVT ∧ 
           (∀ Q : QuantumCorrelation, maxCHSH Q > 2 →
             ∃ a a' b b', generalCHSH Q a a' b b' > 2) := by
  sorry
```

### The Detection Theorem (Parallel to P26's Gap Detection)

```lean
/-- Detection: an IVT instance has a computable root iff the corresponding
    Bell angle is computable -/
-- This would be the analogue of "Φ([φ]) = 0 iff φ is refutable"
-- But the analogy is weaker here: "computable" is not as clean as "zero"
```

**Honest assessment**: The P26 correspondence had a clean binary signal: gap element is zero (refutable) or nonzero (consistent). The P27 analogue would need a clean binary signal for IVT instances: root is computable or not. But "computable" is not a decidable property — you can't in general tell whether a root is computable or not. This means the detection theorem may not have a clean P26 parallel.

---

## Risk Assessment and Fallback Positions

### Tier 1 (high confidence — should work):

1. **LLPO definition in Lean** — straightforward
2. **Bell correlation functions** — continuous, bounded, standard analysis
3. **Singlet CHSH violation** — trigonometric computation, similar to Paper 11
4. **Forward calibration: LLPO → angle findable** — via IVT
5. **IVT → LLPO direction** — established in literature, needs careful formalization

### Tier 2 (medium confidence — might work):

6. **LLPO → IVT direction** — encoding binary sequences into continuous functions is delicate
7. **Bell → IVT reduction for general states** — needs Horodecki criterion formalization
8. **Full calibration chain LLPO ↔ angle-finding** — depends on 6 + 7

### Tier 3 (speculative — might fail):

9. **Reverse encoding: IVT → Bell** — constructing quantum states from continuous functions
10. **Full correspondence with detection theorem** — requires clean binary signal
11. **Parallel structure to P26** — the Lindenbaum-algebra analogue may not exist cleanly

### Fallback Strategy

**If Tier 3 fails** (probable): The paper becomes "The Logical Cost of Bell Angle Optimization: An LLPO Calibration." It proves:
- LLPO ↔ IVT (formalized from literature)
- Bell angle optimization requires IVT (for general states)
- Therefore Bell angle optimization calibrates at LLPO

This is a one-directional calibration (angle-finding ≤ LLPO via IVT) plus the known IVT ↔ LLPO. It's not a correspondence in the P26 sense, but it's a genuine result that places Bell angle-finding at a specific point in the constructive hierarchy.

**If Tier 2 also fails**: The paper becomes even simpler: "IVT ↔ LLPO: A Lean 4 Formalization" with Bell angle optimization as a motivating application. Formalizing IVT ↔ LLPO in Lean would be a genuine contribution to the Lean/Mathlib library, independent of Bell.

**If even Tier 1's IVT proofs are too hard**: Axiomatize IVT ↔ LLPO and focus on the Bell connection only. Minimal but honest.

---

## Comparison: P26 vs P27

| Feature | P26 (Gödel-Gap) | P27 (LLPO-Bell) |
|---------|------------------|------------------|
| Logical algebra | Lindenbaum (Π⁰₁/∼_PA) | IVT instances (?) |
| Physical space | ℓ∞/c₀ | Bell correlations |
| Principle | WLPO | LLPO |
| Map | Φ: sentence → sequence | Ψ: IVT instance → angle problem |
| Detection | zero ↔ refutable | computable root ↔ computable angle |
| Binary signal | clean (0 vs ≠0) | unclear |
| Forward direction | proved | feasible |
| Reverse direction | proved | speculative |
| Literature support | WLPO ↔ Π⁰₁ known | IVT ↔ LLPO known |
| Overall confidence | HIGH | MEDIUM |

The table makes clear that P27 is a riskier project than P26. The mathematical infrastructure exists (IVT ↔ LLPO is known, Bell correlations are well-understood) but the *correspondence* structure — a clean embedding with a detection theorem — may not be achievable. The fallback (LLPO calibration of angle-finding) is still a good paper.

---

## Concrete Lean Implementation Plan

### Week 1: Foundations
- `Basic.lean`: LLPO, LLPO', their equivalence (~100 lines)
- `IVTInstances.lean`: IVT statement, continuous functions infrastructure (~150 lines)
- Begin `ivt_implies_llpo` proof — the encoding of sequences into continuous functions

### Week 2: IVT ↔ LLPO
- Complete `ivt_implies_llpo` and `llpo_implies_ivt` (or axiomatize if stuck)
- `BellCorrelation.lean`: CHSH, singlet correlation, continuity (~150 lines)

### Week 3: Bell Connection
- `AngleFinding.lean`: general angle optimization problem (~150 lines)
- `Calibration.lean`: forward direction LLPO → angle findable (~100 lines)
- Attempt reverse direction

### Week 4: Assembly
- `Correspondence.lean`: whatever level of correspondence was achieved
- `Main.lean`: aggregator, axiom audit
- Decision: full correspondence paper vs. calibration paper vs. IVT formalization paper

### Estimated total: 800-1200 lines across 7-8 modules

---

## Technical Warnings

1. **Derivatives in Lean/Mathlib**: Mathlib's `deriv` and `HasDerivAt` are well-developed but can be painful for composite functions. The gradient of CHSH involves derivatives of correlation functions, which are compositions of trig functions. Use `Differentiable.comp` and `HasDerivAt.comp` carefully.

2. **Piecewise linear functions**: The IVT → LLPO proof constructs piecewise linear functions from binary sequences. Lean's treatment of piecewise-defined functions requires careful case-splitting. Consider using `Set.piecewise` or `Function.piecewise` from Mathlib.

3. **Compactness**: The extreme value theorem (continuous function on compact set attains its supremum) is in Mathlib (`IsCompact.exists_isMaxOn`). Use this for the existence of optimal angles.

4. **Do NOT attempt to formalize Horodecki's criterion** unless absolutely necessary for the reverse encoding. It requires spectral decomposition of T^T · T for 3×3 real matrices, which is available in Mathlib but adds significant complexity.

5. **The "correspondence" language**: Be prepared to downgrade from "correspondence" to "calibration" if the reverse direction doesn't work. The paper title can be adjusted. An honest calibration result is better than a forced correspondence.

6. **Connection to P26**: In the conclusion, state explicitly how P27 relates to P26 — both are "logical algebra embeds into physical space" results calibrated at specific constructive principles. If P27 achieves full correspondence, state that the two papers provide the n=2 data point needed for a future categorical framework. If P27 achieves only calibration, state that the categorical question remains open.

---

## Success Criteria

**Full success**: LLPO ↔ Bell angle-finding equivalence proved in Lean, with IVT ↔ LLPO as intermediate step. Detection theorem or close analogue. Clean parallel to P26. 0 sorry in main chain.

**Good success**: LLPO ↔ IVT formalized in Lean. Bell angle-finding shown to require IVT (forward direction). LLPO calibration of angle-finding established. 0 sorry in IVT chain, ≤ 3 sorry in Bell connection.

**Acceptable success**: IVT ↔ LLPO axiomatized. Bell angle-finding → IVT reduction proved. One-directional calibration. Honest about limitations.

**Failure**: IVT ↔ LLPO encoding doesn't compile. In this case, document what broke — the information is valuable for understanding limits of formalizing constructive analysis in Lean 4.

## Deliverables

1. Clean Lean 4 build (0 errors)
2. IVT ↔ LLPO equivalence (proved or axiomatized with justification)
3. Bell angle-finding connection (at whatever level was achieved)
4. Calibration link to LLPO
5. Honest assessment of correspondence vs. calibration status
6. Documentation connecting P27 to P26 for future categorical work

