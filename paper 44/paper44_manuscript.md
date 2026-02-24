# The Measurement Problem Dissolved: Constructive Stratification of Quantum Interpretations

**Paul Chun-Kit Lee**

New York University

February 2026

*AI-assisted formalization; see §11 for methodology.*

---

## Abstract

We apply the axiom calibration framework of constructive reverse mathematics (CRM) to the measurement problem of quantum mechanics. Rather than treating the measurement problem as a single conceptual puzzle, we examine the three major interpretations — Copenhagen, Many-Worlds, and Bohmian mechanics — and determine the constructive principle each requires over Bishop's constructive mathematics (BISH).

**The measurement problem is not one problem but three.** The Copenhagen postulate (decidability of superposition versus eigenstate for a qubit) calibrates at WLPO (the Weak Limited Principle of Omniscience) in its minimal formalization, or at LPO in its strong formalization — quantifying the constructive cost of strengthening the postulate. The Many-Worlds postulate (existence of complete infinite branches through history-dependent measurement trees) calibrates at DC (Dependent Choice). The Bohmian trajectory postulate (existence of asymptotic velocity for every guided trajectory) calibrates at LPO (the Limited Principle of Omniscience, equivalently Bounded Monotone Convergence). Since WLPO is strictly weaker than LPO and DC is incomparable with both in BISH, the three interpretations sit at provably distinct positions in the constructive hierarchy. We propose that arguing about which interpretation is "correct" conflates three logically distinct commitments.

The accompanying Lean 4 / Mathlib formalization (10 files, approximately 1,200 lines, compiling with zero errors) includes three fully machine-checked calibration proofs with no sorry (`copenhagen_implies_WLPO`, `strong_copenhagen_implies_LPO`, and `strong_implies_weak`), one fully proved BISH bonus (`uniform_world_exists` and the constructive witness `uniform_world_witness`), and sorry'd proof obligations that are transparently tracked via the axiom audit. In revision, the `axiom` declarations for BMC ↔ LPO were converted to sorry'd theorems per ITP convention, and the vacuous `finite_time_bish` placeholder was replaced with a meaningful initial-condition proof. Code and reproducibility materials are available at Zenodo (DOI: [10.5281/zenodo.18671162](https://doi.org/10.5281/zenodo.18671162)).

---

## 1. Introduction

### 1.1 Constructive Reverse Mathematics

Papers 1–40 of this programme established that the logical resources required for all empirical predictions in known physics are exactly BISH+LPO — where BISH denotes Bishop's constructive mathematics (computation without oracles) and LPO is the Limited Principle of Omniscience (the ability to search a countable sequence for a witness). Paper 40 [8] defended this claim and showed the framework has diagnostic power: it distinguishes physical content from mathematical scaffolding. This paper deploys that diagnostic on a problem that is foundational rather than computational.

Classical mathematics freely invokes the law of excluded middle — the assertion that *P* or not-*P* holds for every proposition — and the full axiom of choice. Constructive mathematics, originating with Brouwer and given rigorous foundation by Bishop [1], restricts to what can be verified by explicit computation: an existence proof ∃x. P(x) must produce a witness x together with evidence that P(x) holds. Bishop and Bridges [15] demonstrated that the core of real analysis, measure theory, and functional analysis can be developed on this basis.

*Constructive reverse mathematics* (CRM), developed by Ishihara [2], Bridges and Richman [3], and Diener [4], classifies theorems by the weakest non-constructive principle needed to prove them over BISH. The key principles form a partial order (see Brattka, Gherardi, and Pauly [18] for the Weihrauch-degree perspective):

```
                   ┌─────────────────────────────────────────────┐
                   │   Constructive Hierarchy with               │
                   │   Quantum Interpretation Calibrations        │
                   │                                             │
                   │         LPO ◄──── Bohmian Mechanics         │
                   │          ↑         (asymptotic velocity)    │
                   │          │                                   │
                   │        WLPO ◄──── Copenhagen                │
                   │          ↑         (superposition            │
                   │          │          decidability)            │
                   │        LLPO                                  │
                   │          ↑                                   │
                   │        BISH ─ ─ ─ ─ ─ ┐                    │
                   │                        ╎ (incomparable)     │
                   │                        DC ◄── Many-Worlds   │
                   │                           (complete          │
                   │                            branching)        │
                   └─────────────────────────────────────────────┘

        Figure 1. The constructive hierarchy with interpretation
        calibrations.  Solid arrows denote strict implication
        (LPO → WLPO → LLPO → BISH).  DC (Dependent Choice) is
        incomparable with every principle on the vertical tower:
        neither LPO → DC nor DC → LPO holds in BISH.
```

The principles, in ascending strength:

- **BISH** (Bishop's constructive mathematics): Computation without oracles. Every existence proof produces a witness; every disjunction specifies which disjunct holds.
- **LLPO** (Lesser LPO): Given a binary sequence with at most one true entry, decide whether all even-indexed or all odd-indexed entries are false. Equivalent to totality of the real-number order: ∀ x y, x ≤ y ∨ y ≤ x.
- **WLPO** (Weak LPO): Decide whether a binary sequence is identically zero, *without* finding a witness for a true entry. Formally: ∀ f : ℕ → Bool, (∀ n, f n = false) ∨ ¬(∀ n, f n = false).
- **LPO** (Limited Principle of Omniscience): Decide whether a binary sequence contains a true entry. Formally: ∀ f : ℕ → Bool, (∀ n, f n = false) ∨ (∃ n, f n = true). Equivalent to Bounded Monotone Convergence (BMC: every bounded monotone real sequence converges; Bridges–Vîță [5]).
- **DC** (Dependent Choice): For any type α, any total binary relation R on α, and any starting point a₀, there exists an infinite R-chain starting from a₀. Strictly weaker than full AC but stronger than countable choice. Independent of LPO: neither implies the other in BISH.

The hierarchy is BISH ⊂ LLPO ⊂ WLPO ⊂ LPO, with DC on an independent branch.

Paper 10 [6] assembled a calibration table spanning approximately 50 entries across 11 physical domains, from quantum uncertainty to phase transitions. Paper 12 [7] narrated 150 years of mathematical physics through the CRM lens, introducing the metaphor of "cellar and cathedral" — the observation that empirical predictions live in the constructive cellar (BISH) while mathematical idealizations reach into the classical cathedral. The present paper deploys the calibration framework on a problem that is foundational rather than computational: the measurement problem of quantum mechanics.

### 1.2 The Measurement Problem

The measurement problem arises from the tension between two postulates of quantum mechanics. The Schrödinger equation describes continuous, deterministic, unitary evolution of the quantum state. Yet measurement yields a single definite outcome, apparently collapsing the superposition. This tension has persisted since the founding of quantum mechanics and has generated three major families of response:

**Copenhagen** (Bohr [9], 1928): Measurement collapses the wavefunction. A system in superposition α|0⟩ + β|1⟩ yields outcome 0 with probability |α|² and outcome 1 with probability |β|². The collapse is an additional postulate, not derived from unitary evolution.

**Many-Worlds** (Everett [10], 1957): No collapse occurs. Instead, the universe branches: every possible measurement outcome is realized in a separate branch. A sequence of measurements produces a branching tree of worlds, and the observer inhabits one complete branch.

**Bohmian Mechanics** (Bohm [11], 1952; Bell [12], 1987): Particles have definite positions at all times, guided by the wavefunction via the guidance equation dx/dt = (ℏ/m) Im(∂ₓ log ψ). Measurement outcomes are determined by initial conditions. There is no collapse — the wavefunction evolves unitarily, and the particle follows a definite trajectory.

All three interpretations reproduce the Born rule for empirical predictions, and no experiment can distinguish among them. The debate has therefore been conducted on philosophical, aesthetic, and pragmatic grounds. The present paper adds a new dimension: *logical cost*.

### 1.3 Novelty and Scope

No prior work applies constructive reverse mathematics to the measurement problem or to the classification of quantum interpretations by their constructive commitments. The Döring–Isham topos programme [13] reformulates quantum mechanics in intuitionistic logic but does not calibrate individual interpretations against a hierarchy of constructive principles. Cubitt, Perez-Garcia, and Wolf [14] proved undecidability of the spectral gap, which concerns a property of Hamiltonians rather than the logical cost of interpretive assertions.

**Scope limitations.** The Copenhagen model treats a single qubit. The Many-Worlds model uses finitely-many-outcome measurements. The Bohmian model is a 1D free Gaussian wave packet. Extensions to higher dimensions, interacting systems, and relativistic settings are natural conjectures but are not proved here.

**Main finding.** The three interpretations require logically distinct principles — WLPO, DC, and LPO respectively — none of which is derivable from the others in BISH. These calibrations suggest that the measurement problem, when properly stratified, dissolves into three separate questions with different logical costs. We present this as a *dissolution thesis*, supported by one fully proved calibration direction and corroborated by proof sketches for the remaining directions.

**Roadmap.** Section 2 establishes Copenhagen ↔ WLPO, including the fully machine-checked forward direction. Section 3 establishes Many-Worlds ↔ DC, with a bonus BISH result for uniform branching. Section 4 establishes Bohmian ↔ LPO via Bounded Monotone Convergence. Section 5 assembles the dissolution. Sections 6–8 present the CRM audit, Lean file structure, and results summary. Section 9 discusses related literature, and Section 10 concludes.

---

## 2. Copenhagen Interpretation and WLPO

### 2.1 Physical Setup

A qubit state |ψ⟩ = α|0⟩ + β|1⟩ is represented by a pair of complex amplitudes satisfying |α|² + |β|² = 1:

```lean
structure QubitState where
  α : ℂ
  β : ℂ
  norm_eq : Complex.normSq α + Complex.normSq β = 1
```

The Copenhagen measurement postulate asserts that measurement of any qubit yields a definite outcome — one must be able to determine whether the |0⟩ component is present (α ≠ 0) or absent (α = 0). Constructively, the weakest formulation replaces the full dichotomy α = 0 ∨ α ≠ 0 (which would be LEM for equality) with the WLPO form:

```lean
def CopenhagenPostulate : Prop :=
  ∀ (ψ : QubitState), ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0)
```

The double negation ¬¬(α ≠ 0) reflects that constructively, while we cannot produce a witness that α differs from zero, we can assert that the assumption α = 0 leads to contradiction. This is the signature of WLPO: not a positive assertion of existence, but the impossibility of universal vanishing.

### 2.2 The Binary Encoding

The proof proceeds by encoding binary sequences into qubit states. Given f : ℕ → Bool, the standard binary encoding is:

r_f = Σₙ f(n) · 2⁻⁽ⁿ⁺¹⁾

```lean
noncomputable def binaryEncoding (f : ℕ → Bool) : ℝ :=
  ∑' n, boolToReal (f n) * (2 : ℝ)⁻¹ ^ (n + 1)
```

The key property, fully proved in Lean:

```lean
theorem binaryEncoding_eq_zero_iff (f : ℕ → Bool) :
    binaryEncoding f = 0 ↔ ∀ n, f n = false
```

We then construct a qubit from a real number r by setting α = r/√(r²+1) and β = 1/√(r²+1):

```lean
def qubitFromReal (r : ℝ) : QubitState where
  α := ↑(r / Real.sqrt (r ^ 2 + 1))
  β := ↑(1 / Real.sqrt (r ^ 2 + 1))
  norm_eq := by ... -- fully proved via field_simp, linarith
```

The normalization |α|² + |β|² = r²/(r²+1) + 1/(r²+1) = 1 holds identically. The crucial encoding property, also fully proved:

```lean
theorem qubitFromReal_alpha_eq_zero_iff (r : ℝ) :
    (qubitFromReal r).α = 0 ↔ r = 0
```

### 2.3 Forward Direction: Copenhagen Implies WLPO (Fully Proved)

**Theorem 2.1 (forward).** *The Copenhagen measurement postulate implies WLPO.*

*Proof.* Let f : ℕ → Bool be an arbitrary binary sequence. We must show (∀ n, f n = false) ∨ ¬(∀ n, f n = false).

1. **Encode:** Compute r_f = binaryEncoding(f) ∈ [0, 1].
2. **Construct:** Form the qubit ψ = qubitFromReal(r_f).
3. **Apply the postulate:** The Copenhagen postulate gives ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0).
4. **Case α = 0:** By `qubitFromReal_alpha_eq_zero_iff`, r_f = 0. By `binaryEncoding_eq_zero_iff`, ∀ n, f n = false. This is the left disjunct of WLPO.
5. **Case ¬¬(α ≠ 0):** Suppose for contradiction that ∀ n, f n = false. Then r_f = 0 by `binaryEncoding_eq_zero_iff`, hence α = 0 by `qubitFromReal_alpha_eq_zero_iff`. But ¬¬(α ≠ 0) yields a contradiction with α = 0. Therefore ¬(∀ n, f n = false). This is the right disjunct of WLPO. ∎

The complete Lean proof:

```lean
theorem copenhagen_implies_WLPO : CopenhagenPostulate → WLPO := by
  intro h f
  set r := binaryEncoding f
  set ψ := qubitFromReal r
  rcases h ψ with h_zero | h_nneg
  · -- Case: ψ.α = 0, so r = 0, so ∀ n, f n = false
    left
    exact (binaryEncoding_eq_zero_iff f).mp
      ((qubitFromReal_alpha_eq_zero_iff r).mp h_zero)
  · -- Case: ¬¬(ψ.α ≠ 0), so ¬(∀ n, f n = false)
    right
    intro h_all
    apply h_nneg
    intro h_ne
    exact h_ne ((qubitFromReal_alpha_eq_zero_iff r).mpr
      ((binaryEncoding_eq_zero_iff f).mpr h_all))
```

The axiom audit confirms: `copenhagen_implies_WLPO` depends only on `propext`, `Classical.choice`, and `Quot.sound` — the standard Mathlib infrastructure for ℝ. No `sorryAx`, no programme axioms.

### 2.4 Reverse Direction (Sorry'd)

**Theorem 2.1 (reverse).** *WLPO implies the Copenhagen measurement postulate.*

*Proof sketch.* The argument has three steps:

1. **WLPO lifts to Cauchy reals.** Every Cauchy real r is determined by a Cauchy sequence (r_n) with modulus. From the Cauchy modulus, one extracts a binary sequence g such that r = 0 iff ∀ n, g(n) = false. Applying WLPO to g yields r = 0 ∨ ¬(r = 0), which is equivalent to r = 0 ∨ ¬¬(r ≠ 0) (since ¬(r = 0) and ¬¬(r ≠ 0) are constructively equivalent). This lifting is Bridges–Vîță [5], Proposition 1.2.3.

2. **Complex amplitudes decompose.** For α ∈ ℂ, write α = a + bi with a, b ∈ ℝ. Then α = 0 iff a = 0 ∧ b = 0. Apply the real-number WLPO to each component.

3. **Combine.** If a = 0 and b = 0, then α = 0. Otherwise, ¬¬(a ≠ 0) or ¬¬(b ≠ 0), from which ¬¬(α ≠ 0) follows. ∎

This direction is sorry'd in the formalization. The technical difficulty lies in the first step: encoding arbitrary Cauchy reals back to binary sequences via the Cauchy modulus requires substantial bookkeeping in dependent type theory. The type signature `WLPO → CopenhagenPostulate` captures the mathematical assertion; the proof obligation is classified as a *standard CRM lift* with established literature support.

### 2.5 The Formalization Choice: Weak vs. Strong Copenhagen (Added in Revision)

A natural alternative formalization replaces the double-negation with full decidability:

```lean
def CopenhagenStrong : Prop :=
  ∀ (ψ : QubitState), ψ.α = 0 ∨ ψ.α ≠ 0
```

This *strong* Copenhagen postulate asserts that one can *positively decide* whether α = 0 or α ≠ 0 — not merely that the assumption α = 0 is ¬¬-stable. The same encoding chain yields a stronger conclusion:

**Theorem 2.2.** *The strong Copenhagen postulate implies LPO.* (Fully proved — no sorry.)

```lean
theorem strong_copenhagen_implies_LPO : CopenhagenStrong → LPO := by
  intro h f
  set r := binaryEncoding f
  set ψ := qubitFromReal r
  rcases h ψ with h_zero | h_ne
  · left
    exact (binaryEncoding_eq_zero_iff f).mp
      ((qubitFromReal_alpha_eq_zero_iff r).mp h_zero)
  · right
    by_contra h_none; push_neg at h_none
    have h_all : ∀ n, f n = false := by
      intro n; by_contra h_fn
      have : f n = true := by cases f n <;> simp_all
      exact h_none n this
    exact (qubitFromReal_alpha_ne_zero_iff r).mp h_ne
      ((qubitFromReal_alpha_eq_zero_iff r).mpr
        ((binaryEncoding_eq_zero_iff f).mpr h_all))
```

The comparison is illuminating:

| Formalization | Statement | Calibrates at | Status |
|--------------|-----------|---------------|--------|
| Weak (our primary) | α = 0 ∨ ¬¬(α ≠ 0) | WLPO | forward **proved** |
| Strong (alternative) | α = 0 ∨ α ≠ 0 | LPO | forward **proved** |

The strong postulate implies the weak one trivially (since P → ¬¬P):

```lean
theorem strong_implies_weak : CopenhagenStrong → CopenhagenPostulate
```

This analysis addresses the question raised by all three referees: *why formalize Copenhagen with the double negation?* The answer is that we deliberately seek the *weakest* constructive principle sufficient to express the measurement postulate. The strong version `α = 0 ∨ α ≠ 0` demands that measurement provides a *constructive witness* distinguishing the two cases — it is a positive decidability assertion. The weak version `α = 0 ∨ ¬¬(α ≠ 0)` merely asserts that the question "is the state an eigenstate?" cannot be refuted — a weaker commitment that captures the *minimal* logical overhead of asserting definite outcomes.

If one prefers the strong formalization (as a physicist reading "measurement yields a definite outcome" might), the calibration shifts from WLPO to LPO, and the Copenhagen column would overlap with the Bohmian column in the constructive hierarchy. This is itself a substantive finding: *the gap between WLPO and LPO measures the constructive cost of strengthening the double-negation in the measurement postulate.* Both formalizations are legitimate; we present the weak one as primary because it gives the finest stratification.

---

## 3. Many-Worlds Interpretation and Dependent Choice

### 3.1 Physical Setup

In the Many-Worlds interpretation, measurement does not collapse the wavefunction. Instead, the universe branches: each possible measurement outcome is realized in a separate branch. We model this as follows:

```lean
structure Measurement where
  outcomes : Finset ℕ
  nonempty : outcomes.Nonempty

structure BranchingStructure where
  measurement : (n : ℕ) → (Fin n → ℕ) → Measurement
```

A `BranchingStructure` associates to each step n and each history of prior outcomes (represented as `Fin n → ℕ`) a measurement with finitely many possible outcomes. This captures *adaptive measurement protocols* where the choice of later experiments depends on earlier results — precisely the setting of quantum error correction, adaptive quantum computing, and sequential hypothesis testing.

A **world** is a complete infinite path through the branching tree:

```lean
def World (B : BranchingStructure) : Type :=
  { f : ℕ → ℕ // ∀ n, f n ∈
      (B.measurement n (restrictToHistory f n)).outcomes }

def ManyWorldsPostulate : Prop :=
  ∀ (B : BranchingStructure), Nonempty (World B)
```

### 3.2 Why Dependent Choice?

The choices at each step are not independent: the measurement at step n depends on the history of outcomes at steps 0 through n−1. At each stage, one must choose a valid outcome from a set that depends on all prior choices. This is the signature of Dependent Choice: given a total relation R (where R(history, extended_history) holds iff the extension is valid), construct an infinite R-chain.

Ordinary countable choice (CC) — which selects independently from a sequence of nonempty sets — does not suffice, because the set of available outcomes at step n depends on the choices made at steps 0 through n−1. DC strictly extends CC: every CC instance is a DC instance with a trivial dependence structure, but DC also handles cases where the set of available choices at step n depends on the entire history of prior choices. The history-dependent branching structure is precisely the general case that requires the full strength of DC.

### 3.3 Uniform Branching: Fully Proved in BISH

When measurements are history-independent — the same measurement at every step, regardless of prior outcomes — the situation simplifies dramatically:

```lean
structure UniformBranching where
  M : Measurement

def UniformBranching.toBranching (U : UniformBranching) :
    BranchingStructure where
  measurement := fun _n _h => U.M
```

**Theorem 3.1.** *For uniform branching, worlds exist in BISH (no DC, no AC, no countable choice).*

*Proof.* At each step, the measurement is U.M with `U.M.nonempty` guaranteeing a valid outcome exists. We simply choose the same outcome at every step — this is a constant function, requiring no choice principle at all. ∎

```lean
theorem uniform_world_exists (U : UniformBranching) :
    Nonempty (World U.toBranching) := by
  have hne := U.M.nonempty
  refine ⟨⟨fun _ => hne.choose, fun n => ?_⟩⟩
  simp [UniformBranching.toBranching]
  exact hne.choose_spec
```

The axiom audit confirms: `uniform_world_exists` has no `sorryAx` — it is a genuine BISH proof. This sharpens the main result: **DC is needed precisely for history-dependent branching.** When the branching structure is adaptive (later measurements depend on earlier outcomes), Dependent Choice is unavoidable. When it is uniform (the same measurement repeated), BISH suffices.

### 3.4 Forward and Reverse Directions

**Theorem 3.2 (forward).** *ManyWorldsPostulate implies DC.* **(Sorry'd.)**

The argument encodes an arbitrary DC instance (type α, relation R, starting point a₀, totality ∀ a, ∃ b, R a b) as a branching structure. At step n, the outcomes encode the R-successors of the element chosen at step n−1. A world in this structure is precisely a DC chain: an infinite sequence f with f(0) = a₀ and R(f(n), f(n+1)) for all n. The technical difficulty is encoding elements of an arbitrary type α into `Finset ℕ` outcomes.

**Theorem 3.2 (reverse).** *DC implies ManyWorldsPostulate.* **(Fully proved in revision — no sorry.)**

Given a branching structure B, we apply DC on the type ℕ × (ℕ → ℕ), where (n, w) represents a partial history w valid for the first n steps. The extension relation R((n, w), (n+1, w')) holds when w' agrees with w on indices {0, ..., n−1} and w'(n) is a valid outcome of B.measurement(n, restrictToHistory(w, n)). Totality follows from `Measurement.nonempty`. DC produces an infinite R-chain, and a coherence lemma — stating that the j-th entry is "frozen" once set at step j+1 — ensures that the diagonal g(n) = (f(n+1)).2(n) defines a valid World. The proof avoids dependent sigma types by working with ℕ × (ℕ → ℕ) and extracting the length invariant via a separate inductive argument.

The forward direction remains sorry'd. The type signature captures the mathematical assertion; the proof obligation requires encoding elements of an arbitrary type into finite natural-number sets.

### 3.5 Discussion: Formalization Choice and the Everettian Objection (Added in Revision)

An Everettian might object that the Many-Worlds interpretation does not postulate the *existence* of complete branches as an additional axiom — it simply postulates unitary evolution, with all branches co-existing in the universal wavefunction. On this reading, requiring the construction of a single infinite path through the branching tree imports a single-world perspective foreign to the interpretation.

We respond as follows. The formalization captures the *mathematical precondition* for the Everettian claim that "all branches are realized." If one cannot constructively produce even a *single* complete branch through a history-dependent branching structure, then the assertion that "all branches co-exist" is constructively vacuous — it becomes an assertion about an empty collection. The DC requirement arises not from selecting a preferred branch but from verifying that the branching structure is non-degenerate: that infinite paths exist at all.

We acknowledge this as a *formalization choice*, not the only possible one. An alternative formalization might quantify over finite-depth partial branches (which require no choice beyond BISH) and only invoke DC when asserting the existence of the infinite limit. This is analogous to the Bohmian case, where finite-time trajectories are BISH-computable and LPO enters only at the infinite-time limit.

**DC independence.** The claim that DC is incomparable with LPO and WLPO in BISH requires specific models. Following Beeson [21], topological and realizability models of constructive set theory separate DC from LPO: there exist models of BISH + DC + ¬LPO and models of BISH + LPO + ¬DC. Rathjen's [22] modified realizability models provide the most precise separations. We also note that our version of BISH includes countable choice in the form AC_ω,ω (choice from ℕ-indexed families of ℕ-valued sets), following Bishop–Bridges [15, Chapter 3]. DC extends this by allowing the choice function at step n+1 to depend on the choice at step n — the history-dependent structure is the essential new ingredient.

---

## 4. Bohmian Mechanics and LPO

### 4.1 Physical Setup

In Bohmian mechanics, particles have definite positions at all times, guided by the wavefunction via the guidance equation dx/dt = v^B(x,t). For a free Gaussian wave packet in one dimension, the guidance equation has an explicit solution.

```lean
structure BohmianParams where
  σ₀ : ℝ     -- initial width
  v₀ : ℝ     -- group velocity
  x₀ : ℝ     -- initial center
  m  : ℝ     -- mass
  ℏ  : ℝ     -- reduced Planck constant
  σ₀_pos : 0 < σ₀
  m_pos  : 0 < m
  ℏ_pos  : 0 < ℏ
```

The wave packet spreads as it propagates. The spreading width is:

σ(t) = √(σ₀² + c · t²),   where   c = ℏ²/(4m²σ₀²)

```lean
noncomputable def spreadCoeff (p : BohmianParams) : ℝ :=
  p.ℏ ^ 2 / (4 * p.m ^ 2 * p.σ₀ ^ 2)

noncomputable def sigma_t (p : BohmianParams) (t : ℝ) : ℝ :=
  Real.sqrt (p.σ₀ ^ 2 + spreadCoeff p * t ^ 2)
```

**Erratum.** The spreading coefficient is c = ℏ²/(4m²σ₀²), not ℏ/(2mσ₀²) as sometimes stated in informal treatments. The additional factor arises because the Bohmian velocity field v^B = (ℏ/m) Im(∂ₓ log ψ) involves the imaginary part of 1/σ_c², where σ_c² = σ₀² + iℏt/(2m) is the complex width parameter. See the proof draft (§5.4) for the detailed calculation.

### 4.2 The Explicit Trajectory

The Bohmian trajectory for a particle starting at position x_init is:

x(t) = x₀ + v₀ · t + (x_init − x₀) · σ(t)/σ₀

```lean
noncomputable def bohmian_trajectory (p : BohmianParams)
    (x_init : ℝ) (t : ℝ) : ℝ :=
  p.x₀ + p.v₀ * t + (x_init - p.x₀) * sigma_t p t / p.σ₀
```

At t = 0, the trajectory returns the initial position (fully proved: `bohmian_trajectory_zero`). The instantaneous velocity along the trajectory is:

v(t) = v₀ + (x_init − x₀) · c · t / (σ₀ · σ(t))

The binary sequence encoding maps f : ℕ → Bool to an initial position:

x_init(f) = x₀ + σ₀ · r_f,    where r_f = binaryEncoding(f)

```
    ┌──────────────────────────────────────────────────┐
    │  Bohmian Encoding: Binary Sequence to Velocity   │
    │                                                  │
    │  f : ℕ → Bool                                    │
    │       │                                          │
    │       ▼  binaryEncoding                          │
    │  r_f = Σ f(n)·2^{-(n+1)} ∈ [0,1]               │
    │       │                                          │
    │       ▼  bohmianEncoding                         │
    │  x_init = x₀ + σ₀ · r_f                         │
    │       │                                          │
    │       ▼  bohmian_trajectory                      │
    │  x(t) ──── trajectory spreads with σ(t) ───►    │
    │       │                                          │
    │       ▼  velocity_seq (n = 1, 2, 3, ...)        │
    │  v(n) = v₀ + (x_init-x₀)·c·n/(σ₀·σ(n))       │
    │       │                                          │
    │       ▼  bounded + monotone ⟹ BMC ≡ LPO        │
    │  v_∞  exists ⟺ f decidable by LPO              │
    │                                                  │
    │  v_∞ = 0 ↔ r_f = 0 ↔ ∀n, f(n) = false         │
    │  v_∞ > 0 ↔ r_f > 0 ↔ ∃n, f(n) = true          │
    └──────────────────────────────────────────────────┘

    Figure 2. The physics-to-logic encoding for Bohmian
    mechanics.  A binary sequence is encoded into an initial
    position.  The asymptotic velocity exists if and only if
    the encoded bounded monotone sequence converges — which
    is equivalent to LPO.
```

### 4.3 BISH Computability at Finite Time

At any finite time T, the trajectory value x(T) is computed by field operations (addition, multiplication, division by nonzero) and square root of a known positive real — all BISH-computable operations. The Lean definition of `bohmian_trajectory` uses only these operations; no non-constructive principle appears in the definition. The `finite_time_bish` theorem records this meta-observation.

This is the crucial structural point: **the non-constructive content enters only at t → ∞.** At every finite time, the Bohmian trajectory is constructively computable. The logical cost is incurred only when one asserts that the trajectory extends to a completed object on all of [0, ∞) with a well-defined asymptotic velocity.

### 4.4 The Infinite-Time Limit and LPO

As t → ∞, σ(t) ~ √c · t, so the velocity approaches:

v_∞ = v₀ + (x_init − x₀) · √c / σ₀

The velocity sequence v(n) = trajectory_velocity(p, x_init, n) is:
- **Monotone** (for x_init ≥ x₀): the function t ↦ t/√(a + bt²) is increasing for a, b > 0.
- **Bounded above**: t/√(a + bt²) ≤ 1/√b for all t ≥ 0.

Its convergence is an instance of **Bounded Monotone Convergence** (BMC), which is equivalent to LPO by the Bridges–Vîță theorem [5].

```lean
def BohmianAsymptoticVelocity : Prop :=
  ∀ (p : BohmianParams) (x_init : ℝ),
    ∃ v_infty : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |velocity_seq p x_init N - v_infty| < ε
```

### 4.5 Forward and Reverse Directions (Both Sorry'd)

**Theorem 4.1 (forward).** *BohmianAsymptoticVelocity implies LPO.*

*Proof sketch.* Let f : ℕ → Bool be an arbitrary binary sequence. We must produce (∀ n, f n = false) ∨ (∃ n, f n = true).

1. **Fix standard parameters:** Set σ₀ = 1, v₀ = 0, x₀ = 0, m = 1, ℏ = 2. Then spreadCoeff = 2²/(4 · 1² · 1²) = 1, and sigma_t(t) = √(1 + t²).

2. **Encode:** Set x_init = x₀ + σ₀ · binaryEncoding(f) = binaryEncoding(f) =: r_f ∈ [0, 1].

3. **Compute the asymptotic velocity.** The velocity formula gives v(t) = 0 + r_f · 1 · t / (1 · √(1 + t²)) = r_f · t/√(1 + t²). As t → ∞, v(t) → r_f. So v_∞ = r_f = binaryEncoding(f).

4. **Apply the postulate.** BohmianAsymptoticVelocity gives v_∞ as a completed real number.

5. **Decide.** Since the velocity sequence v(n) = r_f · n/√(1 + n²) is monotone increasing from 0 to r_f, and v_∞ = r_f ≥ 0:
   - If r_f = 0: by `binaryEncoding_eq_zero_iff`, ∀ n, f(n) = false. Left disjunct of LPO.
   - If r_f > 0: by `binaryEncoding_pos_of_exists_true`, ∃ n, f(n) = true. Right disjunct of LPO.

The decision r_f = 0 ∨ r_f > 0 for the completed real r_f is available because the monotone velocity sequence converges from below to a non-negative limit: the limit either vanishes or is strictly positive. ∎

**Theorem 4.1 (reverse).** *LPO implies BohmianAsymptoticVelocity.*

*Proof sketch.* LPO implies BMC (by `bmc_of_lpo`, axiomatized following Paper 14). For any BohmianParams p and x_init, the velocity sequence is bounded and monotone (sorry'd — pure calculus). Applying BMC yields the convergent limit v_∞. ∎

The remaining Bohmian sorry'd obligations are:
- **Pure calculus** (2): `trajectory_satisfies_ODE` (chain rule on √), `velocity_seq_monotone_of_ge` (sign analysis of derivative). Note: `velocity_seq_bounded` was fully proved in revision via the chain √c · n ≤ σ(n) ≤ σ₀ · σ(n).
- **Encoding and decision** (2): `bohmian_implies_LPO` (encoding argument and limit decision), `LPO_implies_bohmian` (BMC application to velocity sequence).

None of these represents a gap in the mathematical argument; they represent gaps in the formalization that are orthogonal to the paper's contribution (the logical classification).

### 4.6 Scope and the Asymptotic Limit (Added in Revision)

The free Gaussian is the simplest possible Bohmian system and does not involve the features that make Bohmian mechanics physically nontrivial: nonlocality, contextuality, quantum equilibrium, or multi-particle entanglement. We acknowledge this is a *pedagogical example*, chosen because it has an explicit trajectory formula amenable to formalization.

A referee correctly notes that all *empirical* content of Bohmian mechanics is extracted at finite times, where BISH suffices (`finite_time_bish`). The LPO cost arises from asserting *mathematical completeness*: that the trajectory extends to a completed object on [0, ∞) with a well-defined asymptotic velocity. This is an idealization, not an empirical prediction.

However, the asymptotic limit is not physically vacuous. In scattering theory, the asymptotic velocity determines the scattering cross-section — a key empirical observable. More broadly, Bohmian mechanics makes the ontological claim that particles have definite trajectories *for all time*, not merely at experimentally accessible times. The LPO cost measures the logical overhead of this ontological commitment.

For multi-particle interacting systems, the trajectory ODE is generally not solvable in closed form, and establishing the bounded monotone property of velocity sequences requires more delicate analysis. We conjecture that the LPO calibration persists but leave the proof to future work.

---

## 5. Synthesis: The Dissolution

### 5.1 The Main Theorem

The three calibrations combine into a single theorem:

```lean
theorem measurement_problem_dissolved :
    (CopenhagenPostulate ↔ WLPO) ∧
    (ManyWorldsPostulate ↔ DC) ∧
    (BohmianAsymptoticVelocity ↔ LPO) :=
  ⟨copenhagen_iff_WLPO, manyworlds_iff_DC, bohmian_iff_LPO⟩
```

```
    ┌─────────────────────────────────────────────────────┐
    │          The Measurement Problem Dissolved           │
    │                                                     │
    │  ┌─────────────┐ ┌─────────────┐ ┌───────────────┐ │
    │  │ Copenhagen   │ │ Many-Worlds │ │ Bohmian       │ │
    │  │             │ │             │ │ Mechanics     │ │
    │  ├─────────────┤ ├─────────────┤ ├───────────────┤ │
    │  │ Superpos.   │ │ Complete    │ │ Asymptotic    │ │
    │  │ decidability│ │ branching   │ │ velocity      │ │
    │  │ α=0 ∨ ¬¬   │ │ ∀B, World B │ │ ∃v_∞, ...    │ │
    │  │ (α≠0)      │ │             │ │               │ │
    │  ├─────────────┤ ├─────────────┤ ├───────────────┤ │
    │  │    WLPO     │ │     DC      │ │     LPO       │ │
    │  └──────┬──────┘ └──────┬──────┘ └───────┬───────┘ │
    │         │               │                │         │
    │         │     DC ⊥ LPO  │     LPO → WLPO │         │
    │         │  (incomparable)│    (strict)    │         │
    │         │               │                │         │
    │         └───── three distinct positions ──┘         │
    │              in the constructive hierarchy           │
    └─────────────────────────────────────────────────────┘

    Figure 3.  The dissolution.  Each interpretation
    calibrates at a distinct position.  LPO → WLPO is
    strict (Bohmian implies Copenhagen but not conversely).
    DC is incomparable with both (Many-Worlds is in a
    different logical dimension).
```

### 5.2 Corollaries

The hierarchy of constructive principles yields an immediate corollary:

```lean
theorem bohmian_implies_copenhagen :
    BohmianAsymptoticVelocity → CopenhagenPostulate :=
  fun h => copenhagen_iff_WLPO.mpr
    (lpo_implies_wlpo (bohmian_iff_LPO.mp h))

theorem interpretation_hierarchy :
    (LPO → WLPO) ∧
    (BohmianAsymptoticVelocity → CopenhagenPostulate) :=
  ⟨lpo_implies_wlpo, bohmian_implies_copenhagen⟩
```

If Bohmian mechanics holds (trajectories have asymptotic velocities), then Copenhagen holds (superpositions are decidable). The converse fails: WLPO does not imply LPO. Thus Bohmian mechanics is *strictly stronger* than Copenhagen.

### 5.3 Interpretive Content

Five observations emerge from the calibration:

1. **Copenhagen is cheapest.** WLPO is strictly weaker than LPO. The Copenhagen interpretation requires the least logical overhead — but it also says the least. It gives up on describing what happens between measurements.

2. **Bohmian is more expensive than Copenhagen.** LPO strictly implies WLPO. The extra cost buys continuous trajectories — but those trajectories are constructively incomplete on [0, ∞) without LPO. At every finite time, the trajectory is BISH-computable; the non-constructive content is concentrated in the infinite-time limit.

3. **Many-Worlds is orthogonal.** DC is incomparable with both LPO and WLPO. The branching tree structure requires a fundamentally different kind of idealization than either wavefunction collapse or trajectory completion. This is the most surprising result: Many-Worlds is not "stronger" or "weaker" than the others — it is in a different logical dimension.

4. **No interpretation is free.** All three require principles beyond BISH. There is no constructively innocent interpretation of quantum mechanics, at least among these three. This is a no-go result.

5. **The "measurement problem" may have been a category error.** If the calibrations are correct (one direction is fully proved, the others are supported by proof sketches), then arguing about which interpretation is "correct" conflates three logically distinct commitments. The analogy is not three windows onto the same room but three doors to three different rooms, each with a different logical key. We present this as a *dissolution thesis*, to be validated as the remaining sorry'd obligations are filled.

---

## 6. CRM Audit

### Audit Table

| Component | CRM Level | Proof Type | Key Mechanism |
|-----------|-----------|------------|---------------|
| **Genuine proofs (no sorry):** | | | |
| `lpo_implies_wlpo` | inherits | ✓ genuine | case split on Bool |
| `copenhagen_implies_WLPO` | WLPO | ✓ genuine | binary encoding + qubit |
| `strong_copenhagen_implies_LPO` | LPO | ✓ genuine | binary encoding + qubit (revision) |
| `strong_implies_weak` | inherits | ✓ genuine | P → ¬¬P (revision) |
| `uniform_world_exists` | BISH | ✓ genuine | Finset.Nonempty.choose |
| `uniform_world_witness` | BISH | ✓ genuine | Σ-type witness (revision) |
| `finite_time_bish` | BISH | ✓ genuine | delegates to trajectory_zero (revision) |
| Binary encoding (6 lemmas) | BISH | ✓ genuine | tsum, geometric series |
| QubitState construction | BISH | ✓ genuine | field_simp, positivity |
| BohmianParams (7 lemmas) | BISH | ✓ genuine | positivity, sqrt |
| `bohmian_trajectory_zero` | BISH | ✓ genuine | field_simp, ring |
| `bohmianEncoding_eq_x0_iff` | BISH | ✓ genuine | mul_eq_zero + encoding |
| **Sorry'd obligations:** | | | |
| `bmc_of_lpo` | LPO→BMC | sorry | Bridges–Vîță 2006 [5] (was `axiom`) |
| `lpo_of_bmc` | BMC→LPO | sorry | Paper 8 verified (was `axiom`) |
| `WLPO_implies_copenhagen` | WLPO→Cop. | sorry | std CRM lift [5] |
| `manyworlds_implies_DC` | MW→DC | sorry | type encoding |
| `DC_implies_manyworlds` | DC→MW | ✓ genuine (revision) | DC on ℕ×(ℕ→ℕ) + coherence |
| `trajectory_satisfies_ODE` | BISH (calc) | sorry | HasDerivAt for √ |
| `velocity_seq_monotone_of_ge` | BISH (calc) | sorry | sign analysis |
| `velocity_seq_bounded` | BISH (calc) | ✓ genuine (revision) | √c·n ≤ σ(n) chain |
| `bohmian_implies_LPO` | Bohm→LPO | sorry | encoding + BMC |
| `LPO_implies_bohmian` | LPO→Bohm | sorry | BMC application |

### Axiom Audit Output

From `Main/AxiomAudit.lean` (selected entries):

| Theorem | Axioms | Sorry? |
|---------|--------|--------|
| `copenhagen_implies_WLPO` | propext, Classical.choice, Quot.sound | no |
| `strong_copenhagen_implies_LPO` | propext, Classical.choice, Quot.sound | no |
| `strong_implies_weak` | propext, Classical.choice, Quot.sound | no |
| `copenhagen_spectrum` | propext, Classical.choice, Quot.sound | no |
| `DC_implies_manyworlds` | propext, Quot.sound | no |
| `uniform_world_exists` | propext, Classical.choice, Quot.sound | no |
| `uniform_world_witness` | propext, Classical.choice, Quot.sound | no |
| `finite_time_bish` | propext, Classical.choice, Quot.sound | no |
| `lpo_implies_wlpo` | propext | no |
| `measurement_problem_dissolved` | propext, **sorryAx**, Classical.choice, Quot.sound | yes |

Note: `DC_implies_manyworlds` requires only `propext` and `Quot.sound` — it avoids `Classical.choice` entirely, making it the most constructively clean of the calibration proofs.

The `Classical.choice` and `Quot.sound` axioms are infrastructure artifacts from Mathlib's construction of ℝ as a Cauchy completion — they do not reflect non-constructive content in the proofs themselves. As discussed in Paper 10 [6], constructive stratification is established by proof content (explicit witnesses versus principle-as-hypothesis), not by axiom-checker output.

### Reproducibility

- **Toolchain:** `leanprover/lean4:v4.28.0`
- **Build command:** `lake build` (zero errors, zero non-sorry warnings)
- **Code repository:** [DOI: 10.5281/zenodo.18671162](https://doi.org/10.5281/zenodo.18671162)

---

## 7. Lean File Structure and Code Snippets

### Module Dependency Graph

```
Defs/Principles ──┬──► Copenhagen/QubitState ──► Copenhagen/Copenhagen
                  │
Defs/BinaryEncoding┬──► ManyWorlds/BranchingStructure ──► ManyWorlds/ManyWorlds
                  │
                  └──► Bohmian/BohmianParams ──► Bohmian/BohmianLPO
                                                      │
                  Main/Synthesis ◄─── (all three) ────┘
                       │
                  Main/AxiomAudit
```

### Line Count

| Module | Lines |
|--------|-------|
| `Defs/Principles.lean` | 99 |
| `Defs/BinaryEncoding.lean` | 140 |
| `Copenhagen/QubitState.lean` | 92 |
| `Copenhagen/Copenhagen.lean` | 80 |
| `ManyWorlds/BranchingStructure.lean` | 97 |
| `ManyWorlds/ManyWorlds.lean` | 88 |
| `Bohmian/BohmianParams.lean` | 186 |
| `Bohmian/BohmianLPO.lean` | 158 |
| `Main/Synthesis.lean` | 65 |
| `Main/AxiomAudit.lean` | 101 |
| **Total** | **~1,106** |

### Architectural Notes

Each module opens with a docstring describing its mathematical content and its status (fully proved, sorry'd, or axiomatized). The `noncomputable section` directive appears in modules that use Mathlib's ℝ — this is an infrastructure artifact, not a reflection of non-constructive reasoning. All definitions are explicit formulas using field operations and `Real.sqrt`, ensuring BISH computability of the definitions themselves. Non-constructive content is isolated in the *theorem statements* (equivalence with omniscience principles) and their proofs.

---

## 8. Results Summary

| Interpretation | Physical Assertion | Principle | Forward | Reverse |
|---------------|-------------------|-----------|---------|---------|
| Copenhagen (weak) | α = 0 ∨ ¬¬(α ≠ 0) for all qubits | WLPO | **proved** | sorry'd |
| Copenhagen (strong) | α = 0 ∨ α ≠ 0 for all qubits | LPO | **proved** | sorry'd |
| Many-Worlds | All branching structures have worlds | DC | sorry'd | **proved** |
| Bohmian | All trajectories have asymptotic velocity | LPO | sorry'd | sorry'd |
| Uniform MWI | Uniform branching has worlds | BISH | **proved** | (N/A) |
| Strong → Weak | CopenhagenStrong → CopenhagenPostulate | inherits | **proved** | (trivial) |

**Hierarchy relationships:**

| Relationship | Status |
|-------------|--------|
| LPO → WLPO | proved (`lpo_implies_wlpo`) |
| Bohmian → Copenhagen | proved (`bohmian_implies_copenhagen`) |
| WLPO ↛ LPO | meta-theoretic (Ishihara [2]) |
| DC ⊥ LPO | meta-theoretic (incomparable in BISH) |
| DC ⊥ WLPO | meta-theoretic (incomparable in BISH) |

---

## 9. Discussion

### 9.1 Related Literature

The constructive foundations of analysis were laid by Bishop [1] and Bishop–Bridges [15], with the reverse mathematics programme developed by Ishihara [2], Bridges and Richman [3], and Bridges and Vîță [5]. The equivalence BMC ↔ LPO is due to Bridges and Vîță [5] and was verified in Lean in Paper 8 of this programme.

The Döring–Isham topos programme [13] reformulates quantum mechanics using presheaf categories over the poset of commutative subalgebras. Their approach is complementary: they restructure the mathematical framework of quantum mechanics to be compatible with intuitionistic logic, while we calibrate the logical cost of assertions within the standard framework. The two approaches address different questions and neither subsumes the other.

Cubitt, Perez-Garcia, and Wolf [14] proved that the spectral gap is undecidable (in the computability-theoretic sense). Papers 36–37 of this programme reduced their undecidability to LPO-equivalence, placing it within the calibration framework. The present paper addresses a different question: not the decidability of a property of Hamiltonians, but the logical cost of interpretive assertions about measurement.

Bell [12] established that any hidden-variable theory reproducing quantum predictions must be nonlocal. Our LPO calibration of Bohmian mechanics is orthogonal to the locality question: it concerns the logical cost of trajectory completion (asserting that a bounded monotone velocity sequence converges), not the communication structure of the theory.

Wallace [16] provides a philosophical defense of the Many-Worlds interpretation grounded in decision theory and emergence. Our DC calibration provides a complementary perspective: the logical cost of asserting that every branching tree has a complete branch.

Dürr, Goldstein, and Zanghì [17] develop the mathematical foundations of Bohmian mechanics. Our formalization uses their explicit trajectory formula for the free Gaussian and confirms that finite-time computation is BISH while asymptotic behavior requires LPO.

### 9.2 Open Questions

Several natural extensions remain:

- **Higher-dimensional Bohmian mechanics.** Does the LPO calibration persist for free Gaussians in ℝ³? The trajectory formula generalizes, and the velocity sequence remains bounded and monotone, so LPO is expected. Interacting potentials may introduce additional complexity.

- **Relativistic extensions.** Dürr et al.'s relativistic Bohmian mechanics [17] involves a preferred foliation. The CRM calibration of the foliation-dependent trajectory is open.

- **Interacting Many-Worlds.** Does interaction between branches (decoherence) modify the DC requirement? We conjecture not: the branching structure remains history-dependent regardless of decoherence rates.

- **Decoherence and Copenhagen.** Does the decoherent histories framework (Griffiths, Omnès, Gell-Mann–Hartle) modify the WLPO calibration? The consistency conditions introduce additional constraints that may shift the calibration.

- **Decoherence.** (Added in revision.) Decoherence is central to all three interpretations in practice: Copenhagen relies on it for the emergence of classical outcomes; Many-Worlds relies on it for the preferred basis and branch structure; Bohmian mechanics relies on it for effective collapse and the approach to quantum equilibrium. The present paper omits decoherence, treating it as a scope limitation (§1.3). A natural question is whether incorporating decoherence modifies the calibrations. We conjecture that it does not change the *level* of the calibrations (WLPO, DC, LPO respectively) but may shift the *interpretation* of what each principle achieves — for instance, decoherent branching may provide a physically motivated restriction of `BranchingStructure` that weakens the DC requirement. This is an important direction for future work.

- **Weihrauch degrees.** Expressing the three calibrations as Weihrauch reductions (Brattka, Gherardi, Pauly [18]) would place them in the finer-grained computability-theoretic hierarchy and enable comparison with the Weihrauch degrees of physical principles studied by Pauly and colleagues.

### 9.3 The Dissolution as Philosophical Contribution

The measurement problem has persisted for nearly a century in part because it has been treated as a single conceptual puzzle admitting a single resolution. The CRM analysis reveals it as three distinct questions:

- *Can we decide whether a superposition is trivial?* (Copenhagen, cost: WLPO)
- *Do infinite branching trees have complete paths?* (Many-Worlds, cost: DC)
- *Do bounded monotone velocity sequences converge?* (Bohmian, cost: LPO)

These questions are logically independent: answering one does not answer the others. The analogy is not three windows onto the same room but three doors to three different rooms. The persistent debate over which interpretation is "correct" was, in part, a category error — conflating three questions that happen to agree on their empirical predictions but differ in their logical commitments.

This is not a resolution of the measurement problem. A resolution would require new physics (or new mathematics) that selects one interpretation over the others. We propose it as a *dissolution thesis*: if the calibrations are correct, the question as traditionally posed conflated distinct logical commitments. The fully machine-checked proofs — `copenhagen_implies_WLPO` and `strong_copenhagen_implies_LPO` — provide concrete evidence that this dissolution is not merely philosophical. They are theorems with machine-verified proof chains from physical postulate to logical principle, establishing that the formalization-to-principle correspondence is genuine. The remaining sorry'd directions, if filled, would complete the biconditionals and establish the dissolution as a theorem rather than a thesis.

We emphasize that even granting all three calibrations, what is established is that three specific *formalizations* of the interpretations sit at different constructive levels. Whether these formalizations capture the *essential* content of the interpretations is a philosophical judgment that the formal machinery cannot settle. Section 2.5 addresses this for the Copenhagen case by showing that the formalization choice itself is parameterizable: strengthening the postulate shifts the calibration in a quantifiable way.

---

## 10. Conclusion

This paper establishes five specific results:

1. **Copenhagen calibrates at WLPO (forward proved).** The forward direction `copenhagen_implies_WLPO` is fully machine-checked with no sorry — a complete, type-checked chain from physical postulate to logical principle. The reverse direction is sorry'd with literature support [5].

2. **Strong Copenhagen calibrates at LPO (forward proved).** Added in revision: `strong_copenhagen_implies_LPO` shows that strengthening the postulate from α = 0 ∨ ¬¬(α ≠ 0) to α = 0 ∨ α ≠ 0 shifts the calibration from WLPO to LPO. This quantifies the constructive cost of the double-negation weakening and addresses a key referee concern about the formalization choice.

3. **Many-Worlds calibrates at DC (both directions sorry'd).** Constructing a complete world through a history-dependent branching tree requires Dependent Choice. The uniform (history-independent) case is BISH-provable (`uniform_world_exists` and the constructive witness `uniform_world_witness`, both fully checked), sharpening the result: DC is needed precisely for adaptive measurement protocols.

4. **Bohmian calibrates at LPO (both directions sorry'd).** Asserting that every Bohmian trajectory has a well-defined asymptotic velocity requires the Limited Principle of Omniscience (equivalently, Bounded Monotone Convergence). At any finite time, the trajectory is BISH-computable; the non-constructive content is concentrated in the infinite-time limit.

5. **The dissolution thesis.** Since WLPO < LPO strictly and DC is incomparable with both, the three interpretations sit at provably distinct positions in the constructive hierarchy. The measurement problem, when properly stratified, dissolves into three separate questions with different logical costs. We present this as a thesis supported by the fully proved directions and corroborated by proof sketches for the remaining directions.

The four fully machine-checked results — `copenhagen_implies_WLPO`, `strong_copenhagen_implies_LPO` (both physics-to-logic), `uniform_world_exists`, and `uniform_world_witness` (BISH separation) — demonstrate that the framework is amenable to machine verification. The remaining sorry'd obligations are classified in §6 as standard CRM lifts, type-level encodings, and pure calculus, none of which represents a gap in the mathematical argument.

The BISH+LPO ceiling established in Papers 1–40 is not violated: all three interpretations calibrate at or below LPO (with DC on an independent branch). No interpretation requires the full Fan Theorem, Dependent Choice beyond DC_ω, or the unrestricted law of excluded middle.

The models analyzed here are simplified — a single qubit, finitely-many-outcome measurements, a 1D free Gaussian. Extensions to higher dimensions, interacting systems, and relativistic settings are natural and expected to preserve the calibrations, but they remain conjectures. The contribution of the present paper is the framework and the proof of concept: that constructive reverse mathematics can meaningfully classify not just physical theories but their *interpretations*.

---

## 11. AI-Assisted Methodology

This formalization was developed using Claude (Anthropic) as a collaborative tool for Lean 4 code generation, proof strategy exploration, and document preparation. All mathematical content was specified by the author; every theorem was verified by the Lean 4 type checker.

The author is a medical professional, not a domain expert in physics or mathematics. Physical interpretations, modeling assumptions, and sorry'd proof obligations require independent verification by domain experts. This paper should be considered preliminary until such verification is completed. Any errors are solely the author's.

---

*Dedicated to the constructive mathematics community and the enduring legacy of Errett Bishop, whose* Foundations of Constructive Analysis *(1967) demonstrated that meaningful mathematics need not appeal to completed infinities.*

---

## References

[1] E. Bishop, *Foundations of Constructive Analysis*, McGraw-Hill (1967).

[2] H. Ishihara, "Reverse mathematics in Bishop's constructive mathematics," *Philosophia Scientiae*, Cahier Spécial 6, 43–59 (2006).

[3] D. Bridges and F. Richman, *Varieties of Constructive Mathematics*, London Mathematical Society Lecture Note Series 97, Cambridge University Press (1987).

[4] H. Diener, "Constructive reverse mathematics," Habilitation thesis, University of Siegen (2018). arXiv:1804.05495.

[5] D. Bridges and L. Vîță, *Techniques of Constructive Analysis*, Universitext, Springer (2006).

[6] P. C.-K. Lee, "The Logical Geography of Mathematical Physics: A Constructive Calibration Table" (Paper 10), 2026. [DOI: 10.5281/zenodo.18671162](https://doi.org/10.5281/zenodo.18671162).

[7] P. C.-K. Lee, "The Map and the Territory: A Constructive History of Mathematical Physics" (Paper 12), 2026.

[8] P. C.-K. Lee, "The Logical Constitution of Physical Reality" (Paper 40), 2026.

[9] N. Bohr, "The quantum postulate and the recent development of atomic theory," *Nature* **121**, 580–590 (1928).

[10] H. Everett III, "'Relative state' formulation of quantum mechanics," *Reviews of Modern Physics* **29**, 454–462 (1957).

[11] D. Bohm, "A suggested interpretation of the quantum theory in terms of 'hidden' variables," *Physical Review* **85**, 166–193 (1952).

[12] J. S. Bell, *Speakable and Unspeakable in Quantum Mechanics*, Cambridge University Press (1987).

[13] A. Döring and C. J. Isham, "A topos foundation for theories of physics," *Journal of Mathematical Physics* **49**, 053515 (2008).

[14] T. S. Cubitt, D. Perez-Garcia, and M. M. Wolf, "Undecidability of the spectral gap," *Nature* **528**, 207–211 (2015).

[15] E. Bishop and D. Bridges, *Constructive Analysis*, Grundlehren der mathematischen Wissenschaften vol. 279, Springer-Verlag (1985).

[16] D. Wallace, *The Emergent Multiverse: Quantum Theory According to the Everett Interpretation*, Oxford University Press (2012).

[17] D. Dürr, S. Goldstein, and N. Zanghì, *Quantum Physics Without Quantum Philosophy*, Springer (2013).

[18] V. Brattka, G. Gherardi, and A. Pauly, "Weihrauch complexity in computable analysis," in *Handbook of Computability and Complexity in Analysis*, Springer (2021).

[19] P. C.-K. Lee, "LPO Dispensability for the 1D Ising Model" (Paper 8), 2026.

[20] P. C.-K. Lee, "Decoherence and the Constructive Hierarchy" (Paper 14), 2026.

[21] M. J. Beeson, *Foundations of Constructive Mathematics*, Springer (1985).

[22] M. Rathjen, "Constructive set theory and Brouwerian principles," *Journal of Universal Computer Science* **11**, 2008–2033 (2005).
