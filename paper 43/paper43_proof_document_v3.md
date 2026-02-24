# Paper 43: What the Ceiling Means — Constructive Schools, Physical Actualisation, and the Fine Structure of BISH+LPO

## Proof Document for Lean 4 Formalisation

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose

### 0.1 What this paper is

Paper 40 established the ceiling: BISH + LPO is the logical constitution of empirically accessible physics. Paper 43 asks: *what does this mean?*

The constructive mathematics community contains three schools that disagree about which principles beyond BISH are legitimate. The programme's calibration table, read correctly, distinguishes exactly where these schools diverge about physics. This paper makes that distinction explicit and identifies the physical phenomenon — stochastic actualisation — that sits at the disputed border.

Paper 43 does not extend the ceiling. It interprets it.

### 0.2 The three schools

**Bishop (BISH).** Neither accepts nor rejects any principle beyond BISH. Uses only constructive methods — every existence claim comes with a computable witness. Silent on MP, LPO, and all omniscience principles. Maintains neutrality as a deliberate strategy: BISH is compatible with classical mathematics, with Brouwer, and with Markov.

**Brouwer (Intuitionism).** Rejects LPO, MP, and the law of excluded middle for infinite collections. Accepts the Fan Theorem and bar induction (from the theory of choice sequences). Demands that existence claims provide bounded constructions. A search that "can't fail" but has no deadline is not a construction.

**Markov (Russian Constructivism).** Accepts MP and Church's Thesis (every function is computable). Under Church's Thesis, MP is provable: a computable search that can't fail will terminate if you run it. Rejects LPO (undecidable even with Church's Thesis). Accepts unbounded search as legitimate computation.

### 0.3 What the calibration table shows each school

The programme's ~60 calibrations across 12 domains produce a table with three layers:

| Layer | Content | Constructive status |
|-------|---------|-------------------|
| **Mathematical predictions** | Probabilities, energy levels, cross-sections, detection times | BISH. All schools accept. |
| **Thermodynamic limits** | Free energy density, phase transitions, spectral gaps | LPO. Markov rejects. Brouwer rejects. Bishop is silent. |
| **Physical actualisation** | "This atom decays." "This orbit recurs." | Cournot + MP. Brouwer rejects. Markov accepts. Bishop is silent. |

The three schools draw different lines through the same table. The programme doesn't choose a line. It reports where all three lines fall.

---

## 1. The Hierarchy: LPO Implies MP

### 1.1 Theorem

**Theorem 1 (LPO ⟹ MP).** Over BISH, LPO strictly implies MP.

### 1.2 Proof

Let α : ℕ → Bool satisfy ¬(∀n, α(n) = false). By LPO: (∃n, α(n) = true) ∨ (∀n, α(n) = false). The second disjunct contradicts the hypothesis. Therefore the first holds. ∎

### 1.3 Consequence

The BISH + LPO ceiling already contains MP. Any physical system whose calibration involves a thermodynamic limit (LPO) automatically has MP available. The ceiling does not extend.

### 1.4 The partial order

```
              LPO  (= WLPO + MP)
             /   \
          WLPO    MP
             \   /
              ??? (WLPO and MP are independent)
              |
             LLPO (independent of MP)
              |
             BISH
```

FT and DC are independent of all the above and dispensable for physics (Papers 30, 31).

### 1.5 Lean formalisation

```lean
/-- LPO strictly implies MP. --/
theorem lpo_implies_mp : LPO → MP := by
  intro lpo α h_not_all_false
  rcases lpo α with ⟨n, hn⟩ | hall
  · exact ⟨n, hn⟩
  · exact absurd hall h_not_all_false
```

---

## 2. The BISH Content of Exponential Decay

### 2.1 Statement

**Theorem 2.** For all λ > 0 and ε > 0, there exists a computable t₀ such that exp(-λt₀) < ε. The witness is t₀ = (ln(1/ε) + 1)/λ.

### 2.2 Significance

This theorem shows that the *mathematical prediction* of radioactive decay is fully constructive. For any measured decay rate (a known positive rational with error bars), every computable quantity — the survival probability, the detection time, the probability distribution, the moments — is BISH. No omniscience principle is needed for the mathematics.

This corrects a misimpression left by Paper 22, which framed eventual decay as requiring MP. The MP content enters not through the mathematics but through the physical interpretation (§3 below).

### 2.3 Lean sketch

```lean
theorem detection_time_bish (λ ε : ℝ) (hλ : 0 < λ) (hε : 0 < ε) (hε1 : ε < 1) :
    let t₀ := (Real.log (1/ε) + 1) / λ
    0 < t₀ ∧ Real.exp (-λ * t₀) < ε := by
  constructor
  · apply div_pos
    · linarith [Real.log_pos (by linarith : 1 < 1/ε)]
    · exact hλ
  · -- exp/log chain: see §2.4
    sorry
```

### 2.4 Lean strategy

Required Mathlib lemmas: `Real.exp_lt_exp` (strict monotonicity), `Real.exp_log` (exp-log inverse), `Real.log_pos` (log positive for argument > 1). Helper lemma:

```lean
lemma exp_neg_lt_of_gt_log_inv (λ t ε : ℝ) (hλ : 0 < λ) (hε : 0 < ε)
    (ht : λ * t > Real.log (1/ε)) :
    Real.exp (-(λ * t)) < ε := by
  rw [Real.exp_neg, inv_lt (Real.exp_pos _) hε]
  calc ε⁻¹ = Real.exp (Real.log ε⁻¹) := (Real.exp_log (by positivity)).symm
    _ < Real.exp (λ * t) := Real.exp_lt_exp.mpr ht
```

---

## 3. Cournot's Principle and Physical Actualisation

### 3.1 The postulate

**Cournot's Principle (1843):** An event whose probability is zero does not occur in a single realisation of the experiment.

This is not a theorem. It is a physical postulate — the bridge between mathematical probability and empirical physics. Without it, probability theory describes ensembles, not individual events. With it, measure-zero exclusions become physical impossibilities.

### 3.2 Where MP enters

For radioactive decay:

1. **BISH:** P(survive forever) = lim_{t→∞} exp(-λt) = 0. (Computable limit of a computable function.)
2. **Cournot:** The actual atom's trajectory does not belong to the measure-zero set {eternal survival}. Therefore: ¬(atom survives forever).
3. **MP:** From ¬(∀t, undecayed at t), extract ∃t, decayed by t.

Step 1 is mathematics. Step 2 is a physical postulate. Step 3 is MP. The chain is: BISH → Cournot → ¬∀ → MP → ∃.

### 3.3 What the three schools say

**Brouwer:** Accepts step 1. Rejects step 3 — the ¬∀ → ∃ inference is illegitimate without a bounded construction. Also suspicious of step 2 as a mathematical principle (Cournot is physics, not mathematics). Conclusion: mathematics can compute all probabilities but cannot assert actual decay.

**Markov:** Accepts all three steps. Step 3 is exactly MP, which the Russian school endorses. The atom decays because a process that can't fail to terminate does terminate. Conclusion: actual decay is a legitimate mathematical consequence.

**Bishop:** Accepts step 1. Takes no position on steps 2-3. BISH computes the probabilities. Whether you additionally assert actual decay is outside BISH's scope. Conclusion: the mathematical content is constructive; the rest is your problem.

### 3.4 Formalisation

```lean
/-- Cournot's Principle. BRIDGE AXIOM encoding a physical postulate. --/
axiom cournot {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {A : Set Ω} (hA : μ A = 0) (ω : Ω) (hω : ω ∈ A) : False
```

---

## 4. Three Readings of the Calibration Table

### 4.1 The strict Bishopian reading

Physics = computable predictions only. Every quantity an experiment can check to finite precision is BISH. LPO enters through the thermodynamic limit, which is a mathematical idealisation — no experiment measures an infinite system. The "free energy density" is a convenient fiction; the actual finite-volume free energy is BISH.

Under this reading: the logical constitution of *measured* physics is **BISH alone**. LPO is the cost of a useful idealisation. MP is irrelevant.

This reading is defensible but radical. It says phase transitions don't "really" happen — there's no sharp Curie temperature, just a very steep crossover. Many physicists would object. But the objection is physical, not logical.

### 4.2 The programme's standard reading

Physics = computable predictions + thermodynamic limits. The infinite-volume limit is part of physics because physicists use it, its predictions are confirmed, and the alternative (working only with finite systems) is computationally intractable. LPO is genuinely required.

Under this reading: the logical constitution is **BISH + LPO**. MP is subsumed.

This is Paper 40's position.

### 4.3 The inclusive reading

Physics = computable predictions + thermodynamic limits + physical actualisation. The assertion "this atom decays" is an empirical prediction, confirmed trillions of times. Cournot's Principle is a physical commitment. MP is part of the logical constitution.

Under this reading: the logical constitution is **BISH + LPO + MP**. But LPO implies MP, so this reduces to **BISH + LPO**. The MP content is present but not independent — it is automatically subsidised by the thermodynamic limit.

This reading adds nothing to the ceiling but makes explicit that actualisation is a distinct physical commitment with a distinct logical signature.

### 4.4 What the programme contributes

The programme does not choose between these readings. It provides the measurements that make the choice precise. Before the programme, "how much non-constructive reasoning does physics need?" was a vague philosophical question. After the programme, it is a question with three precise answers — BISH, BISH + LPO, or BISH + LPO + MP — corresponding to three precise demarcation choices. The measurements are the same regardless of which reading you adopt.

---

## 5. Calibration: Poincaré Recurrence

### 5.1 Physics

Measure-preserving map φ on finite measure space (X, μ). Poincaré's theorem: for any A with μ(A) > 0, almost every point returns to A.

### 5.2 BISH content

**Theorem 3.** Let B = {x ∈ A : ∀k ≥ 1, φᵏ(x) ∉ A}. Then μ(B) = 0.

Proof: The preimages φ⁻ⁿ(B) are pairwise disjoint (combinatorial, BISH) and equimeasured (measure preservation, BISH). If μ(B) > 0, their union has infinite measure, contradicting μ(X) < ∞. So ¬(μ(B) > 0), which with μ(B) ≥ 0 gives μ(B) = 0. BISH throughout. ∎

### 5.3 MP content

"This specific orbit returns to A" requires Cournot (ω ∉ B since μ(B) = 0) followed by MP (¬∀¬ → ∃). Same structure as radioactive decay.

### 5.4 Notable difference

Unlike radioactive decay, Poincaré recurrence has no computable return time. The detection time for decay is BISH-computable (Theorem 2). The return time for Poincaré recurrence depends on Diophantine properties of the orbit and is generally not computable. Yet the logical cost is the same: Cournot + MP. The non-computability of the return time adds nothing to the logical cost because the obstacle is not the principle needed (still MP) but the *witness quality* (no bound available).

### 5.5 Bridge axioms

```lean
axiom phase_space_finite : μ (Set.univ : Set X) < ⊤
axiom dynamics_preserving : MeasureTheory.MeasurePreserving φ μ μ
```

---

## 6. Calibration: False Vacuum Decay

### 6.1 BISH content

Tunnelling rate Γ/V computable from bounce action (Picard iteration, BISH). Survival probability P(T) = exp(-(Γ/V)·V·T) computable for all finite T. Detection time T(ε) computable. P(survive forever) = 0, constructive limit.

### 6.2 MP content

"The false vacuum eventually decays somewhere" = Cournot + MP. Structurally identical to radioactive decay.

---

## 7. Nature at the Disputed Border

### 7.1 The striking observation

Of all the principles in the constructive hierarchy, MP is the one the three schools *disagree about*. LPO is rejected by both Brouwer and Markov. LLPO is rejected by both. FT is accepted by Brouwer, rejected by Markov. BISH is accepted by everyone.

MP is the unique point of three-way disagreement: Markov accepts, Brouwer rejects, Bishop abstains.

And MP governs the most basic physical process imaginable: a single unstable thing decaying. Not a phase transition (LPO). Not a quantum foundation result (LLPO). Not a compactness argument (FT). Just: a thing falls apart, eventually.

The programme cannot determine whether this is a deep fact or a coincidence. But it can state precisely what the coincidence is: the physical process of stochastic actualisation — the passage from "probability says this will happen" to "it actually happens" — sits at exactly the principle where the constructive schools part company.

### 7.2 Connection to algorithmic randomness

The structure of the MP step — from ¬∀ to ∃ for outcomes of a random process — is identical to a well-studied phenomenon in constructive probability theory. A Martin-Löf random binary sequence cannot be identically zero (BISH, since {000...} has measure zero). But asserting that a specific random sequence has a 1 somewhere requires MP. The literature on constructive measure theory (Bishop 1967, Chan, Spitters) has explored this boundary from the mathematical side. The programme adds the physical side: the same boundary governs radioactive atoms, Poincaré orbits, and metastable vacua.

---

## 8. Assembly

### 8.1 The fine structure of the ceiling

```
              LPO
         (thermodynamic limits:
          Fekete, phase transitions,
          spectral gaps, condensates)
             /    \
          WLPO     MP
      (phase ID)  (actualisation:
                   Cournot + ¬∀ → ∃,
                   decay, recurrence,
                   tunnelling)
             \    /
              LLPO
          (Bell, KS, IVT,
           quantum foundations)
              |
             BISH
         (all mathematical
          predictions: probabilities,
          energies, cross-sections,
          detection times, spectra)
```

### 8.2 Three universal mechanisms

| Principle | Mechanism | Physical context |
|-----------|-----------|-----------------|
| LPO | Fekete's subadditive lemma | Finite → infinite volume |
| LLPO | Intermediate value theorem | Root-finding, quantum measurement |
| MP | Cournot + ¬∀ → ∃ | Probability → actuality |

Each principle enters physics through a single mechanism across all calibrations examined.

---

## 9. Module Structure

```
Paper43_Actualisation/
├── Defs/
│   ├── Principles.lean          -- MP, LPO, WLPO, LLPO
│   ├── Cournot.lean             -- Bridge axiom
│   └── Decay.lean               -- Survival probability defs
├── Hierarchy/
│   ├── LPO_implies_MP.lean      -- Theorem 1
│   └── Placement.lean           -- Partial order
├── BISHContent/
│   ├── ExponentialWitness.lean  -- Theorem 2
│   ├── PoincareMeasure.lean     -- Theorem 3
│   └── FalseVacuumRate.lean     -- Tunnelling rate computable
├── Actualisation/
│   ├── RadioactiveDecay.lean    -- Cournot + MP → decay
│   ├── PoincarePointwise.lean   -- Cournot + MP → return
│   └── FalseVacuum.lean         -- Cournot + MP → tunnelling
├── Assembly/
│   └── FineStructure.lean       -- Summary theorems
└── Main.lean                    -- #print axioms
```

**Estimated total: ~550 lines.**

---

## 10. Axiom Audit

**BISH theorems** (Theorems 2, 3, tunnelling rate): `propext`, `Quot.sound`, possibly `Classical.choice` (Mathlib infrastructure — see Paper 10 §3).

**Actualisation theorems** (decay, return, tunnelling): Above plus `cournot` (bridge axiom) and `MP` as explicit hypotheses in the theorem statement.

**Hierarchy theorem** (LPO ⟹ MP): `propext`, `Quot.sound` only. Pure logic.

---

## 11. Revision Instructions for Paper 22

Paper 22's formal results are correct. The Lean code compiles. **Nothing is retracted.**

Six edits correct the interpretation:

1. **Abstract:** Replace "eventual decay is equivalent to MP" with "the mathematical prediction of decay is BISH; physical actualisation requires Cournot + MP."

2. **§0.1:** Add paragraph noting that for measured λ₀ > 0, the detection time is a computable BISH witness.

3. **Part A:** Add Theorem 2 (exponential witness is BISH) as a new lemma.

4. **Part B:** Clarify that the binary-sequence encoding calibrates the abstract mathematical statement, not the physical situation.

5. **Discussion:** Add subsection on Cournot's Principle and the three-school distinction.

6. **Hierarchy:** Add LPO ⟹ MP proof. Correct any claim that MP is "independent" of LPO.

**Lean additions for Paper 22:**

```lean
-- In Hierarchy.lean:
theorem lpo_implies_mp : LPO → MP := by
  intro lpo α h_not_all_false
  rcases lpo α with ⟨n, hn⟩ | hall
  · exact ⟨n, hn⟩
  · exact absurd hall h_not_all_false

-- New file: Defs/Cournot.lean
axiom cournot {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {A : Set Ω} (hA : μ A = 0) (ω : Ω) (hω : ω ∈ A) : False

-- New file or addition to PartA:
theorem detection_time_bish (λ ε : ℝ) (hλ : 0 < λ) (hε : 0 < ε) (hε1 : ε < 1) :
    let t₀ := (Real.log (1/ε) + 1) / λ
    0 < t₀ ∧ Real.exp (-λ * t₀) < ε := by
  sorry -- see Paper 43 §2.4 for strategy
```

---

## 12. What This Paper Does Not Do

- Does not extend the ceiling. BISH + LPO remains the ceiling.
- Does not adjudicate between the three schools. Reports where they disagree.
- Does not claim MP is physically necessary. Claims MP is the logical cost of a specific physical interpretation (actualisation via Cournot).
- Does not revise any formal result in Papers 1–42. Revises the interpretation of Paper 22.
- Does not require Paper 40 to be edited.

---

## 13. References to Verify

- Cournot, A.A. (1843). *Exposition de la Théorie des Chances et des Probabilités*. [Original Cournot's Principle]
- Bridges, D., Richman, F. (1987). *Varieties of Constructive Mathematics*. [LPO ⟹ MP; MP independent of LLPO]
- Ishihara, H. (2006). "Constructive reverse mathematics." [WLPO + MP = LPO]
- Bishop, E. (1967). *Foundations of Constructive Analysis*. [BISH; constructive measure theory]
- Markov, A.A. (1954). *Theory of Algorithms*. [MP; Russian constructivism]
- Shafer, G., Vovk, V. (2001). *Probability and Finance: It's Only a Game!* [Game-theoretic alternative to Cournot]
- Spitters, B. Constructive measure theory. [Verify specific reference]
- Chan, Y.K. Constructive probability. [Verify specific reference]
