# Paper 43 — What the Ceiling Means: Constructive Schools, Physical Actualisation, and the Fine Structure of BISH+LPO

## Abstract

Paper 40 established that the logical resources required for all empirical predictions in known physics are exactly BISH+LPO. This paper asks what that ceiling means. The constructive mathematics community contains three schools — Bishop, Brouwer, and Markov — that disagree about which principles beyond BISH are legitimate. We show that the programme's calibration table, read through these three schools, localizes their disagreement to a single principle: Markov's Principle (MP). LPO strictly implies MP (five-line proof), so the BISH+LPO ceiling already contains MP. The mathematical content of radioactive decay is BISH: the detection time t₀ = (log(1/ε) + 1)/λ is a computable witness requiring no omniscience principle. What requires MP is *physical actualisation* — the step from "the probability of eternal survival is zero" to "this specific atom actually decays." This step requires Cournot's Principle (a physical postulate, not a theorem) followed by MP. The same three-step chain — BISH computation, Cournot exclusion, MP witness extraction — governs Poincaré recurrence and false vacuum decay. Three readings of the calibration table are defensible: strict Bishopian (BISH alone), standard (BISH+LPO, Paper 40's position), and inclusive (BISH+LPO+MP, which reduces to BISH+LPO since LPO implies MP). The programme does not choose between readings. It reports where the three schools draw different lines through the same table. This paper corrects a framing in Paper 22, which implied MP was independent of LPO. Nothing in Paper 22 is retracted; the formal results compile unchanged. The Lean 4 formalization (12 files, approximately 770 lines, zero sorry) is archived at doi:10.5281/zenodo.18665418.


## §1. Introduction: Not Extending the Ceiling — Interpreting It

Papers 1–39 established that the axiom cost of every empirical prediction in known physics falls within BISH+LPO. Paper 40 defended this ceiling against objections. Papers 41–42 applied the framework as a diagnostic tool — to the AdS/CFT correspondence and the cosmological constant problem, respectively. This paper changes direction. It does not add a new physical system to the calibration table. It asks what the completed table reveals about the foundations of constructive mathematics itself.

The calibration table has approximately 60 entries across 12 physics domains. All sit at BISH or LPO, with the Fan Theorem entering only as dispensable scaffolding (Papers 23, 30, 31). What does this uniformity tell us? The answer: it tells different things to different schools of constructive mathematics, and the disagreement localizes to one principle — Markov's Principle.

A consultant review of Paper 22 (February 2026) identified two points. The correction: LPO strictly implies MP. Paper 22 implied MP was independent of LPO — this is wrong. MP sits strictly below LPO in the hierarchy. The confirmation: the exponential decay witness t₀ = −ln(ε)/λ is computable for any known positive rate. The mathematical content of radioactive decay is BISH. MP enters not through the probability calculation but through the physical interpretation: asserting that a specific atom actually decays.

This paper formalizes three small results (LPO implies MP, detection time is BISH, Poincaré non-return set has measure zero), three actualisation proofs (radioactive decay, Poincaré recurrence, false vacuum decay), and a reinterpretation of the calibration table through three constructive schools. It does not extend the ceiling.


## §2. The Three Schools

### §2.1. Bishop's BISH

Bishop's constructive mathematics (Bishop, 1967) uses only constructive methods: every existence claim must come with a computable witness. BISH neither accepts nor rejects any principle beyond its core methods. It is compatible with classical mathematics, with Brouwer's intuitionism, and with Markov's Russian constructivism. This deliberate neutrality is a strategic choice: BISH is the minimal common ground on which all schools agree. The programme's calibration operates over BISH precisely because it is the only base accepted by everyone.

### §2.2. Brouwer's Intuitionism

Brouwer's programme (1920s) rejects the law of excluded middle for infinite collections, and with it LPO, MP, and all omniscience principles. It accepts the Fan Theorem and bar induction, which arise from the theory of choice sequences — Brouwer's distinctive ontological commitment. The key demand: existence claims must provide bounded constructions. A search that "cannot fail" but has no deadline is not a construction. This is why Brouwer rejects MP: the inference from ¬(∀n, α(n) = 0) to ∃n, α(n) = 1 asserts that an unbounded search terminates, without supplying a bound.

### §2.3. Markov's Russian Constructivism

The Russian school (Markov, 1954) accepts MP and Church's Thesis — the thesis that every function on the natural numbers is computable. Under Church's Thesis, MP becomes provable: a computable search that cannot fail will terminate if you run it, because a computable function that is not identically zero on every input must produce a nonzero output at some finite step. The Russian school rejects LPO because decidability of ∀n, α(n) = 0 is not guaranteed even under Church's Thesis — the halting problem prevents it.

### §2.4. The Unique Point of Disagreement

| Principle | Bishop | Brouwer | Markov |
|-----------|--------|---------|--------|
| BISH core | Accepts | Accepts | Accepts |
| LPO | Silent | Rejects | Rejects |
| WLPO | Silent | Rejects | Rejects |
| LLPO | Silent | Rejects | Rejects |
| FT | Silent | Accepts | Rejects |
| **MP** | **Silent** | **Rejects** | **Accepts** |

MP is the unique principle where the three major schools have three distinct positions: acceptance (Markov), rejection (Brouwer), and deliberate silence (Bishop). LPO is rejected by both Brouwer and Markov. FT is accepted by Brouwer and rejected by Markov. Only MP produces a genuine three-way split. The programme's calibration table cuts through exactly this disagreement.


## §3. The Hierarchy: LPO Strictly Implies MP

### §3.1. Theorem 1

**Theorem 1 (LPO implies MP).** Over BISH, the Limited Principle of Omniscience strictly implies Markov's Principle.

*Proof.* Let α : ℕ → Bool satisfy ¬(∀n, α(n) = false). Apply LPO to α: either (∃n, α(n) = true) or (∀n, α(n) = false). The second disjunct contradicts the hypothesis. Therefore the first holds. ∎

This is pure logic. The Lean formalization requires only `propext`.

### §3.2. The Partial Order

```
              LPO  (= WLPO + MP)
             /   \
          WLPO    MP
             \   /
              ??? (independent)
              |
             LLPO (independent of MP)
              |
             BISH
```

Key relationships: WLPO + MP = LPO (Ishihara, 2006). WLPO and MP are independent — neither implies the other (model-theoretic separation). LLPO is independent of MP (Bridges and Richman, 1987). The Fan Theorem is independent of all the above and enters physics only as scaffolding (Paper 23).

### §3.3. Consequence for the Ceiling

The BISH+LPO ceiling already contains MP. Any physical system whose calibration involves a thermodynamic limit — computed via Fekete's Subadditive Lemma (Paper 29: Fekete ≡ LPO) — automatically has MP available. No new tier is needed. This corrects Paper 22's implicit framing that MP represented a cost beyond the existing ceiling.

Paper 23 established that the Fan Theorem is independent of LPO, MP, and the entire omniscience chain. The hierarchy therefore has four distinct roles in mathematical physics: LPO (thermodynamic limits), WLPO (phase identification), LLPO (quantum foundations), MP (actualisation), and FT (scaffolding) — with FT and DC dispensable.


## §4. The BISH Content of Exponential Decay

### §4.1. Theorem 2

**Theorem 2.** For all λ > 0 and ε ∈ (0, 1), there exists a computable t₀ such that exp(−λt₀) < ε. The witness is:

    t₀ = (log(1/ε) + 1) / λ

*Proof.* Positivity: since ε < 1, we have 1/ε > 1, so log(1/ε) > 0, hence log(1/ε) + 1 > 0, and t₀ > 0 (dividing by λ > 0). Bound: λ · t₀ = log(1/ε) + 1 > log(1/ε), so exp(−λt₀) < exp(−log(1/ε)) = ε. ∎

This is BISH: an explicit formula, no limits, no search, no omniscience. The proof in Lean uses only standard Mathlib real analysis (`exp_log`, `exp_lt_exp_of_lt`, `inv_lt_comm₀`, `div_pos`).

### §4.2. Correction of Paper 22

Paper 22 proved that "eventual decay for a rate λ known only to be nonzero" is equivalent to MP. This formal equivalence is correct and is not retracted. The binary-sequence encoding (where λ encodes a sequence with ¬(λ = 0) but not λ # 0) makes this a valid mathematical equivalence.

But the physical situation is different. A measured decay rate λ₀ is a known positive rational (with error bars). For any such λ₀, the detection time t₀ is a closed-form BISH witness. The MP content enters not through computing the probability or the detection time — both BISH — but through asserting that a specific atom actually decays (§5).

### §4.3. Significance

Every computable quantity in exponential decay — the survival probability, the detection time, the probability distribution, the moments — is BISH. No omniscience principle is needed for the mathematics. The distinction between mathematical prediction (BISH) and physical actualisation (MP) is the central structural finding of this paper.


## §5. Cournot's Principle and Physical Actualisation

### §5.1. The Postulate

**Cournot's Principle (1843):** An event whose probability is zero does not occur in a single realisation of the experiment.

This is not a theorem. It is a physical postulate — the bridge between mathematical probability and empirical physics. Without Cournot's Principle, probability theory describes ensembles and limiting frequencies. It says nothing about what happens to a specific atom in a specific experiment. With Cournot's Principle, measure-zero exclusions become physical impossibilities: if the set of eternal survivors has probability zero, then this atom is not an eternal survivor.

### §5.2. The Three-Step Actualisation Chain

For radioactive decay with rate λ > 0:

1. **BISH:** P(survive forever) = lim_{t→∞} exp(−λt) = 0. This is a computable limit of a computable function. The eternal survival set has measure zero.
2. **Cournot:** The actual atom's trajectory does not belong to the measure-zero eternal survival set. Therefore: ¬(∀t, undecayed at t).
3. **MP:** From ¬(∀t, undecayed at t), extract ∃t, decayed by t.

Step 1 is mathematics. Step 2 is a physical postulate. Step 3 is Markov's Principle. The chain is: BISH → Cournot → ¬∀ → MP → ∃.

### §5.3. What Each School Says

**Brouwer** accepts step 1. Rejects step 3 — the ¬∀ → ∃ inference is illegitimate without a bounded construction. Also suspicious of step 2 as a mathematical principle (Cournot is physics, not mathematics). Conclusion: mathematics can compute all probabilities but cannot assert actual decay.

**Markov** accepts all three steps. Step 3 is exactly MP, which the Russian school endorses. The atom decays because a process that cannot fail to terminate does terminate. Conclusion: actual decay is a legitimate mathematical consequence.

**Bishop** accepts step 1. Takes no position on steps 2–3. BISH computes the probabilities. Whether you additionally assert actual decay is outside BISH's scope. Conclusion: the mathematical content is constructive; the rest is your problem.

This is not an academic disagreement. It concerns whether mathematical physics can assert that unstable things actually fall apart. The three most influential schools of constructive mathematics give three different answers to the most basic physical process imaginable.


## §6. Poincaré Recurrence and False Vacuum Decay

### §6.1. Poincaré Recurrence: BISH Content

**Theorem 3.** Let φ be a measure-preserving map on a finite measure space (X, μ). For any measurable set A, let B = {x ∈ A : ∀k ≥ 1, φᵏ(x) ∉ A} be the set of points that never return. Then μ(B) = 0.

*Proof sketch.* The preimages φ⁻ⁿ(B) are pairwise disjoint (combinatorial, BISH) and equimeasured (measure preservation, BISH). If μ(B) > 0, their union has infinite measure, contradicting μ(X) < ∞. So μ(B) = 0. BISH throughout. ∎

The Lean formalization wraps Mathlib's `Conservative.measure_mem_forall_ge_image_notMem_eq_zero`, extracting the result for the non-return set defined above.

### §6.2. Poincaré Recurrence: MP Content

"This specific orbit returns to A" requires Cournot (ω ∉ B since μ(B) = 0) followed by MP (¬∀¬ → ∃). The logical structure is identical to radioactive decay.

**Notable difference.** Unlike radioactive decay, Poincaré recurrence has no computable return time. Theorem 2 gives an explicit BISH detection time for decay. The return time for Poincaré recurrence depends on Diophantine properties of the orbit and is generally not computable. Yet the logical cost is the same: Cournot + MP. The non-computability of the return time adds nothing to the logical cost. The obstacle is witness quality (no bound available), not the principle needed (still MP).

### §6.3. False Vacuum Decay

The false vacuum tunnelling rate Γ/V is computable from the bounce action via Picard iteration (BISH). The survival probability P(T) = exp(−(Γ/V)·V·T) is computable for all finite T. The detection time is computable. The probability of eternal metastability is zero.

The actualisation assertion — "the false vacuum eventually decays somewhere" — is Cournot + MP. Structurally identical to radioactive decay. In the Lean formalization, `vacuum_decays_mp` is defined as `atom_decays_mp` with the tunnelling rate in place of the decay rate.

### §6.4. The Pattern

| System | Mathematical prediction | Physical actualisation |
|--------|------------------------|----------------------|
| Radioactive decay | BISH (computable detection time) | Cournot + MP |
| Poincaré recurrence | BISH (non-return set measure zero) | Cournot + MP |
| False vacuum decay | BISH (computable detection time) | Cournot + MP |

Three physically distinct systems. One logical mechanism. The same axiom cost.


## §7. Three Readings of the Calibration Table

### §7.1. The Strict Bishopian Reading

Physics = computable predictions only. Every quantity an experiment can check to finite precision is BISH. LPO enters through the thermodynamic limit, which is a mathematical idealisation — no experiment measures an infinite system. The "free energy density" is a convenient fiction; the actual finite-volume free energy is BISH. Under this reading, the logical constitution of measured physics is **BISH alone**. LPO is the cost of a useful idealisation. MP is irrelevant.

This reading is defensible but radical. It says phase transitions do not "really" happen — there is no sharp Curie temperature, just a very steep crossover. Many physicists would object. But the objection is physical, not logical.

### §7.2. The Standard Reading (Paper 40)

Physics = computable predictions + thermodynamic limits. The infinite-volume limit is part of physics because physicists use it, its predictions are confirmed, and the alternative (working only with finite systems) is computationally intractable. LPO is genuinely required. Under this reading, the logical constitution is **BISH + LPO**. MP is subsumed (since LPO implies MP).

This is Paper 40's position and the programme's default reading.

### §7.3. The Inclusive Reading

Physics = computable predictions + thermodynamic limits + physical actualisation. The assertion "this atom decays" is an empirical prediction, confirmed trillions of times. Cournot's Principle is a physical commitment. MP is part of the logical constitution. Under this reading: **BISH + LPO + MP**. But LPO implies MP, so this reduces to **BISH + LPO**. The MP content is present but not independent — automatically subsidized by the thermodynamic limit.

This reading adds nothing to the ceiling but makes explicit that actualisation is a distinct physical commitment with a distinct logical signature.

### §7.4. What the Programme Contributes

The programme does not choose between these readings. It provides the measurements that make the choice precise. Before the programme, "how much non-constructive reasoning does physics need?" was a vague philosophical question. After the programme, it is a question with three precise answers — BISH, BISH+LPO, or BISH+LPO+MP — corresponding to three precise demarcation choices. The measurements are the same regardless of which reading you adopt. This is the paper's central contribution: the meta-mathematical precision of the question, not the answer.


## §8. The Fine Structure of the Ceiling

### §8.1. The Annotated Hierarchy

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

### §8.2. Three Universal Mechanisms

| Principle | Mechanism | Physical context |
|-----------|-----------|-----------------|
| LPO | Fekete's Subadditive Lemma | Finite → infinite volume |
| LLPO | Intermediate Value Theorem | Root-finding, quantum measurement |
| MP | Cournot + ¬∀ → ∃ | Probability → actuality |

Each principle enters physics through a single mechanism across all calibrations examined.

### §8.3. Nature at the Disputed Border

Of all principles in the constructive hierarchy, MP is the one the three schools disagree about. And MP governs the most basic physical process imaginable: a single unstable thing decaying. Not a phase transition (LPO). Not a quantum foundation result (LLPO). Not a compactness argument (FT). Just: a thing falls apart, eventually.

The programme cannot determine whether this is a deep fact or a coincidence. But it can state precisely what the coincidence is: the physical process of stochastic actualisation — the passage from "probability says this will happen" to "it actually happens" — sits at exactly the principle where the constructive schools part company. The structure of the MP step — from ¬∀ to ∃ for outcomes of a random process — is identical to a well-studied phenomenon in constructive probability theory. A Martin-Löf random binary sequence cannot be identically zero (BISH, since {000...} has measure zero). But asserting that a specific random sequence has a 1 somewhere requires MP. The literature on constructive measure theory (Bishop, 1967; Spitters; Chan) has explored this boundary from the mathematical side. The programme adds the physical side.


## §9. Relation to the Programme

### §9.1. Paper 22 (Markov Decay)

Paper 22 established the formal equivalence between eventual decay (binary-sequence encoding) and MP. Paper 43 corrects the framing: the mathematical prediction is BISH; MP enters only through physical actualisation. Paper 22's formal results are correct and not retracted. Six interpretive edits are specified in the proof document. The LPO → MP proof was always implicit in the hierarchy but not previously stated in the programme.

### §9.2. Paper 23 (Fan Theorem)

Paper 23 established that the Fan Theorem is equivalent to CompactOptimization and independent of LPO, MP, WLPO, and LLPO. Paper 43 completes the logical map: the four distinct roles in mathematical physics are LPO (thermodynamic limits), LLPO (quantum foundations), MP (actualisation), and FT (scaffolding). Of these, FT and DC are dispensable. The three indispensable principles — LPO, LLPO, MP — sit in a single partial order with LPO at the top.

### §9.3. Paper 40 (The Ceiling)

Paper 40 declared BISH+LPO as the ceiling. Paper 43 does not change this verdict. The three readings of the calibration table (§7) show that Paper 40's position is one of three defensible choices — but all three yield the same formal ceiling (BISH+LPO), since MP is subsumed.

### §9.4. Paper 29 (Fekete/LPO)

Paper 29 established that Fekete's Subadditive Lemma is equivalent to LPO. Since LPO implies MP, every system calibrated at LPO via Fekete automatically has MP available. The actualisation cost is always subsidized by the thermodynamic limit cost. This is why the ceiling does not extend.


## §10. Lean 4 Formalization

### §10.1. Code Architecture

```
P43_Actualisation/
  Defs/         Principles.lean, Cournot.lean, Decay.lean
  Hierarchy/    LPOImpliesMP.lean
  BISHContent/  ExponentialWitness.lean, PoincareMeasure.lean
  Actualisation/ RadioactiveDecay.lean, PoincarePointwise.lean, FalseVacuum.lean
  Assembly/     FineStructure.lean, AxiomAudit.lean
  Main.lean
```

Twelve source files, approximately 770 lines. Builds with `lake build` on Lean 4.28.0 with Mathlib. Zero errors, zero sorry, zero warnings.

### §10.2. Bridge Axioms

Two custom axioms: (1) `cournot` — Cournot's Principle, encoding the physical postulate that measure-zero events do not occur in single realisations; (2) `survival_prob_zero` — a bridge from the exponential probability model to the measure-space formulation. Markov's Principle appears as a *hypothesis* in theorem statements, not as an axiom — this is by design. The programme takes principles as hypotheses, allowing the formalization to remain agnostic about which school is adopted.

### §10.3. Code Vignette: The Actualisation Chain

```lean
theorem atom_decays_mp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (hMP : MarkovPrinciple)
    (decayed : Ω → ℕ → Bool) (undecayed : Ω → ℕ → Prop)
    (h_equiv : ∀ ω t, undecayed ω t ↔ decayed ω t = false)
    (rate : ℝ) (hr : 0 < rate)
    (h_model : ∀ t, μ {ω | undecayed ω t} =
      ENNReal.ofReal (survivalProb rate ↑t))
    (ω : Ω) :
    ∃ t, decayed ω t = true := by
  apply hMP (fun n => decayed ω n)      -- Step 3: MP
  intro h_all_false
  apply not_eternal_survival undecayed rate hr h_model ω  -- Step 2: Cournot
  intro t
  rw [h_equiv]                           -- Step 1: BISH encoding
  exact h_all_false t
```

The three-step chain is visible in the proof term: MP is applied first (outermost), then Cournot (via `not_eternal_survival`), then the BISH encoding (rewriting via `h_equiv`).

### §10.4. CRM Audit

| Module | Custom axioms | Infrastructure |
|--------|--------------|----------------|
| Hierarchy (LPO → MP, WLPO, LLPO) | None | propext (pure logic) |
| BISH content (Theorems 2, 3) | None | propext, Classical.choice, Quot.sound |
| Actualisation (decay, recurrence, vacuum) | cournot, survival_prob_zero | propext, Classical.choice, Quot.sound |
| Assembly (fine structure) | None | propext, Classical.choice, Quot.sound |

Classical.choice appears through Mathlib's real number infrastructure (Cauchy completion), not through proof content. Constructive stratification is established by proof content, not by axiom checker output (Paper 10, §Methodology).


## §11. Reproducibility

The complete Lean 4 formalization is archived at **doi:10.5281/zenodo.18665418**.

**Toolchain:** leanprover/lean4:v4.28.0. **Dependency:** Mathlib4 (pinned via `lake-manifest.json`).

**Build:**

    cd P43_Actualisation && lake exe cache get && lake build

**Result:** 0 errors, 0 sorry, 0 warnings. Twelve source files, approximately 770 lines. All theorems verified by the Lean 4 type checker. The axiom audit (`Assembly/AxiomAudit.lean`) confirms that BISH theorems use only Mathlib infrastructure, hierarchy theorems use propext only, and actualisation theorems add exactly the two declared bridge axioms.
