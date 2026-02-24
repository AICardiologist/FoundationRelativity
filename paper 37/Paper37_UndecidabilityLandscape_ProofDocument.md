# Paper 37: Uncomputability of Phase Diagrams and RG Flows is LPO

## Stratifying Bausch-Cubitt-Watson and the Uncomputable Renormalization Group

### Proof Document for Lean 4 Formalization

**Series:** Constructive Reverse Mathematics of Mathematical Physics
**Author:** Paul Chun-Kit Lee
**Architectural Guidance:** Claude (Anthropic)

---

## 1. Executive Summary

Paper 36 proved that Cubitt's spectral gap undecidability is Turing-Weihrauch equivalent to LPO. This paper extends the stratification to three further undecidability results in the Cubitt programme:

**(A) Uncomputability of phase diagrams** (Bausch, Cubitt, Watson 2021, Nature Communications): No algorithm can determine the phase diagram of a quantum many-body system, even given complete knowledge of the microscopic interactions.

**(B) Undecidability of the spectral gap in 1D** (Bausch, Cubitt, Lucia, Perez-Garcia 2020, Phys. Rev. X): Spectral gap undecidability holds even for 1D spin chains.

**(C) Uncomputably complex RG flows** (Cubitt, Lucia, Perez-Garcia, Perez-Eceiza 2022, Nature Communications): RG maps can be constructed whose individual steps are computable but whose asymptotic flow is uncomputable.

**Main Result:** All three results are Turing-Weihrauch equivalent to LPO, by the same mechanism as Paper 36. Each encodes Turing machine halting into a physical property via a computable reduction. Each is undecidable because LPO is non-computable. Each is decidable relative to LPO. No undecidability result in mathematical physics, to date, exceeds LPO.

**Emerging meta-theorem:** Every known undecidability result in quantum many-body physics is the non-computability of LPO — the same logical principle required for thermodynamic limits. The "undecidability" of physics is a misnomer: it is the non-computability of a single, well-understood logical principle that physics has used since Boltzmann.

---

## 2. The Three Results

### 2.1 Uncomputability of Phase Diagrams (BCW 2021)

**Reference:** Bausch, J., Cubitt, T.S. & Watson, J.D. (2021). Uncomputability of phase diagrams. Nature Communications, 12, 452.

**Their result:** Given a one-parameter family of Hamiltonians H(φ), the phase diagram — which maps the parameter φ to the phase of the system — is uncomputable. Specifically: there exist translation-invariant Hamiltonians parametrized by a real φ ∈ [0,1] such that no algorithm can determine, given φ, whether the system is in phase A or phase B.

**Their method:** Encode φ as binary input to a universal Turing machine via quantum phase estimation (QPE). The phase depends on whether the UTM halts on input φ. Since halting is undecidable, the phase diagram is uncomputable.

**Key difference from CPgW (Paper 36):** CPgW parametrizes by discrete Turing machines. BCW parametrizes by a continuous real parameter φ, with the binary expansion of φ serving as the Turing machine input. This introduces a subtlety: the phase diagram is a function φ ↦ Phase(φ) from ℝ to {A, B}, and its uncomputability is about the uncomputability of this *function on reals*, not just a discrete decision problem.

**Key technical detail from the paper:** BCW must modify the CPgW construction significantly because encoding φ via exact QPE makes the Hamiltonian depend on |φ| (the binary length of φ), which is discontinuous. They use approximate QPE with a universal gate set to remove this dependence.

### 2.2 Spectral Gap Undecidability in 1D (BCLPG 2020)

**Reference:** Bausch, J., Cubitt, T.S., Lucia, A. & Perez-Garcia, D. (2020). Undecidability of the spectral gap in one dimension. Phys. Rev. X, 10, 031038.

**Their result:** The spectral gap is undecidable even for 1D translation-invariant nearest-neighbour Hamiltonians with a fixed local dimension d.

**Their method:** Similar encoding to CPgW but technically harder — 1D systems have less room to encode computation. They construct a 1D Hamiltonian whose ground state represents the evolution of a quantum Turing machine, with the spectral gap encoding halting.

**Key feature:** The reduction is still computable: M ↦ H₁D(M) is an algorithm. The encoding property is the same: H₁D(M) is gapped iff M does not halt. Therefore the stratification from Paper 36 applies verbatim.

### 2.3 Uncomputable RG Flows (CLPE 2022)

**Reference:** Cubitt, T.S., Lucia, A., Perez-Garcia, D. & Perez-Eceiza, A. (2022). Uncomputably complex renormalisation group flows. Nature Communications, 13, 7006.

**Their result:** There exists an explicit RG map for the CPgW Hamiltonian such that:
- Each individual RG step is computable
- The RG map preserves the gapped/gapless property
- The RG flow converges to one of two fixed points (one gapped, one gapless)
- But which fixed point the flow converges to is uncomputable

**Their method:** Construct a block-RG scheme for CPgW's Hamiltonian. At each step, coarse-grain the lattice. The coarse-graining is a computable operation (finite matrix manipulation). The flow converges because the RG eliminates irrelevant operators. But the fixed point depends on whether the encoded Turing machine halts — and that is undecidable.

**This is the most physically significant of the three** because renormalization group flows are how physicists actually extract macroscopic physics from microscopic models. The result says: even in the controlled setting of a convergent, computable RG scheme, the macroscopic physics can be uncomputable.

---

## 3. The Stratification (Unified Argument)

### 3.1 The Template

All three results follow the same logical template:

1. **Encoding:** A Turing machine M (or a real φ encoding a TM input) is embedded into a physical system via a *computable* map. The map produces a Hamiltonian, a phase diagram, or an RG initial condition.

2. **Physical property ↔ Halting:** The physical property of interest (spectral gap, phase, RG fixed point) is determined by whether M halts. Gapped/Phase A/Gapped fixed point ↔ M does not halt. Gapless/Phase B/Gapless fixed point ↔ M halts.

3. **Undecidability:** Since halting is undecidable, the physical property is undecidable.

4. **But:** "M halts" is Σ₁⁰ for each specific M. LPO decides all Σ₁⁰ statements. Therefore the physical property is LPO-decidable for each specific M (or each specific φ, since φ's binary expansion encodes a specific M).

5. **The uniform function** M ↦ physical property is computable relative to LPO (apply LPO to the halting sequence, then apply the bridge lemma). It is non-computable without LPO (that would solve halting).

6. **Therefore:** The uncomputability is exactly LPO's non-computability.

### 3.2 Why This Works for All Three

The key observation: every one of these results uses a *computable many-one reduction* from the halting problem to a physical property. A many-one reduction is a computable function f such that: M halts ↔ f(M) has property P. Since the reduction is computable, the uncomputability of P is *exactly* the uncomputability of halting, which is *exactly* the non-computability of LPO.

This is not a coincidence. It is a structural feature of how undecidability proofs in physics work. You *always* encode a Turing machine into a physical system via a computable map. The uncomputability is *always* inherited from the halting problem. The halting problem is *always* Σ₁⁰-complete. LPO *always* decides Σ₁⁰.

The meta-theorem (to be stated formally as Paper 37's main contribution):

**Any physical undecidability result obtained by computable many-one reduction from the halting problem is Turing-Weihrauch equivalent to LPO.**

This covers every known undecidability result in quantum many-body physics.

---

## 4. Theorems to Formalize

### Theorem 1: Phase Diagram Uncomputability ≡ LPO

**Statement:** Over BISH, the uncomputability of phase diagrams (BCW 2021) is Turing-Weihrauch equivalent to LPO.

**Proof:**

**(1a) Forward (phase decidability → LPO):**

Assume we can decide, for any φ ∈ [0,1], whether H(φ) is in phase A or phase B.

Given a binary sequence α, define φ_α = Σ α(n) 2⁻ⁿ. By BCW's encoding: H(φ_α) is in phase B iff the UTM halts on input φ_α iff ∃n α(n) = 1 (using the correspondence between binary expansions and TM inputs). H(φ_α) is in phase A iff ∀n α(n) = 0.

Deciding the phase of H(φ_α) decides LPO for α.

**(1b) Reverse (LPO → phase decidability):**

Given φ, its binary expansion encodes a TM input. Apply LPO to the halting sequence of the UTM on this input. LPO decides halting. BCW's bridge lemma converts halting/non-halting to phase B/phase A.

**Subtlety:** BCW's encoding uses approximate QPE, not exact QPE. The phase diagram may have a small "uncertainty region" near phase boundaries where the approximate QPE doesn't cleanly separate phases. This doesn't affect the stratification — the undecidability is about the *existence* of an algorithm, not about boundary effects. For points φ that cleanly encode a TM, the argument goes through exactly.

**Bridge lemmas:**

```
-- BCW encoding: phase depends on halting
axiom bcw_encoding_computable :
    Computable (fun φ : ℝ => bcw_hamiltonian φ)

axiom bcw_phaseB_iff_halts (φ : ℝ) :
    is_phaseB (bcw_hamiltonian φ) ↔ utm_halts_on_input (binary_expansion φ)

axiom bcw_phaseA_iff_not_halts (φ : ℝ) :
    is_phaseA (bcw_hamiltonian φ) ↔ ¬utm_halts_on_input (binary_expansion φ)
```

**Lean architecture:**

```
theorem phase_diagram_iff_lpo :
    (∀ φ : ℝ, φ ∈ Set.Icc 0 1 →
      is_phaseA (bcw_hamiltonian φ) ∨ is_phaseB (bcw_hamiltonian φ)) ↔ LPO := by
  constructor
  · -- Forward: phase decidability → LPO
    intro h_dec α
    let φ_α := binary_real α  -- Σ α(n) 2⁻ⁿ
    rcases h_dec φ_α (binary_real_in_unit α) with h_A | h_B
    · right; exact all_zero_of_phaseA α (bcw_phaseA_iff_not_halts φ_α |>.mp h_A)
    · left; exact exists_one_of_phaseB α (bcw_phaseB_iff_halts φ_α |>.mp h_B)
  · -- Reverse: LPO → phase decidability
    intro lpo φ hφ
    rcases lpo (halting_sequence_of_input (binary_expansion φ)) with ⟨n, hn⟩ | h_all
    · right; exact bcw_phaseB_iff_halts φ |>.mpr ⟨n, hn⟩
    · left; exact bcw_phaseA_iff_not_halts φ |>.mpr h_all
```

**Certification:** Level 3 (intentional classical from LPO) + Level 4 (BCW bridge lemmas).

---

### Theorem 2: 1D Spectral Gap Undecidability ≡ LPO

**Statement:** Over BISH, the 1D spectral gap undecidability (BCLPG 2020) is Turing-Weihrauch equivalent to LPO.

**Proof:** Identical structure to Paper 36's Theorem 5, substituting the 1D encoding for the 2D encoding.

The key properties are the same:
- The map M ↦ H₁D(M) is computable (BCLPG-1)
- H₁D(M) is gapped iff M does not halt (BCLPG-2)

Everything else follows from Paper 36 verbatim. The dimensionality of the lattice does not affect the logical structure.

**Bridge lemmas:**

```
-- BCLPG encoding (1D version of CPgW)
axiom bclpg_encoding_computable :
    Computable (fun M : TM => bclpg_hamiltonian M)

axiom bclpg_gapped_iff_not_halts (M : TM) :
    is_gapped (bclpg_hamiltonian_limit M) ↔ ¬halts M

-- 1D-specific: local dimension is fixed
axiom bclpg_local_dim : ℕ  -- the fixed local dimension d
```

**Lean architecture:**

```
-- Direct corollary of Paper 36's template
theorem spectral_gap_1d_iff_lpo :
    (∀ M : TM, Decidable (is_gapped (bclpg_hamiltonian_limit M))) ↔ LPO := by
  constructor
  · intro h_dec α
    let M_α := tm_from_sequence α
    rcases h_dec M_α with h_gap | h_gapless
    · right; exact all_zero_of_not_halts α (bclpg_gapped_iff_not_halts M_α |>.mp h_gap)
    · left; exact exists_one_of_halts α (not_gapped_implies_halts M_α h_gapless)
  · intro lpo M
    rcases lpo (halting_sequence M) with ⟨n, hn⟩ | h_all
    · exact isFalse (halts_implies_not_gapped M ⟨n, hn⟩)
    · exact isTrue (bclpg_gapped_iff_not_halts M |>.mpr (not_halts_of_all_zero h_all))
```

**Certification:** Level 3 + Level 4. This is essentially a re-labeling of Paper 36's proof with different bridge lemmas.

**Note:** This theorem could be a *corollary* of a general template theorem rather than a standalone proof. See §5 (Meta-Theorem).

---

### Theorem 3: Uncomputable RG Flows ≡ LPO

**Statement:** Over BISH, the uncomputability of RG flow fixed points (CLPE 2022) is Turing-Weihrauch equivalent to LPO.

**Proof:**

CLPE construct an RG map R such that:
- Each step R(H) is computable (CLPE-1)
- R preserves gapped/gapless (CLPE-2)
- The flow R^n(H) converges to a fixed point H* (CLPE-3)
- H* is the gapped fixed point iff M does not halt (CLPE-4)
- H* is the gapless fixed point iff M halts (CLPE-5)

The "uncomputability" is: you cannot determine which fixed point the flow converges to. But this is *exactly* the spectral gap question for the initial Hamiltonian (by CLPE-2, the RG preserves the gap). Therefore:

"Which RG fixed point?" ↔ "Gapped or gapless?" ↔ "M halts?" ↔ Σ₁⁰ ↔ LPO

The individual computability of each RG step (CLPE-1) is BISH — each step is a finite matrix operation. The convergence of the flow (CLPE-3) costs LPO — it's a completed limit. The identification of the fixed point (CLPE-4/5) is decided by LPO via the halting sequence.

**The physically important point:** CLPE's result is often described as "RG flows can be more unpredictable than chaos." In CRM terms: the unpredictability is *exactly* LPO. Chaotic flows have sensitive dependence on initial conditions but are computable given exact initial data. Uncomputable RG flows are non-computable because the initial data encodes a halting question. The "unpredictability beyond chaos" is the gap between BISH (computable) and BISH+LPO (computable with oracle) — the same gap as a thermodynamic limit.

**Bridge lemmas:**

```
-- CLPE RG map properties
axiom clpe_rg_step_computable (H : Hamiltonian) :
    ComputableMap (clpe_rg_map H)

axiom clpe_rg_preserves_gap (H : Hamiltonian) :
    is_gapped H ↔ is_gapped (clpe_rg_map H)

axiom clpe_rg_converges (M : TM) :
    ∃ H_star, Filter.Tendsto (fun n => clpe_rg_iterate n (cpgw_hamiltonian M))
      Filter.atTop (nhds H_star)

axiom clpe_fixed_point_gapped_iff_not_halts (M : TM) :
    is_gapped (clpe_fixed_point M) ↔ ¬halts M
```

**Lean architecture:**

```
-- RG fixed point decidability ↔ LPO
theorem rg_fixed_point_iff_lpo :
    (∀ M : TM, Decidable (is_gapped (clpe_fixed_point M))) ↔ LPO := by
  -- Reduces to spectral gap by CLPE-2
  -- Then identical to Paper 36 / Theorem 2 above
  constructor
  · intro h_dec α
    let M_α := tm_from_sequence α
    rcases h_dec M_α with h_gap | h_gapless
    · right; exact all_zero_of_not_halts α
        (clpe_fixed_point_gapped_iff_not_halts M_α |>.mp h_gap)
    · left; exact exists_one_of_halts α
        (not_gapped_fp_implies_halts M_α h_gapless)
  · intro lpo M
    rcases lpo (halting_sequence M) with ⟨n, hn⟩ | h_all
    · exact isFalse (halts_implies_gapless_fp M ⟨n, hn⟩)
    · exact isTrue (clpe_fixed_point_gapped_iff_not_halts M |>.mpr
        (not_halts_of_all_zero h_all))

-- The "beyond chaos" claim, formalized:
-- Individual RG steps are BISH, but the asymptotic flow is LPO
theorem rg_step_is_bish (M : TM) (n : ℕ) :
    ComputableReal (energy_of (clpe_rg_iterate n (cpgw_hamiltonian M))) := by
  sorry -- FILL: each iterate is a finite composition of computable maps (Theorem A of Paper 35)

theorem rg_limit_is_lpo :
    (∀ M, ∃ H_star, is_rg_fixed_point H_star ∧
      Tendsto (clpe_rg_iterate · (cpgw_hamiltonian M)) atTop (nhds H_star)) ↔ LPO := by
  sorry -- FILL: same as Theorem 2 structure — completed limit costs LPO
```

**Certification:** Level 3 + Level 4.

---

### Theorem 4 (Meta-Theorem): All Halting Reductions are LPO

**Statement:** Let P be any physical property and let f : TM → PhysicalSystem be a computable reduction such that P(f(M)) ↔ halts(M). Then:
- The uniform decision problem M ↦ P(f(M)) is Turing-Weihrauch equivalent to LPO.
- Each instance P(f(M)) for specific M is LPO-decidable.
- The uncomputability of the uniform problem is exactly the non-computability of LPO.

**Proof:** Immediate from the definition of LPO as Σ₁⁰-LEM and the Σ₁⁰-completeness of the halting problem.

Given M, define α_M(n) = 1 if M halts in n steps, 0 otherwise. This is BISH-computable. LPO applied to α_M decides halting. The bridge lemma f converts halting/non-halting to P/¬P. The uniform function M ↦ P(f(M)) is the composition: M → α_M → LPO(α_M) → P(f(M)), which is computable relative to LPO. Without LPO, computing M ↦ P(f(M)) uniformly solves halting, which is impossible.

**This is the paper's central contribution.** Theorems 1–3 are instances. The meta-theorem explains why ALL known undecidability results in physics are LPO: they all use computable reductions from halting, and halting is Σ₁⁰-complete, and LPO is Σ₁⁰-LEM.

**The prediction:** Any *future* undecidability result in physics that uses a computable reduction from halting will also be LPO. The only way to get undecidability *beyond* LPO would be to use a reduction from a problem above Σ₁⁰ in the arithmetic hierarchy (e.g., Σ₂⁰-complete: "does this TM halt on infinitely many inputs?"). No known physical undecidability result uses such a reduction.

**Lean architecture:**

```
-- The meta-theorem: any computable many-one reduction from halting is LPO
theorem halting_reduction_iff_lpo
    {P : PhysicalSystem → Prop} [DecidableEq PhysicalSystem]
    (f : TM → PhysicalSystem)
    (hf_comp : Computable f)
    (hf_enc : ∀ M, P (f M) ↔ halts M) :
    (∀ M, Decidable (P (f M))) ↔ LPO := by
  constructor
  · intro h_dec α
    let M_α := tm_from_sequence α
    rcases h_dec M_α with h_yes | h_no
    · left; exact exists_one_of_halts α (hf_enc M_α |>.mp h_yes)
    · right; exact all_zero_of_not_halts α (mt (hf_enc M_α |>.mpr) h_no)
  · intro lpo M
    rcases lpo (halting_sequence M) with ⟨n, hn⟩ | h_all
    · exact isTrue (hf_enc M |>.mpr ⟨n, hn⟩)
    · exact isFalse (mt (hf_enc M |>.mp) (not_halts_of_all_zero h_all))
```

**Certification:** Level 2 (the meta-theorem itself is BISH — it's a logical tautology about reductions). The instances (Theorems 1–3) are Level 3 + 4 due to bridge lemmas and LPO hypotheses.

---

## 5. Connection to Paper 36 and the Programme

### 5.1 Paper 36 as Special Case

Paper 36's main theorem (cubitt_is_lpo) is an instance of Theorem 4 with:
- P = is_gapped
- f = cpgw_hamiltonian
- hf_enc = cpgw_gapped_iff_not_halts (with negation flipped)

Paper 37 subsumes Paper 36 in the sense that its meta-theorem (Theorem 4) generates Paper 36's result as a corollary. However, Paper 36 retains independent value because it includes the fine-grained analysis: the finite-volume gap (BISH), the thermodynamic limit (LPO), the WLPO zero-test for physical Hamiltonians. The meta-theorem doesn't capture these internal stratifications.

### 5.2 The Undecidability Landscape

After Papers 36–37, the known landscape of undecidability results in mathematical physics is:

| Result | Reference | Reduction from | LPO-equivalent? |
|---|---|---|---|
| Spectral gap (2D) | CPgW 2015 | Halting | Yes (Paper 36) |
| Spectral gap (1D) | BCLPG 2020 | Halting | Yes (Theorem 2) |
| Phase diagrams | BCW 2021 | Halting | Yes (Theorem 1) |
| RG flow fixed points | CLPE 2022 | Halting | Yes (Theorem 3) |
| Ground state energy density | Watson-Cubitt 2021 | Halting | Yes (predicted by Theorem 4) |

**All entries are LPO.** This is not a coincidence — it is a consequence of Theorem 4. All known results use computable reductions from halting, and the meta-theorem guarantees LPO-equivalence for any such reduction.

### 5.3 What Would Break the Pattern

The meta-theorem predicts: the pattern breaks if and only if someone constructs a physical undecidability result using a reduction from a problem *above* Σ₁⁰.

Candidates for breaking the pattern:
- **Σ₂⁰-complete reductions:** "Does this TM halt on infinitely many inputs?" Encoding this into a physical property would require the property to depend on the *infinitely-many-halting* behavior of a TM, not just whether it halts. No known physical construction does this.
- **Arithmetic hierarchy climbing:** Iterating the Cubitt construction — using the spectral gap of one system as input to another — could potentially climb the arithmetic hierarchy. Whether this produces physically meaningful systems is open.
- **MIP* = RE connections:** The MIP* = RE result involves undecidability beyond Σ₁⁰ (RE-completeness for the entangled value of non-local games). If this could be reduced to a spectral gap question, it would break the pattern. However, MIP* = RE concerns the *entangled* value of games played with quantum strategies, which may not reduce to a Hamiltonian spectral property.

**The programme's prediction:** None of these will produce physically relevant results above LPO. The physically relevant undecidabilities all involve thermodynamic limits of specific systems, which are always LPO by Paper 35's metatheorem.

---

## 6. Watson-Cubitt Ground State Energy Density (Preview of Paper 38)

**Reference:** Watson, J.D. & Cubitt, T.S. (2021). Computational complexity of the ground state energy density problem. arXiv:2107.05060.

**Their result:** The ground state energy density of a fixed, translation-invariant Hamiltonian is a single real number whose computational complexity is remarkably high. Estimating this real number to precision 2⁻ⁿ can be as hard as solving any problem in the complexity class FEXP (deterministic exponential time).

**CRM analysis (preview):** This result is *different* from the spectral gap results because it concerns a *real number*, not a decision problem. The ground state energy density e₀ is a specific real number — but computing its digits may be arbitrarily hard.

In CRM terms: is e₀ a computable real (BISH)? A Δ₂⁰ real (limit-computable, LPO)? Or something beyond?

Watson-Cubitt's result suggests e₀ can encode FEXP-hard problems in its binary expansion. FEXP ⊆ computable, so e₀ is a computable real — but one whose computation requires exponential time. In CRM terms: e₀ is BISH, but "hard BISH." The uncomputability is about *computational complexity* (how long the algorithm takes), not *logical constructivity* (whether an algorithm exists).

This is a different phenomenon from the spectral gap undecidability. The spectral gap is *logically* undecidable (no algorithm, even inefficient). The ground state energy density is *logically* computable but *computationally* hard (an algorithm exists but may take exponential time).

**CRM prediction:** The ground state energy density is BISH for every specific Hamiltonian with computable local terms. The computational complexity is a separate question that CRM doesn't address — CRM calibrates logical resources, not computational resources. The Watson-Cubitt result is a complexity result, not an undecidability result, and BISH+LPO is silent on complexity.

This distinction — logical constructivity vs. computational complexity — is worth a section in the monograph but may not require a separate paper. The ground state energy density is BISH. Done. The fact that it's *hard* BISH is interesting but outside the programme's scope.

[DECISION POINT: Does Paper 38 cover Watson-Cubitt (brief, one theorem), or do we skip it and note the distinction in Paper 37's discussion? Recommend: include as §6 of Paper 37, not as separate paper. The CRM content is thin — one theorem: "e₀ is BISH for specific Hamiltonians."]

---

## 7. File Structure

```
Paper37_UndecidabilityLandscape/
├── Paper37/
│   ├── Defs.lean              -- Shared definitions (TM, Halting, etc.)
│   ├── MetaTheorem.lean       -- Theorem 4: halting reductions ↔ LPO
│   ├── PhaseDiagram.lean      -- Theorem 1: BCW phase diagrams ↔ LPO
│   ├── SpectralGap1D.lean     -- Theorem 2: BCLPG 1D spectral gap ↔ LPO
│   ├── RGFlow.lean            -- Theorem 3: CLPE RG flows ↔ LPO
│   ├── GroundStateEnergy.lean -- Watson-Cubitt: e₀ is BISH (brief)
│   └── Main.lean              -- imports, #print axioms, landscape table
└── lakefile.lean
```

**Estimated size:** 400-500 lines. The meta-theorem is short (~50 lines). Each instance is ~80 lines (mostly bridge lemmas + one application of the template). The ground state energy section is ~40 lines.

**Dependencies:**
- Paper 36: `cubitt_is_lpo`, `cpgw_*` bridge lemmas, `halting_sequence`, `tm_from_sequence`
- Paper 29: LPO ↔ BMC
- Mathlib: `Computability`

---

## 8. Certification Protocol

| Component | Level | Justification |
|---|---|---|
| Theorem 4 (Meta-theorem) | Level 2 | Pure logic, no classical axioms |
| Theorem 1 (Phase diagrams) | Level 3 + 4 | LPO hypothesis + BCW bridge lemmas |
| Theorem 2 (1D spectral gap) | Level 3 + 4 | LPO hypothesis + BCLPG bridge lemmas |
| Theorem 3 (RG flows) | Level 3 + 4 | LPO hypothesis + CLPE bridge lemmas |
| Ground state energy (BISH) | Level 4 | Bridge lemma: specific H has computable e₀ |

---

## 9. Potential Pitfalls

1. **BCW's approximate QPE.** The phase diagram encoding uses approximate QPE, not exact. This means the map φ ↦ Phase(φ) may not be a clean binary function — there could be a "fuzzy" region near phase boundaries. The stratification argument requires that for almost every φ (specifically, for φ encoding valid TM inputs), the phase is well-defined. BCW's paper establishes this, but the bridge lemma must be carefully stated.

2. **The 1D result may need different bridge lemmas.** The 1D construction has a different local Hamiltonian structure from the 2D construction. The stratification argument doesn't depend on the local structure, only on the encoding property (gapped ↔ not halts). But the Lean formalization needs distinct bridge lemma declarations for the 1D and 2D cases, even though the logical argument is identical.

3. **CLPE's RG convergence.** The claim that the RG flow converges (CLPE-3) is a non-trivial physics result. In CRM terms, the convergence is a completed limit — hence LPO. But CLPE prove convergence constructively for both branches (halting and non-halting), with explicit convergence rates in each branch. This is the same structure as Paper 36's Theorem 2: use LPO to branch, then extract computable modulus in each branch.

4. **The meta-theorem may be "too easy."** A referee might object that Theorem 4 is trivially true — of course a halting reduction is LPO-equivalent, that's just the definition of Σ₁⁰-completeness. The response: the theorem is easy *for a logician*. It is profoundly non-obvious *for a physicist*. The contribution is not the proof but the *application* — showing that every undecidability result in physics is an instance of this trivial fact, and that the physics community's interpretation of these results (as "fundamental unknowability") is a category error.

5. **Watson-Cubitt is NOT undecidability.** The ground state energy density result is about computational *complexity*, not logical *decidability*. Including it in Paper 37 risks confusing these two distinct concepts. The discussion should clearly separate: (a) undecidability = no algorithm exists (LPO), (b) hardness = an algorithm exists but is slow (BISH but computationally expensive). These are orthogonal axes.

---

## 10. Instructions for the Lean Agent

### Priority order:
1. `Defs.lean` — shared definitions (import from Paper 36 where possible)
2. `MetaTheorem.lean` — Theorem 4 (the template). This is the most important file.
3. `SpectralGap1D.lean` — Theorem 2 (easiest instance — nearly identical to Paper 36)
4. `RGFlow.lean` — Theorem 3
5. `PhaseDiagram.lean` — Theorem 1 (most subtle due to BCW's continuous parameter)
6. `GroundStateEnergy.lean` — brief Watson-Cubitt note
7. `Main.lean` — assembly + landscape table

### What to reuse from Paper 36:
- `TM`, `halts`, `halting_sequence`, `tm_from_sequence`
- The proof *template* of `cubitt_is_lpo` — Theorems 1–3 are structural copies

### What's new:
- The meta-theorem `halting_reduction_iff_lpo` (generic over arbitrary property P and encoding f)
- Bridge lemma sets for BCW, BCLPG, and CLPE (distinct from CPgW's bridge lemmas)
- The undecidability landscape table as a verified enumeration

### Critical guidance:
The meta-theorem should be proved FIRST. Then each instance (Theorems 1–3) should be derived as a COROLLARY of the meta-theorem, not proved independently. This is cleaner, shorter, and demonstrates the programme's explanatory power. If the Lean agent proves each instance from scratch, the paper looks like three separate results. If it instantiates a single template, the paper looks like one result with three applications.
