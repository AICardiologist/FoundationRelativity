# Paper 36: Stratifying Spectral Gap Undecidability

## Cubitt's Theorem is LPO: Macroscopic Quantum Undecidability Costs Exactly One Thermodynamic Limit

### Proof Document for Lean 4 Formalization

**Series:** Constructive Reverse Mathematics of Mathematical Physics
**Author:** Paul Chun-Kit Lee
**Architectural Guidance:** Claude (Anthropic), Math Genius Agent

---

## 1. Executive Summary

Cubitt, Perez-Garcia, and Wolf (Nature 2015) proved that the spectral gap problem is undecidable: no algorithm determines whether an arbitrary translation-invariant Hamiltonian on a 2D lattice is gapped or gapless in the thermodynamic limit. This result is widely interpreted as demonstrating that macroscopic quantum physics contains fundamentally unknowable truths.

This paper proves that interpretation is wrong — or more precisely, that it conflates two distinct mathematical phenomena.

**Main Theorem (Stratification):** Cubitt's spectral gap undecidability is Turing-Weihrauch equivalent to the Limited Principle of Omniscience (LPO). The uniform spectral gap function is computable relative to LPO and non-computable without it. Since LPO is already required for thermodynamic limits (Paper 29), phase transitions (Paper 29), and gauge coupling existence (Paper 32), Cubitt's undecidability introduces zero additional logical resources into physics.

**The sentence:** The spectral gap is undecidable for the same reason, and at the same logical cost, as boiling water.

**Stratification across the constructive hierarchy:**

| Level | Content | Mechanism |
|---|---|---|
| BISH | Finite-volume spectral gap Δ_L is computable | Algebraic eigenvalue computation |
| WLPO | "Is Δ = 0 or Δ > 0?" for a specific physical Hamiltonian | Zero-test on completed real |
| LPO | Thermodynamic limit Δ = lim Δ_L exists | BMC / Cauchy completeness |
| LPO | Each specific instance of Cubitt's family is decidable | LPO decides Σ₁⁰ (halting for specific M) |
| BISH^LPO | The uniform function M ↦ gapped/gapless | Computable relative to LPO oracle |
| Non-computable | The uniform function without oracle | = Halting problem = non-computability of LPO itself |

The bottom row — the only row that is "undecidable" — is not a new phenomenon. It is the non-computability of LPO, which the programme has known about since Paper 1. Cubitt discovered that the spectral gap encodes this non-computability. The programme reveals that it encodes *nothing else*.

---

## 2. Background

### 2.1 Cubitt-Perez-Garcia-Wolf (CPgW)

**The construction:** Given a Turing machine M, CPgW construct a translation-invariant, nearest-neighbour Hamiltonian H(M) on the 2D square lattice ℤ² with local dimension d (originally ~10⁸, later reduced). The construction has two key properties:

**(CPgW-1)** The map M ↦ H(M) is computable. Given M's transition table, one can algorithmically produce the local interaction terms of H(M).

**(CPgW-2)** H(M) is gapped if and only if M does NOT halt. H(M) is gapless if and only if M halts.

Since the halting problem is undecidable, the spectral gap problem is undecidable.

**Technical details of the encoding:**
- When M does not halt, H(M) is in a stable, translation-invariant gapped phase. The gap is bounded away from zero.
- When M halts at step T, the Hamiltonian undergoes a phase transition at a lattice size determined by T. For L >> T, the ground state energy density changes and the gap closes.
- The finite-volume gaps Δ_L are computable for each L (finite-dimensional eigenvalue problem).
- The gaps Δ_L are NOT monotone in L — they fluctuate before the lattice size exceeds the halting time T.

**References:**
- Cubitt, T.S., Perez-Garcia, D., & Wolf, M.M. (2015). Nature, 528, 207-211.
- Extended version: arXiv:1502.04135 (140+ pages).
- Bausch, Cubitt, Lucia, Perez-Garcia (2020). Phys. Rev. X, 10, 031038. (1D extension)

### 2.2 The CRM Programme's Relevant Results

**Paper 29 (Fekete ≡ LPO):** BMC ↔ LPO. Phase transitions require LPO. LPO is physically instantiated.

**Paper 26 (Gödel-Gap Correspondence):** Π₁⁰ arithmetic order-embeds into ℓ∞/c₀. WLPO is the meeting point of physical measurement limits and arithmetic incompleteness.

**Paper 33 (QCD mass gap):** The mass gap Δ > 0 costs Markov's Principle (subsumed by LPO). Finite lattice spectral gap is BISH.

**Paper 35 (Conservation Metatheorem):** LPO sits at Σ₁⁰ in the arithmetic hierarchy. Physics never exceeds Σ₁⁰.

### 2.3 The Key Identification

LPO, in computability-theoretic terms, is the Σ₁⁰ oracle — the oracle that decides statements of the form ∃n P(n) for decidable P. This is exactly the halting oracle: "M halts" is ∃n (M halts in n steps), which is Σ₁⁰.

Therefore: LPO = halting oracle (for individual instances). This identification is standard in computability theory but has never been applied to Cubitt's result.

---

## 3. Theorems to Formalize

### Theorem 1 (Sub-Result 1): Finite-Volume Spectral Gap is BISH

**Statement:** For any Turing machine M and any finite lattice Λ of size L × L, the spectral gap Δ_L(M) = E₁(L) - E₀(L) is a BISH-computable real number.

**The hidden trap (identified by Math Genius):**

Computing the spectral gap requires finding the two smallest *distinct* eigenvalues. Deciding whether two eigenvalues are equal (E₀ = E₁?) costs WLPO in general. If we can't decide degeneracy, we can't identify the first excited state.

**The BISH bypass:**

CPgW's Hamiltonians are finite matrices with rational (in fact algebraic) entries, because M's transition table is finite and the encoding uses rational coefficients. Therefore:

1. The characteristic polynomial p(λ) = det(H - λI) has algebraic coefficients. Computable in BISH via exact rational arithmetic on the (exponentially large but finite) matrix.

2. Compute the square-free part q(λ) of p(λ) using Euclidean polynomial GCD. This eliminates repeated roots. BISH — polynomial GCD is a finite algorithm.

3. The roots of q(λ) are the *distinct* eigenvalues. Since algebraic reals form a decidable ordered field, we can isolate and sort these roots using Sturm sequences. BISH.

4. The gap is the difference between the two smallest roots of q(λ). Computable. BISH.

**Note on complexity:** The matrix is d^(L²) × d^(L²), which is exponentially large. "Computable in BISH" means the gap exists as a computable real with an explicit algorithm, NOT that the algorithm is efficient. Computational complexity is orthogonal to constructive status. BISH certifies logical existence, not polynomial runtime.

**Lean architecture:**

```
-- Bridge lemma: CPgW Hamiltonians have algebraic matrix entries
axiom cpgw_algebraic_entries (M : TM) (L : ℕ) :
    AlgebraicMatrix (cpgw_hamiltonian M L)

-- Algebraic eigenvalues are BISH-computable (via square-free factorization)
-- This is axiomatized because constructive algebraic geometry is a
-- multi-year Mathlib project beyond our scope
axiom algebraic_eigenvalues_computable (A : AlgebraicMatrix) :
    ∃ (eigs : List AlgebraicReal), eigs = sorted_distinct_eigenvalues A

-- Main: finite-volume gap is BISH
theorem fin_vol_gap_is_BISH (M : TM) (L : ℕ) :
    ComputableReal (spectral_gap (cpgw_hamiltonian M L)) := by
  sorry -- FILL: apply algebraic_eigenvalues_computable, extract gap from sorted list
  -- The gap is eigs[1] - eigs[0] where eigs is the sorted distinct eigenvalue list
```

**Certification:** Level 4 (axiomatized). The algebraic eigenvalue computation is BISH in principle but impractical to formalize. The axiom `algebraic_eigenvalues_computable` is well-justified by constructive algebra (Mines, Richman, Ruitenburg — "A Course in Constructive Algebra").

---

### Theorem 2 (Sub-Result 2): Thermodynamic Limit Costs Exactly LPO

**Statement:** Over BISH, asserting that the thermodynamic limit Δ(M) = lim_{L→∞} Δ_L(M) exists for all Turing machines M in CPgW's family is equivalent to LPO.

**Proof (Forward: Limit existence → LPO):**

Assume: for every M, the limit Δ(M) = lim Δ_L(M) exists as a completed real.

Goal: derive LPO.

Given an arbitrary binary sequence α, construct a Turing machine M_α that halts iff ∃n α(n) = 1. (Standard construction: M_α searches through α sequentially and halts when it finds a 1.)

By CPgW-2: H(M_α) is gapless iff M_α halts iff ∃n α(n) = 1.

By hypothesis, Δ(M_α) exists as a completed real. By CPgW's bounds, Δ(M_α) ∈ {0} ∪ [γ, ∞) for some fixed γ > 0 (the Hamiltonian is either gapless with gap 0, or gapped with gap bounded below by a computable constant).

Compute a rational approximation q to Δ(M_α) with |Δ(M_α) - q| < γ/2.

If q < γ/2: then Δ(M_α) < γ, so Δ(M_α) = 0 (the gap is either 0 or ≥ γ), so M_α halts, so ∃n α(n) = 1.

If q ≥ γ/2: then Δ(M_α) > 0, so M_α does not halt, so ∀n α(n) = 0.

This decides LPO for α. Since α was arbitrary, we have LPO.

**Proof (Reverse: LPO → Limit existence):**

Assume LPO. Given M, apply LPO to the halting sequence of M: β(n) = 1 if M halts in n steps, 0 otherwise. LPO decides: either M halts (at some step T) or M does not halt.

**Case 1 (M halts at step T):** CPgW's physics guarantees that for L sufficiently larger than T (specifically, L > f(T) for a computable function f derived from the encoding), the gap Δ_L = 0. The halting time T provides an explicit computable modulus of convergence: for all L > f(T), |Δ_L - 0| = 0 < ε for any ε. By Paper 35 Theorem B1, a limit with computable modulus is BISH.

**Case 2 (M does not halt):** CPgW's physics guarantees the Hamiltonian is in a stable gapped phase. The gap Δ_L converges to some Δ∞ > 0. The stability of the gapped phase provides a computable modulus (the gap convergence rate is determined by the spectral properties of the infinite-volume Hamiltonian, which are uniform in the absence of a phase transition).

In both cases, the limit exists with a computable modulus (provided by LPO's case distinction). The case distinction itself uses LPO. Therefore: LPO suffices for the thermodynamic limit.

**The subtlety (flagged by Math Genius):**

The sequence Δ_L is NOT monotone. Unlike the Ising free energy (Paper 8), the finite-volume gaps in CPgW's construction fluctuate wildly before the lattice size exceeds the halting time. You cannot apply BMC/Fekete directly. The proof works by using LPO *first* to branch the logical context, then extracting a Cauchy modulus separately in each branch. This is a different proof architecture from Paper 29 — there, the monotonicity was intrinsic. Here, the monotonicity emerges only *after* LPO resolves the halting question.

**Bridge lemma needed:**

```
-- CPgW asymptotic behavior: axiomatizes the key physics
-- In halting case: gap closes with computable rate
axiom cpgw_halting_asymptotics (M : TM) (T : ℕ) (hT : halts_at M T) :
    ∃ (f : ℕ → ℕ), ∀ L > f T, spectral_gap (cpgw_hamiltonian M L) = 0

-- In non-halting case: gap stabilizes with computable rate
axiom cpgw_nonhalting_asymptotics (M : TM) (hM : ¬halts M) :
    ∃ (Δ∞ : ℝ) (μ : ℕ → ℕ),
      Δ∞ > 0 ∧
      ∀ k, ∀ L > μ k, |spectral_gap (cpgw_hamiltonian M L) - Δ∞| < (2 : ℝ)⁻¹ ^ k

-- The gap dichotomy: gap is either 0 or bounded below
axiom cpgw_gap_dichotomy (M : TM) :
    ∃ (γ : ℝ), γ > 0 ∧ ∀ M, thermo_limit_gap M ∈ ({0} : Set ℝ) ∪ Set.Ici γ
```

**Lean architecture:**

```
-- Main equivalence
theorem cpgw_thermo_limit_iff_lpo :
    (∀ M : TM, ∃ Δ : ℝ, Filter.Tendsto (fun L => spectral_gap (cpgw_hamiltonian M L))
      Filter.atTop (nhds Δ)) ↔ LPO := by
  constructor
  · -- Forward: limit existence → LPO
    intro h_lim
    intro α
    -- Construct M_α from α
    let M_α := tm_from_sequence α
    -- Get the limit
    obtain ⟨Δ, hΔ⟩ := h_lim M_α
    -- Approximate Δ within γ/2
    -- Branch on approximation
    sorry -- FILL: rational approximation, case split, CPgW-2
  · -- Reverse: LPO → limit existence
    intro lpo M
    -- Apply LPO to halting sequence of M
    rcases lpo (halting_sequence M) with ⟨n, hn⟩ | h_all
    · -- M halts: apply cpgw_halting_asymptotics
      sorry -- FILL: extract T, apply bridge lemma, exhibit Cauchy modulus
    · -- M doesn't halt: apply cpgw_nonhalting_asymptotics
      sorry -- FILL: apply bridge lemma, exhibit Cauchy modulus

-- #print axioms cpgw_thermo_limit_iff_lpo
-- Expected: cpgw_halting_asymptotics, cpgw_nonhalting_asymptotics,
--           cpgw_gap_dichotomy, tm_from_sequence (all bridge lemmas)
--           Classical.choice (from LPO hypothesis in reverse direction — Level 3)
```

**Certification:** Level 3 (intentional classical) in the reverse direction. Level 4 (axiomatized physics) for bridge lemmas. The forward direction is Level 2 (structurally verified).

---

### Theorem 3 (Sub-Result 3): Pointwise Decidability is Σ₁⁰ (LPO)

**Statement:** For any specific Turing machine M, the question "Is H(M) gapped or gapless?" is decidable given LPO.

**Proof:**

1. Define α_M : ℕ → {0,1} by α_M(n) = 1 if M halts in n steps, 0 otherwise. This is BISH-computable (simulate M for n steps — a finite computation).

2. Apply LPO to α_M: either ∃n α_M(n) = 1 (M halts) or ∀n α_M(n) = 0 (M doesn't halt).

3. By CPgW-2: if M halts, H(M) is gapless. If M doesn't halt, H(M) is gapped.

The entire argument is a single application of LPO to a computable sequence, followed by a bridge lemma. No additional logical resources needed.

**Lean architecture:**

```
-- Halting sequence is BISH-computable
def halting_sequence (M : TM) : ℕ → Fin 2 :=
  fun n => if simulates_and_halts M n then 1 else 0

-- Pointwise decidability
theorem pointwise_gap_decidable (M : TM) (lpo : LPO) :
    (is_gapped (cpgw_hamiltonian_limit M)) ∨
    (is_gapless (cpgw_hamiltonian_limit M)) := by
  rcases lpo (halting_sequence M) with ⟨n, hn⟩ | h_all
  · right; exact cpgw_gapless_of_halts M ⟨n, hn⟩
  · left; exact cpgw_gapped_of_not_halts M h_all
```

**Certification:** Level 3 (intentional classical — LPO is the hypothesis).

---

### Theorem 4 (Sub-Result 4): Physical Hamiltonians' Zero-Test is WLPO

**Statement:** For a specific physical Hamiltonian (not from CPgW's family) whose thermodynamic-limit spectral gap Δ exists as a completed real, deciding "Δ = 0 or Δ > 0" costs exactly WLPO.

**Proof:**

Forward (WLPO → decision): Given Δ ≥ 0 (physical gaps are non-negative). WLPO decides: Δ = 0 or ¬(Δ = 0). Since Δ ≥ 0, ¬(Δ = 0) implies Δ > 0 (by Markov's Principle, which WLPO implies for non-negative reals).

Reverse (decision → WLPO): Given an arbitrary binary sequence α, construct a physical Hamiltonian whose gap encodes α (e.g., the Ising model with field h = Σ α(n) 2⁻ⁿ — Paper 20's construction). The gap is zero iff h = 0 iff ∀n α(n) = 0. Deciding the gap decides WLPO.

**Connection to Paper 26:** This is the physical instantiation of the Gödel-Gap embedding. The Π₁⁰ sentence "∀n α(n) = 0" maps to the physical question "is the spectral gap zero?" Both are WLPO.

**Connection to Paper 33:** The QCD mass gap (Δ_QCD > 0) is exactly this: a WLPO zero-test on a specific physical Hamiltonian's completed gap. Paper 33 calibrated it at Markov's Principle, subsumed by WLPO.

**Lean architecture:**

```
-- Physical gap zero-test is WLPO
theorem physical_gap_zero_test_iff_wlpo :
    (∀ Δ : ℝ, Δ ≥ 0 → (Δ = 0 ∨ Δ > 0)) ↔ WLPO := by
  sorry -- FILL: forward is MP + WLPO; reverse encodes α into Ising field
```

**Certification:** Level 2 (structurally verified) for both directions.

---

### Theorem 5 (Sub-Result 5): Uniform Problem is LPO-Computable

**Statement:** The uniform function G : TM → {Gapped, Gapless} defined by G(M) = Gapped if ¬halts(M), G(M) = Gapless if halts(M), is:
- (a) Not computable (no Turing machine computes G)
- (b) Computable relative to LPO (BISH^LPO-computable)

**This is the paper's central theorem.** It says Cubitt's undecidability is *exactly* the non-computability of LPO — nothing more, nothing less.

**Proof of (a): G is not computable.**

If G were computable, then for any M, we could compute G(M) and thereby decide halting. Since halting is undecidable, G is not computable. Standard. BISH.

**Proof of (b): G is computable relative to LPO.**

Given M:
1. Compute α_M(n) = 1 if M halts in n steps, 0 otherwise. (BISH — finite simulation.)
2. Apply LPO to α_M. (This is a single oracle call.)
3. If ∃n α_M(n) = 1: output Gapless. If ∀n α_M(n) = 0: output Gapped.

The composition (step 1 is computable, step 2 is the oracle, step 3 is a case split) is a computable function relative to LPO. The function is *uniform* — the same algorithm works for every M. No additional oracle calls or non-constructive principles are needed beyond LPO.

**The identification:** Cubitt's spectral gap function is a many-one reduction from the Halting problem. The Halting problem is Σ₁⁰-complete. LPO is the Σ₁⁰ oracle. Therefore the spectral gap function is computable relative to LPO. This is a standard fact in computability theory; what is new is applying it to Cubitt's specific construction and interpreting it through the CRM programme.

**Lean architecture:**

```
-- The uniform spectral gap function
def spectral_gap_decision : TM → Prop :=
  fun M => is_gapped (cpgw_hamiltonian_limit M)

-- (a) Not computable
theorem gap_not_computable :
    ¬ Computable spectral_gap_decision := by
  sorry -- FILL: reduce to halting, standard diagonal argument

-- (b) Computable relative to LPO
theorem gap_computable_relative_to_lpo :
    ∀ M : TM, LPO → Decidable (spectral_gap_decision M) := by
  intro M lpo
  rcases lpo (halting_sequence M) with ⟨n, hn⟩ | h_all
  · exact isFalse (cpgw_gapless_of_halts M ⟨n, hn⟩)
  · exact isTrue (cpgw_gapped_of_not_halts M h_all)

-- The main identification: Cubitt's undecidability IS LPO's uncomputability
theorem cubitt_is_lpo :
    (∀ M, Decidable (spectral_gap_decision M)) ↔ LPO := by
  constructor
  · -- Forward: uniform decidability → LPO
    intro h_dec α
    let M_α := tm_from_sequence α
    rcases h_dec M_α with h_gap | h_gapless
    · right; exact all_zero_of_gapped M_α h_gap
    · left; exact exists_one_of_gapless M_α h_gapless
  · -- Reverse: LPO → uniform decidability
    intro lpo M
    exact gap_computable_relative_to_lpo M lpo

-- #print axioms cubitt_is_lpo
-- Expected: cpgw bridge lemmas (Level 4), tm_from_sequence (Level 4)
-- NO Classical.choice in the forward direction
-- Classical.choice from LPO in the reverse direction (Level 3, intentional)
```

**Certification:** Forward direction Level 2 + Level 4 bridge lemmas. Reverse direction Level 3 (intentional classical from LPO).

---

### Theorem 6 (Synthesis): The Stratification Theorem

**Statement (Main Theorem of Paper 36):**

The Cubitt-Perez-Garcia-Wolf spectral gap undecidability is Turing-Weihrauch equivalent to LPO over BISH. Specifically:

(i) The finite-volume spectral gap is BISH-computable for every Hamiltonian in CPgW's family (Theorem 1).

(ii) The thermodynamic limit of the spectral gap exists iff LPO holds (Theorem 2).

(iii) Each specific instance of CPgW's family is LPO-decidable (Theorem 3).

(iv) The zero-test on a completed physical spectral gap is WLPO (Theorem 4).

(v) The uniform spectral gap function is computable relative to LPO and non-computable without it (Theorem 5).

(vi) Consequently, Cubitt's undecidability introduces no logical resources beyond LPO — the same principle required for thermodynamic limits (Paper 29), coupling constants (Paper 32), and phase transitions (Paper 29). Macroscopic quantum undecidability costs exactly one thermodynamic limit.

**Lean architecture:**

```
-- The stratification theorem: assembles all sub-results
theorem stratification :
    -- (i) Finite-volume is BISH
    (∀ M L, ComputableReal (spectral_gap (cpgw_hamiltonian M L))) ∧
    -- (ii) Thermo limit ↔ LPO
    ((∀ M, ∃ Δ, Tendsto (fun L => spectral_gap (cpgw_hamiltonian M L)) atTop (nhds Δ)) ↔ LPO) ∧
    -- (iii) Pointwise ↔ LPO
    ((∀ M, Decidable (is_gapped_limit M)) ↔ LPO) ∧
    -- (iv) Zero-test ↔ WLPO
    ((∀ Δ ≥ 0, Δ = 0 ∨ Δ > 0) ↔ WLPO) ∧
    -- (v) Uniform is LPO-computable but not computable
    (¬Computable spectral_gap_decision) ∧
    (LPO → ∀ M, Decidable (spectral_gap_decision M)) := by
  exact ⟨fin_vol_gap_is_BISH,
         cpgw_thermo_limit_iff_lpo,
         cubitt_is_lpo,
         physical_gap_zero_test_iff_wlpo,
         gap_not_computable,
         gap_computable_relative_to_lpo⟩
```

---

## 4. Connection to Paper 26 (Gödel-Gap Correspondence)

Paper 36 is the physical realization of Paper 26's abstract embedding.

Paper 26 proved: Π₁⁰ arithmetic sentences order-embed into ℓ∞/c₀, with WLPO as the logical barrier governing the embedding.

Cubitt's construction does the physical version of exactly this:

1. The Turing machine state M is encoded into local translation-invariant tensor interactions. This is the physical analogue of Paper 26's map from Π₁⁰ sentences to elements of ℓ∞.

2. The sequence of finite-volume gaps (Δ₁, Δ₂, Δ₃, ...) is a sequence in ℓ∞ (bounded by the operator norm). This is the physical analogue of the sequence in ℓ∞ that Paper 26 constructs from a Π₁⁰ sentence.

3. The thermodynamic limit projects this sequence into the quotient ℓ∞/c₀ (modding out by sequences that vanish at infinity). The gap is zero iff the sequence is in c₀. This is literally Paper 26's embedding.

4. The zero-test — "Is Δ = 0 or Δ > 0?" — is WLPO, exactly as in Paper 26.

Paper 26 identified the abstract structure. Cubitt built the physical hardware. Paper 36 proves they are the same construction at different levels of realization.

**The hierarchy of results:**

```
Paper 26: Π₁⁰ sentences embed into ℓ∞/c₀ (abstract, WLPO)
     ↓ (physical realization)
Cubitt: TM halting encodes into spectral gaps (concrete, LPO)
     ↓ (stratification via CRM)
Paper 36: Cubitt's undecidability ≡ LPO (identification)
```

---

## 5. What This Means for Physics

### 5.1 For Condensed Matter Physicists

Cubitt's result, as currently understood in the condensed matter community, says: "there exist materials whose spectral gap you can never determine." This creates anxiety — does this mean my lattice simulation is pointless? Can I trust my DMRG calculation?

Paper 36 says: your simulation is fine. For any specific material — any *one* Hamiltonian — the spectral gap is LPO-decidable. The undecidability applies only to the problem of building a single algorithm that works for *all possible* materials simultaneously. Since you study specific materials, not all possible materials, Cubitt's undecidability is irrelevant to your practice.

The analogy: the halting problem says you can't build a universal bug-detector for all possible programs. This doesn't mean you can't debug any specific program. Cubitt says you can't build a universal gap-detector for all possible Hamiltonians. This doesn't mean you can't determine the gap of any specific Hamiltonian.

### 5.2 For Foundations of Physics

Cubitt's result is often cited as evidence that physics contains "Gödelian" phenomena — truths that are fundamentally inaccessible. Paper 36 shows this interpretation is precisely wrong. Cubitt's undecidability is not Gödelian (which would involve self-reference and incompleteness at a meta-mathematical level). It is *computational* — it is the non-computability of LPO, the same non-computability that governs thermodynamic limits.

The spectral gap is undecidable in the same way, for the same reason, and at the same logical cost as the assertion "this bounded monotone sequence converges." Physicists have been comfortable with the non-computability of limits for centuries. Cubitt's result is a new instance of this old phenomenon, not a new kind of undecidability.

### 5.3 For the CRM Programme

Paper 36 is the first application of the programme's framework to an *external* result — a famous theorem proved by other mathematicians, reinterpreted through the constructive hierarchy. This demonstrates the programme's value as an *analytical tool*, not just a classification scheme.

The stratification also provides the sharpest possible test of the BISH+LPO characterization. Cubitt's Hamiltonians are the most pathological quantum systems ever constructed — they were built specifically to encode undecidability. If even these systems live at BISH+LPO (which they do — each instance is LPO-decidable), then the characterization has survived its most severe stress test.

---

## 6. File Structure

```
Paper36_CubittStratification/
├── Paper36/
│   ├── Defs.lean                -- TM, CPgW encoding, spectral gap definitions
│   ├── BridgeLemmas.lean        -- CPgW-1, CPgW-2, asymptotics axioms
│   ├── FiniteGap.lean           -- Theorem 1: finite-volume gap is BISH
│   ├── ThermoLimit.lean         -- Theorem 2: thermo limit ↔ LPO
│   ├── Pointwise.lean           -- Theorem 3: pointwise LPO-decidability
│   ├── ZeroTest.lean            -- Theorem 4: physical gap zero-test ↔ WLPO
│   ├── UniformDecidability.lean -- Theorem 5: uniform function ↔ LPO
│   ├── Stratification.lean      -- Theorem 6: main assembly
│   └── Main.lean                -- imports, #print axioms
└── lakefile.lean
```

**Estimated size:** 400-600 lines. The paper is conceptually deep but Lean-light. Most theorems are short once the bridge lemmas are stated. The hardest Lean work is Theorem 2 (the non-monotone limit argument with LPO branching).

**Dependencies:**
- Paper 29: LPO ↔ BMC (import the equivalence)
- Paper 26: WLPO ↔ Gödel-Gap (for the Paper 26 connection, Theorem 4)
- Paper 33: QCD mass gap calibration (for physical context in Theorem 4)
- Mathlib: `Computability` (Turing machines), `Topology.Algebra.Order` (limits), basic real analysis

---

## 7. Certification Protocol

| Component | Level | Justification |
|---|---|---|
| Theorem 1 (finite gap BISH) | Level 4: Axiomatized | Algebraic eigenvalue computation axiomatized |
| Theorem 2 forward (limit → LPO) | Level 2 + Level 4 | Structurally verified + CPgW bridge lemmas |
| Theorem 2 reverse (LPO → limit) | Level 3 + Level 4 | Intentional classical (LPO) + CPgW bridge lemmas |
| Theorem 3 (pointwise LPO) | Level 3 | Intentional classical (LPO hypothesis) |
| Theorem 4 (zero-test WLPO) | Level 2 | Both directions structurally verified |
| Theorem 5a (not computable) | Level 2 | Standard diagonal, no classical |
| Theorem 5b (LPO-computable) | Level 3 | Intentional classical (LPO hypothesis) |
| Theorem 6 (assembly) | Inherits from components | |

---

## 8. Potential Pitfalls

1. **CPgW bridge lemma accuracy.** The asymptotics axioms (halting case: gap closes with computable rate; non-halting case: gap stabilizes with computable rate) must faithfully represent CPgW's 140-page proof. The computable modulus claims are physically motivated but not trivially extracted from their paper. A careful reading of the extended arXiv version (1502.04135) is needed to verify these claims. If the convergence rate in the non-halting case is not explicitly computable from CPgW's proof, the bridge lemma is weaker and Theorem 2's reverse direction requires additional work.

2. **The square-free factorization in Theorem 1.** The BISH bypass works for algebraic matrices. If CPgW's construction involves irrational entries (transcendental coupling constants, for instance), the square-free factorization argument fails and the degeneracy trap returns. Verify that CPgW's encoding uses only rational/algebraic coefficients.

3. **The identification LPO = halting oracle.** This is standard in classical computability theory. In the constructive setting, some care is needed: LPO is a *principle* (an axiom), not a *function* (an oracle). The statement "computable relative to LPO" means "provable in BISH+LPO," which is the constructive analogue of "computable with a Σ₁⁰ oracle." This identification should be made explicit in the Lean formalization.

4. **Turing-Weihrauch equivalence.** The theorem statement uses "Turing-Weihrauch equivalent." This is a specific notion of equivalence in computable analysis (Weihrauch reducibility). The Lean formalization may use a simpler notion (logical equivalence over BISH) rather than full Weihrauch reducibility, which would require formalizing Weihrauch degrees. This is acceptable — the logical equivalence captures the essential content.

5. **Later refinements of CPgW.** Bausch et al. (2020) extended undecidability to 1D. The stratification theorem applies equally to 1D — the argument depends only on CPgW-1 and CPgW-2, not on the spatial dimension. The 1D case should be noted as a corollary, not a separate theorem.

---

## 9. The Sentence

For the paper's abstract:

> The spectral gap undecidability of Cubitt, Perez-Garcia, and Wolf is Turing-Weihrauch equivalent to the Limited Principle of Omniscience — the same logical principle required for thermodynamic limits and phase transitions. Relativized to LPO, the uniform spectral gap problem is decidable. Macroscopic quantum undecidability introduces no logical resources beyond those already required to boil water.

For the monograph (Chapter 8):

> Cubitt et al. proved that the spectral gap is undecidable uniformly. The CRM programme proves that each instance is decidable at LPO, and the uniform function is computable relative to LPO. The undecidability is the non-computability of LPO itself — the same non-computability that makes thermodynamic limits non-algorithmic. The spectral gap problem and the existence of phase transitions are logically identical phenomena.

For a condensed matter physicist:

> The spectral gap of your specific material is decidable. Cubitt's undecidability applies to the impossible task of building a single algorithm for all possible materials. Since you study specific materials, the undecidability is irrelevant to your work.

---

## 10. Instructions for the Lean Agent

### Priority order:
1. `Defs.lean` — TM encoding, CPgW Hamiltonian type, spectral gap definition
2. `BridgeLemmas.lean` — all CPgW axioms (CPgW-1, CPgW-2, asymptotics, gap dichotomy)
3. `UniformDecidability.lean` — Theorem 5: the main identification (cubitt_is_lpo)
4. `Pointwise.lean` — Theorem 3 (trivial once bridge lemmas exist)
5. `ZeroTest.lean` — Theorem 4 (connect to Paper 26)
6. `ThermoLimit.lean` — Theorem 2 (hardest — the non-monotone branching argument)
7. `FiniteGap.lean` — Theorem 1 (axiomatize — don't try to formalize algebraic eigenvalues)
8. `Stratification.lean` + `Main.lean` — assembly

### What to reuse:
- Paper 29: `LPO`, `BMC`, `bmc_iff_lpo`
- Paper 26: `WLPO`, Gödel-Gap embedding (for Theorem 4 connection)
- Paper 33: QCD mass gap calibration (for physical context)
- Paper 35: `CRMCategory`, calibration table structure

### What's new:
- `TM` (Turing machine) type — may use Mathlib's `Computability.TM`
- `cpgw_hamiltonian` — the CPgW encoding (axiomatized)
- `spectral_gap` — for finite and infinite volume
- `halting_sequence` — the BISH-computable sequence α_M
- `tm_from_sequence` — the reverse encoding (binary sequence → TM)
- `cubitt_is_lpo` — the main theorem

### Critical warning:
The bridge lemmas axiomatize CPgW's physics. They must be stated carefully:
- `cpgw_encoding_computable`: the map M ↦ H(M) is computable (essential for the reduction)
- `cpgw_gapped_iff_not_halts`: H(M) is gapped ↔ M doesn't halt (the core encoding)
- `cpgw_halting_asymptotics`: in the halting case, gap closes with computable rate
- `cpgw_nonhalting_asymptotics`: in the non-halting case, gap stabilizes with computable rate
- `cpgw_gap_dichotomy`: gap is either 0 or ≥ γ for some fixed γ > 0

Do NOT introduce `Classical.choice` into the bridge lemmas themselves. They should be pure axioms, not classical proofs. The only `Classical.choice` in the entire formalization should come from LPO hypotheses in Theorems 2 (reverse), 3, and 5b.
