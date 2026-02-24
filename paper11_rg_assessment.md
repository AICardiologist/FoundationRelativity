# Paper 11: The Constructive Cost of Renormalization

## Project Assessment — February 2026

---

## The Question

What is the constructive cost of the ultraviolet (UV) / continuum limit in quantum field theory? The thermodynamic limit (IR, infinite-volume) was calibrated to LPO in Paper 8. The UV limit — removing the short-distance cutoff — is the other great idealization of theoretical physics. Does it calibrate to the same principle, a different one, or something new?

---

## Candidate 1: Gaussian Free Field Continuum Limit

### Setup

The Gaussian free field in d dimensions with UV cutoff Λ has covariance (Green's function):

G_Λ(x,y) = ∫_{|k|<Λ} e^{ik·(x−y)} / (k² + m²) dk

The continuum limit is Λ → ∞.

### Proof Draft

**Part A (Dispensability).** The finite-cutoff error is:

|G_Λ(x,y) − G(x,y)| = |∫_{|k|>Λ} e^{ik·(x−y)} / (k² + m²) dk| ≤ ∫_{|k|>Λ} 1/(k² + m²) dk

For d = 3, this integral equals C/(Λ + O(1/Λ)) for an explicit constant C depending on m. For d = 2, it's C·log(m/Λ) + O(1/Λ). Both bounds are BISH-computable. The finite-cutoff theory approximates the continuum answer with constructive error bounds.

**Part B (Calibration).** For the massive theory (m > 0), G_Λ(x,y) is monotone increasing in Λ (each shell |k| ∈ [Λ, Λ+dΛ] adds a positive contribution since the integrand is positive for real k). The sequence is bounded above by G(x,y) = ∫_{ℝ^d} ... dk < ∞ for d ≥ 2, m > 0. So convergence is BMC ↔ LPO.

Backward direction: encode α : ℕ → {0,1} into the mass parameter of successive shells, making convergence of G_Λ decide α. Same encoding strategy as Paper 8.

### Verdict

**Logical cost: LPO (same as thermodynamic limit).**

Novelty: Low. The mathematical structure is identical to Paper 8 — monotone bounded convergence. The UV limit of the free field is just BMC in a different physical context. A referee would say: "This is Paper 8 with a Fourier transform."

Effort: ~2 weeks Lean formalization (reuses Paper 8 infrastructure, adds Fourier analysis for the error bound).

Probability of success: 95%.

**Recommendation: Skip.** Confirms the table without extending it.

---

## Candidate 2: φ⁴ Theory in 2D (Rigorous Construction)

### Setup

The 2D φ⁴ theory was rigorously constructed by Glimm-Jaffe (1970s). The UV divergence is logarithmic, requiring only mass renormalization. The continuum limit exists as a weak limit of finite-cutoff measures after subtracting a mass counterterm δm²(Λ) ~ g·log(Λ).

### Proof Draft (Sketch)

The construction proceeds in three stages:

**Stage 1.** Finite-volume, finite-cutoff: a finite-dimensional integral. BISH.

**Stage 2.** Remove UV cutoff (Λ → ∞): The renormalized measures {μ_Λ} form a tight family on the space of tempered distributions S'(ℝ²). Existence of the limit uses Prokhorov's theorem: tightness implies relative compactness in the space of probability measures. This is a compactness extraction — not monotone convergence but Bolzano-Weierstrass on a function space.

**Stage 3.** Remove IR cutoff (V → ∞): thermodynamic limit, same as Paper 8.

### Constructive Audit of Stage 2

Prokhorov's theorem in full generality uses sequential compactness of probability measures on Polish spaces. In the constructive hierarchy, sequential compactness of [0,1]^ℕ is equivalent to WKL (Weak König's Lemma), which in the classical reverse math setting is strictly between RCA₀ and ACA₀. The constructive analogue: extracting a convergent subsequence from a bounded sequence in a complete metric space requires at least LPO (it's a form of Bolzano-Weierstrass).

However, the Glimm-Jaffe construction is more specific than generic Prokhorov. The correlation functions satisfy uniform bounds (Nelson's hypercontractive estimates) and the convergence can potentially be established through explicit estimates rather than compactness extraction. If so, the logical cost might reduce to LPO (or even BISH for the finite-precision content).

### Verdict

**Logical cost: Likely LPO, possibly higher if compactness extraction is essential.**

Novelty: High. This would be the first constructive audit of a nontrivial renormalization. The answer — whether the UV limit costs exactly LPO or something more — is genuinely unknown.

Effort: 6–12 months minimum. The Glimm-Jaffe construction is hundreds of pages. The Lean formalization would require building Nelson's hypercontractive estimates, Euclidean field theory axioms, and measure theory on infinite-dimensional spaces from scratch. None of this exists in Mathlib.

Probability of success: 20%. The formalization is out of reach. Even a pen-and-paper constructive audit would be a substantial research project.

**Recommendation: Flag as a long-term target. Do not attempt now.**

---

## Candidate 3: Block-Spin RG for the 1D Ising Model (Decimation)

### Setup

The Kadanoff block-spin renormalization group for the 1D Ising model with blocking factor b = 2 (decimation: integrate out every other spin) yields an exact recursion on the coupling constant K = βJ:

tanh(K') = tanh(K)²

Equivalently, K' = arctanh(tanh(K)²).

The RG fixed points are K* = 0 (high-temperature / disordered) and K* = ∞ (zero-temperature / ordered). For any 0 < K < ∞, the RG orbit K → K' → K'' → ... converges to K* = 0.

### Proof Draft

**Definitions.** Let R : ℝ₊ → ℝ₊ be the RG map R(K) = arctanh(tanh(K)²). Let K^(0) = K and K^(n+1) = R(K^(n)).

**Lemma 1 (RG map is constructive).** R is a composition of tanh, squaring, and arctanh, all of which are constructively defined continuous functions on their domains. R is BISH-definable.

**Lemma 2 (Monotone decrease).** For K > 0: R(K) < K.

*Proof.* tanh(K) ∈ (0,1) for K > 0, so tanh(K)² < tanh(K), so arctanh(tanh(K)²) < arctanh(tanh(K)) = K. □

**Lemma 3 (Bounded below).** K^(n) > 0 for all n (since tanh and arctanh preserve positivity).

**Lemma 4 (Super-exponential convergence rate).** Let t = tanh(K). Then tanh(K^(n)) = t^{2^n}. The coupling satisfies:

K^(n) = arctanh(t^{2^n}) ≤ 2·t^{2^n}

for t^{2^n} < 1/2 (using arctanh(x) ≤ 2x for x ∈ [0, 1/2]). The bound is BISH-computable: given any ε > 0, we can constructively find N such that K^(N) < ε, namely any N > log₂(log(1/(2ε)) / log(1/t)).

**Part A (Dispensability).** The finite-step RG approximation K^(n) ≈ 0 has error bounded by 2·t^{2^n}, which is BISH-computable. Any physical quantity derived from the RG fixed point can be approximated to arbitrary precision by n steps of the constructive RG map, with explicit error bounds, in BISH.

For example, the correlation length ξ = −1/log(tanh(K)) of the original system can be recovered from n RG steps as ξ = 2^n · ξ^(n) where ξ^(n) = −1/log(tanh(K^(n))). The finite-step approximation converges super-exponentially, with BISH-computable error.

**Part B (Calibration).** The assertion that lim_{n→∞} K^(n) exists as a completed real number is an instance of BMC (bounded monotone convergence): K^(n) is monotone decreasing and bounded below by 0. By the Bridges-Vîță equivalence, this is equivalent to LPO over BISH.

Backward direction (LPO-hardness): encode α : ℕ → {0,1} into perturbations of the RG orbit. Define:

K̃^(0) = K, and K̃^(n+1) = R(K̃^(n)) + α(n)·δ_n

where δ_n > 0 is chosen small enough that the perturbed orbit remains monotone decreasing and bounded, but large enough that convergence of K̃^(n) to a limit decides whether α is eventually zero. Specifically, set δ_n = c·t^{2^n} for a small constant c. Then:

- If (∀n)(α(n) = 0), the orbit is the unperturbed orbit, converging to 0.
- If (∃n₀)(α(n₀) = 1), the orbit receives a kick at step n₀ but still converges (the kicks are summable). The limit is 0 in either case, but the *rate of convergence* differs detectably.

Actually, a cleaner encoding: define a coupling-dependent sequence. Given α, set K_α = K₀ + Σ_n α(n)·2^{−n}·ε for small ε. The RG orbit of K_α converges to 0 for any α (since any finite K flows to 0). The limit exists iff BMC holds for this particular sequence, and BMC ↔ LPO. This inherits the Paper 8 encoding through the initial condition rather than through perturbation of the dynamics — cleaner.

**Part C (New observation: the RG map is BISH, the fixed point is LPO).** This is the conceptual payoff. Decompose the renormalization group into:

- The RG transformation R: a constructive map. BISH.
- Finite RG iteration R^n: a constructive computation. BISH.
- The RG fixed point as lim R^n: requires BMC. LPO.
- Physical predictions extracted from finite iterations: BISH (with explicit error bounds from Lemma 4).

The logical cost of renormalization is not in the *renormalization* — it is in the *assertion that renormalization has a limit*. The constructive content of the RG is its finite approximations; the non-constructive content is the completed fixed point.

### Lean Formalization Plan

**Module structure** (estimated ~500–700 lines of new code, building on Paper 8):

1. `RGMap.lean` (~80 lines): Define R(K) = arctanh(tanh(K)²), prove continuity, monotonicity, positivity preservation.

2. `RGOrbit.lean` (~100 lines): Define K^(n) by iteration, prove monotone decrease (Lemma 2), bounded below (Lemma 3).

3. `RGRate.lean` (~120 lines): Prove tanh(K^(n)) = tanh(K)^{2^n} by induction. Derive the super-exponential bound (Lemma 4).

4. `RGDispensability.lean` (~100 lines): State and prove the BISH error bound for finite-step RG. Mark with \leanok. The `#print axioms` certificate should show no classical axioms.

5. `RGCalibration.lean` (~150 lines): The BMC ↔ LPO instantiation. Forward: LPO → BMC → RG orbit converges. Backward: encode α into initial coupling, reduce convergence to BMC. Reuse `LPO_equiv_BMC` from Paper 8.

6. `RGCorrelationLength.lean` (~80 lines): Optional. Show the correlation length extraction ξ = 2^n · ξ^(n) is BISH with explicit error propagation.

**Dependencies:** Paper 8's `LPO_equiv_BMC`, `tanh`/`arctanh` from Mathlib or Paper 8's transfer matrix modules, basic real analysis.

### Verdict

**Logical cost: LPO (same principle, new mechanism).**

Novelty: Medium-high. The result itself — RG fixed point costs LPO — is not surprising given Paper 8. But the *decomposition* (map is BISH, iteration is BISH, limit is LPO) is new and directly addresses the "constructive cost of renormalization" question. This is the first formal statement that renormalization per se is constructive; only the assertion of a fixed point is not.

The table gains a new row:

| Layer | Principle | Status | Source |
|---|---|---|---|
| Finite-volume physics | BISH | Calibrated | Trivial |
| Finite-size approximations | BISH | Calibrated | Paper 8, Part A |
| RG map and finite iterations | BISH | Calibrated | **Paper 11** |
| Bidual-gap / singular states | ≡ WLPO | Calibrated | Papers 2, 7 |
| Thermodynamic limit existence | ≡ LPO | Calibrated | Paper 8, Part B |
| RG fixed point existence | ≡ LPO | Calibrated | **Paper 11** |
| Spectral gap decidability | Undecidable | Established | Cubitt et al. 2015 |

The new rows (RG map = BISH, RG fixed point = LPO) tell a story that the old rows don't: the *dynamics* of scale transformation are constructive, but the *endpoint* is not. This is a finer-grained statement about renormalization than "the continuum limit costs LPO."

Effort: ~3 weeks. 1 week for the mathematics (clean up the proof draft above), 2 weeks for the Lean formalization (building on Paper 8 modules). The 1D Ising RG is elementary — no new hard analysis.

Probability of success: 85%. The mathematics is straightforward. The main risk is the encoding in Part B: the backward direction (RG convergence → LPO) needs a clean encoding that doesn't feel artificial. The proposed encoding through the initial condition is natural but needs checking. If the backward direction fails, you still have a one-directional result (LPO → RG fixed point exists), which is weaker but publishable as a route-costing.

**Recommendation: Do this one.**

---

## Candidate 4: Wilson's Lattice Gauge Theory (U(1) or SU(2))

### Setup

Wilson's lattice formulation: gauge fields U_ℓ ∈ G on links, action S = β Σ_P (1 − Re Tr U_P / dim(G)). The continuum limit is lattice spacing a → 0 with β(a) tuned by asymptotic freedom (non-abelian) or triviality (abelian in 4D).

### Constructive Audit (Sketch)

Finite-lattice theory: a finite-dimensional integral over G^{|links|}. BISH (G is compact Lie, the integral is a finite product of Haar integrals).

Continuum limit: requires a → 0. For non-abelian theories (QCD), the continuum limit is the Yang-Mills millennium problem — not rigorously constructed. Cannot audit what doesn't exist.

For compact U(1) in 4D: believed to be trivial (continuum limit is free field). The triviality proof is not rigorous. If it were, the constructive audit would reduce to Candidate 1 (Gaussian free field), giving LPO.

### Verdict

**Logical cost: Unknown (continuum limit not rigorously constructed for interesting cases).**

Novelty: Very high if achievable. Zero chance of achieving it.

Effort: Years to decades. No Lean infrastructure for Lie groups on lattices.

Probability of success: < 5%.

**Recommendation: Completely out of scope. Ignore.**

---

## Summary and Recommendation

| Candidate | Logical Cost | Novelty | Effort | P(success) | Recommend |
|---|---|---|---|---|---|
| 1. Gaussian free field | LPO | Low | 2 weeks | 95% | Skip |
| 2. φ⁴ in 2D | LPO (likely) | High | 6–12 months | 20% | Long-term |
| 3. Block-spin RG, 1D Ising | LPO | Medium-high | 3 weeks | 85% | **Yes** |
| 4. Lattice gauge theory | Unknown | Very high | Years | <5% | No |

**Candidate 3 is the clear choice.** It directly addresses Problem 6 of Paper 10 ("What are the logical costs of renormalization?") with a clean answer: the RG map is BISH, the RG fixed point is LPO. It reuses Paper 8 infrastructure, requires modest new Lean code (~500–700 lines), and the conceptual payoff — separating the constructive cost of the dynamics from the cost of the endpoint — is genuine and not available from the other candidates.

The result doesn't change the calibration *level* (it's still LPO), but it adds *resolution*: the table now distinguishes the RG map (BISH) from the RG fixed point (LPO), showing that renormalization itself is constructive. That's a substantive claim about the structure of quantum field theory, not just another instance of BMC.

**Decision point:** If after Paper 8 and Paper 9 you want one more formalization paper before the synthesis (Paper 10), this is it. If you want to stop, Paper 10 already has enough calibrated entries to be publishable — Problem 6 stays open and you flag it honestly. The marginal value of Paper 11 is real but not essential.

---

## If We Proceed: Timeline

- Week 1: Clean up proof draft, verify backward encoding, write mathematical exposition.
- Week 2: Lean formalization of RGMap, RGOrbit, RGRate, RGDispensability.
- Week 3: Lean formalization of RGCalibration (LPO equivalence), integration testing, `#print axioms` verification.
- Week 4: Paper writeup, update Paper 10's calibration table, submit.

Total: ~4 weeks from start to submission-ready draft. Can overlap with Paper 9 (formulation-invariance) since the codebases are independent.
