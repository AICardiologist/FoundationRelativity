# LPO Formalization Roadmap

## The Core Question

You have two calibrated rungs:
- BISH: finite-volume quantum mechanics (no omniscience needed)
- WLPO ↔ bidual-gap witness for S₁(H)

The next rung is LPO. Two distinct questions arise:

**Question A (equivalence):** Is there a physically natural statement in quantum statistical mechanics that is *equivalent* to LPO over BISH?

**Question B (dispensability):** Can the empirical content of the thermodynamic limit — finite-system predictions with error bounds — be recovered in BISH without passing through LPO?

These are logically independent. A could be true (yes, there's an equivalence) while B is also true (yes, empirical content is recoverable). That would mean: the *idealization* costs LPO, but the *physics* doesn't need it. That combination is exactly your working hypothesis.

---

## Known Facts

1. **Bounded monotone convergence ↔ LPO** over BISH [Bridges-Vîță 2006]. This is the anchor.

2. **Free energy density convergence** in lattice models (Ising, Heisenberg) proceeds by monotone convergence of f_Λ(β) = -|Λ|⁻¹ log Z_Λ(β). The sequence is bounded and monotone (by subadditivity of log Z). So the *existence* of the limit imports LPO via this route.

3. **Finite-volume partition functions** are finite sums of exponentials with rational coefficients — fully constructive, no omniscience.

4. **1D Ising model** has an exact solution (transfer matrix method). The finite-volume free energy and the infinite-volume free energy are both known in closed form. The convergence rate is exponential in system size.

---

## Candidate Problems, Ranked

### Candidate 1: 1D Ising — Finite-Size Bound without Monotone Convergence

**Statement:** For the 1D Ising model at inverse temperature β with N spins, show constructively (in BISH) that |f_N(β) - f_∞(β)| < C·exp(-αN) for explicit C, α depending on β.

**Why it matters:** If you can prove this in BISH, you've shown that the empirical content (finite-system free energy approximates infinite-volume prediction) is BISH-recoverable. The LPO-level monotone convergence was a convenience, not a necessity. This is evidence for Question B (dispensability).

**Likelihood of success: HIGH (85%)**

Reason: The 1D Ising model is exactly solvable. The transfer matrix gives f_∞(β) = -β - log(cosh(βJ)) in closed form (or similar, depending on conventions). The finite-size correction is exponentially small and explicitly computable. The proof that |f_N - f_∞| < ε for given N doesn't need monotone convergence at all — it's a direct calculation with rational arithmetic and elementary inequalities. This should be formalizable in Lean 4 using Mathlib's real analysis library.

**What you learn:** BISH suffices for finite-system empirical content in at least one concrete model. The LPO cost of the thermodynamic limit is an artifact of taking an unnecessary infinite-volume detour.

**Risk:** The result is "too easy" — critics will say the 1D Ising model is trivial and the real challenge is models without exact solutions. Fair, but you have to start somewhere.

---

### Candidate 2: Monotone Convergence of Free Energy ↔ LPO

**Statement:** Over BISH, the following are equivalent:
1. LPO
2. For every translation-invariant finite-range Hamiltonian on ℤ^d, the free energy density f(β) = lim f_Λ(β) exists.

**Why it matters:** This would be a *calibrated* LPO equivalence with direct physical content — the third rung of the ladder, matching the WLPO equivalence in structure.

**Likelihood of success: MODERATE (50%)**

Reason: The forward direction (LPO → limit exists) is straightforward — it's just bounded monotone convergence. The hard direction is backward: given that all free energy limits exist, extract LPO. You'd need to encode a binary sequence into a Hamiltonian such that the convergence behavior of f_Λ detects whether all terms are zero or some term is one. This is the Ishihara-style construction, but for Hamiltonians instead of Banach spaces. It's plausible but requires finding the right encoding. The space of translation-invariant Hamiltonians is rich enough that this might work, but I don't see the construction immediately.

**What you learn:** If it works, LPO is genuinely *equivalent* to thermodynamic-limit existence — not just sufficient. The calibration landscape gets its third verified rung.

**Risk:** The backward direction might fail. It's possible that free energy convergence is strictly weaker than LPO (some special structure of partition functions might allow convergence without full monotone convergence). In that case you'd learn something interesting but wouldn't get the clean equivalence.

---

### Candidate 3: Phase Transition Sharpness Requires LPO

**Statement:** Over BISH, the existence of a sharp (discontinuous) phase transition — a point β_c where the free energy f(β) is non-analytic — implies LPO.

**Why it matters:** This would connect LPO directly to the physical phenomenon van Wierst was discussing, but with a machine-verified proof instead of a philosophical argument.

**Likelihood of success: LOW-MODERATE (35%)**

Reason: Non-analyticity of a real function is a strong property. Constructively, proving a function is non-analytic requires showing that no analytic extension exists, which is a universal statement with existential content. The connection to LPO is plausible (you need to decide whether certain derivatives diverge), but the formalization would require substantial real analysis infrastructure in Lean 4 that may not yet exist in Mathlib.

**What you learn:** The logical cost of *phase transitions themselves* (not just the limit that enables them) is at least LPO.

**Risk:** Mathlib infrastructure gap. You might spend weeks building real-analytic function theory in Lean 4 before you can even state the theorem properly.

---

### Candidate 4: KMS State Uniqueness/Non-Uniqueness at LPO

**Statement:** Over BISH, deciding whether the set of KMS states at inverse temperature β is a singleton or contains multiple elements requires LPO (or some specific omniscience principle).

**Why it matters:** KMS state multiplicity is the algebraic formulation of phase coexistence. This is physically central.

**Likelihood of success: LOW (20%)**

Reason: KMS states are defined via the KMS condition on a C*-algebra, which requires substantial operator algebra infrastructure. Mathlib's C*-algebra library is growing but is nowhere near KMS states. The formalization overhead would be enormous. The mathematical content is also harder to pin down — you'd need to know what "deciding uniqueness" means constructively for a compact convex set of states.

**What you learn:** Deep connection between phase structure and omniscience. But the cost-benefit ratio is poor given current infrastructure.

---

## Recommendation

**Do Candidate 1 first.** It's high-likelihood, directly addresses Question B (dispensability), and produces a concrete Lean-verified result: "the empirical content of the 1D Ising thermodynamic limit is BISH-recoverable." This is a publishable result on its own — a short paper titled something like "Constructive Finite-Size Bounds for the 1D Ising Free Energy: A Lean 4 Formalization."

**Then attempt Candidate 2.** If Candidate 1 succeeds, you know the empirical content is dispensable. Candidate 2 asks whether the *idealization itself* is exactly LPO. Even a partial result (e.g., showing the backward direction for a restricted class of Hamiltonians) would be valuable.

**Skip Candidates 3 and 4** unless Mathlib's analysis and operator algebra libraries improve dramatically in the next year.

---

## What the Combined Results Would Mean

If both Candidates 1 and 2 succeed, you'd have:

- **BISH:** Finite-volume physics, AND finite-size approximations to infinite-volume predictions (empirical content)
- **WLPO ↔** Bidual-gap witness for S₁(H) (singular state existence as positive witness)
- **LPO ↔** Thermodynamic limit existence (the infinite-volume free energy as a completed object)

This is a three-rung calibrated ladder where the physical interpretation is sharp:
- What you can measure: BISH
- What you can't prepare but can't rule out: WLPO
- What requires an infinite idealization to state: LPO

The synthesis paper — if you ever write it — would then have three calibrated rows instead of two, and the pattern would be unmistakable. But the formalization papers would speak for themselves even without the synthesis.

---

## Practical Estimate

**Candidate 1 (1D Ising finite-size bound in Lean 4):**
- Mathematical content: 2-3 pages of standard statistical mechanics
- Lean formalization: ~2,000-4,000 lines, depending on Mathlib coverage of exp, log, finite sums
- Time estimate: 3-6 weeks with AI assistance
- Dependencies: Mathlib real analysis (exp, log, series bounds), finite sums, basic inequalities
- Blocker risk: LOW — the math is elementary; the question is whether Mathlib's API makes it smooth or painful

**Candidate 2 (free energy convergence ↔ LPO):**
- Mathematical content: The backward direction requires a novel encoding argument
- Lean formalization: ~3,000-5,000 lines
- Time estimate: 6-12 weeks, with significant uncertainty on the backward direction
- Dependencies: Candidate 1 infrastructure + the encoding construction
- Blocker risk: MODERATE — the backward direction might not exist as a clean equivalence
