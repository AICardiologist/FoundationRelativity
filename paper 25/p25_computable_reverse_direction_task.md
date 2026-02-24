# P25 Task: Type-Level Computable Reverse Direction

## Objective

Prove the reverse direction of the CC ↔ Mean Ergodic equivalence in a way that is **non-trivial in Lean 4** — i.e., cannot be short-circuited by `Classical.choice`.

The current reverse direction (`meanErgodic_implies_cc` in `MeanErgodicReverse.lean`) is a classical triviality: it discards the Mean Ergodic hypothesis and proves CC directly via `Classical.choice`. This tells us nothing about constructive strength. We want a proof where the Mean Ergodic hypothesis is *actually used* and `Classical.choice` cannot substitute for it.

## Core Idea

Lean 4 distinguishes `Prop` (proof-irrelevant, classical) from `Type` (computationally relevant). `Classical.choice` gives you `Prop`-level existence but cannot produce `Type`-level witnesses without computational content. By reformulating CC and Mean Ergodic at the `Type` level, we force the reverse direction to do genuine mathematical work.

## Phase 1: Define Computable Choice Principles (Type-level)

Create a new file `Computable.lean`.

### Computable CC

```lean
/-- Countable Choice at the Type level: given a sequence of nonempty types,
    produce an actual choice function — not just a Prop-level existence proof. -/
def CC_N_computable :=
  ∀ (A : ℕ → Type) [inst : ∀ n, Nonempty (A n)], (n : ℕ) → A n
```

**Critical check**: Verify that `CC_N_computable` is NOT provable in Lean without `Classical.choice` leaking through. Test this:

```lean
-- This should FAIL or require Classical.choice in #print axioms
noncomputable def cc_test : CC_N_computable :=
  fun A inst n => @Classical.choice (A n) (inst n)
```

If `cc_test` compiles, it will be `noncomputable` (because `Classical.choice` is noncomputable). That's actually fine — it means a `computable` (no `noncomputable` marker) proof of `CC_N_computable` would demonstrate genuine computational content. The distinction we care about is `computable` vs `noncomputable`.

**Alternative formulation if the above doesn't give clean separation:**

```lean
/-- Constructive CC: produce a choice function together with a proof that
    it could have been computed by a specific algorithm. We encode this
    by requiring the choice function to be defined by a provided strategy. -/
structure CC_N_constructive where
  choose : ∀ (A : ℕ → Type) [∀ n, Nonempty (A n)], (n : ℕ) → A n
  /-- The choice function is definable without classical axioms -/
  computable_witness : True  -- placeholder; see discussion below
```

The exact formulation may need iteration. The key invariant: **a proof of the computable/constructive CC must use the hypothesis, not classical logic.**

### Computable DC

```lean
/-- Dependent Choice at the Type level. -/
def DC_computable :=
  ∀ (X : Type) (R : X → X → Prop) [∀ x, ∃ y, R x y] (x₀ : X),
    Σ (f : ℕ → X), f 0 = x₀ ∧ ∀ n, R (f n) (f (n + 1))
```

Note the `Σ` (sigma type) instead of `∃` (existential in Prop). This forces a computable witness.

## Phase 2: Computable Mean Ergodic Theorem

Create or modify to define a Type-level version of the Mean Ergodic conclusion.

The key output of the Mean Ergodic Theorem that we need at the Type level is the **computable convergence rate**. The theorem says Cesàro averages converge; the computable version says: given ε, I can compute N such that ‖A_n x − Px‖ < ε for all n ≥ N.

```lean
/-- Computable Mean Ergodic: Cesàro averages converge with a computable modulus. -/
structure MeanErgodicComputable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →L[ℝ] H) (hU : Isometry U) where
  /-- The projection onto Fix(U) -/
  proj : H → H
  /-- Computable modulus of convergence: given x and ε, produce N -/
  modulus : H → (ε : ℝ) → (hε : 0 < ε) → ℕ
  /-- The modulus is correct -/
  modulus_spec : ∀ x ε (hε : 0 < ε) (n : ℕ),
    modulus x ε hε ≤ n → ‖cesaro U n x - proj x‖ < ε
```

**Important**: Check whether the existing forward proof (`meanErgodic_of_cc`) already implicitly computes such a modulus. The 600-line proof builds the convergence constructively — it may already contain the rate, just wrapped in `Prop` existentials. If so, unwrapping it to `Type` level may be straightforward.

## Phase 3: The Encoding (This Is the Hard Part)

Prove:

```lean
theorem meanErgodic_computable_implies_cc_computable :
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
       (U : H →L[ℝ] H) (hU : Isometry U),
       MeanErgodicComputable H U hU) →
    CC_N_computable
```

### Encoding Strategy

Given: a sequence of nonempty types `A : ℕ → Type` with `[∀ n, Nonempty (A n)]`.
Goal: produce a function `(n : ℕ) → A n` using only the Mean Ergodic theorem.

**Construction outline:**

1. **Build a Hilbert space from the choice problem.**

   For each n, `A n` is nonempty. Consider the "indicator" construction:
   
   Define `H = ℓ²(ℕ)` (standard separable Hilbert space — this is in Mathlib as `lp 2 ℕ`).
   
   Actually, we need H to encode information about the `A n`. Consider:
   
   For each n, let `B n = if A n is inhabited then 1 else 0` — but this is classical and defeats the purpose.
   
   **Better approach**: Use a direct sum of finite-dimensional spaces indexed by n, where the dimension of the n-th component is determined by a "probe" of `A n`.

   **Alternative — the shift approach:**
   
   Define a unitary operator U on ℓ²(ℕ × ℕ) (or ℓ²(ℕ) with a suitable decomposition into blocks) such that:
   - The n-th block is a cyclic shift of dimension determined by `A n`
   - The Cesàro limit in the n-th block encodes a choice from `A n`
   
   The key insight: the Cesàro average of a cyclic shift of order k converges to the uniform distribution over the cycle. If we can read off which cycle element we're at from the limit, and the cycle elements correspond to elements of `A n`, we've extracted a choice.

   **Concrete attempt:**
   
   For each n, since `A n` is nonempty, pick a "canonical probe" — but wait, picking an element is exactly CC, which is what we're trying to prove. So the encoding must avoid choosing from `A n` until the Mean Ergodic output gives it to us.
   
   This is the crux of the difficulty. The Hilbert space construction itself seems to require knowing something about `A n` that we can only get from CC.

2. **Alternative: encode via characteristic functions.**

   Suppose `A n ⊆ ℕ` for simplicity (this is WLOG if we're working with countable types).
   
   Define: `x ∈ ℓ²(ℕ)` by `x(k) = 1` if `k` encodes a pair `(n, a)` with `a ∈ A n`, and `x(k) = 0` otherwise.
   
   Define: U = right shift on ℓ².
   
   The Cesàro average of U^k x converges to the projection of x onto Fix(U) = {constant sequences} ∩ ℓ² = {0}.
   
   This doesn't obviously extract choices. The projection is just zero.

3. **Alternative: direct sum of ergodic systems.**

   For each n, build a separate ergodic system (H_n, U_n) such that:
   - H_n is finite-dimensional (e.g., ℂ^2 or ℝ^2)
   - U_n is a rotation by an angle θ_n that encodes information about A n
   - The Cesàro limit depends on whether A n has an element with a certain property
   
   Then H = ⊕_n H_n (ℓ²-direct sum), U = ⊕_n U_n.
   
   The Mean Ergodic conclusion gives convergence in each component, which extracts information from each A n.
   
   **Problem**: How does the Cesàro limit *select* an element of A n? The limit is the projection onto Fix(U_n). If U_n is an irrational rotation, Fix(U_n) = {0}, which gives no information. If U_n = Id, Fix(U_n) = H_n, which gives too much.

4. **The honest difficulty.**

   The encoding problem is: construct a Hilbert space and unitary operator *without making choices from the A n*, such that the Mean Ergodic conclusion *produces* choices from the A n. This is a bootstrapping problem. The construction of the Hilbert space must use only the *nonemptiness* of A n (a Prop-level fact), not actual elements (Type-level data). The Mean Ergodic theorem must then upgrade this Prop-level information to Type-level data.
   
   This is exactly the Prop-to-Type lifting that `Classical.choice` does — but we're asking the Mean Ergodic theorem to do it instead. The question is whether the analytical content of mean ergodic convergence provides enough computational content to perform this lifting.

### Fallback: Weaker But Still Non-Trivial Results

If the full encoding doesn't work, consider these partial results that would still be non-trivial at the Type level:

**Option A: CC for ℕ-valued sequences.**

Restrict to `A : ℕ → Set ℕ` (subsets of ℕ) with `∀ n, (A n).Nonempty`. Prove that MeanErgodicComputable implies a computable choice function for this restricted case. The encoding is easier because elements of `A n` are natural numbers and can be encoded directly in ℓ².

**Option B: Weaker extraction.**

Instead of extracting a full choice function, show that MeanErgodicComputable implies *some* non-trivial computational content that is not available without it. For example: a computable modulus of convergence for the mean ergodic theorem on a *specific* family of operators implies the ability to compute witnesses for a specific family of choice instances. This would be a "local" reverse rather than a full equivalence, but it would still demonstrate that the Mean Ergodic hypothesis is doing computational work.

**Option C: The contrapositive approach.**

Show that without CC (in some precise sense), MeanErgodicComputable fails for a specific system. This means: construct a Hilbert space H and unitary U such that MeanErgodicComputable for (H, U) implies CC_N_computable. This is the standard reverse-math move — you don't need to encode *arbitrary* choice problems, just *one* that's hard enough.

For this, consider:
- H = ℓ²(ℕ × ℕ)
- U = a carefully chosen block-diagonal unitary where the n-th block is an operator whose fixed space is nontrivial iff A n is nonempty
- The computable projection onto Fix(U) restricted to the n-th block would yield an element of A n

**This is probably the most promising approach.** You're not encoding arbitrary choice problems into arbitrary ergodic systems. You're building ONE specific system where the Mean Ergodic output implies choice. The Lean proof would:
1. Define the specific H and U
2. Assume MeanErgodicComputable for this specific (H, U)
3. Extract a choice function from the computable modulus

## Phase 4: Verification

Once any version of the reverse direction compiles:

1. `#print axioms` on the theorem. If it shows `[propext, Quot.sound]` or similar WITHOUT `Classical.choice`, that's the gold standard — a genuinely constructive proof in classical Lean.

2. If it shows `Classical.choice`, check WHERE it enters. It might enter through Mathlib lemmas about Hilbert spaces (which is fine — the analytical infrastructure is classical) as opposed to entering through the choice extraction (which would defeat the purpose).

3. The key test: does `#print axioms` show anything beyond what the FORWARD direction uses? If the reverse direction has the same axiom profile as `meanErgodic_of_cc`, it's using classical logic for analysis but not for the choice extraction itself. That's the realistic best case.

## Time Box

**2 weeks maximum.** Here's the suggested allocation:

- Days 1-2: Phase 1 (computable definitions). This should be quick.
- Days 3-4: Phase 2 (computable Mean Ergodic). Check if existing proof already has the rates.
- Days 5-10: Phase 3 (the encoding). Try Option C first (specific system, contrapositive). If stuck after 5 days, try Option A (restricted to ℕ-valued). If stuck after 8 days, try Option B (weaker extraction).
- Days 11-14: Phase 4 (verification, cleanup, documentation).

**Exit criteria:**
- SUCCESS: A theorem `meanErgodic_computable_implies_cc_computable` (or a meaningful variant) that compiles with `Classical.choice` appearing only in analytical lemmas, not in the choice extraction. `#print axioms` confirms.
- PARTIAL SUCCESS: A weaker result (Option A, B, or C) that demonstrates non-trivial computational extraction. Document what works and what the obstacles are.
- FAILURE: No encoding compiles. Document what was tried, what broke, and why. This information is valuable for the paper even in failure — it sharpens the conjecture and identifies exactly where the difficulty lies.

**In case of failure**: The bundle is already wrapped and publishable as-is (upper bounds paper). This attempt is a high-risk/high-reward addition. Do not let it block publication.

## Summary

The goal is to make Lean 4 do something it wasn't designed for: prove a constructive reverse-mathematics result despite being a classical system. The trick is to use the Prop/Type distinction as a proxy for the classical/constructive distinction. If it works, we have a machine-checked proof that the Mean Ergodic theorem has the computational strength of Countable Choice — a result that would be credible, novel, and impossible to dismiss. If it doesn't work, we learn something about the limits of this approach and publish the forward-direction paper.
