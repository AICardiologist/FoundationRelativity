# Axiom Calibration of Black Hole Entropy:
# Spin Network State Counting and the Bekenstein-Hawking Formula

## Paper 17 — Proof Draft for Lean 4 Formalization

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose and Formalization Notes

This document provides a complete, step-by-step mathematical proof for
the axiom calibration of the Bekenstein-Hawking black hole entropy
formula S = A/4 as derived from loop quantum gravity (LQG) spin
network state counting.

**What we show:** Over BISH, the following results hold:

**Part A (BISH):** For any finite horizon area A > 0 and Immirzi
parameter γ > 0, the number of admissible spin configurations
N(A, γ, δ) is a computable natural number, and the entropy
S(A) = log N(A, γ, δ) is a computable real. The leading-order
ratio S(A)/A converges to γ₀/(4γ) where γ₀ is the critical
Immirzi value — and this convergence has a BISH-computable rate.

**Part B (LPO):** The assertion that S(A)/A converges to a completed
real number as A → ∞ is equivalent to Bounded Monotone Convergence
(BMC), hence to LPO over BISH.

**Part C (Open — the discovery module):** The subleading logarithmic
correction S(A) = γ₀A/(4γ) - (3/2)log(A) + O(1) is investigated
for its constructive content. The coefficient -3/2 arises from
saddle-point asymptotics of the generating function. We determine
whether this requires omniscience beyond BISH.

**Expected axiom readout:**
- Part A: Clean. No Classical.choice beyond Lean metatheory.
- Part B: Classical.choice appears in exactly the BMC↔LPO bridge.
- Part C: Unknown a priori — this is the research question.

**Why this matters:** String theory and LQG both derive S = A/4.
If LQG's derivation has strictly lower logical cost than string
theory's (which requires Calabi-Yau compactification, D-brane
counting, AdS/CFT identification — none of which are formalizable
without importing the full landscape apparatus), the axiom
calibration framework provides a principled, formally grounded
criterion for preferring one derivation over the other. This is
the first application of CRM to quantum gravity.

**Dependencies:** This formalization is self-contained. It does NOT
depend on any previous paper's codebase. It uses only Mathlib for
basic real analysis, combinatorics, and number theory.

---

## 1. Mathematical Background

### 1.1 The Bekenstein-Hawking Formula

Classical black hole thermodynamics assigns entropy S = A/(4ℓ_P²)
to a black hole with horizon area A, where ℓ_P is the Planck
length. In natural units (ℓ_P = 1), this is S = A/4.

### 1.2 LQG Horizon Model

In loop quantum gravity, the black hole horizon is punctured by
edges of a spin network. Each puncture i carries a spin label
j_i ∈ {1/2, 1, 3/2, 2, ...} (positive half-integers). The area
contribution of puncture i is:

  a_i = 8πγℓ_P² √(j_i(j_i + 1))

where γ is the Immirzi parameter. In Planck units:

  a_i = 8πγ √(j_i(j_i + 1))

The total area of a configuration (j_1, ..., j_N) is:

  A_total = Σᵢ aᵢ = 8πγ Σᵢ √(jᵢ(jᵢ + 1))

### 1.3 The State Counting Problem

Fix a macroscopic area A > 0 and a tolerance δ > 0. The number of
admissible configurations is:

  N(A, γ, δ) = |{ (j_1,...,j_N) : N ≥ 1, jᵢ ∈ {1/2, 1, 3/2,...},
                   |A_total - A| ≤ δ }|

The entropy is S(A, γ, δ) = log N(A, γ, δ).

### 1.4 The Immirzi Parameter

The Immirzi parameter γ is fixed by demanding S(A)/A → 1/4 as
A → ∞. This yields a specific value γ₀ determined by:

  γ₀ = the unique solution of: lim_{A→∞} S(A,γ)/A = 1/4

The existence and value of γ₀ are determined by the asymptotic
analysis in Part C.

### 1.5 Notation

Throughout this document:
- ℕ⁺ = {1, 2, 3, ...} (positive naturals)
- HalfInt⁺ = {1/2, 1, 3/2, 2, ...} (positive half-integers)
- For j ∈ HalfInt⁺: C(j) = √(j(j+1)) (Casimir square root)
- For j ∈ HalfInt⁺: a(j) = 8πγ · C(j) (area eigenvalue)
- log denotes natural logarithm throughout

---

## 2. Definitions (Lean Module: Defs.lean)

### 2.1 Half-Integer Type

```
structure HalfInt where
  twice : ℕ    -- stores 2j, so j = twice/2
  pos : twice ≥ 1  -- ensures j ≥ 1/2
```

**Lean note:** Represent half-integers as natural numbers storing 2j.
This avoids rationals entirely. All arithmetic on half-integers
reduces to natural number arithmetic on the `twice` field.

### 2.2 Casimir Value

For j with `twice = k` (so j = k/2):

```
def casimir_sq (j : HalfInt) : ℚ :=
  (j.twice : ℚ) * (j.twice + 2) / 4
  -- This is j(j+1) = (k/2)(k/2 + 1) = k(k+2)/4
```

**Key property:** casimir_sq is strictly increasing in j.twice.
Proof: if k₁ < k₂ then k₁(k₁+2) < k₂(k₂+2) since both factors
are larger. This is finite arithmetic. BISH.

### 2.3 Area Eigenvalue

```
def area_eigenvalue (gamma : ℝ) (j : HalfInt) : ℝ :=
  8 * Real.pi * gamma * Real.sqrt (casimir_sq j)
```

**Key property:** area_eigenvalue is strictly increasing in j (since
casimir_sq is, and sqrt is monotone). Minimum value at j = 1/2:

  a_min = 8πγ √(3/4) = 4πγ√3

This is the **area gap** — the smallest nonzero area eigenvalue.

### 2.4 Spin Configuration

A configuration is a finite list of positive half-integers:

```
def SpinConfig := List HalfInt
```

The total area of a configuration:

```
def total_area (gamma : ℝ) (config : SpinConfig) : ℝ :=
  config.map (area_eigenvalue gamma) |>.sum
```

### 2.5 Admissible Configurations

```
def admissible (A gamma delta : ℝ) (config : SpinConfig) : Prop :=
  |total_area gamma config - A| ≤ delta
```

### 2.6 Bounded Admissible Set

**Critical lemma for Part A:** The set of admissible configurations
is finite. Proof: each puncture contributes at least a_min to the
total area. So the number of punctures N satisfies N ≤ (A + δ)/a_min.
Each spin j satisfies a(j) ≤ A + δ, hence j ≤ j_max where
a(j_max) ≤ A + δ < a(j_max + 1/2). The number of configurations
is at most j_max^N_max, which is finite.

```
def N_max (A gamma delta : ℝ) : ℕ :=
  Nat.ceil ((A + delta) / (4 * Real.pi * gamma * Real.sqrt 3))

def j_max (A gamma delta : ℝ) : ℕ :=
  -- largest k such that 8πγ√(k(k+2)/4) ≤ A + delta
  -- equivalently: k(k+2) ≤ ((A+delta)/(4πγ))²
  -- solve: k ≤ (-2 + √(4 + 4·((A+delta)/(4πγ))²))/2
  -- = -1 + √(1 + ((A+delta)/(4πγ))²)
  -- take floor
  sorry -- exact formula not needed; existence of bound suffices
```

**Lean note for agent:** The exact formula for j_max is not
essential. What matters is the *existence* of a computable bound.
The agent should prove:

```
theorem admissible_set_finite (A gamma delta : ℝ)
    (hA : A > 0) (hg : gamma > 0) (hd : delta > 0) :
    Set.Finite {config : SpinConfig | admissible A gamma delta config} := by
  sorry -- bounded length, bounded entries → finite
```

The proof strategy: a SpinConfig with total area ≤ A + δ has
length ≤ N_max and each entry has twice ≤ 2 * j_max. The set
of such lists is a subset of Finset.range(...) products, hence
finite. This is purely combinatorial. BISH.

---

## 3. Part A: Finite Entropy is BISH (Modules: FiniteCount.lean, Entropy.lean)

### 3.1 The Counting Function

```
noncomputable def count_configs (A gamma delta : ℝ) : ℕ :=
  (admissible_set_finite A gamma delta ‹_› ‹_› ‹_›).toFinset.card
```

**Theorem 3.1 (Computability of count):**
For rational A, γ, δ, count_configs is a computable natural number.

Proof: The admissible set is decidable — for each candidate
configuration (bounded length, bounded entries), checking
|total_area - A| ≤ δ is a decidable comparison of computable
reals (sums of square roots of rationals compared to a rational
bound). Enumerate all candidates, check each. BISH. ∎

**Lean note:** The "computable" claim means the function terminates
and produces a natural number without any axiom of choice. The
Lean implementation should avoid `Classical.choice` in the
counting itself. Use `Decidable` instances on the admissible
predicate.

### 3.2 Entropy

```
noncomputable def entropy (A gamma delta : ℝ) : ℝ :=
  Real.log (count_configs A gamma delta)
```

**Theorem 3.2 (Entropy is BISH):**
entropy(A, γ, δ) is a well-defined computable real for any
A > 0, γ > 0, δ > 0.

Proof: count_configs is a natural number (Theorem 3.1). Real.log
of a natural number is a computable real (log is computable on
positive rationals, and log(n) = log(n/1)). BISH. ∎

### 3.3 Entropy Density

```
noncomputable def entropy_density (A gamma delta : ℝ) : ℝ :=
  entropy A gamma delta / A
```

### 3.4 Finite-Size Approximation

**Theorem 3.3 (BISH finite-size bound):**
For any ε > 0, there exists a computable A₀ such that for all
A ≥ A₀:

  |entropy_density A γ δ - γ₀/(4γ)| < ε

where γ₀ is determined by the asymptotic analysis.

**THIS IS THE MAIN BISH RESULT.** The proof requires the
asymptotic analysis from Part C (§5), but the *structure* is:
given the asymptotic expansion with explicit error bounds,
the modulus of convergence is computable. The BISH content is
that the finite-size approximation has a computable rate —
you can compute how large A needs to be to achieve any desired
precision.

**Lean note:** This theorem may need to be stated with the
asymptotic coefficient as a hypothesis rather than derived
internally, depending on how Part C resolves. If the saddle-point
asymptotics are BISH, the whole thing is self-contained. If not,
state:

```
theorem entropy_density_approx
    (gamma : ℝ) (hg : gamma > 0)
    (gamma_0 : ℝ) (h_asymp : IsAsymptoticCoeff gamma_0 gamma)
    (eps : ℝ) (he : eps > 0) :
    ∃ A₀ : ℝ, ∀ A ≥ A₀,
      |entropy_density A gamma delta - gamma_0 / (4 * gamma)| < eps := by
  sorry
```

### 3.5 Axiom Certificate for Part A

**Expected #print axioms output:**
```
'FiniteCount.count_configs' depends on axioms:
[propext, Quot.sound]
-- NO Classical.choice
```

If `Classical.choice` appears, it's a Lean artifact from Finset
API usage, not a logical dependency. Document which lemma
introduces it and whether it can be eliminated by using
Decidable instances explicitly.

---

## 4. Part B: The Limit Costs LPO (Module: LPO_Equiv.lean)

### 4.1 The Convergence Statement

Define the entropy density sequence:

```
def S_seq (gamma delta : ℝ) : ℕ → ℝ :=
  fun n => entropy_density (n : ℝ) gamma delta
  -- entropy density at integer area values A = n
```

**Actually, use a cleaner parameterization.** Let A_n = n · a_min
where a_min = 4πγ√3 is the area gap. Then:

```
def S_seq (gamma delta : ℝ) : ℕ → ℝ :=
  fun n => entropy_density (n * area_gap gamma) gamma delta
```

The convergence statement is:

  ∃ L : ℝ, ∀ ε > 0, ∃ N₀, ∀ n ≥ N₀, |S_seq γ δ n - L| < ε

### 4.2 Forward Direction: LPO → Convergence

**Theorem 4.1:** LPO → BMC → S_seq converges.

Proof sketch:
1. LPO implies BMC (Bridges-Vîță 2006). Axiomatize this.
2. S_seq is bounded: 0 ≤ S(A)/A ≤ log(j_max^N_max)/A, and the
   right side is bounded uniformly (grows sublinearly).
3. S_seq is "eventually monotone" in an appropriate sense —
   adding more area generally increases the density of states
   faster than it increases the area. (This needs care; see §4.4.)
4. BMC applied to the bounded monotone subsequence gives convergence.

**Lean note:** The forward direction is short. Axiomatize BMC:

```
axiom BMC : ∀ (f : ℕ → ℝ), (∀ n, f n ≤ f (n+1)) →
    (∃ B, ∀ n, f n ≤ B) → ∃ L, ∀ ε > 0, ∃ N, ∀ n ≥ N, |f n - L| < ε
```

Then apply to S_seq with boundedness and monotonicity lemmas.

### 4.3 Backward Direction: Convergence → LPO (The Encoding)

This is the hard direction and the core contribution.

**Strategy:** Given an arbitrary binary sequence α : ℕ → {0,1},
encode it into a sequence of horizon configurations whose entropy
density convergence decides α.

**Step 1: Define the encoding.**

Given α : ℕ → {0,1}, define a "running maximum area" sequence:

```
def A_alpha (alpha : ℕ → Bool) : ℕ → ℝ :=
  fun n => A_base + (A_high - A_base) * (running_max alpha n)
```

where:
- A_base > 0 is a base area (large enough for meaningful counting)
- A_high > A_base is a higher area
- running_max α n = max_{k ≤ n} α(k) (which is 0 or 1)

So A_alpha n = A_base if α(k) = 0 for all k ≤ n, and
A_alpha n = A_high once some α(k) = 1 is found.

**Step 2: The entropy density gap.**

The key requirement is that the entropy density at A_base differs
from the entropy density at A_high. Specifically, we need:

  entropy_density A_base γ δ ≠ entropy_density A_high γ δ

This is guaranteed because the entropy density function is not
constant — it varies with A (this is a consequence of the
combinatorial structure of the state counting problem, and is
true for all sufficiently large A_base, A_high).

**Lean note:** This is the "gap lemma" and it requires care.
For the Ising model (Paper 8), the gap came from the free energy
function g(J) being strictly decreasing. Here, the gap comes from
the entropy density function being non-constant. The simplest
approach:

**Lemma 4.2 (Entropy density gap):** There exist rational
A_base, A_high with A_base < A_high such that:

  entropy_density A_high γ δ - entropy_density A_base γ δ > gap

for some explicit gap > 0.

Proof strategy: Choose A_base = K · a_min and A_high = 2K · a_min
for some large K. The entropy density at area A grows like
(γ₀/4γ) - (3/2)log(A)/A + O(1/A). For large enough K, the
difference |(3/2)log(2K)/2K - (3/2)log(K)/K| provides a nonzero
gap. But this uses the asymptotic expansion from Part C.

**Alternative (self-contained):** Compute entropy_density at two
specific small values of A and verify the gap numerically. For
example, with γ chosen appropriately, count configs at A = 10·a_min
and A = 20·a_min, compute the log of the count divided by A, and
verify these differ. This is a finite computation — BISH. The
gap lemma then holds by explicit computation.

**Lean note for agent:** The self-contained approach is preferred.
Use:

```
-- Explicit witness: two specific areas with different entropy densities
theorem entropy_density_gap (gamma : ℝ) (hg : gamma > 0)
    (delta : ℝ) (hd : delta > 0) :
    ∃ A_lo A_hi gap : ℝ,
      A_lo > 0 ∧ A_hi > A_lo ∧ gap > 0 ∧
      entropy_density A_hi gamma delta -
        entropy_density A_lo gamma delta > gap := by
  sorry -- finite computation witness
```

If the explicit computation is too expensive for Lean, axiomatize
the gap:

```
axiom entropy_density_gap_axiom (gamma : ℝ) (hg : gamma > 0) :
    ∃ A_lo A_hi gap : ℝ,
      A_lo > 0 ∧ A_hi > A_lo ∧ gap > 0 ∧
      entropy_density A_hi gamma delta -
        entropy_density A_lo gamma delta > gap
```

Document clearly that this axiom is a finite computation, verifiable
in principle, axiomatized for performance. This does NOT compromise
the BISH status — finite decidable computations are BISH.

**Step 3: The decision procedure.**

Given the gap, the decision procedure works as follows:

Suppose S_seq(A_alpha, γ, δ) converges to some limit L.

Case analysis:
- If α is identically 0: A_alpha n = A_base for all n, so
  S_seq converges to entropy_density(A_base, γ, δ) = L_base.
- If ∃k with α(k) = 1: A_alpha n = A_high for all n ≥ k, so
  S_seq converges to entropy_density(A_high, γ, δ) = L_high.

Since L_base ≠ L_high (by the gap lemma), the limit L decides:
- If |L - L_base| < gap/2: α is identically 0.
- If |L - L_high| < gap/2: ∃k with α(k) = 1.

The witness k is found by bounded search: once we know ∃k,
test α(0), α(1), ... up to the point where the entropy density
stabilizes.

**Step 4: Extracting the LPO witness.**

```
theorem convergence_implies_lpo
    (h_conv : ∀ alpha : ℕ → Bool,
      ∃ L, ∀ eps > 0, ∃ N, ∀ n ≥ N, |S_alpha alpha n - L| < eps) :
    LPO := by
  intro alpha
  obtain ⟨L, hL⟩ := h_conv alpha
  -- Get L to within gap/4
  obtain ⟨N₀, hN₀⟩ := hL (gap/4) (by linarith [gap_pos])
  -- Compare L to L_base and L_high
  -- Use decidability of rational comparison
  sorry
```

**Detailed proof of Step 4:**

Let gap > 0 be from Lemma 4.2. Given α, let L be the limit of
S_alpha. Choose N₀ such that |S_alpha n - L| < gap/4 for n ≥ N₀.

Compute L_approx = S_alpha N₀ (this is a computable real, being
log of a finite count divided by a known area).

Compute L_base_approx = entropy_density A_base γ δ (computable).
Compute L_high_approx = entropy_density A_high γ δ (computable).

Test: is |L_approx - L_base_approx| < gap/2?

If yes: L is within gap/2 + gap/4 = 3gap/4 of L_base. Since
|L_base - L_high| > gap, L is closer to L_base. But L = L_base
only if α is identically 0 (because if any α(k) = 1, the
sequence eventually equals L_high, and |L_high - L_base| > gap
would give |L - L_base| > gap/2, contradicting our test). So
conclude ∀n, α(n) = 0.

Actually, wait. We need to be more careful. If α(k) = 1 for some
k > N₀, then S_alpha N₀ = entropy_density A_base γ δ (because
the running max hasn't seen the 1 yet). So L_approx would be
close to L_base even though the true limit is L_high.

**This is the same issue as in Paper 8.** Resolution: we use the
actual limit L, not the approximation. Since the sequence converges
to L, and L is either L_base or L_high, we can decide which by
computing S_alpha at a sufficiently large N.

**Corrected procedure:**

1. Obtain N₀ from convergence: |S_alpha n - L| < gap/4 for n ≥ N₀.
2. Compute s = S_alpha N₀.
3. s is within gap/4 of L.
4. L is either L_base or L_high (these are the only two possible
   limit points, since A_alpha is eventually constant at one of
   two values).
5. Since |L_base - L_high| > gap, and |s - L| < gap/4:
   - If |s - L_base| < gap/2: then L = L_base (if L were L_high,
     |s - L_high| < gap/4 would give |s - L_base| > gap - gap/4 =
     3gap/4 > gap/2, contradiction). Conclude: A_alpha is eventually
     A_base, which means α(k) = 0 for all k ≤ N₀. But we also need
     α(k) = 0 for all k > N₀...

**Problem:** Knowing L = L_base tells us α is identically 0. But
our computation only gives |s - L| < gap/4, not L exactly. We need
to decide between L = L_base and L = L_high from a finite
approximation.

**Resolution:** The approximation suffices. Since L ∈ {L_base, L_high}
and |L_base - L_high| > gap and |s - L| < gap/4:
- If L = L_base: |s - L_base| < gap/4.
- If L = L_high: |s - L_high| < gap/4, so |s - L_base| > gap - gap/4
  = 3gap/4.

So test |s - L_base| < gap/2 (strictly between gap/4 and 3gap/4).
This is decidable (computable reals, rational comparison after
sufficient precision). The test correctly identifies which limit.

If L = L_base: α is identically 0. Return (inl proof).
If L = L_high: ∃k with α(k) = 1. Bounded search over k = 0,...,N₀
plus continued search finds the witness. Return (inr ⟨k, proof⟩).

Wait — if L = L_high, the switch must have happened at some k.
If k ≤ N₀, then S_alpha N₀ already reflects A_high, and bounded
search over 0,...,N₀ finds the witness.

But what if the limit is L_high yet no α(k) = 1 has appeared by N₀?
This cannot happen: if α(k) = 0 for all k ≤ N₀, then
S_alpha N₀ = entropy_density A_base γ δ = L_base, so
|s - L_base| = 0 < gap/2, and our test would have concluded
L = L_base. The only way L = L_high with our test confirming it
is if s is close to L_high, which requires the running max to have
switched, which requires α(k) = 1 for some k ≤ N₀.

Therefore the bounded search over k = 0,...,N₀ is sufficient. ∎

### 4.4 The Monotonicity Question

For BMC to apply, we need S_seq to be bounded and monotone (or
at least eventually monotone).

**Boundedness:** S(A)/A ≥ 0 (entropy is log of a count ≥ 1).
S(A)/A ≤ C for some constant C (the number of configurations
grows at most exponentially in A, so log grows linearly, so
the ratio is bounded). Explicit: N(A,γ,δ) ≤ j_max^{N_max},
so S/A ≤ N_max · log(j_max) / A, and both N_max and j_max
grow linearly in A, so this ratio is bounded. BISH.

**Monotonicity:** This is subtle. The entropy density S(A)/A
is NOT necessarily monotone in A for general γ, δ. The issue
is that increasing A by a small amount may not add new
configurations if δ is small relative to the area gap.

**Resolution (same as Paper 8):** We don't need monotonicity of
the raw sequence. We use a modified encoding.

**Modified approach:** Instead of encoding through the entropy
density, encode through the *entropy itself* S(A), which is
monotone (more area allows at least as many configurations,
so N(A₂) ≥ N(A₁) for A₂ ≥ A₁ when δ is suitably scaled).

Actually, the cleanest approach: use the *log partition function*
directly. Define:

```
def log_count_cumulative (gamma : ℝ) (n : ℕ) : ℝ :=
  Real.log (count_configs_up_to (n * area_gap gamma) gamma)
```

where count_configs_up_to(A, γ) counts all configurations with
total area ≤ A. This is manifestly non-decreasing (more area →
more configurations → higher count). And it's bounded by
n * C for some constant C.

Then S_n / (n · a_min) = log_count_cumulative n / (n · a_min)
and the sequence log_count_cumulative is bounded and non-decreasing.

Actually, for the encoding to work, we need the *density*
log_count / A to have different limits at A_base and A_high.
The monotonicity of log_count doesn't directly give monotonicity
of the density.

**Simplest clean resolution:** Abandon BMC and use a direct
encoding into LPO via the gap argument. The convergence hypothesis
(∃L, ...) is the *hypothesis* we're given. We don't need to prove
convergence — we need to show that *assuming* convergence for all
encoded sequences implies LPO. The convergence is the hypothesis,
not the conclusion.

So the backward direction is:

  (∀ α, S_alpha converges) → LPO

We're given convergence as a hypothesis. We use it to decide α.
We don't need BMC at all for the backward direction. BMC is only
needed for the forward direction (LPO → convergence), where we
axiomatize it.

**This simplifies the proof considerably.** The backward direction
is purely the encoding + gap + decision procedure from §4.3.
No monotonicity needed.

**Lean note:** The equivalence is:

```
theorem bh_entropy_lpo_equiv :
    (∀ alpha : ℕ → Bool,
      ∃ L, ∀ eps > 0, ∃ N, ∀ n ≥ N,
        |S_alpha alpha n - L| < eps)
    ↔ LPO := by
  constructor
  · exact convergence_implies_lpo  -- backward: encoding + gap
  · exact lpo_implies_convergence  -- forward: LPO → BMC → apply
```

### 4.5 Axiom Certificate for Part B

**Expected #print axioms output for convergence_implies_lpo:**
```
'convergence_implies_lpo' depends on axioms:
[propext, Quot.sound]
-- NO Classical.choice — this direction is constructive
```

The convergence_implies_lpo direction is the constructive consumer:
given convergence (hypothesis), extract a decision. No classical
axioms needed.

**Expected #print axioms output for lpo_implies_convergence:**
```
'lpo_implies_convergence' depends on axioms:
[propext, Quot.sound, Classical.choice]
```

Classical.choice enters through BMC (axiomatized from LPO).
This is the meta-classical producer.

---

## 5. Part C: The Logarithmic Correction (Module: Subleading.lean)

### 5.1 The Generating Function Approach

The exact state count N(A, γ, δ) for large A is analyzed via a
generating function. Define:

  Z(t) = Σ_{j ∈ HalfInt⁺} exp(-t · C(j))

where C(j) = √(j(j+1)) and t > 0 is a "temperature" parameter.
The generating function counts spin configurations weighted by
total Casimir value.

The number of configurations with total Casimir value ≈ s is
recovered by inverse Laplace transform:

  ρ(s) ≈ (1/2πi) ∫ Z(t)^∞ · e^{ts} dt

More precisely, for N punctures with total Casimir s:

  Ω(N, s) = coefficient of e^{-ts} in Z(t)^N

The entropy is:

  S(A) ≈ log Σ_N Ω(N, A/(8πγ))

### 5.2 Saddle-Point Approximation

For large A, the sum is dominated by the saddle point of:

  f(t, N) = N · log Z(t) + t · A/(8πγ) - log(...)

The saddle-point equations are:

  ∂f/∂t = 0: N · Z'(t)/Z(t) + A/(8πγ) = 0
  ∂f/∂N = 0: log Z(t) = 0, i.e., Z(t*) = 1

The second equation determines t* (the critical "temperature"):

  Z(t*) = Σ_j exp(-t* · C(j)) = 1

**Theorem 5.1 (Existence of saddle point):**
There exists a unique t* > 0 such that Z(t*) = 1.

Proof: Z(t) is strictly decreasing (each term decreases), Z(0+) = ∞
(infinite sum of 1's), and Z(t) → 0 as t → ∞ (each term → 0).
By IVT, ∃t* with Z(t*) = 1. By strict monotonicity, unique.

**CONSTRUCTIVE STATUS:** This is where it gets interesting.

The intermediate value theorem for continuous functions on [a,b] is
equivalent to LLPO over BISH (Ishihara). But here we have a
*strictly monotone* function, and for strictly monotone functions,
the IVT is equivalent to... what?

For strictly monotone functions on [a,b], the IVT is provable in
BISH + MP (Markov's Principle). Without MP, it requires LLPO.

**THIS IS THE KEY DISCOVERY QUESTION:**

Does the saddle point t* require LLPO, MP, or is it BISH?

The answer depends on the specific structure of Z(t). Since Z(t)
is a sum of exponentials (each computable, the partial sums are
computable, and the tail is exponentially small for t > 0), the
function Z is *computably continuous* and *computably monotone*.
For such functions, the IVT *is* constructive — you can compute
t* to any precision by bisection, and the strict monotonicity
gives you a computable modulus.

**Claim (to be verified by Lean):** t* is BISH-computable.

Proof sketch: Given ε > 0, compute Z at rational points by
truncating the series (finitely many terms, each computable,
tail bounded by geometric series). Use bisection: Z(a) > 1 > Z(b)
with rational a < b. Bisect: compute Z((a+b)/2) to sufficient
precision to determine which half contains t*. After O(log(1/ε))
steps, locate t* within ε. All steps are finite computation. BISH.

**Lean note:** The key lemma is:

```
theorem saddle_point_computable (gamma : ℝ) (hg : gamma > 0) :
    ∃ t_star : ℝ, Z t_star = 1 ∧
      ∀ eps > 0, ∃ q : ℚ, |t_star - q| < eps := by
  sorry -- bisection on computable monotone function
```

If this goes through cleanly (no Classical.choice), the saddle
point is BISH and the logarithmic correction computation can
proceed constructively.

### 5.3 The Logarithmic Correction

Assuming t* is BISH-computable, the saddle-point expansion gives:

  S(A) = γ₀A/(4γ) - (3/2) · log(A) + O(1)

where γ₀ = t*/(2π√3) (or similar relation depending on conventions).

The coefficient -3/2 comes from the Gaussian integral around the
saddle point. In the two-variable saddle (t, N), the Hessian is a
2×2 matrix, and the Gaussian correction gives:

  correction = -(1/2) · log(det(Hessian)) = -(1/2) · log(A^3 · const)
             = -(3/2) · log(A) + O(1)

**Constructive status of the Gaussian correction:**

The Hessian is a 2×2 matrix of second derivatives of f(t, N) at
the saddle point. Each entry is a computable function of t*.
The determinant is a polynomial in these entries. log of the
determinant is computable. The coefficient -3/2 is exact (it's
the dimension of the saddle divided by 2, times the power of A
in the determinant).

**Claim:** The -3/2 coefficient is BISH-derivable.

This would mean: both LQG's leading term AND subleading correction
are BISH, with the only LPO cost being the assertion that the
limit exists as a completed real number.

### 5.4 What Could Go Wrong

The saddle-point approximation involves:
1. Asserting that the saddle point dominates (error is O(1/A)).
2. Computing the Gaussian correction.
3. Bounding the remainder.

Step 1 is the delicate one. The assertion that the saddle-point
approximation is valid with an explicit error bound requires:
- The function f has a unique maximum (BISH by strict concavity,
  which follows from Z being a sum of convex exponentials).
- The error in the Gaussian approximation is O(1/A) with a
  computable constant.

The error bound requires bounding the third and higher derivatives
of f, which are computable from the series Z. If all bounds are
effective (computable constants), the whole expansion is BISH.

If some bound requires knowing that a certain supremum is attained
(e.g., sup of a third derivative on an interval), this could
introduce WLPO or LPO.

**Lean note:** This is genuinely open. The agent should:
1. Attempt the saddle-point computation with explicit bounds.
2. Run #print axioms on each lemma.
3. Report where (if anywhere) Classical.choice enters.

The readout is the result.

### 5.5 Module Structure for Part C

```
-- Subleading/GeneratingFunction.lean
-- Define Z(t), prove basic properties (monotone, continuous, limits)

-- Subleading/SaddlePoint.lean
-- Find t* by bisection, prove Z(t*) = 1

-- Subleading/Hessian.lean
-- Compute 2x2 Hessian at saddle point
-- Compute determinant, derive -3/2 coefficient

-- Subleading/ErrorBound.lean
-- Bound remainder of saddle-point expansion
-- THIS IS WHERE THE DISCOVERY HAPPENS
-- Run #print axioms here
```

---

## 6. Module Plan and File Structure

```
Paper17_BHEntropy/
├── Defs.lean                    -- HalfInt, Casimir, area eigenvalue, SpinConfig
├── FiniteCount.lean             -- admissible set finiteness, count_configs
├── Entropy.lean                 -- entropy, entropy_density
├── GapLemma.lean                -- entropy_density_gap (finite computation or axiom)
├── Encoding.lean                -- A_alpha, S_alpha, running_max encoding
├── LPO_Equiv.lean               -- convergence_implies_lpo, lpo_implies_convergence
├── Subleading/
│   ├── GeneratingFunction.lean  -- Z(t), monotonicity, limits
│   ├── SaddlePoint.lean         -- t* computation, bisection
│   ├── Hessian.lean             -- 2x2 Hessian, determinant, -3/2 coefficient
│   └── ErrorBound.lean          -- Remainder bound (THE DISCOVERY MODULE)
└── Main.lean                    -- imports, #print axioms audit
```

**Estimated lines:** 1500-2000 total.

**Priority order:**
1. Defs + FiniteCount + Entropy (foundation, ~300 lines)
2. GapLemma + Encoding + LPO_Equiv (Part B core, ~400 lines)
3. GeneratingFunction + SaddlePoint (Part C foundation, ~400 lines)
4. Hessian + ErrorBound (Part C discovery, ~400 lines)

**Stop points:** If Part B compiles cleanly, that's already a
publishable result (first CRM application to quantum gravity).
Part C is bonus — the discovery module. If it stalls on Lean
infrastructure for saddle-point asymptotics, report what was
achieved and what remains open.

---

## 7. Key Theorems — Summary

### Part A (BISH expected):

```
theorem admissible_set_finite :
    Set.Finite {config : SpinConfig | admissible A gamma delta config}

theorem count_configs_computable :
    ∃ n : ℕ, n = count_configs A gamma delta

theorem entropy_computable :
    ∃ s : ℝ, s = entropy A gamma delta ∧ s ≥ 0
```

### Part B (LPO equivalence):

```
theorem bh_entropy_lpo_equiv :
    (∀ alpha, ∃ L, ∀ eps > 0, ∃ N, ∀ n ≥ N, |S_alpha alpha n - L| < eps)
    ↔ LPO

-- Equivalently, via BMC:
theorem lpo_iff_bmc : LPO ↔ BMC  -- axiomatized from Bridges-Vîță

theorem bmc_implies_entropy_convergence :
    BMC → ∀ gamma delta, ∃ L, ... (S_seq converges)

theorem entropy_convergence_implies_lpo :
    (∀ alpha, S_alpha converges) → LPO
```

### Part C (open — run and report):

```
theorem saddle_point_exists :
    ∃ t_star > 0, Z t_star = 1

-- DISCOVERY: does this need Classical.choice?
theorem saddle_point_computable :
    ∀ eps > 0, ∃ q : ℚ, |t_star - q| < eps

-- DISCOVERY: what's the axiom profile?
theorem log_correction_coefficient :
    subleading_coeff = -3/2

-- DISCOVERY: BISH or not?
theorem saddle_point_error_bound :
    ∀ A ≥ A₀, |S(A) - (γ₀A/(4γ) - (3/2)log(A))| ≤ C
```

---

## 8. Axiom Audit Instructions

After all modules compile with zero sorry:

```
-- In Main.lean:

-- Part A audit
#print axioms admissible_set_finite
#print axioms count_configs_computable
#print axioms entropy_computable

-- Part B audit
#print axioms entropy_convergence_implies_lpo
#print axioms lpo_implies_entropy_convergence
#print axioms bh_entropy_lpo_equiv

-- Part C audit (THE READOUT)
#print axioms saddle_point_exists
#print axioms saddle_point_computable
#print axioms log_correction_coefficient
#print axioms saddle_point_error_bound
```

**What to report:**

For each theorem, list the axioms. Expected pattern:
- Part A: [propext, Quot.sound] only
- Part B backward: [propext, Quot.sound] only
- Part B forward: [propext, Quot.sound, Classical.choice]
- Part C: UNKNOWN — this is the experiment

If Part C shows [propext, Quot.sound] only: the subleading
correction is BISH. Major result.

If Part C shows [Classical.choice]: identify exactly which
lemma introduces it. Is it the saddle-point existence (LLPO)?
The error bound (LPO)? Something else? The WHERE matters.

---

## 9. Comparison with String Theory (For the Paper, Not for Lean)

The Strominger-Vafa derivation of S = A/4 requires:
1. Type IIB string theory compactified on K3 × S¹
2. D1-D5 brane system wrapping the compact dimensions
3. Identification of BPS states with black hole microstates
4. AdS₃/CFT₂ correspondence
5. Cardy formula for asymptotic density of states in the CFT
6. Taking the large-charge limit

None of (1)-(4) are mathematical theorems — they are physical
postulates that cannot be stated as Lean propositions without
formalizing string theory, which requires:
- Calabi-Yau geometry (6D compact manifolds)
- D-brane dynamics (open string boundary conditions)
- Modular invariance of CFT partition functions
- The AdS/CFT dictionary

The contrast: LQG's derivation reduces to finite combinatorics
(Lean-formalizable) plus a saddle-point expansion (possibly
Lean-formalizable). String theory's derivation requires importing
an entire theoretical framework that is not mathematically
axiomatized.

This asymmetry IS the calibration result. The paper doesn't
formalize the string side — it observes that the string side
*resists formalization* in a way that the LQG side does not,
and this resistance is precisely what the axiom calibration
framework is designed to detect.

---

## 10. Known Risks and Fallbacks

**Risk 1: Finset API forces Classical.choice in Part A.**
Mitigation: Use explicit Decidable instances. If unavoidable,
document and explain (same methodology as Papers 6, 11).

**Risk 2: Gap lemma requires explicit computation too expensive
for Lean.**
Mitigation: Axiomatize with clear documentation that it's a
finite computation. Does not compromise logical structure.

**Risk 3: Saddle-point asymptotics too complex for Lean.**
Mitigation: This is Part C. Report whatever the agent achieves.
Even partial results (e.g., t* is BISH but the error bound
status is open) are publishable.

**Risk 4: The encoding in Part B has a subtle error.**
Mitigation: The encoding follows the Paper 8 template exactly.
The gap lemma is the only new ingredient. If the encoding fails,
fall back to the abstract BMC ↔ LPO equivalence and note that
the physical instantiation remains open.

**Risk 5: The entropy density is actually constant (gap = 0).**
This would kill Part B. But it's physically absurd — the entropy
density must vary with area. If Lean can't prove it, axiomatize.

---

END OF PROOF DRAFT
