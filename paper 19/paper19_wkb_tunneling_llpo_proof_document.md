# Paper 19 Proof Document: The Logical Cost of Quantum Tunneling — LLPO and the WKB Turning Points

## For the Lean 4 Coding Agent

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose and Context

This is Paper 19 in the Constructive Reverse Mathematics (CRM) series. It is the
first paper in the "post-LPO" phase of the programme, targeting the level LLPO
(Lesser Limited Principle of Omniscience) — strictly between BISH and LPO in the
constructive hierarchy.

**Programme status:** Papers 2–16 calibrated physical idealizations at BISH, WLPO,
LPO, and DC_ω. The hierarchy BISH < LLPO < WLPO < LPO is known in constructive
mathematics, but only BISH, WLPO, and LPO have verified physical instantiations
in the calibration table. No physical result has been calibrated at LLPO. This
paper fills that gap.

**Physical setting:** Quantum tunneling through a potential barrier, analyzed via
the WKB (Wentzel-Kramers-Brillouin) semiclassical approximation. Every quantum
mechanics textbook discusses this. The tunneling amplitude through a barrier
V(x) at energy E is:

  T ~ exp(-1/ℏ ∫_{x₁}^{x₂} √(2m(V(x) - E)) dx)

where x₁, x₂ are the classical turning points satisfying V(x₁) = V(x₂) = E.

**Main result:** Over BISH, the WKB tunneling amplitude for a general continuous
barrier decomposes as:

  (a) For a specific polynomial barrier with algebraically known turning points,
      the tunneling amplitude is BISH-computable. (Part A)

  (b) For a general continuous barrier V : [a,b] → ℝ with V(a) < E < V(c) > E > V(b),
      the existence of turning points x₁, x₂ with V(x₁) = V(x₂) = E is equivalent
      to LLPO. (Part B)

  (c) The full WKB tunneling rate for a general barrier, requiring both the
      turning points and the limit ℏ → 0, costs LPO (the semiclassical limit
      is a completed limit). (Part C)

This gives the first entry in the calibration table at LLPO — strictly between
BISH and LPO — and the decomposition (BISH / LLPO / LPO) mirrors the pattern
established in Papers 8 and 13: empirical content is BISH, intermediate
structure costs LLPO, and the full idealization costs LPO.

---

## 1. Mathematical Background

### 1.1 LLPO (Lesser Limited Principle of Omniscience)

**Definition.** LLPO is the following assertion:

  For every binary sequence α : ℕ → {0, 1} with at most one n such that
  α(n) = 1, either α(2n) = 0 for all n, or α(2n+1) = 0 for all n.

Equivalently: if a binary sequence has at most one 1, the 1 (if it exists) is
on an even index or on an odd index, but we need not determine which.

**Position in the hierarchy:**

  BISH < LLPO < WLPO < LPO

where:
- BISH: no omniscience (base constructive mathematics)
- LLPO: can decide disjunctions about at-most-one-1 sequences
- WLPO: can decide whether a sequence is identically zero
- LPO: can decide whether a sequence has a 1 somewhere

All implications are strict (no reverse implications hold over BISH).

### 1.2 The IVT ↔ LLPO Equivalence

**Known result** [Bridges-Richman 1987, Ishihara 1989]:

Over BISH, the following are equivalent:

  (i)  LLPO
  (ii) The Intermediate Value Theorem for continuous functions on [0,1]:
       If f : [0,1] → ℝ is continuous with f(0) < 0 < f(1), then there
       exists x ∈ [0,1] with f(x) = 0.

More precisely: the general IVT (existence of a root for a continuous function
that changes sign) is equivalent to LLPO over BISH.

**Constructive note:** In BISH, one can prove the *approximate* IVT: for every
ε > 0, there exists x with |f(x)| < ε. This is the "constructive content" of
IVT — it does not require LLPO. What costs LLPO is the assertion of an *exact*
root f(x) = 0.

### 1.3 WKB Semiclassical Approximation

Consider a particle of mass m in a one-dimensional potential V(x) at energy E.
The classically forbidden region is {x : V(x) > E}. The WKB tunneling
amplitude through the barrier is:

  T_WKB = exp(-S/ℏ)

where the classical action through the barrier is:

  S = ∫_{x₁}^{x₂} √(2m(V(x) - E)) dx

and x₁, x₂ are the classical turning points: V(x₁) = E, V(x₂) = E, with
V(x) > E for x ∈ (x₁, x₂).

**The turning points are roots of V(x) - E = 0.** This is an IVT problem.

---

## 2. Part A: Specific Barriers are BISH

### 2.1 Setup

Fix the following specific barrier (the standard textbook example):

  V(x) = V₀ - V₀(x/a)² for |x| ≤ a, and V(x) = 0 for |x| > a

Or more simply, the rectangular barrier:

  V(x) = V₀ for 0 ≤ x ≤ a, and V(x) = 0 otherwise.

For the rectangular barrier, the turning points are exactly x₁ = 0, x₂ = a
(given by the definition, not by root-finding). The tunneling amplitude is:

  T = exp(-a√(2m(V₀ - E))/ℏ)

for 0 < E < V₀.

**Constructive note:** All quantities here are algebraic combinations of the
given parameters V₀, E, a, m, ℏ. No root-finding, no IVT, no limits. This is
BISH.

### 2.2 Parabolic Barrier

For the inverted parabolic barrier V(x) = V₀(1 - x²/a²), the turning points
at energy E are:

  x₁ = -a√(1 - E/V₀),  x₂ = a√(1 - E/V₀)

These are algebraically computable from E, V₀, a (using constructive square
root of a positive rational, which is BISH). The action integral:

  S = ∫_{x₁}^{x₂} √(2m(V₀(1 - x²/a²) - E)) dx

is an integral of a continuous function on a compact interval with constructively
known endpoints — BISH-computable.

**Lean formalization approach:** Define the barrier function, compute the turning
points explicitly, evaluate the integral (or bound it). The entire computation
lives in BISH.

### 2.3 General Polynomial Barrier

For V(x) = Σᵢ cᵢxⁱ (degree d) with rational coefficients, and rational energy
E, the turning points are roots of the polynomial V(x) - E = 0.

For degree 2: quadratic formula gives algebraic turning points — BISH.
For degree 3: Cardano's formula — BISH (with appropriate care about cube roots
of positive rationals).
For degree 4: Ferrari's formula — BISH.
For degree ≥ 5: no general algebraic formula (Abel-Ruffini), but for specific
polynomials with known rational roots, the turning points are still BISH.

**Key point:** For ANY specific polynomial with explicitly given turning points,
the WKB action integral is BISH. The non-constructivity enters only when the
turning points must be found by root-finding on a general continuous function.

### 2.4 Theorem 1 (BISH Computability of Specific Barriers)

**Theorem 1.** Let V : [a,b] → ℝ be a polynomial barrier with rational
coefficients, E a rational energy with 0 < E < max V, and suppose the turning
points x₁, x₂ satisfying V(x₁) = V(x₂) = E are given constructively (i.e.,
as computable reals with V(xᵢ) = E provable in BISH). Then:

  (a) The WKB action S = ∫_{x₁}^{x₂} √(2m(V(x) - E)) dx exists and is
      BISH-computable.

  (b) The tunneling amplitude T = exp(-S/ℏ) is BISH-computable for any
      rational ℏ > 0.

**Lean signature:**

```lean
/-- Part A: WKB action is computable when turning points are given -/
theorem wkb_action_computable
    (V : ℝ → ℝ) (hV : Polynomial V) (E : ℚ)
    (x₁ x₂ : ℝ) (hx₁ : V x₁ = E) (hx₂ : V x₂ = E)
    (hlt : x₁ < x₂) (hbar : V x > E for x ∈ (x₁, x₂)) :
    ∃ S : ℝ, S = ∫ x in x₁..x₂, Real.sqrt (2 * m * (V x - E)) := by
  sorry

/-- The tunneling amplitude is computable -/
theorem tunneling_amplitude_computable
    (S : ℝ) (hS : S ≥ 0) (ℏ : ℚ) (hℏ : (ℏ : ℝ) > 0) :
    ∃ T : ℝ, T = Real.exp (-S / ℏ) := by
  sorry
```

**Constructive note:** The integral exists by continuity on a compact interval
(constructive Riemann integration). The square root of a nonneg real is
constructive. exp is constructive. Every step is BISH.

**Axiom audit expectation:** Theorems 1a, 1b should compile with only
`[propext, Quot.sound]` — no `Classical.choice`, no LPO, no WLPO, no LLPO.

---

## 3. Part B: General Turning Points Cost LLPO

This is the core new result.

### 3.1 The Turning Point Problem

**Definition (Turning Point Problem, TPP).** Given:
- A continuous function V : [0, 1] → ℝ
- A real number E
- The conditions V(0) < E and V(1/2) > E (so V - E changes sign on [0, 1/2])
  and V(1) < E (so V - E changes sign back on [1/2, 1])

Assert: there exist x₁ ∈ [0, 1/2] and x₂ ∈ [1/2, 1] such that V(x₁) = E
and V(x₂) = E.

**Physical interpretation:** V is a potential barrier, E is the particle energy,
x₁ is the left turning point, x₂ is the right turning point. Between x₁ and x₂
the particle is in the classically forbidden region.

### 3.2 Forward Direction: LLPO → TPP

**Theorem 2 (LLPO → Turning Points Exist).**

Assume LLPO. Let V : [0,1] → ℝ be continuous with V(0) < E, V(1/2) > E,
V(1) < E. Then there exist x₁ ∈ [0, 1/2] and x₂ ∈ [1/2, 1] with
V(x₁) = E and V(x₂) = E.

**Proof.**

Define f : [0, 1/2] → ℝ by f(x) = V(x) - E. Then f(0) < 0 and f(1/2) > 0.
By LLPO (which is equivalent to IVT over BISH), there exists x₁ ∈ [0, 1/2]
with f(x₁) = 0, i.e., V(x₁) = E.

Similarly, define g : [1/2, 1] → ℝ by g(x) = V(x) - E. Then g(1/2) > 0 and
g(1) < 0. By LLPO/IVT, there exists x₂ ∈ [1/2, 1] with g(x₂) = 0, i.e.,
V(x₂) = E.

**Constructive note:** Each application of IVT costs LLPO. Two applications
still cost only LLPO (LLPO is closed under finite conjunction — this needs
verification, see §3.5).

**Lean signature:**

```lean
/-- LLPO implies turning points exist -/
theorem llpo_implies_turning_points
    (hLLPO : LLPO)
    (V : C([0,1], ℝ)) (E : ℝ)
    (h0 : V 0 < E) (hmid : V (1/2) > E) (h1 : V 1 < E) :
    ∃ x₁ ∈ Set.Icc 0 (1/2), ∃ x₂ ∈ Set.Icc (1/2) 1,
      V x₁ = E ∧ V x₂ = E := by
  sorry
```

### 3.3 Backward Direction: TPP → LLPO

**Theorem 3 (Turning Points → LLPO).**

If the Turning Point Problem is solvable for all continuous barriers, then LLPO
holds.

**Proof.**

We encode a binary sequence into a potential barrier so that the existence
of a turning point decides the sequence.

Let α : ℕ → {0, 1} be a binary sequence with at most one 1. We need to
decide: do all 1's (if any) occur at even indices, or at odd indices?

**Step 1: Construct the encoding function.**

Define a continuous function f : [0, 1] → ℝ that encodes α as follows.

On the interval [1/(n+2), 1/(n+1)], define f to be a bump function of
height α(n) · (-1)^n / (n+1). Specifically:

For each n ∈ ℕ, let Iₙ = [1/(n+2), 1/(n+1)]. Define:

  f(x) = α(n) · (-1)^n · hₙ(x)

where hₙ : Iₙ → [0, 1] is a continuous hat function (triangle or smooth
bump) with hₙ = 0 at endpoints and hₙ = 1/(n+1) at midpoint.

Set f(0) = 0.

**Step 2: Verify f is continuous.**

Each hₙ is continuous and vanishes at the endpoints of Iₙ. The intervals
Iₙ tile (0, 1] and the bump heights 1/(n+1) → 0 as n → ∞. Hence f
extends continuously to [0, 1] with f(0) = 0.

Since α has at most one 1, at most one bump is nonzero. If α(n₀) = 1
for some n₀, then f has exactly one nonzero bump on Iₙ₀, with sign
(-1)^{n₀}/(n₀+1).

**Step 3: Construct the barrier.**

Define the potential barrier:

  V(x) = 1 + f(x)

and set E = 1. Then V(x) - E = f(x).

We need V(0) < E at the left, V(c) > E somewhere in the middle, and
V(1) < E at the right. But this doesn't quite work because f(0) = 0
gives V(0) = E (not < E).

**Revised construction:** Instead, use the standard IVT ↔ LLPO encoding
from Bridges-Richman. The key idea is simpler.

**Step 3 (revised): Direct IVT encoding.**

Given α with at most one 1, define g : [0, 1] → ℝ by:

  g(x) = Σₙ α(n) · bₙ(x)

where bₙ is a continuous function supported on a small interval around
x = 1/2, with bₙ(1/2) = (-1)^n · εₙ for some εₙ > 0 decreasing to 0.

Actually, the cleanest encoding uses the known equivalence directly.

**Step 3 (clean version): Use IVT ↔ LLPO.**

The equivalence IVT ↔ LLPO is proven in the constructive analysis literature
[Bridges-Richman 1987, Ishihara 1989, Bridges-Vîță 2006 §4.3]. The backward
direction constructs, from any α with at most one 1, a continuous function
f_α : [0,1] → ℝ with:
- f_α(0) < 0 and f_α(1) > 0
- f_α has a root iff we can decide which parity class the 1 is in

The construction proceeds by defining f_α as a piecewise linear function
that has a positive bump at x = 1/3 if α has a 1 at an even index, and
a negative bump at x = 1/3 if α has a 1 at an odd index. The heights
are chosen so that the existence of a root near x = 1/3 decides the
parity.

**We do not need to reinvent this encoding.** The correct approach for
the Lean formalization is:

  (a) Axiomatize the IVT ↔ LLPO equivalence as a known result, citing
      Bridges-Richman and Ishihara.
  (b) Show that TPP is an instance of IVT (two applications).
  (c) Show that IVT is an instance of TPP (by constructing a barrier
      from any sign-changing continuous function).

This gives TPP ↔ LLPO via IVT ↔ LLPO.

**Lean signature:**

```lean
/-- IVT ↔ LLPO (axiomatized, citing Bridges-Richman 1987) -/
axiom ivt_iff_llpo : IVT ↔ LLPO

/-- Turning Point Problem is equivalent to two applications of IVT -/
theorem tpp_iff_ivt : TPP ↔ IVT := by
  sorry

/-- Main equivalence: Turning points ↔ LLPO -/
theorem turning_points_iff_llpo : TPP ↔ LLPO := by
  exact tpp_iff_ivt.trans ivt_iff_llpo
```

### 3.4 Alternative: Direct Encoding (Full Proof)

For a self-contained formalization that does NOT axiomatize IVT ↔ LLPO,
the backward direction can be proved directly. Here is the complete
construction.

**Theorem 3 (direct proof).** TPP → LLPO.

Let α : ℕ → {0, 1} with at most one n having α(n) = 1. We construct
a continuous barrier V_α and energy E such that the existence of a left
turning point decides the parity of the index of the 1.

**Construction:**

Define the partial sums:

  S_even(N) = Σ_{k=0}^{N} α(2k)
  S_odd(N)  = Σ_{k=0}^{N} α(2k+1)

Since α has at most one 1, we have S_even(N) + S_odd(N) ≤ 1 for all N,
and both are monotone nondecreasing.

Define:

  a_N = Σ_{k=0}^{N} α(2k) · 2^{-(2k+1)}
  b_N = Σ_{k=0}^{N} α(2k+1) · 2^{-(2k+2)}

These are partial sums of rapidly convergent series, hence Cauchy sequences.
Let a = lim a_N and b = lim b_N. Since at most one α(n) = 1:

  a + b ≤ 1, and a · b = 0 (at most one is nonzero).

Now define:

  V(x) = (x - 1/4)² + a - b    for x ∈ [0, 1]

with E = a.

Then V(x) - E = (x - 1/4)² - b.

Case analysis:
- If some α(2k) = 1: then a = 2^{-(2k+1)} > 0 and b = 0.
  V(x) - E = (x - 1/4)². This is ≥ 0, with root at x = 1/4.
  The left turning point exists at x₁ = 1/4.

- If some α(2k+1) = 1: then a = 0 and b = 2^{-(2k+2)} > 0.
  V(x) - E = (x - 1/4)² - b. The roots are x = 1/4 ± √b.
  These are the two turning points.

- If α ≡ 0: then a = 0, b = 0. V(x) - E = (x - 1/4)², root at x = 1/4.

**Wait — this doesn't cleanly separate the cases.** The issue is that
in BISH, we cannot distinguish between a = 0 and a > 0 without LLPO.

**Better encoding (following Ishihara's method):**

Given α with at most one 1, define:

  f(x) = x - Σ_n α(n) · gₙ(x)

where gₙ : [0,1] → ℝ is a continuous function with:
- gₙ(x) = 0 for x ∉ (1/3 - 1/n, 1/3 + 1/n)
- gₙ(1/3) = (-1)^n · x for an appropriate value

**This is getting complex. For the formalization, the recommended approach
is Option 1: axiomatize IVT ↔ LLPO and derive TPP ↔ LLPO from it.**

### 3.5 Design Decision: Axiomatize vs. Prove IVT ↔ LLPO

**Option 1 (RECOMMENDED): Axiomatize IVT ↔ LLPO.**

Declare:
```lean
/-- IVT is equivalent to LLPO over BISH.
    Reference: Bridges-Richman, "Varieties of Constructive Mathematics", 1987.
    Also: Ishihara, "Continuity and Nondiscontinuity in Constructive Mathematics", 1989. -/
axiom ivt_iff_llpo : IVT ↔ LLPO
```

This follows the precedent of Papers 8 and 14, which axiomatized BMC ↔ LPO
(citing Bridges-Vîță 2006). The IVT ↔ LLPO equivalence is equally
well-established in the constructive analysis literature.

**Advantages:** Clean, short, focuses formalization effort on the physical
content (barrier → turning points → tunneling), not on reproving known
constructive analysis.

**Option 2: Prove directly.**

Formalize the Bridges-Richman/Ishihara proof of IVT ↔ LLPO in Lean.
This would be ~500-800 lines of real analysis and requires constructive
bisection arguments. Valuable as a Mathlib contribution but orthogonal
to the CRM physics content.

**Recommendation:** Option 1 for Paper 19. Option 2 as a separate
infrastructure contribution if desired later.

### 3.6 Finite Conjunction of LLPO

**Claim:** Two applications of LLPO cost only LLPO (not more).

**Proof:** LLPO → LLPO ∧ LLPO is trivial. We need: LLPO is not
"used up" by one application.

More precisely: if S₁ and S₂ are each equivalent to LLPO, then S₁ ∧ S₂
is also equivalent to LLPO (not to something stronger like WLPO).

This holds because LLPO is a *scheme* (universally quantified over all
binary sequences), not a single instance. Each application uses a different
instance. The scheme persists.

**Lean note:** In the formalization, `LLPO` will be defined as:

```lean
def LLPO : Prop :=
  ∀ (α : ℕ → Bool), AtMostOne α →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)
```

A single LLPO hypothesis suffices for any finite number of applications.

### 3.7 Theorem 4: TPP ↔ LLPO

**Theorem 4 (Main Equivalence).** Over BISH, TPP ↔ LLPO.

**Proof (forward):** TPP → IVT (given a sign-changing continuous f on [a,b],
construct V(x) = f(x) + E with appropriate E and endpoints to make it a
barrier problem; the root of f is a turning point of V). IVT → LLPO by
Bridges-Richman.

**Proof (backward):** LLPO → IVT → TPP (§3.2).

**Lean signature:**

```lean
/-- Main equivalence: Turning Point Problem ↔ LLPO -/
theorem turning_point_problem_iff_llpo : TPP ↔ LLPO := by
  constructor
  · -- Forward: TPP → LLPO
    intro hTPP
    rw [← ivt_iff_llpo]
    exact ivt_of_tpp hTPP
  · -- Backward: LLPO → TPP
    intro hLLPO
    exact tpp_of_llpo hLLPO
```

**Axiom audit expectation:** Theorem 4 should have axiom profile:

  `[propext, Quot.sound, ivt_iff_llpo]`

The custom axiom `ivt_iff_llpo` is the declared equivalence. No
`Classical.choice`. The axiom cost is LLPO, strictly below LPO.

---

## 4. Part C: The Full WKB Limit Costs LPO

### 4.1 The Semiclassical Limit

The WKB approximation improves as ℏ → 0 (the semiclassical limit). The
exact tunneling probability is:

  T_exact(ℏ) = |ψ_transmitted|² / |ψ_incident|²

computed by solving the Schrödinger equation. The WKB approximation gives:

  T_WKB(ℏ) = exp(-2S/ℏ) · (1 + O(ℏ))

The assertion "T_WKB approximates T_exact to within ε as ℏ → 0" involves:

  lim_{ℏ → 0} |T_exact(ℏ) - T_WKB(ℏ)| / T_WKB(ℏ) = 0

This is a limit statement — a completed infinite process — which costs LPO
via bounded monotone convergence.

### 4.2 More precisely: Why LPO

The sequence of errors eₙ = |T_exact(ℏₙ) - T_WKB(ℏₙ)| / T_WKB(ℏₙ)
for ℏₙ = 1/n is a sequence converging to 0. The assertion "lim eₙ = 0"
is a universal statement ∀ε > 0, ∃N, ∀n ≥ N, eₙ < ε.

For a specific barrier (Part A), this sequence is computable and its
convergence rate is known (from the asymptotic expansion of the exact
solution). The ε-N relationship is BISH-computable.

For a general barrier (after obtaining turning points via LLPO from Part B),
the convergence still involves a limit. The assertion that the WKB
expansion converges to the exact solution requires bounded monotone
convergence of the asymptotic series, which is LPO.

### 4.3 Theorem 5: Full WKB for General Barriers Costs LPO

**Theorem 5.** Over BISH, the full semiclassical tunneling computation for
a general continuous barrier — including both turning point identification
and the ℏ → 0 limit — requires LPO.

**Proof sketch:**

  LLPO (turning points, Part B) + BMC/LPO (semiclassical limit) = LPO

since LPO ≥ LLPO, the dominant cost is LPO.

**Lean signature:**

```lean
/-- Full WKB for general barriers requires LPO -/
theorem full_wkb_general_barrier_requires_lpo :
    FullWKBGeneralBarrier → LPO := by
  sorry

/-- LPO suffices for full WKB -/
theorem lpo_implies_full_wkb :
    LPO → FullWKBGeneralBarrier := by
  sorry

/-- Equivalence -/
theorem full_wkb_iff_lpo : FullWKBGeneralBarrier ↔ LPO := by
  exact ⟨full_wkb_general_barrier_requires_lpo, lpo_implies_full_wkb⟩
```

**Note:** The backward direction (LPO → FullWKB) uses:
- LPO → LLPO (known, strict weakening)
- LLPO → turning points exist (Theorem 4)
- LPO → BMC (Bridges-Vîță) → semiclassical limit exists
- Combine to get full WKB.

### 4.4 Dispensability (BISH Recovery)

**Theorem 6 (Dispensability).** For any specific polynomial barrier V with
rational coefficients and rational energy E, and for any rational ε > 0,
there exists a BISH-computable bound on the tunneling probability within ε.

This is already established by Part A: specific barriers are BISH. The
point is that the "post-LLPO" and "post-LPO" structure (turning points,
semiclassical limit) are not needed for empirical predictions at any
finite precision.

**Lean signature:**

```lean
/-- Dispensability: specific barriers don't need LLPO or LPO -/
theorem specific_barrier_bish
    (V : Polynomial ℝ) (E : ℚ) (ε : ℚ) (hε : (ε : ℝ) > 0)
    (x₁ x₂ : ℝ) (hroots : V.eval x₁ = E ∧ V.eval x₂ = E) :
    ∃ T_approx : ℝ, |T_approx - T_exact V E| < ε := by
  sorry
```

---

## 5. Module Structure

### 5.1 Lean Module Layout

```
CRM/Paper19/
├── Basic/
│   ├── LLPO.lean           -- LLPO definition, basic properties
│   ├── IVT.lean            -- IVT definition, IVT ↔ LLPO axiom
│   └── Hierarchy.lean      -- BISH < LLPO < WLPO < LPO implications
├── Barrier/
│   ├── Definitions.lean    -- Barrier, TurningPoint, TPP definitions
│   ├── Rectangular.lean    -- Rectangular barrier, BISH computation
│   ├── Parabolic.lean      -- Parabolic barrier, BISH computation
│   └── General.lean        -- General continuous barrier
├── WKB/
│   ├── Action.lean         -- WKB action integral S
│   ├── Amplitude.lean      -- Tunneling amplitude T = exp(-S/ℏ)
│   └── Limit.lean          -- Semiclassical limit ℏ → 0
├── Calibration/
│   ├── PartA.lean          -- Theorem 1: specific barriers BISH
│   ├── PartB.lean          -- Theorem 4: TPP ↔ LLPO
│   ├── PartC.lean          -- Theorem 5: full WKB ↔ LPO
│   └── Dispensability.lean -- Theorem 6: BISH recovery
└── Main.lean               -- Imports, summary, #print axioms
```

### 5.2 Estimated Line Counts

| Module              | Lines | Content                              |
|---------------------|-------|--------------------------------------|
| LLPO.lean           | 60    | Definition, AtMostOne, basic lemmas  |
| IVT.lean            | 40    | Definition, axiom declaration        |
| Hierarchy.lean      | 80    | LLPO → WLPO, LPO → LLPO, etc.      |
| Definitions.lean    | 100   | Barrier, TPP, WKB structures         |
| Rectangular.lean    | 80    | Rectangular barrier BISH proof        |
| Parabolic.lean      | 120   | Parabolic barrier with sqrt           |
| General.lean        | 60    | General barrier setup                 |
| Action.lean         | 100   | Integral definition and properties    |
| Amplitude.lean      | 60    | exp(-S/ℏ) computation                |
| Limit.lean          | 80    | Semiclassical limit structure         |
| PartA.lean          | 100   | Theorem 1 assembly                    |
| PartB.lean          | 200   | TPP ↔ LLPO main equivalence          |
| PartC.lean          | 150   | Full WKB ↔ LPO                       |
| Dispensability.lean | 80    | BISH recovery theorem                 |
| Main.lean           | 50    | Summary and axiom audit               |
| **Total**           |**1360**| **15 files**                         |

### 5.3 Dependencies

**Mathlib dependencies:**
- `Mathlib.Analysis.SpecificLimits.Basic` (convergence)
- `Mathlib.Analysis.Calculus.Integral` (Riemann integration)
- `Mathlib.Data.Real.Basic` (ℝ, sqrt, exp, log)
- `Mathlib.Data.Polynomial.Basic` (polynomial evaluation)
- `Mathlib.Topology.ContinuousFunction.Basic` (C(X, ℝ))
- `Mathlib.Order.Filter.Basic` (limits)

**Custom infrastructure (from earlier papers):**
- LPO definition and BMC ↔ LPO (from Paper 8)
- WLPO definition (from Paper 2)
- Axiom audit methodology (#print axioms)
- HasLPO / HasWLPO typeclasses (from Paper 14)

**New infrastructure needed:**
- LLPO definition and HasLLPO typeclass
- IVT ↔ LLPO axiom declaration
- LLPO < WLPO and LPO → LLPO implications

---

## 6. Key Definitions for the Lean Agent

### 6.1 LLPO

```lean
/-- A binary sequence has at most one `true` value -/
def AtMostOne (α : ℕ → Bool) : Prop :=
  ∀ m n, α m = true → α n = true → m = n

/-- Lesser Limited Principle of Omniscience -/
def LLPO : Prop :=
  ∀ (α : ℕ → Bool), AtMostOne α →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)

/-- Typeclass for assuming LLPO -/
class HasLLPO where
  llpo : LLPO
```

### 6.2 IVT (Constructive Formulation)

```lean
/-- Approximate IVT: BISH-valid, no omniscience needed -/
def ApproxIVT : Prop :=
  ∀ (f : C(Set.Icc (0:ℝ) 1, ℝ)) (ε : ℝ), ε > 0 →
    f ⟨0, by norm_num⟩ < 0 → f ⟨1, by norm_num⟩ > 0 →
    ∃ x ∈ Set.Icc (0:ℝ) 1, |f ⟨x, ‹_›⟩| < ε

/-- Exact IVT: equivalent to LLPO -/
def ExactIVT : Prop :=
  ∀ (f : C(Set.Icc (0:ℝ) 1, ℝ)),
    f ⟨0, by norm_num⟩ < 0 → f ⟨1, by norm_num⟩ > 0 →
    ∃ x ∈ Set.Icc (0:ℝ) 1, f ⟨x, ‹_›⟩ = 0

/-- The known equivalence (axiomatized) -/
axiom exact_ivt_iff_llpo : ExactIVT ↔ LLPO
```

### 6.3 Barrier and Turning Points

```lean
/-- A potential barrier on [0, 1] -/
structure Barrier where
  V : C(Set.Icc (0:ℝ) 1, ℝ)
  E : ℝ
  h_left : V ⟨0, by norm_num⟩ < E
  h_peak : ∃ c ∈ Set.Icc (0:ℝ) 1, V ⟨c, ‹_›⟩ > E
  h_right : V ⟨1, by norm_num⟩ < E

/-- Classical turning points -/
structure TurningPoints (B : Barrier) where
  x₁ : Set.Icc (0:ℝ) 1
  x₂ : Set.Icc (0:ℝ) 1
  h_left_root : B.V x₁ = B.E
  h_right_root : B.V x₂ = B.E
  h_order : x₁.val < x₂.val
  h_barrier : ∀ x ∈ Set.Ioo x₁.val x₂.val, B.V ⟨x, sorry⟩ > B.E

/-- The Turning Point Problem -/
def TPP : Prop :=
  ∀ (B : Barrier), Nonempty (TurningPoints B)
```

### 6.4 WKB Action

```lean
/-- WKB action integral through the barrier -/
noncomputable def wkb_action (B : Barrier) (tp : TurningPoints B) (m : ℝ) : ℝ :=
  ∫ x in tp.x₁.val..tp.x₂.val, Real.sqrt (2 * m * (B.V ⟨x, sorry⟩ - B.E))

/-- WKB tunneling amplitude -/
noncomputable def wkb_amplitude (B : Barrier) (tp : TurningPoints B)
    (m : ℝ) (ℏ : ℝ) : ℝ :=
  Real.exp (-(wkb_action B tp m) / ℏ)
```

---

## 7. What to Report

After formalization, the Lean agent should report:

### 7.1 Axiom Certificates

Run `#print axioms` on each main theorem and report the output.

**Expected:**

| Theorem                          | Expected Axioms                              |
|----------------------------------|----------------------------------------------|
| Theorem 1 (specific BISH)       | [propext, Quot.sound]                        |
| Theorem 4 (TPP ↔ LLPO)          | [propext, Quot.sound, exact_ivt_iff_llpo]    |
| Theorem 5 (full WKB ↔ LPO)     | [propext, Quot.sound, exact_ivt_iff_llpo, bmc_iff_lpo] |
| Theorem 6 (dispensability)       | [propext, Quot.sound]                        |

If `Classical.choice` appears in Theorems 1 or 6, it is a Mathlib leak and
must be isolated (same methodology as Papers 2, 8, 11, 14).

### 7.2 Line Count

Report lines per module and total.

### 7.3 Sorry Audit

All `sorry` must be eliminated before submission. Report any remaining
`sorry` with the theorem name and reason.

---

## 8. Success Criteria

The formalization succeeds if:

1. **Theorem 4 compiles sorry-free** with axiom profile containing
   `exact_ivt_iff_llpo` but NOT `Classical.choice` or `bmc_iff_lpo`.
   This certifies the LLPO calibration.

2. **Theorem 1 compiles sorry-free** with NO custom axioms.
   This certifies the BISH dispensability.

3. **Theorem 5 compiles sorry-free** with both `exact_ivt_iff_llpo` and
   `bmc_iff_lpo` in its axiom profile. This certifies the LPO cost of
   the full WKB.

4. The three-tier decomposition BISH / LLPO / LPO is cleanly visible
   in the axiom audit.

---

## 9. Design Decisions Summary

| Decision | Choice | Rationale |
|----------|--------|-----------|
| IVT ↔ LLPO | Axiomatize | Known result, follows Paper 8 precedent |
| BMC ↔ LPO | Import from Paper 8 | Already formalized |
| LLPO definition | AtMostOne + parity | Standard, matches literature |
| Barrier domain | [0, 1] | Simplest, matches IVT domain |
| Specific barriers | Rectangular + parabolic | Standard textbook examples |
| Turning point structure | Bundle with proofs | Lean-idiomatic |
| WKB action | Mathlib integral | Uses existing infrastructure |
| HasLLPO typeclass | Mirror HasLPO/HasWLPO | Consistent with series |

---

## 10. Paper Outline (for the LaTeX Write-Up)

§1. Introduction
    — Quantum tunneling as a universal physical phenomenon
    — The turning point problem: where does non-constructivity enter?
    — Summary of results: BISH / LLPO / LPO decomposition

§2. Background
    — 2.1 WKB approximation (standard physics)
    — 2.2 LLPO and the constructive hierarchy
    — 2.3 IVT ↔ LLPO (Bridges-Richman, Ishihara)

§3. Part A: Specific Barriers are BISH
    — 3.1 Rectangular barrier (Theorem 1a)
    — 3.2 Parabolic barrier (Theorem 1b)
    — 3.3 General polynomial with known roots (Theorem 1c)

§4. Part B: General Turning Points Cost LLPO
    — 4.1 TPP → IVT (embedding)
    — 4.2 IVT → TPP (barrier construction)
    — 4.3 TPP ↔ LLPO (Theorem 4)

§5. Part C: The Semiclassical Limit Costs LPO
    — 5.1 The ℏ → 0 limit
    — 5.2 Full WKB ↔ LPO (Theorem 5)
    — 5.3 Dispensability (Theorem 6)

§6. Updated Calibration Table
    — Add LLPO row with TPP entry
    — Note: first physical calibration at LLPO in the series

§7. Lean 4 Formalization
    — 7.1 Module structure
    — 7.2 Axiom audit
    — 7.3 Design decisions

§8. Discussion
    — 8.1 The three-tier structure of tunneling
    — 8.2 LLPO as "knowing where but not what"
    — 8.3 Relation to the measurement problem
    — 8.4 Future directions (LLPO in other physical settings)

References

Appendix: Hierarchy proofs (BISH < LLPO < WLPO < LPO)

---

## 11. Critical Notes for the Lean Agent

1. **Do NOT use Classical.choice anywhere in the Part A or Part B proofs.**
   If Mathlib imports pull it in, isolate the contamination using the same
   technique as Paper 14 (wrapper lemmas that avoid Decidable instances on ℝ).

2. **The LLPO definition must be Prop-valued**, not Bool-valued. The
   disjunction is ∨ (Prop), not || (Bool).

3. **AtMostOne is a Prop**: ∀ m n, α m = true → α n = true → m = n.
   This is decidable for any finite prefix but not globally — which is
   exactly the point.

4. **The IVT axiom should use C(Set.Icc 0 1, ℝ)** (continuous functions on
   the unit interval), not arbitrary functions. This matches the standard
   formulation and avoids Mathlib issues with continuity on arbitrary domains.

5. **The integral in wkb_action uses `MeasureTheory.integral`** via
   `∫ x in a..b, f x`. The integrand √(2m(V(x) - E)) is continuous
   on [x₁, x₂] and nonneg, so the integral exists by standard Mathlib
   results.

6. **Import the LPO and BMC machinery from Paper 8** if available in
   the same repository. If not, re-declare:
   ```lean
   axiom bmc_iff_lpo : BMC ↔ LPO
   ```

7. **The hierarchy proofs** (LLPO → WLPO, LPO → LLPO, etc.) are
   standard and short. Prove them directly in Hierarchy.lean:
   - LPO → WLPO: if α has a 1, it has a 1 (trivial weakening)
   - LPO → LLPO: if you can find any 1, you can determine its parity
   - WLPO → LLPO: if you can decide "all zero", you can decide parity
     (actually this is not trivial — WLPO does imply LLPO but the proof
     requires care; verify from Bridges-Vîță)
   - LLPO does NOT imply WLPO: this is a separation result, not needed
     for the formalization but note it in comments.

---

## 12. Philosophical Punchline

The paper's key insight, stated informally:

Quantum tunneling through a barrier has a three-layer logical structure:

- **What you can compute** (BISH): the tunneling rate for any specific,
  explicitly given barrier. This is all an experimentalist needs.

- **Where the barrier ends** (LLPO): the existence of classical turning
  points for a general continuous barrier. This is the IVT content —
  you know the barrier starts and stops, but locating the exact boundary
  requires LLPO.

- **The semiclassical world** (LPO): the assertion that quantum mechanics
  reduces to classical mechanics as ℏ → 0. This is a completed limit.

The decomposition reveals that tunneling — one of the most distinctly quantum
phenomena — has its non-constructive content not in the quantum mechanics
itself (which is BISH for specific systems) but in the classical geometry
of the barrier (LLPO for turning points) and the classical limit (LPO for
ℏ → 0). Quantum mechanics is logically cheaper than classical mechanics.
That's the headline.
