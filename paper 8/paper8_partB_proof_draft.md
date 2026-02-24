# LPO Equivalence via Free Energy Convergence

## Paper 8, Part B — Proof Draft for Lean 4 Formalization

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose and Formalization Notes

This document provides a complete, step-by-step mathematical proof that
the existence of the thermodynamic limit (as a completed real number) is
equivalent to LPO over BISH. It is the companion to Part A, which showed
the *empirical content* (finite-size error bounds) is BISH-provable.

**Key constraint:** The backward direction (free energy convergence → LPO)
must be constructively valid modulo the convergence hypothesis. The
encoding of binary sequences into free energy sequences must use only
BISH-available operations.

**What we show:** Over BISH, the following are equivalent:
1. LPO (Limited Principle of Omniscience)
2. Bounded Monotone Convergence (every bounded monotone sequence of reals
   has a limit)
3. For every bounded non-decreasing coupling sequence J : ℕ → [J₀, J₁],
   the sequence F(N) := -log(2·cosh(β·J(N))) converges.

The equivalence (1) ↔ (2) is [Bridges–Vîță 2006]. We formalize (2) ↔ (3)
and the backward direction (3) → (1) with an explicit encoding.

**Why this matters:** Combined with Part A, this establishes:
- The empirical content of the thermodynamic limit is BISH (Part A)
- The idealization (limit as completed object) costs exactly LPO (Part B)
- The LPO cost is therefore real but dispensable for predictions

**Dependencies on Part A:** This proof reuses the following from Part A:
- `transferEigenPlus`, `transferEigenMinus` definitions
- `Real.cosh`, `Real.log` properties
- `tanh_pos`, `tanh_lt_one`, `eigenPlus_pos`
- The error bound infrastructure (for witness extraction in §4.6)

---

## 1. Definitions

### 1.1 LPO

The Limited Principle of Omniscience:

  LPO: ∀ α : ℕ → {0,1}, (∀n, α(n) = 0) ∨ (∃n, α(n) = 1)

Note the existential witness in the second disjunct — this is strictly
stronger than WLPO, which gives only ¬(∀n, α(n) = 0).

### 1.2 Bounded Monotone Convergence (BMC)

  BMC: For every sequence (aₙ) of reals, if (aₙ) is non-decreasing
  and bounded above, then limₙ aₙ exists.

"Exists" means: there is a constructive real L and a modulus of
convergence M : ℕ → ℕ such that for all k, for all N ≥ M(k),
|aₙ - L| < 1/2^k.

### 1.3 Free energy at coupling J

For β > 0 and J > 0:

  g(J) := -log(2·cosh(β·J))

This is the infinite-volume free energy density of the 1D Ising chain
with uniform coupling J. From Part A, this is a constructively
well-defined real number for rational β, J > 0.

---

## 2. Properties of g(J)

### 2.1 g is strictly decreasing

**Lemma 2.1.** For β > 0, the function g(J) = -log(2·cosh(β·J)) is
strictly decreasing on (0, ∞).

*Proof.*

The derivative: g'(J) = -β·tanh(β·J) < 0 for J > 0 (since β > 0 and
tanh(x) > 0 for x > 0).

For the formalization, we avoid calculus and use the chain of
equivalences directly:

  J₁ > J₂ > 0
  ⟹ β·J₁ > β·J₂ > 0            (multiply by β > 0)
  ⟹ cosh(β·J₁) > cosh(β·J₂)    (cosh strictly increasing on (0,∞))
  ⟹ log(2·cosh(β·J₁)) > log(2·cosh(β·J₂))  (log strictly increasing)
  ⟹ -log(2·cosh(β·J₁)) < -log(2·cosh(β·J₂))
  ⟹ g(J₁) < g(J₂)

**Constructive note:** All steps use strict monotonicity of cosh and log,
which are constructively valid. cosh is strictly increasing on (0,∞)
because cosh'(x) = sinh(x) > 0 for x > 0. In Lean, this can be proved
via the power series or via the identity cosh(a) - cosh(b) =
2·sinh((a+b)/2)·sinh((a-b)/2) > 0 when a > b > 0. ∎

### 2.2 The gap between two coupling values

**Lemma 2.2 (Gap lemma).** Fix β > 0 and 0 < J₀ < J₁. Then:

  δ := g(J₀) - g(J₁) = log(cosh(β·J₁) / cosh(β·J₀)) > 0

*Proof.* Immediate from Lemma 2.1: J₁ > J₀ implies g(J₁) < g(J₀),
so g(J₀) - g(J₁) > 0.

Explicitly:
  δ = -log(2·cosh(β·J₀)) - (-log(2·cosh(β·J₁)))
    = log(2·cosh(β·J₁)) - log(2·cosh(β·J₀))
    = log(cosh(β·J₁) / cosh(β·J₀))

Since cosh(β·J₁) > cosh(β·J₀) > 0, the ratio is > 1, so log > 0. ∎

**Constructive note:** For rational β, J₀, J₁, the gap δ is a
constructively computable positive real. The positivity is witnessed
by an explicit rational lower bound (computable from β, J₀, J₁ via
the power series of cosh). This is important: the decision procedure
in §4 uses δ > 0 as a constructive fact.

---

## 3. Forward Direction: LPO → Free Energy Convergence

**Theorem 3.1.** LPO implies BMC.

*Proof.* This is [Bridges–Vîță 2006, Theorem 2.1.5]. We sketch the
argument for completeness.

Let (aₙ) be non-decreasing and bounded above by M. Define
α : ℕ → {0,1} by: for each candidate rational limit value, use LPO
to decide whether the sequence exceeds it. More precisely:

The sup of a bounded monotone sequence can be computed by binary
search on the value axis, using LPO at each step to decide whether
the sequence eventually exceeds a given rational threshold.

For the formalization, we may axiomatize this direction as:

```
axiom bmc_of_lpo : LPO → BoundedMonotoneConvergence
```

and cite [Bridges–Vîță 2006]. Alternatively, formalize it directly
(~100 lines). The novel content of this paper is the backward direction.
∎

**Corollary 3.2.** LPO implies that for every bounded non-decreasing
coupling sequence J : ℕ → [J₀, J₁], the sequence g(J(N)) converges.

*Proof.* The sequence -g(J(N)) = log(2·cosh(β·J(N))) is non-decreasing
(since J(N) is non-decreasing and cosh, log are increasing) and bounded
(since J(N) ≤ J₁). By BMC (from LPO), it converges. Hence g(J(N))
converges. ∎

---

## 4. Backward Direction: Free Energy Convergence → LPO

This is the main new content.

### 4.1 The encoding

**Construction.** Let α : ℕ → {0,1} be an arbitrary binary sequence.

**Step 1: Running maximum.**

Define m : ℕ → {0,1} by:

  m(0) := α(0)
  m(n+1) := max(m(n), α(n+1))

Equivalently: m(n) = max(α(0), α(1), ..., α(n)).

Properties (all BISH-provable):
- m(n) ∈ {0, 1} for all n
- m is non-decreasing: m(n) ≤ m(n+1)
- m(n) = 0 ↔ ∀k ≤ n, α(k) = 0
- m(n) = 1 ↔ ∃k ≤ n, α(k) = 1

**Constructive status:** m(n) is constructively computable from
(α(0), ..., α(n)) by finite recursion. No omniscience needed.

**Step 2: Coupling sequence.**

Fix rationals 0 < J₀ < J₁ (e.g., J₀ = 1, J₁ = 2). Define:

  J(n) := if m(n) = 0 then J₀ else J₁

Properties:
- J(n) ∈ {J₀, J₁} for all n
- J is non-decreasing (since m is non-decreasing and J₀ < J₁)
- J(n) = J₀ ↔ ∀k ≤ n, α(k) = 0
- J(n) = J₁ ↔ ∃k ≤ n, α(k) = 1
- J₀ ≤ J(n) ≤ J₁ (bounded)

**Step 3: Free energy sequence.**

Define F : ℕ → ℝ by:

  F(n) := g(J(n)) = -log(2·cosh(β·J(n)))

Properties:
- F(n) ∈ {g(J₀), g(J₁)} for all n
- F is non-increasing (since J is non-decreasing and g is strictly
  decreasing)
- g(J₁) ≤ F(n) ≤ g(J₀) (bounded)

**Equivalently:** Define G(n) := -F(n). Then G is non-decreasing and
bounded, so BMC applies to G. The limit of G exists iff the limit of
F exists.

### 4.2 The two regimes

**Case A: α ≡ 0.** Then m ≡ 0, J ≡ J₀, F ≡ g(J₀). The sequence is
constant. Its limit is g(J₀).

**Case B: ∃n₀, α(n₀) = 1.** Then for all n ≥ n₀: m(n) = 1, J(n) = J₁,
F(n) = g(J₁). The sequence is eventually constant at g(J₁). Its limit
is g(J₁).

In both cases, the limit exists (trivially — eventually constant
sequences converge in BISH). But *which* limit obtains depends on α,
and BISH cannot decide this without LPO.

### 4.3 The decision procedure

Assume BMC. Let α : ℕ → {0,1} be given. Construct F as above.

The sequence G(n) := -F(n) is non-decreasing and bounded above (by
-g(J₁)). By BMC, L_G := lim G(n) exists as a constructive real with
a modulus of convergence. Set L := -L_G = lim F(n).

L is a constructive real number — meaning we have a Cauchy sequence
representation and a modulus, so we can compute rational approximations
to L within any desired precision ε > 0.

Recall the gap from Lemma 2.2:

  δ := g(J₀) - g(J₁) > 0

The two possible values of L are g(J₀) and g(J₁), separated by δ.

### 4.4 Rational comparison

Compute a rational approximation q ∈ ℚ satisfying |L - q| < δ/3.
(This is possible because L is a constructive real with a modulus.)

Set the threshold t := (g(J₀) + g(J₁)) / 2. Note t is rational (for
rational β, J₀, J₁).

Compare q with t. This is a decidable comparison (rational arithmetic).

**If q > t:** Then L > q - δ/3 > t - δ/3 = g(J₁) + δ/2 - δ/3 =
g(J₁) + δ/6. And L < q + δ/3 < ... In any case, |L - g(J₀)| < δ/3 +
(gap analysis below). We conclude L is close to g(J₀).

Let me be more careful.

If L = g(J₀): then q ∈ (g(J₀) - δ/3, g(J₀) + δ/3).
Since g(J₀) = t + δ/2, we get q > t + δ/2 - δ/3 = t + δ/6.
So q > t. ✓

If L = g(J₁): then q ∈ (g(J₁) - δ/3, g(J₁) + δ/3).
Since g(J₁) = t - δ/2, we get q < t - δ/2 + δ/3 = t - δ/6.
So q < t. ✓

The intervals are disjoint (separated by 2·δ/6 = δ/3 > 0). So:

  q > t  ⟹  L = g(J₀)  ⟹  Case A  ⟹  ∀n, α(n) = 0
  q ≤ t  ⟹  L = g(J₁)  ⟹  Case B  ⟹  ∃n, α(n) = 1

### 4.5 Rigorous justification of the case analysis

We need to prove: if q > t then α ≡ 0, and if q ≤ t then ∃n, α(n) = 1.

**Case q > t (proving α ≡ 0):**

Suppose for contradiction that ∃n₀, α(n₀) = 1. Then by §4.2 Case B,
L = g(J₁). But then |q - g(J₁)| < δ/3, so q < g(J₁) + δ/3 =
(t - δ/2) + δ/3 = t - δ/6 < t. This contradicts q > t. Therefore
¬(∃n₀, α(n₀) = 1), which in BISH gives ∀n, α(n) = 0 (since α(n) = 1
is decidable for each n, so ¬∃n.P(n) ↔ ∀n.¬P(n) for decidable P).

**Constructive note:** The step from ¬(∃n, α(n) = 1) to ∀n, α(n) = 0
is constructively valid because α(n) ∈ {0, 1} — the predicate is
decidable. We are NOT using ¬∃ → ∀¬ for arbitrary predicates (which
would require Markov's principle or classical logic). For decidable
predicates on ℕ, the equivalence ¬(∃n, P(n)) ↔ ∀n, ¬P(n) is BISH-valid.

**Case q ≤ t (extracting the witness):**

We know L = g(J₁) (by the same gap argument: if L = g(J₀), then q > t,
contradicting q ≤ t). So Case B holds: ∃n₀, α(n₀) = 1. But we need
the actual witness, not just the existence claim.

### 4.6 Witness extraction by bounded search

Since L is a constructive real with modulus M, we can compute N₁ such
that |F(N₁) - L| < δ/3. Specifically, take N₁ = M(k) where 1/2^k < δ/3.

We know:
  L = g(J₁)
  |F(N₁) - g(J₁)| < δ/3
  F(N₁) ∈ {g(J₀), g(J₁)}

Since |g(J₀) - g(J₁)| = δ and δ/3 < δ, the approximation F(N₁) cannot
be g(J₀) (because |g(J₀) - g(J₁)| = δ > δ/3, so g(J₀) is too far
from g(J₁) to satisfy the bound). Therefore F(N₁) = g(J₁).

**Wait — this needs more care.** F(N₁) ∈ {g(J₀), g(J₁)} is a
constructive fact (because J(N₁) ∈ {J₀, J₁}, which is decidable —
just compute m(N₁) from α(0),...,α(N₁)). And |F(N₁) - g(J₁)| < δ/3.
If F(N₁) = g(J₀), then |g(J₀) - g(J₁)| = δ, but we need δ < δ/3,
contradiction. So F(N₁) = g(J₁).

Therefore J(N₁) = J₁ (since g is injective — strictly decreasing).
Therefore m(N₁) = 1. Therefore ∃k ≤ N₁, α(k) = 1.

Now find the witness by bounded search: for k = 0, 1, ..., N₁, check
whether α(k) = 1. This terminates because we know at least one such k
exists, and the search space is finite. The first k with α(k) = 1 is
the witness.

**Constructive note:** Bounded search over a decidable predicate on
{0, 1, ..., N₁} is a BISH-valid operation. It requires no omniscience
principle. The search terminates because we have a proof that the
predicate is satisfied somewhere in the range.  ∎

---

## 5. The Combined Theorem

**Theorem 5.1 (LPO ↔ BMC ↔ Free Energy Convergence).** Over BISH:

(1) LPO
(2) BMC (Bounded Monotone Convergence)
(3) For every non-decreasing sequence J : ℕ → [J₀, J₁] (with
    0 < J₀ < J₁ rationals) and every rational β > 0, the sequence
    g(J(N)) = -log(2·cosh(β·J(N))) converges.

are mutually equivalent.

*Proof.*
(1) → (2): [Bridges–Vîță 2006] or axiomatize.
(2) → (3): Immediate (g(J(N)) is bounded and monotone; apply BMC).
(3) → (1): The encoding of §4 and decision procedure of §§4.3–4.6. ∎

### 5.1 What this means (combined with Part A)

**Part A** showed: for the uniform 1D Ising chain with fixed coupling,
|f_N(β) - f_∞(β)| < ε for constructively computable N₀. No omniscience.
BISH suffices for the empirical prediction.

**Part B** showed: asserting that the free energy limit *exists as a
completed real number* for arbitrary (non-decreasing, bounded) coupling
sequences is equivalent to LPO.

**Together:** The LPO cost of the thermodynamic limit is genuine (it is
equivalent to, not merely sufficient for, a known omniscience principle)
and dispensable (the finite-system predictions with error bounds require
no omniscience at all).

### 5.2 Calibration table update

| Physical layer | Principle | Status | Source |
|---|---|---|---|
| Finite-volume Gibbs states | BISH | Calibrated | Trivial |
| Finite-size approximations | BISH | Calibrated | Part A |
| Bidual-gap witness (S₁(H)) | ≡ WLPO | Calibrated | Papers 2, 7 |
| Thermodynamic limit existence | ≡ LPO | Calibrated | Part B |
| Spectral gap decidability | Undecidable | Established | Cubitt et al. |

---

## 6. Lean 4 Formalization Guide

### 6.1 Definitions

```lean
-- LPO
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

-- Bounded Monotone Convergence
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

-- Running maximum of a binary sequence
def runMax (α : ℕ → Bool) : ℕ → Bool
  | 0 => α 0
  | n + 1 => α (n + 1) || runMax α n

-- Coupling sequence from α
noncomputable def couplingSeq (α : ℕ → Bool) (J₀ J₁ : ℝ) (n : ℕ) : ℝ :=
  if runMax α n then J₁ else J₀

-- Free energy at coupling J (reuses Part A's cosh infrastructure)
noncomputable def freeEnergyAtCoupling (β J : ℝ) : ℝ :=
  -Real.log (2 * Real.cosh (β * J))

-- The encoded sequence
noncomputable def encodedSeq (α : ℕ → Bool) (β J₀ J₁ : ℝ) (n : ℕ) : ℝ :=
  freeEnergyAtCoupling β (couplingSeq α J₀ J₁ n)
```

### 6.2 Key lemmas — Running maximum

```lean
-- runMax is non-decreasing (as Bool with false < true)
lemma runMax_mono (α : ℕ → Bool) (n : ℕ) :
    runMax α n ≤ runMax α (n + 1) := by
  simp [runMax, Bool.or_comm]
  exact Bool.le_or_left _ _
  -- or: unfold runMax; exact le_sup_right (α (n+1)) (runMax α n)

-- runMax false iff all previous terms false
lemma runMax_false_iff (α : ℕ → Bool) (n : ℕ) :
    runMax α n = false ↔ ∀ k, k ≤ n → α k = false := by
  sorry -- induction on n

-- runMax true iff some previous term true
lemma runMax_true_iff (α : ℕ → Bool) (n : ℕ) :
    runMax α n = true ↔ ∃ k, k ≤ n ∧ α k = true := by
  sorry -- induction on n

-- If all terms false, runMax stays false
lemma runMax_of_all_false (α : ℕ → Bool) (h : ∀ n, α n = false) (n : ℕ) :
    runMax α n = false := by
  exact (runMax_false_iff α n).mpr (fun k _ => h k)

-- Once a term is true, runMax stays true
lemma runMax_of_exists_true (α : ℕ → Bool) (n₀ : ℕ) (h : α n₀ = true)
    (n : ℕ) (hn : n₀ ≤ n) :
    runMax α n = true := by
  sorry -- induction from n₀ to n
```

### 6.3 Key lemmas — Coupling sequence

```lean
-- Coupling values are in {J₀, J₁}
lemma couplingSeq_mem (α : ℕ → Bool) (J₀ J₁ : ℝ) (n : ℕ) :
    couplingSeq α J₀ J₁ n = J₀ ∨ couplingSeq α J₀ J₁ n = J₁ := by
  unfold couplingSeq; cases runMax α n <;> simp

-- Coupling is non-decreasing (when J₀ ≤ J₁)
lemma couplingSeq_mono (α : ℕ → Bool) (J₀ J₁ : ℝ) (hJ : J₀ ≤ J₁) :
    Monotone (couplingSeq α J₀ J₁) := by
  sorry -- uses runMax_mono

-- Coupling bounded
lemma couplingSeq_bounded (α : ℕ → Bool) (J₀ J₁ : ℝ) (hJ : J₀ ≤ J₁)
    (n : ℕ) :
    J₀ ≤ couplingSeq α J₀ J₁ n ∧ couplingSeq α J₀ J₁ n ≤ J₁ := by
  sorry -- case split on runMax

-- If α ≡ false: coupling ≡ J₀
lemma couplingSeq_of_all_false (α : ℕ → Bool) (J₀ J₁ : ℝ)
    (h : ∀ n, α n = false) (n : ℕ) :
    couplingSeq α J₀ J₁ n = J₀ := by
  simp [couplingSeq, runMax_of_all_false α h n]

-- If ∃ n₀ with α(n₀) = true: eventually coupling ≡ J₁
lemma couplingSeq_of_exists_true (α : ℕ → Bool) (J₀ J₁ : ℝ)
    (n₀ : ℕ) (h : α n₀ = true) (n : ℕ) (hn : n₀ ≤ n) :
    couplingSeq α J₀ J₁ n = J₁ := by
  simp [couplingSeq, runMax_of_exists_true α n₀ h n hn]
```

### 6.4 Key lemmas — Free energy function

```lean
-- cosh strictly increasing on (0, ∞)
lemma Real.cosh_strictMono_on_pos :
    StrictMonoOn Real.cosh (Set.Ioi 0) := by sorry

-- g(J) = -log(2·cosh(β·J)) is strictly decreasing for β > 0
lemma freeEnergyAtCoupling_strictAnti (β : ℝ) (hβ : 0 < β) :
    StrictAnti (freeEnergyAtCoupling β) := by
  sorry -- chain: J₁ > J₂ → β·J₁ > β·J₂ → cosh increases → log increases → negate

-- g is injective (immediate from strict anti)
lemma freeEnergyAtCoupling_injective (β : ℝ) (hβ : 0 < β) :
    Function.Injective (freeEnergyAtCoupling β) :=
  (freeEnergyAtCoupling_strictAnti β hβ).injective

-- The gap: g(J₀) - g(J₁) > 0 when J₀ < J₁
lemma freeEnergy_gap (β J₀ J₁ : ℝ) (hβ : 0 < β) (hJ : J₀ < J₁) :
    0 < freeEnergyAtCoupling β J₀ - freeEnergyAtCoupling β J₁ := by
  exact sub_pos.mpr (freeEnergyAtCoupling_strictAnti β hβ hJ)

-- g(J₀) > g(J₁) (restatement)
lemma freeEnergy_lt (β J₀ J₁ : ℝ) (hβ : 0 < β) (hJ : J₀ < J₁) :
    freeEnergyAtCoupling β J₁ < freeEnergyAtCoupling β J₀ :=
  freeEnergyAtCoupling_strictAnti β hβ hJ
```

### 6.5 Key lemmas — Encoded sequence

```lean
-- encodedSeq values
lemma encodedSeq_of_all_false (α : ℕ → Bool) (β J₀ J₁ : ℝ)
    (h : ∀ n, α n = false) (n : ℕ) :
    encodedSeq α β J₀ J₁ n = freeEnergyAtCoupling β J₀ := by
  simp [encodedSeq, couplingSeq_of_all_false α J₀ J₁ h n]

lemma encodedSeq_of_exists_true (α : ℕ → Bool) (β J₀ J₁ : ℝ)
    (n₀ : ℕ) (h : α n₀ = true) (n : ℕ) (hn : n₀ ≤ n) :
    encodedSeq α β J₀ J₁ n = freeEnergyAtCoupling β J₁ := by
  simp [encodedSeq, couplingSeq_of_exists_true α J₀ J₁ n₀ h n hn]

-- encodedSeq takes values in {g(J₀), g(J₁)}
lemma encodedSeq_mem (α : ℕ → Bool) (β J₀ J₁ : ℝ) (n : ℕ) :
    encodedSeq α β J₀ J₁ n = freeEnergyAtCoupling β J₀ ∨
    encodedSeq α β J₀ J₁ n = freeEnergyAtCoupling β J₁ := by
  sorry -- from couplingSeq_mem

-- Negated encodedSeq is non-decreasing and bounded
lemma neg_encodedSeq_mono (α : ℕ → Bool) (β J₀ J₁ : ℝ)
    (hβ : 0 < β) (hJ : J₀ < J₁) :
    Monotone (fun n => -encodedSeq α β J₀ J₁ n) := by
  sorry -- from couplingSeq_mono + freeEnergyAtCoupling_strictAnti

lemma neg_encodedSeq_bounded (α : ℕ → Bool) (β J₀ J₁ : ℝ)
    (hβ : 0 < β) (hJ₀ : 0 < J₀) (hJ : J₀ < J₁) (n : ℕ) :
    -encodedSeq α β J₀ J₁ n ≤ -freeEnergyAtCoupling β J₁ := by
  sorry -- g(J₁) ≤ encodedSeq, so -encodedSeq ≤ -g(J₁)
```

### 6.6 Main theorem — backward direction

```lean
/-- The main result: BMC implies LPO. The proof encodes a binary sequence
    into a free energy sequence and uses the limit to decide the sequence. -/
theorem lpo_of_bmc (hBMC : BMC) : LPO := by
  intro α
  -- Fix parameters
  set β : ℝ := 1        -- any positive rational works
  set J₀ : ℝ := 1
  set J₁ : ℝ := 2
  -- Construct the encoded sequence
  set F := encodedSeq α β J₀ J₁
  -- Apply BMC to -F (which is non-decreasing and bounded)
  have hMono : Monotone (fun n => -F n) := neg_encodedSeq_mono α β J₀ J₁ (by norm_num) (by norm_num)
  have hBdd : ∀ n, -F n ≤ -freeEnergyAtCoupling β J₁ :=
    neg_encodedSeq_bounded α β J₀ J₁ (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨L_neg, hL_neg⟩ := hBMC (fun n => -F n) (-freeEnergyAtCoupling β J₁) hMono hBdd
  -- L = -L_neg is the limit of F
  set L := -L_neg
  -- Compute the gap
  have hδ : 0 < freeEnergyAtCoupling β J₀ - freeEnergyAtCoupling β J₁ :=
    freeEnergy_gap β J₀ J₁ (by norm_num) (by norm_num)
  set δ := freeEnergyAtCoupling β J₀ - freeEnergyAtCoupling β J₁
  -- Approximate L to within δ/3
  -- (extract a rational q with |L - q| < δ/3 from the modulus)
  -- Compare q with threshold t = (g(J₀) + g(J₁))/2
  -- Case split on q > t vs q ≤ t (decidable, rational comparison)
  -- If q > t: prove ∀ n, α n = false (by contradiction using Case B → L = g(J₁))
  -- If q ≤ t: extract witness
  --   Get N₁ from modulus with |F(N₁) - L| < δ/3
  --   F(N₁) ∈ {g(J₀), g(J₁)} and |F(N₁) - g(J₁)| < δ/3 forces F(N₁) = g(J₁)
  --   So m(N₁) = true, hence ∃ k ≤ N₁, α k = true
  --   Bounded search finds k
  sorry
```

### 6.7 Module structure

```
Paper8_PartB_LPO/
├── Defs/
│   ├── LPO.lean              -- LPO, BMC definitions
│   ├── RunMax.lean            -- runMax, monotonicity, characterization
│   └── CouplingEncoding.lean  -- couplingSeq, encodedSeq
├── Props/
│   ├── FreeEnergyAnti.lean    -- g strictly decreasing, gap lemma
│   ├── EncodedSeqProps.lean   -- value lemmas, monotonicity, boundedness
│   └── BoundedSearch.lean     -- witness extraction from ∃k ≤ N₁
├── Main/
│   ├── LPO_of_BMC.lean       -- The backward direction (main theorem)
│   ├── BMC_of_LPO.lean       -- Forward direction (axiomatize or prove)
│   └── Equiv.lean            -- LPO ↔ BMC ↔ FreeEnergyConvergence
└── SmokeTest.lean             -- Import check, #print axioms
```

### 6.8 Estimated line counts

| Module | Lines | Difficulty |
|---|---|---|
| LPO.lean | ~20 | Trivial |
| RunMax.lean | ~60 | Easy (induction) |
| CouplingEncoding.lean | ~40 | Easy |
| FreeEnergyAnti.lean | ~80 | Medium (cosh monotonicity) |
| EncodedSeqProps.lean | ~50 | Easy |
| BoundedSearch.lean | ~30 | Easy |
| LPO_of_BMC.lean | ~120 | Hard (rational approximation, case split) |
| BMC_of_LPO.lean | ~50 | Medium or axiomatize (~5) |
| Equiv.lean | ~20 | Trivial |
| SmokeTest.lean | ~10 | Trivial |
| **Total** | **~480** | |

Combined with Part A (~729 lines), the full paper formalization is
~1,200 lines.

### 6.9 Axiom targets

```
#print axioms lpo_of_bmc
-- Target: NO classical axioms beyond propext, Quot.sound
-- (the proof is constructive modulo the BMC hypothesis)
-- BMC appears as a hypothesis, not an axiom

#print axioms lpo_iff_bmc
-- Should show same clean profile
-- LPO and BMC appear only in the statement, not as axioms
```

---

## 7. Key Formalization Challenges

### 7.1 Rational approximation of a constructive real

The hardest step in the Lean formalization is extracting a rational
approximation from the constructive real L. In BISH, a constructive
real comes with a modulus, so this is by definition available. In Lean 4
(Mathlib), ℝ is defined as Cauchy sequences modulo equivalence, and
extracting rational approximations requires going through the quotient.

**Pragmatic approach:** Instead of extracting a rational q and comparing
with t, compare L directly with t. Since t is rational and L is real,
the comparison L < t ∨ L > t - δ/3 is available via the Archimedean
property of ℝ.

Actually, the cleanest approach for Lean:

Since L ∈ {g(J₀), g(J₁)} (the only two possible limit values), and
g(J₀) > g(J₁), we can use:

  Either |L - g(J₀)| < δ/2 or |L - g(J₁)| < δ/2

This is a tautology given L ∈ {g(J₀), g(J₁)}. But constructively
deciding WHICH holds is the issue. We get around this by using the
modulus: approximate L, compare with the midpoint, and the comparison
is decidable because we're comparing rationals.

Alternatively, use the fact that F(N) ∈ {g(J₀), g(J₁)} (decidable for
each N) and F is eventually constant. Once F stabilizes, the limit
equals the stabilized value. So:

**Alternative decision procedure (may be easier to formalize):**

1. Approximate L within δ/3 to get rational q.
2. If q > midpoint: output left disjunct.
3. If q ≤ midpoint: find N₁ from modulus, compute F(N₁) (decidable),
   observe F(N₁) = g(J₁), extract witness by bounded search.

### 7.2 Decidability of F(N₁) ∈ {g(J₀), g(J₁)}

F(N₁) = g(J(N₁)) where J(N₁) ∈ {J₀, J₁}. Since J(N₁) = J₀ or
J(N₁) = J₁ depending on m(N₁) ∈ {false, true}, and m(N₁) is a Bool,
the case split is definitional. No real-number comparison needed.

This is important: we don't need to compare F(N₁) with g(J₀) as real
numbers. We compute m(N₁) as a Bool, and branch on that. If m(N₁) =
true, we already have our witness (bounded search on 0..N₁). If
m(N₁) = false, we derive a contradiction from the convergence bound.

### 7.3 The contradiction in the q > t case

If q > t and ∃n₀ with α(n₀) = 1, then L = g(J₁). Then
|q - L| = |q - g(J₁)| < δ/3, so q < g(J₁) + δ/3 = t - δ/6 < t.
But q > t. Contradiction.

The inequalities g(J₁) + δ/3 = t - δ/6 need:
  g(J₁) = t - δ/2 (definition of t as midpoint)
  g(J₁) + δ/3 = (t - δ/2) + δ/3 = t - δ/6

This is just rational arithmetic. Clean for Lean.

---

## 8. Appendix: Why the Encoding Is Not Circular

A potential objection: "You defined F(N) ∈ {g(J₀), g(J₁)}, which is a
{0,1}-valued sequence in disguise. The convergence of a {0,1}-valued
monotone sequence is trivially decidable. You're just restating BMC for
the simplest possible case."

**Response:** This objection is correct at the mathematical level and
irrelevant at the interpretive level. The point of the encoding is not
to produce a new theorem in constructive reverse mathematics — BMC ↔ LPO
is known [Bridges–Vîță 2006]. The point is to show that BMC, when
instantiated through the free energy function of the 1D Ising model,
IS the assertion that the thermodynamic limit exists. The mathematical
equivalence is known; the physical interpretation is new.

The formalization verifies that the physical instantiation goes through
cleanly — that no hidden axioms are needed for the encoding, that the
gap δ is constructively positive, and that the witness extraction works
in BISH. The Lean code makes explicit what the mathematical prose
leaves implicit.

This is the same methodological move as Paper 2 (WLPO ↔ bidual gap):
the abstract equivalence (WLPO ↔ ¬¬-stable decidability) was known
from Ishihara and Diener. The contribution was the specific Banach-space
instantiation and the machine verification. Here, the abstract
equivalence (LPO ↔ BMC) is known from Bridges–Vîță. The contribution
is the physical instantiation and the machine verification.

---

## 9. Combined Paper Outline (Parts A + B)

§1. Introduction — the question (exact logical cost of thermodynamic
    limit; is it essential or dispensable?)

§2. Setup — 1D Ising, transfer matrix eigenvalues λ₊ = 2cosh(β),
    λ₋ = 2sinh(β), partition function Z_N = λ₊^N + λ₋^N, free energy
    density f_N = -(1/N)·log(λ₊^N + λ₋^N), closed form
    f_∞ = -log(2cosh(β)). [Shared infrastructure]

§3. Part A: BISH Dispensability — |f_N - f_∞| ≤ (1/N)·tanh(β)^N,
    constructive N₀, no omniscience. [From existing Paper 8 draft]

§4. Part B: LPO Calibration — BMC ↔ LPO, physical instantiation
    via coupling encoding, decision procedure, witness extraction.
    [This document]

§5. Synthesis — what the combination means; updated calibration table;
    the LPO cost is real and dispensable.

§6. Lean 4 formalization — module structure, #print axioms, link to
    repository.

§7. Discussion — relation to Bridges–Vîță, the encoding objection
    (§8 above), future directions (higher dimensions, general
    Hamiltonians).
