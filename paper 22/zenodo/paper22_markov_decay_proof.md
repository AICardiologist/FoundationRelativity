# Markov's Principle and the Constructive Cost of Eventual Decay

## Paper 22 — Proof Document for Lean 4 Formalization

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose, Context, and Design Principles

### 0.1 What this paper proves

This paper establishes that the assertion "a radioactive nucleus
with nonzero decay rate eventually decays" is equivalent to
Markov's Principle (MP) over BISH. This is the first CRM
calibration at MP — a principle that sits *outside* the main
BISH < LLPO < WLPO < LPO chain, enriching the programme from a
linear hierarchy to a partially ordered structure.

The paper has three parts:

- **Part A (BISH):** For any *known* decay rate λ with an explicit
  lower bound λ ≥ q > 0, the survival probability P(t) = exp(-λt)
  is computable, and the detection time T(ε, q) = -ln(ε)/q is
  explicitly constructible. No omniscience or Markov required.

- **Part B (MP calibration):** The assertion "for every decay rate λ
  satisfying ¬(λ = 0), the survival probability eventually drops
  below any threshold ε > 0" is equivalent to Markov's Principle
  over BISH.

- **Part C (Stratification and hierarchy placement):** MP is
  independent of LLPO and WLPO but implied by LPO. The calibration
  table is extended from a linear chain to a partial order.

### 0.2 What is Markov's Principle?

Markov's Principle (MP): for any binary sequence α : ℕ → Bool,

  ¬(∀n, α(n) = false) → ∃n, α(n) = true

In words: if a sequence is *not* all zeros, then there exists an
index where it is one. The hypothesis provides a negative fact
(it's not all zeros); the conclusion provides a positive witness
(here's where the one is).

Equivalently for reals: if x ≠ 0, then x is apart from 0
(i.e., ∃q ∈ ℚ, |x| > q > 0).

**Status in constructive mathematics:** MP is accepted in the
Russian constructive school (Markov, Shanin) but rejected in
Brouwerian intuitionism and in Bishop's BISH. It is implied by
LPO (trivially: LPO decides the disjunction outright) and by
Church's Thesis (all functions are computable → one can search
for the witness). MP is independent of LLPO and WLPO.

### 0.3 The key physical insight

Radioactive decay with rate λ > 0 has survival probability
P(t) = exp(-λt). For any ε > 0, the detection time
T = -ln(ε)/λ satisfies P(T) = ε. This T is computable
whenever λ is *known* — meaning we have an explicit rational
lower bound λ ≥ q > 0.

But what if we know only that the nucleus is unstable — i.e.,
¬(λ = 0) — without an explicit lower bound? Constructively,
¬(λ = 0) does NOT give us apartness (λ # 0), because the
Cauchy representation of λ might converge to zero too slowly
to detect. The step from ¬(λ = 0) to ∃q > 0 (λ > q) is
exactly Markov's Principle.

Physical example: proton decay in Grand Unified Theories. The
theory predicts the proton is unstable (¬(λ = 0)), but the
experimental lower bound on the proton lifetime is > 10^34
years (Super-Kamiokande). We know it's unstable but don't have
an explicit positive lower bound on the decay rate. MP says:
if the theory is correct and the proton is genuinely unstable,
then a detection time exists — but MP doesn't tell you *when*.

### 0.4 Relationship to existing papers

- **Paper 8** calibrated LPO ↔ BMC (1D Ising free energy limit).
  LPO decides "stable or unstable" without prior information.
  MP is strictly weaker: it only upgrades ¬stable to ∃witness.

- **Papers 19, 21** calibrated LLPO (WKB turning points, Bell
  sign decision). LLPO and MP are independent — neither implies
  the other over BISH. This paper adds a new dimension to the
  calibration table.

- **Paper 20** calibrated WLPO (Ising magnetization zero-test).
  WLPO and MP are also independent. WLPO decides x = 0 ∨ ¬(x = 0);
  MP takes ¬(x = 0) and produces a witness.

### 0.5 Dependencies

This paper is **self-contained** — it does not import from
Papers 8, 19, 20, or 21. The mathematical content (exponential
decay, geometric series) overlaps with Paper 20's encoded field,
but the Lean code is independent.

### 0.6 What the coding agent should NOT do

- Do NOT import Classical.em or Classical.byContradiction in
  Part A modules.
- Do NOT use Decidable instances from Mathlib that import LEM
  silently.
- Do NOT attempt to formalize quantum field theory, Feynman
  diagrams, or any QFT machinery. The decay law P(t) = exp(-λt)
  is treated as a given mathematical model.
- Do NOT conflate MP with LPO. MP requires the hypothesis
  ¬(∀n, α(n) = false); LPO does not.

---

## 1. Mathematical Setup

### 1.1 Exponential decay

The survival probability of a nucleus with decay rate λ ≥ 0 is:

  P(t, λ) = exp(-λ · t)

For λ > 0 and any threshold ε ∈ (0, 1), the detection time is:

  T(ε, λ) = -ln(ε) / λ = ln(1/ε) / λ

and P(T, λ) = ε. Both P and T are computable when λ is given
as a computable real with a known positive lower bound.

**Lean definitions:**
```lean
/-- Survival probability: P(t, λ) = exp(-λ * t) -/
noncomputable def survivalProb (λ_ t : ℝ) : ℝ :=
  Real.exp (-(λ_ * t))

/-- Detection time: T(ε, λ) = ln(1/ε) / λ -/
noncomputable def detectionTime (ε λ_ : ℝ) : ℝ :=
  Real.log (1 / ε) / λ_
```

### 1.2 Markov's Principle

```lean
/-- Markov's Principle for binary sequences. -/
def MarkovPrinciple : Prop :=
  ∀ (α : ℕ → Bool),
    ¬(∀ n, α n = false) → ∃ n, α n = true
```

### 1.3 Markov's Principle for reals (MP_real)

The real-valued form: if x ≠ 0 then x is apart from 0.

```lean
/-- MP for reals: nonzero implies apart from zero. -/
def MP_real : Prop :=
  ∀ (x : ℝ), x ≠ 0 → ∃ (q : ℚ), (0 < (q : ℝ)) ∧ (q : ℝ) < |x|
```

The equivalence MP ↔ MP_real is standard (Bridges–Richman 1987).
We axiomatize one direction and prove the other.

### 1.4 The EventualDecay assertion

```lean
/-- Eventual decay: for any nonzero decay rate and threshold,
    the survival probability eventually drops below the threshold. -/
def EventualDecay : Prop :=
  ∀ (λ_ : ℝ), λ_ ≠ 0 →
    ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ∃ (T : ℝ), 0 < T ∧ survivalProb λ_ T < ε
```

Note: the hypothesis is λ ≠ 0 (nonzero), not λ > 0 (positive
and apart from zero). The gap between these is exactly where
MP operates.

Actually, we should be more careful. For the decay model to
make physical sense, we need λ ≥ 0 (non-negative decay rate).
And we're asserting eventual decay for λ satisfying ¬(λ = 0)
within the non-negative reals. Let me refine:

```lean
/-- Eventual decay: for any non-negative decay rate that is
    not zero, the survival probability drops below any threshold. -/
def EventualDecay : Prop :=
  ∀ (λ_ : ℝ), 0 ≤ λ_ → λ_ ≠ 0 →
    ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ∃ (T : ℝ), 0 < T ∧ survivalProb λ_ T < ε
```

### 1.5 The encoded decay rate

Given α : ℕ → Bool with ¬(∀n, α(n) = false), define:

  λ_α = Σ_{n=0}^{∞} (if α(n) = true then 2^{-(n+1)} else 0)

This is the same geometric encoding used in Papers 20 and 21.
Properties (proved in those papers, reproved here for
self-containment):

1. **Summability:** The series converges (bounded by geometric
   series Σ 2^{-(n+1)} = 1). BISH.

2. **Non-negativity:** λ_α ≥ 0. Each term is non-negative.

3. **Zero-iff:** λ_α = 0 ↔ ∀n, α(n) = false.

4. **Apartness-from-witness:** If α(k) = true for some k, then
   λ_α ≥ 2^{-(k+1)} > 0. This gives an *explicit* lower bound.

```lean
noncomputable def encodedRate (α : ℕ → Bool) : ℝ :=
  tsum fun n => if α n then (2 : ℝ)⁻¹ ^ (n + 1) else 0

theorem encodedRate_nonneg (α : ℕ → Bool) :
    0 ≤ encodedRate α := sorry

theorem encodedRate_eq_zero_iff (α : ℕ → Bool) :
    encodedRate α = 0 ↔ ∀ n, α n = false := sorry

theorem encodedRate_pos_of_witness (α : ℕ → Bool) (k : ℕ)
    (hk : α k = true) :
    (2 : ℝ)⁻¹ ^ (k + 1) ≤ encodedRate α := sorry
```

---

## 2. Part A: BISH Computability with Known Bounds

### 2.1 Statement

**Theorem (Part A).** For any λ with an explicit lower bound
λ ≥ q > 0, any threshold ε ∈ (0, 1), and any time t ≥ 0, the
survival probability P(t, λ) = exp(-λt) is computable, and the
detection time T(ε, q) = ln(1/ε)/q satisfies P(T, λ) ≤ ε.
No omniscience or Markov required.

### 2.2 Proof

**Lemma (Survival probability at detection time).**
For λ ≥ q > 0 and T = ln(1/ε)/q:

  P(T, λ) = exp(-λ · T) ≤ exp(-q · T) = exp(-ln(1/ε)) = ε

The key step: -λ · T ≤ -q · T because λ ≥ q and T > 0.
Then exp is monotone increasing, and exp(-q · ln(1/ε)/q) =
exp(-ln(1/ε)) = 1/(1/ε) = ε.

```lean
/-- Part A main: with an explicit lower bound, detection time
    is constructively computable. -/
theorem detection_time_works (λ_ q ε : ℝ)
    (hq : 0 < q) (hλq : q ≤ λ_) (hε : 0 < ε) (hε1 : ε < 1) :
    survivalProb λ_ (detectionTime ε q) ≤ ε := by
  sorry
  -- Proof sketch:
  -- 1. detectionTime ε q = ln(1/ε) / q > 0
  -- 2. -λ_ * (ln(1/ε)/q) ≤ -q * (ln(1/ε)/q) = -ln(1/ε)
  -- 3. exp(-λ_ * T) ≤ exp(-ln(1/ε)) = ε
```

**Lemma (Detection time is positive).**
For q > 0 and ε ∈ (0, 1): T = ln(1/ε)/q > 0.
Since ε < 1, we have 1/ε > 1, so ln(1/ε) > 0. Then T > 0.

```lean
theorem detectionTime_pos (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε1 : ε < 1) :
    0 < detectionTime ε q := by
  sorry
  -- ln(1/ε) > 0 because 1/ε > 1, and q > 0
```

**Lemma (Survival probability is computable).**
For any computable λ and t, P(t, λ) = exp(-λt) is computable.
This is immediate: exp is a computable function on computable reals.

### 2.3 The explicit-bound case: witness extraction

When λ is given by the encoded rate λ_α with a known witness
α(k) = true, we have the explicit lower bound λ_α ≥ 2^{-(k+1)}.
The detection time T(ε, 2^{-(k+1)}) = ln(1/ε) · 2^{k+1} is
then computable. This is BISH: the witness k gives an explicit
bound, and everything flows from there.

```lean
/-- With a witness, detection time is explicitly computable. -/
theorem detection_with_witness (α : ℕ → Bool) (k : ℕ)
    (hk : α k = true) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (T : ℝ), 0 < T ∧
      survivalProb (encodedRate α) T ≤ ε := by
  sorry
  -- Use q = 2^{-(k+1)}, T = ln(1/ε) / q
  -- Apply detection_time_works with hλq from encodedRate_pos_of_witness
```

### 2.4 Axiom audit for Part A

All Part A theorems should show:
  [propext, Classical.choice, Quot.sound]

No custom axioms (no MarkovPrinciple, no mp_real_of_mp).
The explicit lower bound makes everything constructive.

---

## 3. Part B: Markov Calibration

### 3.1 The interface axiom

```lean
/-- MP for sequences implies MP for reals.
    Standard (Bridges-Richman 1987, Bridges-Vîță 2006). -/
axiom mp_real_of_mp :
  MarkovPrinciple →
    ∀ (x : ℝ), 0 ≤ x → x ≠ 0 → ∃ (q : ℚ), (0 < (q : ℝ)) ∧ (q : ℝ) ≤ x
```

Note: we use the non-negative form (0 ≤ x, x ≠ 0 → x is apart
from 0 from above) since decay rates are non-negative. The general
form (x ≠ 0 → |x| is apart from 0) is equivalent but the
non-negative restriction is cleaner for the physics.

### 3.2 Forward direction: MP → EventualDecay

**Theorem.** Assume Markov's Principle. Then EventualDecay holds:
for any λ ≥ 0 with λ ≠ 0 and any ε ∈ (0, 1), there exists
T > 0 with P(T, λ) < ε.

**Proof.**

1. Apply mp_real_of_mp to λ: since 0 ≤ λ and λ ≠ 0, obtain
   q : ℚ with 0 < q ≤ λ.

2. Set T = ln(1/ε) / q. By Part A (detection_time_works),
   P(T, λ) ≤ ε.

   Actually, we need P(T, λ) < ε strictly. Since λ ≥ q and
   we want strict inequality, note that if λ > q (which MP
   might not guarantee — it gives q ≤ λ), then we get
   -λT < -qT and exp(-λT) < exp(-qT) = ε.

   If λ = q exactly, then P(T, λ) = ε, not < ε. Fix: use
   T' = T + 1. Then P(T', λ) = exp(-λ(T+1)) = exp(-λT)·exp(-λ)
   < ε · 1 = ε (since exp(-λ) < 1 for λ > 0, and we have
   q ≤ λ, q > 0, so λ > 0).

   Actually simpler: use T = ln(1/ε) / q + 1. Then
   P(T, λ) ≤ exp(-q · T) = exp(-ln(1/ε) - q) = ε · exp(-q) < ε.

   Or even simpler: change ε to ε/2 in the detection time
   computation, getting T = ln(2/ε)/q, and then P(T, λ) ≤ ε/2 < ε.

```lean
/-- Forward: MP implies EventualDecay. -/
theorem eventualDecay_of_mp (hmp : MarkovPrinciple) :
    EventualDecay := by
  intro λ_ hλnn hλne ε hε hε1
  -- Step 1: MP gives apartness
  obtain ⟨q, hqpos, hqle⟩ := mp_real_of_mp hmp λ_ hλnn hλne
  -- Step 2: Use detection time with half-threshold for strict ineq
  -- T = ln(2/ε) / q
  use detectionTime (ε / 2) q
  constructor
  · exact detectionTime_pos q (ε / 2) hqpos (by linarith) (by linarith)
  · calc survivalProb λ_ (detectionTime (ε / 2) q)
        ≤ ε / 2 := detection_time_works λ_ q (ε / 2) hqpos hqle
                      (by linarith) (by linarith)
      _ < ε := by linarith
```

### 3.3 Backward direction: EventualDecay → MP (novel)

**Theorem.** If EventualDecay holds, then Markov's Principle holds.

**Proof.**

Let α : ℕ → Bool with ¬(∀n, α(n) = false). We must produce
∃n, α(n) = true.

**Step 1.** Construct λ_α = Σ α(n) · 2^{-(n+1)}.

**Step 2.** From ¬(∀n, α(n) = false) and encodedRate_eq_zero_iff,
we get ¬(λ_α = 0). Also λ_α ≥ 0 (non-negative series).

**Step 3.** Apply EventualDecay to λ_α with ε = 1/2:
obtain T > 0 with exp(-λ_α · T) < 1/2.

**Step 4.** From exp(-λ_α · T) < 1/2, deduce λ_α · T > ln(2),
hence λ_α > ln(2)/T > 0.

**Step 5.** Now we have an explicit positive lower bound on λ_α:
λ_α > ln(2)/T =: δ > 0.

**Step 6.** Since λ_α = Σ α(n) · 2^{-(n+1)} and the partial sums
s_k = Σ_{n=0}^{k} α(n) · 2^{-(n+1)} converge to λ_α from below,
and λ_α > δ > 0, there exists k₀ such that s_{k₀} > δ/2 > 0.

  **How to find k₀:** Since |λ_α - s_k| ≤ 2^{-k} (tail bound),
  choose k₀ such that 2^{-k₀} < δ/2, i.e., k₀ > log₂(2/δ).
  Then s_{k₀} ≥ λ_α - 2^{-k₀} > δ - δ/2 = δ/2 > 0.

  k₀ is computable from δ (which is ln(2)/T, obtained from
  the EventualDecay oracle). This step uses only BISH
  (explicit computation of k₀ from a known positive bound).

**Step 7.** Since s_{k₀} > 0 and s_{k₀} = Σ_{n=0}^{k₀} α(n) · 2^{-(n+1)},
and each term is either 0 or 2^{-(n+1)}, at least one term must be
nonzero. Search through n = 0, 1, ..., k₀ (a finite, bounded search)
to find some n with α(n) = true.

  This is a bounded search over a *finite* range — BISH. We're not
  searching over all ℕ; we're searching over {0, ..., k₀}, which is
  finite and decidable (since α(n) : Bool is decidable).

**Step 8.** Output this n as the witness for ∃n, α(n) = true. ∎

**⚠ CRITICAL SUBTLETY:** Step 6 requires going from "λ_α > δ" to
"some partial sum exceeds δ/2." This uses the fact that the partial
sums converge to λ_α with a *known rate* (geometric tail bound
|λ_α - s_k| ≤ 2^{-k}). This known rate is essential — without it,
finding k₀ might require unbounded search, which is exactly what
we're trying to avoid. The geometric encoding provides this rate
constructively (BISH).

**⚠ ANOTHER SUBTLETY:** Step 4 (going from exp(-λ_α T) < 1/2 to
λ_α > ln(2)/T) uses:

  exp(-λ_α · T) < 1/2
  → -λ_α · T < ln(1/2) = -ln(2)
  → λ_α · T > ln(2)
  → λ_α > ln(2)/T

This uses that exp is strictly monotone and that T > 0. Both are
BISH. The inequality manipulation is straightforward real arithmetic.

```lean
/-- Backward (novel): EventualDecay implies MarkovPrinciple. -/
theorem mp_of_eventualDecay (hed : EventualDecay) :
    MarkovPrinciple := by
  intro α hne
  -- Step 1-2: construct encoded rate, get nonzero
  have hλnn : 0 ≤ encodedRate α := encodedRate_nonneg α
  have hλne : encodedRate α ≠ 0 := by
    intro heq
    exact hne ((encodedRate_eq_zero_iff α).mp heq)
  -- Step 3: apply EventualDecay with ε = 1/2
  obtain ⟨T, hTpos, hPlt⟩ := hed (encodedRate α) hλnn hλne (1/2)
    (by norm_num) (by norm_num)
  -- Step 4: extract positive lower bound on λ_α
  have hλpos : encodedRate α > 0 := by
    sorry -- From exp(-λT) < 1/2 and T > 0, deduce λ > ln(2)/T > 0
  -- Step 5-6: find k₀ such that partial sum exceeds bound
  have hδ : ∃ (δ : ℝ), 0 < δ ∧ δ ≤ encodedRate α := ⟨_, hλpos, le_refl _⟩
  sorry -- Use tail bound to find k₀, then bounded search
  -- Step 7: bounded search over {0, ..., k₀}
  -- This is decidable: α n is Bool
```

### 3.4 The equivalence theorem

**Theorem (Main).** Over BISH, the following are equivalent:

1. Markov's Principle
2. EventualDecay

```lean
theorem mp_iff_eventualDecay :
    MarkovPrinciple ↔ EventualDecay :=
  ⟨eventualDecay_of_mp, mp_of_eventualDecay⟩
```

---

## 4. Part C: Hierarchy Placement

### 4.1 MP is implied by LPO

LPO decides (∀n, α(n) = false) ∨ (∃n, α(n) = true) without any
hypothesis. MP only needs to produce ∃n from the hypothesis
¬(∀n). So LPO trivially implies MP:

```lean
theorem mp_of_lpo (hlpo : LPO) : MarkovPrinciple := by
  intro α hne
  rcases hlpo α with hall | ⟨n, hn⟩
  · exact absurd hall hne
  · exact ⟨n, hn⟩
```

### 4.2 MP does NOT imply LPO (separation)

This is a standard result (Bridges–Richman 1987): there exist
models of BISH + MP where LPO fails. We do not formalize the
separation (it requires constructing a specific topological model),
but state it as a remark.

### 4.3 MP is independent of LLPO and WLPO

Neither MP → LLPO nor LLPO → MP holds over BISH. Similarly for
WLPO. These are standard independence results. The calibration
table becomes a partial order:

```
        LPO
       / | \
      /  |  \
   WLPO  MP  ...
    |
   LLPO
    |
   BISH
```

Where MP branches off from the main chain. LPO implies everything.
WLPO implies LLPO but not MP. MP doesn't imply WLPO or LLPO.

```lean
/-- LPO implies MP (easy direction). -/
theorem mp_of_lpo (hlpo : LPO) : MarkovPrinciple := by
  intro α hne
  rcases hlpo α with hall | ⟨n, hn⟩
  · exact absurd hall hne
  · exact ⟨n, hn⟩

/-- LPO implies WLPO (for completeness). -/
theorem wlpo_of_lpo (hlpo : LPO) : WLPO := by
  intro α
  rcases hlpo α with hall | ⟨n, hn⟩
  · exact Or.inl hall
  · exact Or.inr (fun hall => by simp [hall n] at hn)
```

### 4.4 The calibration table update

| Paper | Physical System | Observable / Assertion | CRM Level | Position |
|-------|----------------|----------------------|-----------|----------|
| 8 | 1D Ising | Free energy limit | LPO | Main chain |
| 15 | Noether | Global energy conservation | LPO | Main chain |
| 19 | WKB tunneling | Turning points | LLPO | Main chain |
| 19 | WKB tunneling | Full semiclassical limit | LPO | Main chain |
| 20 | 1D Ising | Phase classification | WLPO | Main chain |
| 21 | Bell/CHSH | Sign of Bell asymmetry | LLPO | Main chain |
| **22** | **Radioactive decay** | **Eventual decay** | **MP** | **Branch** |

Paper 22 is the first entry *off the main chain*. It shows the
constructive hierarchy of physics is not purely linear — there's
a branch point at the level of "upgrading non-equality to
apartness."

---

## 5. Lean 4 Formalization Guide

### 5.1 Module structure

```
Paper22_MarkovDecay/
├── Defs/
│   ├── Markov.lean              -- MP, LPO, WLPO, LLPO definitions
│   ├── Decay.lean               -- survivalProb, detectionTime, EventualDecay
│   └── EncodedRate.lean         -- λ_α construction, zero-iff, witness bound
├── PartA/
│   ├── DetectionTime.lean       -- T(ε,q) works for known bound
│   ├── SurvivalComputable.lean  -- P(t,λ) computable (BISH)
│   └── PartA_Main.lean          -- Part A summary
├── PartB/
│   ├── Forward.lean             -- MP → EventualDecay
│   ├── Backward.lean            -- EventualDecay → MP (novel)
│   └── PartB_Main.lean          -- MP ↔ EventualDecay
└── Main/
    ├── Hierarchy.lean           -- LPO → MP, LPO → WLPO, WLPO → LLPO
    ├── Stratification.lean      -- Combined statement
    └── AxiomAudit.lean          -- #print axioms
```

**Estimated lines:** ~600–750 total.

### 5.2 Mathlib dependencies

**Required:**
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv` or `.Exp` — Real.exp
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — Real.log
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — tsum, Summable
- `Mathlib.Analysis.SpecificLimits.Basic` — geometric series

**Used from standard:**
- `Real.exp_neg`, `Real.exp_lt_exp`, `Real.exp_log`
- `Real.log_lt_log`, `Real.log_pos`
- `tsum_eq_zero_iff` for non-negative summable series
- `Summable.tsum_pos` for proving positive contributions

**NOT imported:**
- LinearAlgebra.* (no matrices)
- MeasureTheory.* (no probability theory)
- Analysis.NormedSpace.* (no Banach spaces)

### 5.3 Key formalization challenges

**Challenge 1: exp/log manipulation.**

The backward direction (Step 4) requires:

  exp(-λT) < 1/2  →  -λT < ln(1/2)  →  λT > ln(2)  →  λ > ln(2)/T

This chain uses:
- `Real.exp_lt_exp` (exp is strictly monotone)
- `Real.log_lt_log` or `Real.exp_log` (exp and log are inverses)
- Division by T > 0 preserves inequality direction

Each step is elementary but Lean proofs of exp/log inequalities
can be verbose. The coding agent should check which direction of
`Real.exp_lt_iff_lt` is available.

**Recommended approach:** Prove a helper lemma:
```lean
lemma exp_neg_lt_iff (a b : ℝ) (hb : 0 < b) :
    Real.exp (-(a * b)) < Real.exp (-(c * b)) ↔ c < a := sorry
```
or use `Real.exp_lt_exp` directly.

**Challenge 2: From λ_α > δ to finding k₀ (bounded search).**

This is the most delicate step. We need:

1. λ_α > δ > 0 (from Step 4)
2. |λ_α - s_k| ≤ 2^{-k} (tail bound for geometric series)
3. Choose k₀ with 2^{-k₀} < δ/2
4. Then s_{k₀} > δ - δ/2 = δ/2 > 0
5. Search n = 0, ..., k₀ for α(n) = true

Step 3 requires finding k₀ from δ. Since δ is a *real number*
(ln(2)/T where T came from the EventualDecay oracle), we need
k₀ : ℕ with 2^{-k₀} < δ/2. This exists by the Archimedean
property of ℝ, which is constructive (BISH).

**Lean approach:** Use `exists_pow_lt_of_lt_one` or
`Nat.find` with a decidable predicate. Since 2^{-k} → 0 and
δ/2 > 0, there exists k₀ with 2^{-k₀} < δ/2. Then:

```lean
-- Archimedean: find k₀ with 2^{-k₀} < δ/2
obtain ⟨k₀, hk₀⟩ : ∃ k₀, (2 : ℝ)⁻¹ ^ k₀ < δ / 2 := by
  exact exists_pow_lt_of_lt_one (by linarith) (by norm_num)
```

Step 5 (bounded search) should use:
```lean
-- Finite search: ∃ n ≤ k₀, α n = true
-- Since s_{k₀} > 0 and s_{k₀} = Σ_{n≤k₀} α(n) · 2^{-(n+1)},
-- at least one term is nonzero.
-- Use Finset.exists_ne_zero or a custom bounded search lemma.
```

**Challenge 3: Partial sum definition and tail bound.**

Define partial sums:
```lean
noncomputable def partialRate (α : ℕ → Bool) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sum fun n =>
    if α n then (2 : ℝ)⁻¹ ^ (n + 1) else 0
```

Prove the tail bound:
```lean
theorem partialRate_tail_bound (α : ℕ → Bool) (k : ℕ) :
    |encodedRate α - partialRate α k| ≤ (2 : ℝ)⁻¹ ^ (k + 1) := sorry
-- The tail Σ_{n>k} ≤ Σ_{n>k} 2^{-(n+1)} = 2^{-(k+1)}
```

This is a standard tail estimate for geometric series. Should be
available or easily derived from Mathlib's geometric series lemmas.

**Challenge 4: Bounded search extraction.**

From s_{k₀} > 0, extract ∃n ≤ k₀, α(n) = true.

```lean
theorem witness_from_partial_sum_pos (α : ℕ → Bool) (k : ℕ)
    (hpos : 0 < partialRate α k) :
    ∃ n, n ≤ k ∧ α n = true := by
  sorry
  -- The partial sum is a sum of non-negative terms.
  -- If the sum is positive, at least one term is positive.
  -- A positive term means α(n) = true (since the term is
  -- 2^{-(n+1)} when α(n) = true and 0 when α(n) = false).
  -- Use Finset.exists_pos_of_sum_pos or similar.
```

### 5.4 Axiom audit specification

```lean
-- Part A: no custom axioms (BISH)
#print axioms detection_time_works
-- [propext, Classical.choice, Quot.sound]

#print axioms detectionTime_pos
-- [propext, Classical.choice, Quot.sound]

-- Part B forward: uses MP axiom
#print axioms eventualDecay_of_mp
-- [propext, Classical.choice, Quot.sound, mp_real_of_mp]

-- Part B backward: no custom axioms (novel!)
#print axioms mp_of_eventualDecay
-- [propext, Classical.choice, Quot.sound]

-- Main equivalence:
#print axioms mp_iff_eventualDecay
-- [propext, Classical.choice, Quot.sound, mp_real_of_mp]

-- Hierarchy:
#print axioms mp_of_lpo
-- [propext]  or  [propext, Quot.sound]

-- Encoded rate properties: no custom axioms
#print axioms encodedRate_eq_zero_iff
-- [propext, Classical.choice, Quot.sound]
```

---

## 6. Potential Weaknesses and Mitigations

### 6.1 "MP is not on the main chain — does it belong in the programme?"

It belongs BECAUSE it's not on the main chain. The programme
has been presenting a linear hierarchy BISH < LLPO < WLPO < LPO.
If the calibration table only populates a linear chain, it might
be an artifact of only looking for linear structure. Finding a
physical result at MP — which branches off — shows the physics
itself has a partially ordered logical structure, not just a
linear one. This is a genuine discovery about the programme's
scope.

### 6.2 "The decay model P(t) = exp(-λt) is too simple"

The simplicity is a feature. The CRM content is in the
non-constructivity of ¬(λ = 0) → λ # 0, not in the physics of
decay. The exponential model is the vehicle, not the content.
A more complex decay model (multi-exponential, time-dependent rate)
would obscure the MP content without adding logical information.

### 6.3 "The encoding λ_α is the same as in Papers 20 and 21"

Yes — the geometric encoding Σ α(n) · 2^{-(n+1)} is the
programme's standard tool. But the principle extracted is
different each time:
- Paper 20: zero-test on λ_α → WLPO
- Paper 21: sign-test on the difference of two such sums → LLPO
- Paper 22: apartness-test on λ_α → MP

Same encoding, different questions, different principles. This
reinforces the programme's thesis: the logical cost depends on
the question, not the encoding.

### 6.4 "The backward direction's bounded search is trivial"

The bounded search (finding n ≤ k₀ with α(n) = true) is indeed
trivial as a search. The non-trivial part is obtaining k₀ in the
first place. The chain of reasoning is:

  EventualDecay oracle → T with exp(-λ_α T) < 1/2 → λ_α > ln(2)/T
  → δ := ln(2)/T > 0 → k₀ with 2^{-k₀} < δ/2 → s_{k₀} > δ/2 > 0
  → bounded search over {0,...,k₀} → witness

Each step is elementary, but the full chain — from an oracle about
exponential decay to a witness for a binary sequence — is the
encoding. The oracle provides a detection time T, from which we
extract a lower bound on the rate, from which we compute how many
terms of the sequence to check, from which we find the witness by
finite search. The physics (decay) converts the abstract MP
assertion into a concrete witness-extraction procedure.

---

## 7. Non-Lean Content (for the LaTeX paper)

### 7.1 Introduction framing

Open with the observation that the CRM programme has been
exploring a linear hierarchy (BISH < LLPO < WLPO < LPO). This
paper shows the hierarchy is actually a **partial order** — MP
branches off, implied by LPO but independent of LLPO and WLPO.

The physical motivator: physicists distinguish between "a nucleus
is unstable" (theoretical prediction, ¬(λ = 0)) and "we can
detect its decay" (experimental assertion, λ # 0). The gap
between these — knowing instability but not having an explicit
rate — is precisely Markov's Principle.

### 7.2 Discussion points

1. **The partial order structure.** The CRM programme's calibration
   table is no longer a linear chain but a partial order with a
   branch at MP. This is a structural discovery about the
   relationship between physics and constructive logic.

2. **MP as the "eventually observe" principle.** MP says: if
   something is not impossible, it's eventually observed. This
   is the constructive core of empiricism — the step from
   theoretical impossibility-of-impossibility to empirical
   witness. Radioactive decay is the cleanest physical instance.

3. **Connection to the proton decay problem.** Proton decay in
   GUTs is a real instance of the MP gap: the theory predicts
   instability but no explicit rate. Experimental searches
   (Super-Kamiokande) set lower bounds on the lifetime. The MP
   content is: if the GUT is correct, a detection time exists,
   but computing it requires MP (converting ¬(stable) to an
   explicit bound on the rate).

4. **Comparison with Papers 20 and 21.** Same encoding, different
   principles. Observable-dependent logical cost extends to
   MP: the same encoded rate yields WLPO (zero-test), LLPO
   (sign-test on differences), or MP (apartness-test), depending
   on the question asked.

### 7.3 References

- Bridges, D., Richman, F. (1987). *Varieties of Constructive
  Mathematics*. Cambridge. [MP definition, independence results]
- Bridges, D., Vîță, L. (2006). *Techniques of Constructive
  Analysis*. Springer. [MP ↔ MP_real]
- Markov, A.A. (1954). *Theory of Algorithms*. [Original MP]
- Lee, P.C.K. (2026). Papers 8, 19, 20, 21. Zenodo. [Programme context]
- Ishihara, H. (2006). "Constructive reverse mathematics."
  [CRM methodology, independence results]
- Tanabashi, M. et al. (PDG, 2018). *Review of Particle Physics*.
  [Proton lifetime bounds]

---

## 8. Summary for the Coding Agent

**What to build:** A Lean 4 project with ~600–750 lines across
~11 modules proving that eventual radioactive decay is equivalent
to Markov's Principle over BISH.

**The hard parts:**
1. exp/log inequality chain in backward direction (§3.3, Step 4)
2. Archimedean step: finding k₀ from a real δ (§3.3, Step 6)
3. Bounded search extraction from positive partial sum (§3.3, Step 7)
4. Tail bound for geometric partial sums (Challenge 3)

**The easy parts:**
1. MP definition (one line)
2. Forward direction (apply mp_real_of_mp, then Part A)
3. Hierarchy proofs (LPO → MP is trivial)
4. Encoded rate properties (reuse from Paper 20/21 pattern)

**Axiom budget:**
- Part A: zero custom axioms
- Part B forward: one cited axiom (mp_real_of_mp)
- Part B backward: zero custom axioms
- Combined: one cited axiom total

**Success criterion:** `#print axioms` matches §5.4 specification.
Zero `sorry`. Compiles clean.
