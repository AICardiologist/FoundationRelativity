# Bell / CHSH → LLPO: Feasibility Test

## Exploration Document for Lean 4 Coding Agent

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose

This is NOT a paper-ready proof document. This is an **exploration**
to determine whether the CHSH violation of Bell's inequality can be
shown to have LLPO as its exact constructive cost. If the encoding
works, this becomes Paper 21 and the highest-impact paper in the CRM
programme. If it fails, we document why and move on.

**Time budget:** One focused session. Don't spend more than a day.
If you get stuck, document where and why — that's a useful result.

**The prize:** "Bell nonlocality costs exactly LLPO" would connect
CRM to the largest audience in foundations of physics.

**The risk:** A previous agent argued this can't work because Bell's
theorem is a negation (¬LHV), not a disjunction. We think that
assessment was premature but the concern is real. This session tests
whether the concern is fatal or surmountable.

---

## 1. Background: What LLPO Is

### 1.1 Definition

The Lesser Limited Principle of Omniscience:

```lean
def LLPO : Prop :=
  ∀ (α β : ℕ → Bool),
    (¬ ∃ n, α n = true ∧ β n = true) →
    (∀ n, α n = false) ∨ (∀ n, β n = false)
```

In words: given two binary sequences that never both hit 1 at the
same index, at least one of them is identically 0.

### 1.2 Equivalent formulations

LLPO has several known equivalences (Ishihara 2006, Bridges–Richman
1987):

**(E1) Intermediate Value Theorem:** Every continuous f : [0,1] → ℝ
with f(0) < 0 < f(1) has a root. (Paper 19 uses this.)

**(E2) Disjunctive De Morgan:** ¬(P ∧ Q) → ¬P ∨ ¬Q for
propositions that are ¬¬-stable. (This is the relevant one for
Bell.)

**(E3) Real number trichotomy (weak):** For any real x,
x ≤ 0 ∨ x ≥ 0. (Equivalent to LLPO.)

**(E4) Ordering on reals:** For any reals x, y, ¬(x < y ∧ y < x)
is trivial, but x ≤ y ∨ y ≤ x requires LLPO.

### 1.3 The hierarchy

BISH ⊊ LLPO ⊊ WLPO ⊊ LPO

LLPO is the weakest non-trivial principle above BISH. Finding a
physical result at exactly LLPO fills the bottom rung of the
hierarchy with physical content.

---

## 2. Background: CHSH and Bell's Theorem

### 2.1 The CHSH setup

Two parties (Alice, Bob) share a quantum state. Each chooses one
of two measurement settings:
- Alice: A₁ or A₂ (dichotomic, outcomes ±1)
- Bob: B₁ or B₂ (dichotomic, outcomes ±1)

### 2.2 The classical (LHV) bound

Assume a local hidden variable (LHV) model: there exist
predetermined values a₁, a₂, b₁, b₂ ∈ {-1, +1} (functions of a
hidden variable λ) such that the outcome of each measurement is
determined independently of the distant setting choice.

Define the CHSH correlator:

  S = ⟨A₁B₁⟩ + ⟨A₁B₂⟩ + ⟨A₂B₁⟩ - ⟨A₂B₂⟩

**Theorem (CHSH, BISH).** For any fixed (a₁, a₂, b₁, b₂) ∈ {±1}⁴:

  a₁b₁ + a₁b₂ + a₂b₁ - a₂b₂ ∈ {-2, +2}

Therefore |⟨S⟩| ≤ 2 under any LHV model.

**Proof:** Finite case analysis (16 cases). Pure BISH. ∎

### 2.3 The quantum violation

For the singlet state |ψ⟩ = (|01⟩ - |10⟩)/√2 with optimal
measurement angles (π/8 separation):

  S_quantum = 2√2 ≈ 2.828

**This is a finite computation.** The state is a vector in ℂ⁴, the
observables are 4×4 matrices, the expectation values are traces.
All BISH.

### 2.4 The conclusion — where the logic matters

Classically: S_quantum > 2 contradicts |S_LHV| ≤ 2, so ¬LHV. Done.

Constructively: ¬LHV is the same — a finite contradiction. Still BISH.

But the *physical interpretation* — "which measurement setting lacks
predetermined values?" — requires a disjunction. Classically, ¬(all
four predetermined) gives ¬a₁ ∨ ¬a₂ ∨ ¬b₁ ∨ ¬b₂ by De Morgan.
Constructively, this De Morgan step FAILS. You can't distribute the
negation.

**The question:** Does the CHSH structure provide enough to get a
*binary* disjunction (Alice-side fails ∨ Bob-side fails) at exactly
LLPO?

---

## 3. The Encoding Attempts

### Approach A: Direct De Morgan (most natural, may fail)

**Idea:** ¬(P_Alice ∧ P_Bob) → ¬P_Alice ∨ ¬P_Bob where
P_Alice = "A₁ and A₂ have predetermined values" and
P_Bob = "B₁ and B₂ have predetermined values."

**Why this might work:** LLPO is equivalent to the De Morgan law
for ¬¬-stable propositions (E2 above). The propositions P_Alice
and P_Bob concern the existence of deterministic value assignments,
which are decidable (hence ¬¬-stable) for finite sets.

**Why this might fail:** P_Alice and P_Bob as stated are not
clearly ¬¬-stable in the relevant constructive sense. "Alice's
measurements have predetermined values" means ∃a₁,a₂ ∈ {±1}
consistent with all observations. This is a finite existential
— decidable, hence ¬¬-stable. But the consistency requirement
involves the joint statistics with Bob, which reintroduces the
entanglement.

**⚠ DIFFICULTY LEVEL: HIGH.** The crux is whether the bipartition
¬(P_A ∧ P_B) can be formulated so that P_A and P_B are
independently meaningful propositions whose conjunction is
refuted by CHSH. The entanglement means Alice's and Bob's value
assignments are not independent — the CHSH bound applies to the
JOINT assignment. You can't refute P_A ∧ P_B without the joint
structure.

**What to try:** Formalize P_A := "∃ a₁ a₂ : {±1}, the marginal
statistics of Alice's outcomes are consistent with these values"
and P_B similarly. Then check whether P_A ∧ P_B implies the
existence of a joint LHV model. If it does (via some product
construction), then ¬LHV → ¬(P_A ∧ P_B), and the De Morgan
step ¬(P_A ∧ P_B) → ¬P_A ∨ ¬P_B is exactly LLPO (if P_A, P_B
are ¬¬-stable).

**If this fails:** The failure mode is that P_A ∧ P_B does NOT
imply a joint LHV model. This happens if Alice's marginal can
be deterministic AND Bob's marginal can be deterministic but
no joint model exists that's consistent with both. That's
actually a known subtlety — it's related to the "marginal
problem" in probability theory. If this is the case, the
bipartition doesn't work and Approach A fails.

**Test:** Before touching Lean, work out on paper whether
deterministic Alice-marginal + deterministic Bob-marginal
implies a joint deterministic model for the CHSH setup. For
dichotomic ±1 measurements with two settings each, there are
4 possible Alice assignments (a₁, a₂) ∈ {±1}² and 4 possible
Bob assignments (b₁, b₂) ∈ {±1}². A joint deterministic model
is a probability distribution over the 16 elements of {±1}⁴
(or just a single element if we're talking about a specific λ).
The product of consistent marginals gives a joint model. So
P_A ∧ P_B → ∃ joint LHV for this specific finite setup.

**If the above pencil check works → proceed with Lean.**

---

### Approach B: Encoding via binary sequences (standard CRM style)

**Idea:** Construct from α : ℕ → Bool a family of "partially
deterministic" models where α encodes which party has predetermined
values, and the CHSH violation forces an LLPO decision on α.

**Construction attempt:**

Given α, β : ℕ → Bool with ¬(∃n, α(n) ∧ β(n)), construct a
Bell experiment parameterized by (α, β):

- If α(n) = true: at "round n", Alice's outcome is deterministic
- If β(n) = true: at "round n", Bob's outcome is deterministic
- The constraint ¬(α(n) ∧ β(n)) means not both are deterministic
  at any round

The CHSH violation implies that not all rounds can have a joint
deterministic model. If all of Alice's rounds were deterministic
(∀n, β(n) = false → all non-determinism is on Bob's side), the
model would satisfy CHSH. Contradiction. Similarly for Bob.
Therefore LLPO: (∀n, α(n) = false) ∨ (∀n, β(n) = false).

**⚠ DIFFICULTY LEVEL: VERY HIGH.** This construction is sketchy.
The connection between "round-by-round determinism indexed by α"
and the CHSH bound is not crisp. The CHSH inequality is about
expectation values over many rounds (or over the hidden variable),
not about individual rounds. The encoding conflates the round
index with the hidden variable, which may not be coherent.

**What to try:** Don't try this first. Try Approach A first.
Fall back to this only if A fails for a specific reason that B
might circumvent.

---

### Approach C: LLPO via the sign of a correlation (cleanest)

**Idea:** Use LLPO equivalence (E3): for any real x, x ≤ 0 ∨ x ≥ 0.

Construct a real number x from a Bell experiment such that:
- x > 0 means "the nonlocality is on Alice's side"
- x < 0 means "the nonlocality is on Bob's side"
- x = 0 is the symmetric case

The sign decision x ≤ 0 ∨ x ≥ 0 is exactly LLPO.

**Construction:**

Consider asymmetric CHSH: instead of the standard correlator
S = ⟨A₁B₁⟩ + ⟨A₁B₂⟩ + ⟨A₂B₁⟩ - ⟨A₂B₂⟩, define:

  x(θ_A, θ_B) = S(θ_A) - S(θ_B)

where θ_A, θ_B are measurement angle parameters. When Alice's
angles are suboptimal, the CHSH violation "decreases on Alice's
side," making x positive (Bob contributes more nonlocality).
When Bob's angles are suboptimal, x is negative.

**⚠ DIFFICULTY LEVEL: MODERATE.** The idea is clean but the
specific construction needs work. The quantity x must be defined
so that:

1. x is computable from the experimental setup (BISH)
2. The sign of x genuinely distinguishes "Alice-side vs Bob-side"
   nonlocality
3. The sign decision is non-trivial (x can actually be zero for
   symmetric setups)

The danger is that x is always zero for the singlet state by
symmetry, making the sign decision trivial and the LLPO content
vacuous.

**What to try:** Consider breaking the symmetry explicitly. Use
a NON-maximally-entangled state |ψ(θ)⟩ = cos(θ)|00⟩ + sin(θ)|11⟩
parameterized by θ. For θ = π/4 (maximally entangled), the
nonlocality is symmetric. For θ ≠ π/4, one party's measurements
are "more nonlocal" than the other's. Define x(θ) as some
measure of this asymmetry. Then deciding sign(x(θ)) for arbitrary
θ might calibrate at LLPO.

**Concrete candidate for x:**

For the state |ψ(θ)⟩ = cos(θ)|00⟩ + sin(θ)|11⟩, the optimal
CHSH value is S(θ) = 2√(1 + sin²(2θ)) (Horodecki criterion).
This is symmetric in θ around π/4. Not useful for sign.

Better: fix Alice's measurement angles and vary Bob's. Define
x = S(Alice optimal, Bob suboptimal) - S(Alice suboptimal, Bob optimal).
This breaks symmetry by asymmetric optimization.

**This needs pencil-and-paper work before coding.**

---

### Approach D: Backward direction via IVT (leveraging Paper 19)

**Idea:** The backward direction (LLPO → something about Bell)
might be easier than the forward direction. Use the known LLPO ↔ IVT
equivalence (Paper 19) as a bridge.

**Construction:**

Given LLPO, we have IVT. Define a continuous function f(λ) on
[0,1] where:
- f(0) = S_LHV - 2 < 0 (classical bound violated from below)
- f(1) = S_quantum - 2 > 0 (quantum violation)
- f(λ) interpolates between classical and quantum predictions

IVT gives ∃λ*, f(λ*) = 0, i.e., there's a critical parameter
value where the CHSH bound is exactly saturated.

**⚠ PROBLEM:** This gives an existence result (a critical λ*),
which is interesting but doesn't directly connect to "Alice vs Bob."
The IVT root doesn't have a natural interpretation as "which side
is nonlocal."

**VERDICT:** Probably not productive. The IVT bridge doesn't
carry the right physical content.

---

### Approach E: Finite version — contextuality as LLPO

**Idea:** Retreat from Bell (which involves correlations and
expectations) to a purely combinatorial structure where LLPO
is more naturally expressed.

The **Hardy paradox** is a specific Bell scenario where the
nonlocality is witnessed by a single event (not a statistical
average):

  P(A₁=+1, B₁=+1) > 0   (quantum prediction)
  P(A₁=+1, B₂=+1) = 0    (constraint 1)
  P(A₂=+1, B₁=+1) = 0    (constraint 2)
  P(A₂=+1, B₂=-1) = 0    (constraint 3)

Any LHV model satisfying constraints 1-3 requires
P(A₁=+1, B₁=+1) = 0, contradicting the quantum prediction.

The Hardy argument has the structure: from three "never" constraints,
the LHV model is forced into a corner where a fourth event is
impossible. This is a finite logical argument — no expectations,
no averages, no statistics.

The LLPO content might be cleaner here: the three constraints
force "either A₂ always gives -1 when B₁ gives +1 (Alice is
constrained) OR A₁ always gives -1 when B₂ gives +1 (Alice is
constrained from the other side)." The disjunction might be
exactly LLPO.

**⚠ DIFFICULTY LEVEL: MODERATE.** The Hardy paradox is finitary
and the logical structure is simpler than CHSH. But the LLPO
content is still interpretive — you need to formalize what
"which side is constrained" means as a binary sequence decision.

**What to try:** Write out the Hardy argument as pure propositional
logic. Identify which step requires distributing a negation over
a conjunction. Check if that step has the LLPO form.

---

## 4. Recommended Exploration Order

### Phase 1: Pencil-and-paper (no Lean yet, 1-2 hours)

1. **Check Approach A's key lemma:** In the CHSH setup with
   {±1}-valued dichotomic measurements, does
   (∃a₁,a₂ consistent Alice-marginal) ∧ (∃b₁,b₂ consistent Bob-marginal)
   imply ∃(a₁,a₂,b₁,b₂) joint LHV model? This is a question about
   the product of two finite sets. Work it out for the 4×4 case.

   **If YES → Approach A is viable, proceed to Phase 2.**
   **If NO → Approach A fails. Try Approach E (Hardy).**

2. **Map the Hardy paradox logic:** Write the four Hardy constraints
   as propositional statements. Identify the De Morgan step. Check
   whether it has the form ¬(P ∧ Q) → ¬P ∨ ¬Q with P, Q decidable.

### Phase 2: Lean formalization of the winning approach (4-6 hours)

If Approach A passed Phase 1:

3. **Define the CHSH setup in Lean:**
```lean
structure LHVModel where
  a₁ : Int  -- Alice's outcome for setting 1, value in {-1, +1}
  a₂ : Int  -- Alice's outcome for setting 2
  b₁ : Int  -- Bob's outcome for setting 1
  b₂ : Int  -- Bob's outcome for setting 2
  ha₁ : a₁ = 1 ∨ a₁ = -1
  ha₂ : a₂ = 1 ∨ a₂ = -1
  hb₁ : b₁ = 1 ∨ b₁ = -1
  hb₂ : b₂ = 1 ∨ b₂ = -1
```

4. **Prove CHSH bound (BISH):**
```lean
theorem chsh_bound (m : LHVModel) :
    m.a₁ * m.b₁ + m.a₁ * m.b₂ + m.a₂ * m.b₁ - m.a₂ * m.b₂ ∈ ({-2, 2} : Set Int) := sorry
-- Finite case analysis over 16 cases.
-- Use `decide` or `omega` or explicit case split.
```

5. **Define Alice-marginal and Bob-marginal consistency:**
```lean
def AliceConsistent (a₁ a₂ : Int) (corrs : CHSHCorrelations) : Prop :=
  -- a₁, a₂ are consistent with Alice's observed marginal statistics
  sorry

def BobConsistent (b₁ b₂ : Int) (corrs : CHSHCorrelations) : Prop :=
  sorry
```

   **⚠ THIS IS THE HARD PART.** What does "consistent with marginal
   statistics" mean for a single LHV assignment? This is where the
   encoding either works or breaks. For a deterministic model (single
   hidden variable, not a distribution), "Alice consistent" means
   a₁, a₂ are the actual values Alice would get. The product
   (a₁,a₂) × (b₁,b₂) gives a joint model. This IS the product
   property — so for deterministic models, Approach A works trivially.

   The subtlety: Bell's theorem is about statistical models
   (distributions over λ). For a single λ, the joint model is just
   the product of marginals. The CHSH violation implies that no
   SINGLE (a₁,a₂,b₁,b₂) can reproduce the quantum correlations.
   But the violation is statistical — it's about ⟨·⟩, not about
   single events.

   **This is the crux.** The CHSH inequality for a SINGLE deterministic
   assignment gives |S| ∈ {-2, 2} (always ±2, never violating |S| ≤ 2).
   The quantum violation S = 2√2 is an EXPECTATION VALUE over many
   measurements. The contradiction arises because the expectation of
   something bounded by 2 can't exceed 2 — regardless of the distribution
   over λ.

   So the bipartition ¬(P_A ∧ P_B) → ¬P_A ∨ ¬P_B applies at the
   level of: "no distribution over (a₁,a₂) × (b₁,b₂) reproduces
   the quantum correlations." The product structure of the LHV
   assumption (Alice's values independent of Bob's setting) is what
   CHSH refutes.

   **Revised Approach A:** P_A = "∃ distribution μ_A over (a₁,a₂)
   consistent with Alice's marginals" and P_B similarly. Then
   P_A ∧ P_B → ∃ product distribution μ_A ⊗ μ_B → LHV model →
   |⟨S⟩| ≤ 2 → contradiction with quantum violation. So
   ¬(P_A ∧ P_B). Now: does ¬P_A ∨ ¬P_B follow?

   **Problem:** P_A (existence of a consistent marginal distribution)
   is almost certainly TRUE for any two-outcome measurement — any
   single measurement has a trivial consistent distribution (δ at
   the observed outcome). So ¬P_A is false and ¬P_B is false, and
   ¬P_A ∨ ¬P_B is false. But ¬(P_A ∧ P_B) is true. Contradiction?
   No — it means P_A and P_B are individually true but their
   conjunction leads to a product model that fails.

   **THIS KILLS APPROACH A.** The marginals are individually
   consistent. Only the JOINT model fails. The bipartition doesn't
   localize the failure to one side because neither side individually
   fails.

---

## 5. After Approach A Fails: What Remains

### 5.1 Reframing the question

The failure of Approach A is instructive. Bell nonlocality is
fundamentally about a JOINT property — the correlations between
Alice and Bob. It can't be decomposed into "Alice's failure" ∨
"Bob's failure" because neither party individually fails. This
is the essence of entanglement.

So the LLPO content of Bell's theorem, if it exists, is NOT about
the bipartition "which party fails." It must be about something else.

### 5.2 Approach F: LLPO as the cost of the disjunction in the conclusion

**New idea.** Don't try to localize nonlocality. Instead, observe
that the Bell conclusion has a specific disjunctive structure that
costs LLPO to state.

The CHSH violation proves: ¬∃μ (product distribution over {±1}⁴
reproducing quantum correlations). This is ¬LHV. BISH.

The *physical interpretation* that physicists draw is:
"Either locality fails OR realism (predetermined values) fails."

This is a disjunction: ¬Locality ∨ ¬Realism.

Classically, ¬(Locality ∧ Realism) ↔ ¬Locality ∨ ¬Realism by
De Morgan. Constructively, the left-to-right direction fails.

**Formalization:**

Define:
- `Locality : Prop` := Alice's outcome is independent of Bob's
  setting choice (and vice versa)
- `Realism : Prop` := all observables have simultaneous predetermined
  values

Then CHSH proves ¬(Locality ∧ Realism). The step to
¬Locality ∨ ¬Realism is exactly the weak De Morgan law, which is
equivalent to LLPO for decidable/¬¬-stable propositions.

**⚠ DIFFICULTY LEVEL: MODERATE-HIGH.** The question is whether
Locality and Realism, as formalized here, are ¬¬-stable. If they
are, the De Morgan step is LLPO. If they're not, the connection
is weaker.

Locality is a statement about conditional independence of finite
random variables. For finite outcome spaces, this should be
decidable (and hence ¬¬-stable).

Realism is a statement about the existence of a joint probability
distribution. For finite outcome spaces with finitely many
observables, this is also decidable (it's a linear programming
feasibility problem over a finite polytope).

**If both are decidable → the De Morgan step is exactly LLPO → Paper 21.**

**What to try in Lean:**

```lean
-- The propositions
def Locality (model : JointModel) : Prop := sorry
-- Alice's outcomes are conditionally independent of Bob's settings given λ

def Realism (model : JointModel) : Prop := sorry
-- All four observables have a joint probability distribution

-- Decidability (the key lemma)
instance : Decidable (Locality model) := sorry
instance : Decidable (Realism model) := sorry

-- The BISH part: CHSH violation implies ¬(Locality ∧ Realism)
theorem bell_negation (quantum_violation : S_quantum > 2) :
    ¬(Locality model ∧ Realism model) := sorry

-- The LLPO part: distributing the negation
theorem bell_disjunction_of_llpo (hllpo : LLPO) :
    ¬Locality model ∨ ¬Realism model := sorry
-- Uses: LLPO → weak De Morgan for decidable props

-- The backward direction: if we can always distribute, then LLPO
theorem llpo_of_bell_disjunction
    (hbd : ∀ model, ¬(Locality model ∧ Realism model) →
      ¬Locality model ∨ ¬Realism model) :
    LLPO := sorry
-- This is the hard direction. Encode α, β : ℕ → Bool into
-- a family of Bell models where Locality ↔ ∀n, α(n) = false
-- and Realism ↔ ∀n, β(n) = false.
```

### 5.3 The backward direction of Approach F (hardest part)

The backward direction requires: given α, β : ℕ → Bool with
¬(∃n, α(n) ∧ β(n)), construct a "Bell model" where:

- Locality of the model ↔ ∀n, α(n) = false
- Realism of the model ↔ ∀n, β(n) = false
- The model automatically satisfies ¬(Locality ∧ Realism)
  because ¬(∃n, α(n) ∧ β(n)) gives ¬(∀n,α(n)=false) → ... no,
  that's not right.

**⚠ THIS IS WHERE IT MAY BREAK.** The backward direction requires
encoding arbitrary binary sequences into the Locality and Realism
properties of a Bell model. This is a non-trivial encoding —
Locality and Realism are physical concepts, not arbitrary propositions.
You can't just define Locality := (∀n, α(n) = false) because then
the "Bell model" is a dummy wrapper around the sequences.

**Possible rescue: axiomatize the backward direction.** If the
forward direction (LLPO → Bell disjunction) is clean and
formalizable, but the backward direction is too hard, the paper
could prove:

  LLPO → [¬(L ∧ R) → ¬L ∨ ¬R for decidable L, R]

and then observe that the Bell conclusion ¬(L ∧ R) → ¬L ∨ ¬R
requires AT LEAST LLPO (since it's an instance of weak De Morgan).
The paper would then prove:

  "Bell's disjunctive conclusion requires LLPO"

rather than the full equivalence

  "Bell's disjunctive conclusion IS EQUIVALENT TO LLPO."

The implication is weaker than the equivalence but still
publishable and significant. It says: the step from "local
realism is contradicted" (BISH) to "locality fails or realism
fails" (LLPO) has a non-zero logical cost, and that cost is at
least LLPO.

**This weaker result might be the achievable target.**

---

## 6. Approach G: The Nuclear Option (most radical, possibly cleanest)

### 6.1 Forget physics. Use LLPO ↔ weak De Morgan directly.

**Theorem (known).** Over BISH, LLPO is equivalent to: for all
decidable propositions P, Q, ¬(P ∧ Q) → ¬P ∨ ¬Q.

**Proof.** (→) LLPO gives: for binary sequences α, β that don't both
hit 1, one is all-zeros. Given decidable P, Q with ¬(P ∧ Q), define
α(n) = (if n-th bit of evidence for P then 1 else 0), etc. [This
requires a careful encoding of decidable propositions into binary
sequences.]

(←) Given the De Morgan law, apply it to the propositions
P_α := ∃n, α(n) = true and P_β := ∃n, β(n) = true. These are
Σ₁⁰ (existential over decidable), hence ¬¬-stable. The hypothesis
¬(P_α ∧ P_β) = ¬(∃n, α(n)=1 ∧ ∃m, β(m)=1). We need
¬(∃n, α(n)=1) ∨ ¬(∃n, β(n)=1) = (∀n, α(n)=0) ∨ (∀n, β(n)=0).

Wait — the hypothesis of LLPO is stronger: ¬∃n(α(n) ∧ β(n)), i.e.,
they never SIMULTANEOUSLY hit 1. The De Morgan hypothesis is
¬(P ∧ Q) where P = ∃n, α(n)=1 and Q = ∃m, β(m)=1. These are
DIFFERENT — ¬(P ∧ Q) says "not both sequences have a 1 somewhere,"
while ¬∃n(α(n) ∧ β(n)) says "they never have a 1 at the SAME index."

**⚠ CAREFUL.** LLPO's hypothesis is POINTWISE non-overlap:
∀n, ¬(α(n)=1 ∧ β(n)=1). The De Morgan hypothesis is GLOBAL:
¬(∃n, α(n)=1 ∧ ∃m, β(m)=1). These are different! The pointwise
condition is WEAKER — it allows α(3)=1 and β(7)=1, just not at
the same index. The global condition forbids this.

This means LLPO is NOT simply "De Morgan for decidable propositions."
It's a more specific combinatorial principle. The connection to
De Morgan requires additional structure.

### 6.2 Revised connection

The correct equivalence (Ishihara 2006) is:

  LLPO ↔ (∀ x : ℝ, x ≤ 0 ∨ 0 ≤ x)

The real-number version is cleaner. For Bell, one could define:

  x := ⟨A₁B₁⟩ + ⟨A₁B₂⟩ - (⟨A₂B₁⟩ - ⟨A₂B₂⟩)

This is a real number computable from the quantum state. The sign
decision x ≤ 0 ∨ 0 ≤ x is LLPO. But what does the sign MEAN
physically?

If x > 0: the correlations ⟨A₁B₁⟩ + ⟨A₁B₂⟩ dominate, meaning
setting A₁ is "more correlated" with Bob's settings.
If x < 0: the correlations ⟨A₂B₁⟩ - ⟨A₂B₂⟩ dominate.

This is a statement about which of Alice's measurement settings
carries more Bell-type correlation. The sign decision is LLPO.

**But is the BACKWARD direction possible?** Given LLPO (i.e., the
sign decision for all reals), can we construct something useful
about Bell experiments? Or given the sign decision for all Bell
experiments, can we recover LLPO?

**Backward attempt:** Given α : ℕ → Bool, construct a Bell
experiment (quantum state + measurement settings) such that:

  x(experiment) = Σ_n (if α(n) then 2^{-(n+1)} else 0)
                  - Σ_n (if β(n) then 2^{-(n+1)} else 0)

where β is the complementary sequence. Then x ≤ 0 ∨ 0 ≤ x
decides whether α or β dominates, which relates to LLPO.

**⚠ THIS REQUIRES CONSTRUCTING A QUANTUM STATE WHOSE CHSH
CORRELATIONS EQUAL A PRESCRIBED VALUE.** This is an inverse
problem: given a target x, find a state |ψ⟩ and measurement
angles (θ_A1, θ_A2, θ_B1, θ_B2) such that the correlation
asymmetry equals x. This is likely possible (the set of
achievable correlations is continuous and contains 0) but the
explicit construction needs work.

---

## 7. Summary of Approaches and Recommendation

| Approach | Idea | Difficulty | Likelihood |
|----------|------|------------|------------|
| A | Bipartition: Alice-side ∨ Bob-side | Killed in §5 | 0% |
| B | Binary sequences → round-by-round determinism | Very high | 15% |
| C | Sign of asymmetric correlation | Moderate | 40% |
| D | IVT bridge from Paper 19 | Low | 10% |
| E | Hardy paradox (finite, no statistics) | Moderate | 50% |
| F | Locality ∨ Realism via De Morgan | Moderate-high | 35% |
| F' | (Weaker) Bell disjunction REQUIRES ≥ LLPO | Moderate | 65% |
| G | Direct real-number sign from correlations | Moderate | 30% |

**Recommended exploration order:**

1. **Start with E (Hardy paradox).** It's finite, no expectations
   or distributions, and the logical structure is closest to pure
   LLPO. Write out the Hardy four-constraint argument. Identify the
   De Morgan step. Check if it's LLPO.

2. **If E doesn't yield a clean LLPO instance, try F (Locality ∨
   Realism) in the weaker form F'.** Prove that the step
   ¬(L ∧ R) → ¬L ∨ ¬R requires at least LLPO. This might not give
   a full equivalence but it gives a calibration lower bound.

3. **If you want the full equivalence (both directions), try C or G
   (correlation sign).** This requires the most technical work
   (constructing quantum states with prescribed correlation
   asymmetry) but has the cleanest mathematical structure.

4. **At any point, if you find that Bell's constructive content is
   purely ¬LHV (a negation) with no natural disjunctive structure
   beyond De Morgan, document this and report back.** A negative
   result — "Bell's theorem is constructively a negation, and the
   disjunctive interpretation requires LLPO but does not naturally
   calibrate at LLPO" — is itself a publishable observation.

---

## 8. Success Criteria

**Full success (Paper 21):**
- Forward: LLPO → Bell's disjunctive conclusion
- Backward: Bell's disjunctive conclusion → LLPO
- Axiom audit clean
- ~500-800 lines Lean

**Partial success (still publishable as Paper 21):**
- Forward: LLPO → Bell's disjunctive conclusion
- Lower bound: Bell's disjunctive conclusion requires ≥ LLPO
  (but equivalence not proved)
- The paper would be titled something like "The Constructive Cost
  of Bell Nonlocality: At Least LLPO"

**Informative failure (publishable as a section in a survey paper):**
- Bell's theorem is constructively ¬LHV (BISH)
- The disjunctive interpretation ¬L ∨ ¬R requires LLPO
- No natural encoding achieves the backward direction
- Conclusion: Bell nonlocality is a genuine negation, not a
  disjunction, and the common phrasing "either locality or realism
  fails" has a non-zero logical cost that physicists overlook

**Uninformative failure:**
- Can't even formalize the CHSH bound cleanly in Lean
- If this happens, the problem is infrastructure, not mathematics.
  Report what's missing in Mathlib.

---

## 9. Minimal Lean Skeleton to Start With

```lean
import Mathlib

/-! # Bell / CHSH → LLPO Feasibility Test -/

-- LLPO definition
def LLPO : Prop :=
  ∀ (α β : ℕ → Bool),
    (∀ n, ¬(α n = true ∧ β n = true)) →
    (∀ n, α n = false) ∨ (∀ n, β n = false)

-- CHSH bound for a single deterministic assignment
theorem chsh_single_bound (a₁ a₂ b₁ b₂ : Int)
    (ha₁ : a₁ = 1 ∨ a₁ = -1) (ha₂ : a₂ = 1 ∨ a₂ = -1)
    (hb₁ : b₁ = 1 ∨ b₁ = -1) (hb₂ : b₂ = 1 ∨ b₂ = -1) :
    a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂ = 2 ∨
    a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂ = -2 := by
  -- 16 cases, should be decidable
  rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl <;>
  rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;>
  simp <;> omega

-- Quantum violation (axiomatize — this is a finite computation)
axiom S_quantum_gt_two : (2 : ℝ) * Real.sqrt 2 > 2

-- TODO: The rest depends on which approach works.
-- Start with Hardy paradox (Approach E) or
-- Locality/Realism De Morgan (Approach F).
```

---

## 10. Report Template

When the session ends, fill in:

```
APPROACH TRIED: [A/B/C/D/E/F/G]
OUTCOME: [success / partial success / informative failure / stuck]
WHERE IT BROKE: [specific step or lemma that failed]
WHAT'S NEEDED: [missing Lean infrastructure / mathematical idea / both]
LINES WRITTEN: [N]
RECOMMENDATION: [proceed to full paper / try different approach / abandon]
```
