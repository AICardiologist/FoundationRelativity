# LPO ↔ Free Energy Convergence: Proof Draft for Lean 4 Formalization

## Paper 9 — Proof Blueprint

### Paul C.-K. Lee (proof architecture by Claude)
### February 2026

---

## 0. Status and Dependencies

**Goal:** Prove over BISH:

```
LPO ↔ BoundedMonotoneConvergence
```

where `BoundedMonotoneConvergence` is: every bounded monotone sequence
of reals has a limit. This is already known [Bridges–Vîță 2006]. Our
contribution is to instantiate this via a physically natural encoding:

```
LPO ↔ (∀ translation-invariant finite-range H on ℤ, f_Λ(β) converges)
```

**Dependencies:**
- Paper 2 (Lee 2026a): `gap_equiv_wlpo`, Ishihara kernel infrastructure
- Paper 8 (Lee 2026b): 1D Ising BISH bounds, transfer matrix, tanh properties
- Bridges–Vîță 2006: `LPO ↔ BoundedMonotoneConvergence` (we reprove the
  hard direction with a physical encoding)
- Mathlib: Real.exp, Real.log, finite sums, basic inequalities

**What's new:** The backward direction uses an Ishihara-style encoding of
binary sequences into 1D Ising-type Hamiltonians so that convergence of
the free energy density *decides* the sequence. This is the novel
mathematical content.

---

## 1. Theorem Statement

**Theorem (LPO ↔ Free Energy Convergence).** Over BISH, the following
are equivalent:

1. **LPO:** For every α : ℕ → {0,1}, either (∀n, α(n) = 0) or (∃n, α(n) = 1).

2. **Free Energy Convergence:** For every bounded monotone sequence
   (aₙ)ₙ of real numbers, limₙ aₙ exists.

3. **Physical form:** For every nearest-neighbor Hamiltonian H on ℤ with
   finite-range translation-invariant interaction, and every rational
   β > 0, the free energy density f(β) = lim_{Λ↗ℤ} f_Λ(β) exists.

The equivalence (1) ↔ (2) is [Bridges–Vîță 2006]. We prove (1) ↔ (3)
directly, with the backward direction (3) → (1) being the new content.

---

## 2. Forward Direction: LPO → Free Energy Convergence

This is standard and short.

**Proof.** Assume LPO. Then bounded monotone convergence holds
[Bridges–Vîță 2006]. The free energy density sequence {f_Λ(β)} is
bounded (by 0 ≤ f_Λ ≤ β·‖H‖ / |Λ| type estimates, or more precisely
by the range of the interaction energy per site) and monotone (by
subadditivity of log Z_Λ, which gives superadditivity of f_Λ, hence
monotonicity along nested volumes). Apply bounded monotone convergence. ∎

**For Lean:** This direction is essentially:
```lean
theorem lpo_implies_freeEnergy_convergence (h : LPO) :
    FreeEnergyConvergence :=
  boundedMonotoneConvergence_of_lpo h |>.apply freeEnergy_bounded freeEnergy_monotone
```
The infrastructure needed is the Bridges–Vîță LPO → BMC implication
(which we formalize separately) plus the boundedness and monotonicity
of the free energy sequence (which requires subadditivity of log Z).

---

## 3. Backward Direction: Free Energy Convergence → LPO (Novel)

This is the hard direction and the new mathematical content. We encode
a binary sequence α : ℕ → {0,1} into a family of Hamiltonians such
that free energy convergence decides α.

### 3.1 The Encoding Strategy

**Key idea:** Given α : ℕ → {0,1}, construct a 1D nearest-neighbor
Hamiltonian H_α whose coupling constant at bond (n, n+1) depends on
whether any α(k) = 1 has been seen up to position n. The free energy
density of H_α will converge to different values depending on whether
α is identically zero or has a nonzero term.

**Why this works:** If α ≡ 0, the Hamiltonian is a uniform Ising chain
with coupling J₀. If ∃n₀ with α(n₀) = 1, then past position n₀ the
chain has coupling J₁ ≠ J₀. The free energy density, being an
intensive quantity, is asymptotically determined by the dominant
coupling. But the monotone sequence f_N doesn't "know" which regime
it's in until the limit is taken — and deciding which limit obtains
is exactly LPO.

### 3.2 Construction

Fix α : ℕ → {0,1}. Define the running maximum:

  m(n) := max(α(0), α(1), ..., α(n))

Note: m(n) ∈ {0, 1}, and m is non-decreasing. If α ≡ 0 then m ≡ 0.
If ∃n₀ with α(n₀) = 1, then m(n) = 1 for all n ≥ n₀.

**Constructive status:** m(n) is constructively computable from
(α(0), ..., α(n)). It's a finite maximum of finitely many bits. No
omniscience is needed to *compute* m(n) for any given n.

Fix two distinct positive rationals J₀, J₁ with J₀ ≠ J₁. For
concreteness, set J₀ = 1 and J₁ = 2.

Define the position-dependent coupling:

  J_α(n) := J₀ + (J₁ - J₀) · m(n) = J₀ · (1 - m(n)) + J₁ · m(n)

So J_α(n) = J₀ if m(n) = 0 (no α(k) = 1 seen yet), and J_α(n) = J₁
if m(n) = 1 (some α(k) = 1 has been seen).

**The Hamiltonian** on [1, N] with periodic boundary:

  H_α,N(σ) = - Σ_{i=1}^{N} J_α(i) · σ_i · σ_{i+1}

where σ_{N+1} := σ₁.

**Constructive status:** For each finite N, H_α,N is constructively
computable from (α(0), ..., α(N)). The partition function Z_α,N(β) is
a finite sum of exponentials — fully BISH.

### 3.3 Two regimes

**Case A: α ≡ 0.** Then m ≡ 0, so J_α(n) = J₀ = 1 for all n. The
Hamiltonian is the uniform 1D Ising model with coupling J₀. The free
energy density converges (in fact, is eventually constant up to
exponentially small corrections) to:

  f_A(β) = -log(2·cosh(β·J₀)) = -log(2·cosh(β))

**Case B: ∃n₀, α(n₀) = 1.** Then for all n ≥ n₀, J_α(n) = J₁ = 2.
The chain has finitely many "defect" bonds (where J transitions from
J₀ to J₁) in positions ≤ n₀, and uniform coupling J₁ for all bonds
past n₀. The free energy density converges to:

  f_B(β) = -log(2·cosh(β·J₁)) = -log(2·cosh(2β))

**The gap:** f_A(β) ≠ f_B(β) for any β > 0, since J₀ ≠ J₁ implies
cosh(β·J₀) ≠ cosh(β·J₁) (cosh is strictly increasing on (0,∞)).

### 3.4 The decision procedure

Assume Free Energy Convergence. Given α : ℕ → {0,1}, construct H_α
as above. The sequence f_α,N(β) is bounded and monotone (we verify
this below). By hypothesis, L := lim f_α,N(β) exists.

Now apply constructive cotransitivity of < on ℝ. Set the threshold:

  t := (f_A(β) + f_B(β)) / 2

Since f_A(β) ≠ f_B(β), we have f_A(β) < t < f_B(β) (or the reverse
ordering — it doesn't matter, just pick the correct one; note that
f is negative and -log(2cosh(2β)) < -log(2cosh(β)) since cosh(2β) >
cosh(β), so f_B < f_A, meaning f_B(β) < t < f_A(β)).

Let's be precise. For β > 0:
  cosh(2β) > cosh(β) > 1
  log(2·cosh(2β)) > log(2·cosh(β)) > 0
  -log(2·cosh(2β)) < -log(2·cosh(β))
  f_B(β) < f_A(β)

So we have f_B(β) < t < f_A(β) where t = (f_A + f_B)/2.

The gap:
  δ := f_A(β) - f_B(β) = log(cosh(2β)/cosh(β)) > 0

This δ is a constructively computable positive rational (for
rational β), so δ > 0 is a constructive fact.

Since L = lim f_α,N exists, for large enough N we have |f_α,N - L| <
δ/4. In particular, L is within δ/4 of the eventual behavior.

Apply cotransitivity: L < t or L > t (since t is a rational number
and L is a real number, and cotransitivity of < holds in BISH for
constructive reals via their Cauchy sequence representation — more
precisely, for any real x and rational q, either x < q or x > q - ε
for any ε; but here we use that L is close to one of f_A, f_B which
are separated by δ, so we can decide).

**Wait — this is too fast.** Cotransitivity gives: for any reals
a < b and any real x, either x < b or a < x. It does NOT give
x < t ∨ x > t for a single threshold. That would be WLPO-strength
(or stronger). Let me redo this.

### 3.5 The decision procedure (corrected)

The correct approach does not use cotransitivity on L directly.
Instead, it uses the convergence hypothesis to extract a *rate*.

**Refined approach:** Bounded monotone convergence (= LPO) gives not
just the limit but the limit as a constructive real number. A
constructive real number is a Cauchy sequence with a modulus. Having
the limit L means we can compute rational approximations to L within
any ε > 0.

Compute L to within ε = δ/4 (where δ = f_A - f_B > 0). Obtain a
rational q with |L - q| < δ/4.

Case analysis (this is decidable since q and t are both rational):

  - If q > t - δ/4 = f_B + δ/4: then L > f_B + δ/4 - δ/4 = f_B,
    and L > t - δ/2 = f_B + δ/2 - δ/2 = f_B. Hmm, not tight enough.

Let me redo with the right bounds.

We have:
  f_B < f_A, with f_A - f_B = δ > 0
  t = (f_A + f_B)/2
  f_B = t - δ/2
  f_A = t + δ/2

If α ≡ 0: L = f_A = t + δ/2
If ∃n₀, α(n₀) = 1: L = f_B = t - δ/2

Compute q ∈ ℚ with |L - q| < δ/4.

If L = f_A: q > t + δ/2 - δ/4 = t + δ/4
If L = f_B: q < t - δ/2 + δ/4 = t - δ/4

The intervals (t + δ/4, ∞) and (-∞, t - δ/4) are disjoint. The
comparison q ≥ t or q < t is decidable (rational arithmetic). So:

  - If q ≥ t: then L is close to f_A, so α ≡ 0. Output "∀n, α(n) = 0."
  - If q < t: then L is close to f_B, so ∃n₀, α(n₀) = 1.
    Output "∃n, α(n) = 1."

**But wait:** in the second case, we need an actual *witness* n₀ with
α(n₀) = 1, not just the knowledge that one exists. LPO demands the
existential witness.

### 3.6 Extracting the witness

When q < t (so L ≈ f_B), we know ∃n₀, α(n₀) = 1, but we need to
*find* it. This is where the constructive content of the convergence
hypothesis does additional work.

Since f_α,N(β) → L ≈ f_B, and f_B is the free energy for the chain
with coupling J₁, the convergence tells us that the chain "eventually
looks like" coupling J₁. In particular, for large enough N, the
free energy f_α,N is significantly different from what it would be if
all couplings were J₀.

**Constructive extraction:** Since L < t (a rational inequality,
decidable), we know L ≠ f_A. Since f_α,N → L and L < t < f_A, there
exists N₁ (computable from the modulus of convergence) such that
f_α,N₁ < t. But f_α,N₁ depends on (α(0), ..., α(N₁)). If all of
α(0), ..., α(N₁) were 0, then f_α,N₁ would be the free energy of a
uniform J₀-chain of length N₁, which approaches f_A from above (by
Paper 8 bounds). For large enough N₁, this would give f_α,N₁ > t — a
contradiction.

More precisely: by Paper 8, for the uniform J₀-chain:

  |f_{J₀,N}(β) - f_A(β)| ≤ (1/N) · tanh(β)^N → 0

So for N large enough, f_{J₀,N} > f_A - δ/4 > t + δ/4 > t.

If α(0) = ... = α(N₁) = 0, then f_α,N₁ = f_{J₀,N₁} > t. But we
established f_α,N₁ < t. Contradiction. Therefore, ¬(α(0) = ... =
α(N₁) = 0), which means ∃k ≤ N₁ with α(k) = 1. Since this is a
bounded existential over a decidable predicate, we can find the
witness by bounded search. ∎

### 3.7 The witness extraction in detail

To make this fully rigorous for Lean:

**Step 1.** From the convergence hypothesis, obtain L = lim f_α,N and
a modulus M : ℕ → ℕ such that for all N ≥ M(k), |f_α,N - L| < 1/2^k.

**Step 2.** Compute δ = f_A(β) - f_B(β) = log(cosh(β·J₁)/cosh(β·J₀)),
which is a positive rational for rational β, J₀, J₁.

**Step 3.** Choose k large enough that 1/2^k < δ/4. Compute q ∈ ℚ
approximating L within δ/4 (using the modulus at precision k).

**Step 4.** Compare q with t = (f_A + f_B)/2 (rational comparison,
decidable).

**Step 5a.** If q ≥ t: prove α ≡ 0. This requires showing that if
∃n₀ with α(n₀) = 1, then L = f_B, giving q < t — contradiction.

**Step 5b.** If q < t: find the witness. Choose N₁ = M(k) (large
enough that f_α,N₁ is within δ/4 of L, hence f_α,N₁ < t + δ/4).
Also ensure N₁ is large enough that a uniform J₀-chain of length N₁
has f_{J₀,N₁} > t (using Paper 8 bounds). If α(0) = ... = α(N₁) = 0,
then f_α,N₁ = f_{J₀,N₁} > t, contradicting f_α,N₁ < t + δ/4... 

Wait, this doesn't quite work because f_α,N₁ < t + δ/4 does not
give f_α,N₁ < t. Let me tighten.

We have |f_α,N₁ - L| < δ/4 and |L - q| < δ/4 and q < t, so:
  L < q + δ/4 < t + δ/4
  f_α,N₁ < L + δ/4 < t + δ/2

But for the uniform J₀-chain: f_{J₀,N₁} > f_A - δ/4 = t + δ/2 - δ/4
= t + δ/4, and we need f_α,N₁ ≠ f_{J₀,N₁}.

Actually, let me use ε = δ/8 throughout for cleaner bookkeeping.

**Corrected Step 5b:**

Choose precision ε = δ/8. Obtain N₁ from the modulus such that
|f_α,N₁ - L| < δ/8. From |L - q| < δ/8 and q < t:

  L < t + δ/8
  f_α,N₁ < t + δ/4

For the uniform J₀-chain of length N₁, by Paper 8:
  f_{J₀,N₁} > f_A - δ/8 = t + δ/2 - δ/8 = t + 3δ/8

(provided N₁ is large enough; since the Paper 8 error is
(1/N)·tanh(β)^N which goes to 0, we can ensure this by taking
N₁ ≥ N₂ where N₂ is the Paper 8 bound for the J₀-chain at
precision δ/8).

Now: if α(0) = ... = α(N₁) = 0, then f_α,N₁ = f_{J₀,N₁} >
t + 3δ/8. But we have f_α,N₁ < t + δ/4 = t + 2δ/8. Since
3δ/8 > 2δ/8, this is a contradiction.

Therefore ∃k ≤ N₁ with α(k) = 1. Bounded search finds the witness. ∎

---

## 4. Verification that f_α,N is Bounded and Monotone

For the encoding to work, we need the free energy sequence to satisfy
the hypotheses of bounded monotone convergence.

### 4.1 Boundedness

**Lemma 4.1.** For all N ≥ 1 and β > 0:

  -β · max(J₀, J₁) ≤ f_α,N(β) ≤ -β · min(J₀, J₁) + (log 2)/N

Wait, this isn't quite right. Let me compute properly.

  f_α,N = -(1/N) · log Z_α,N

Lower bound on Z: Z ≥ exp(β · N · max(J₀,J₁)) (all spins aligned)
gives f_α,N ≤ -β · max(J₀,J₁) + (log 2)/N... no.

Actually Z = Σ_σ exp(β Σ J_α(i) σ_i σ_{i+1}). Each term has
|Σ J_α(i) σ_i σ_{i+1}| ≤ N · max(J₀,J₁). So:

  exp(-β N max(J₀,J₁)) ≤ Z/2^N ≤ exp(β N max(J₀,J₁))

Wait, Z has 2^N terms, each between exp(-βN·max(J)) and exp(βN·max(J)).
So:

  2^N · exp(-βN·max(J₀,J₁)) ≤ Z_α,N ≤ 2^N · exp(βN·max(J₀,J₁))

Taking logs and dividing by -N:

  -log 2 - β·max(J₀,J₁) ≤ f_α,N ≤ -log 2 + β·max(J₀,J₁)

Hmm, that's not right either — free energy should be negative for
ferromagnetic systems.

Let me just note: f_α,N is bounded because each coupling J_α(i) is
between J₀ and J₁ (both positive, bounded), and the Hamiltonian
energy per site is bounded. The sequence is bounded uniformly in N.
The exact constants don't matter for the logical argument. ∎

### 4.2 Monotonicity (subadditivity)

**This is the subtle point.** The free energy sequence for a
*translation-invariant* Hamiltonian is monotone by subadditivity of
log Z. But H_α is NOT translation-invariant — the coupling varies
with position.

This is a genuine issue. For non-translation-invariant systems, the
free energy density need not be monotone. The sequence f_α,N may
oscillate.

**Resolution:** We don't need monotonicity of f_α,N. We need
convergence, which is what we're assuming (bounded monotone
convergence as a principle). But actually, the principle says *every*
bounded monotone sequence converges. If f_α,N isn't monotone, we
can't directly apply BMC.

**Alternative approach 1: Use full sequential convergence.** Replace
"bounded monotone convergence" with "every bounded sequence of reals
that is Cauchy has a limit." But Cauchy completeness of ℝ is a BISH
theorem, so this doesn't help.

**Alternative approach 2: Embed into a monotone sequence.** Define:

  g_α,N := sup_{M ≥ N} f_α,M

If this sup exists (which requires LPO-type reasoning), it's
monotone and bounded. But computing the sup is exactly the issue.

**Alternative approach 3: Restrict to translation-invariant encoding.**

This is the clean fix. Instead of making the coupling position-
dependent, encode α into the coupling constant itself.

### 4.3 Revised encoding (translation-invariant)

**New idea:** Instead of a position-dependent coupling, use a
*uniform* coupling that depends on α in a way that makes the free
energy encode the decision.

Given α : ℕ → {0,1}, define:

  J_α := J₀ + (J₁ - J₀) · x_α

where x_α := Σ_{n=0}^{∞} α(n) · 2^{-(n+1)} ∈ [0, 1].

This is a constructively well-defined real number (the partial sums
form a non-decreasing Cauchy sequence of rationals, bounded by 1).

If α ≡ 0: x_α = 0, so J_α = J₀.
If ∃n₀, α(n₀) = 1: x_α ≥ 2^{-(n₀+1)} > 0, so J_α > J₀.

**The Hamiltonian:** H_{J_α} is the uniform 1D Ising chain with
coupling J_α. This IS translation-invariant. The free energy density:

  f_N(β, J_α) = -(1/N) · log(Tr(T_{J_α}^N))

where T_{J_α} is the transfer matrix with coupling J_α.

From Paper 8, the limit is:

  f_∞(β, J_α) = -log(2 · cosh(β · J_α))

And the convergence is exponential: |f_N - f_∞| ≤ (1/N) · tanh(β·J_α)^N.

**Problem:** This convergence is constructively valid for each *fixed*
J_α, using Paper 8. But J_α is a constructive real — we can't in
general decide whether J_α = J₀ or J_α > J₀ without LPO. So the
free energy limit *exists constructively* (by Paper 8 bounds!) and
equals -log(2·cosh(β·J_α)).

But then what's left to decide? The decision is about J_α itself:
is J_α = J₀ or J_α > J₀? This is the zero-test on x_α = J_α - J₀.
And the zero-test on a constructive real is WLPO, not LPO.

**This approach undershoots.** It gives a WLPO-level decision, not LPO.
We already have WLPO from Paper 2. We need something genuinely LPO-
strength.

### 4.4 The correct encoding for LPO

LPO is about the *existential* witness: (∀n, α(n) = 0) ∨ (∃n, α(n) = 1).
The ∃n part demands finding an actual index. BMC (bounded monotone
convergence) is LPO-equivalent because computing the limit of a
bounded monotone sequence requires knowing "when" the sequence
effectively stabilizes — which amounts to searching for a witness.

**The right encoding goes through BMC directly.** Rather than encoding
α into a Hamiltonian and trying to make the free energy non-monotone,
we encode α into a bounded monotone sequence directly and show it
can be interpreted as a free energy.

Given α : ℕ → {0,1}, define:

  s(N) := max(α(0), α(1), ..., α(N))

This is {0,1}-valued, non-decreasing, and bounded. It's the simplest
bounded monotone sequence encoding α.

If α ≡ 0: s(N) = 0 for all N, limit = 0.
If ∃n₀, α(n₀) = 1: s(N) = 1 for all N ≥ n₀, limit = 1.

BMC says lim s(N) exists. Call it L ∈ [0,1]. Since s(N) ∈ {0,1},
L ∈ {0,1} (this requires a short argument: s is eventually constant
at 0 or 1, so L is 0 or 1).

If L = 0: then ∀N, s(N) = 0, so ∀n, α(n) = 0.
If L = 1: then ∃N, s(N) = 1, so ∃n ≤ N, α(n) = 1.

This gives LPO. But it's pure logic — where's the physics?

### 4.5 Physical instantiation of the BMC encoding

**Theorem statement (physical form):** Over BISH, LPO is equivalent
to the statement that for every constructively given coupling
sequence (Jₙ)ₙ with each Jₙ ∈ {J₀, J₁} and the sequence non-
decreasing, the transfer-matrix free energy of the corresponding
1D chain converges.

Actually, the cleanest physical instantiation is:

**Theorem (LPO via transfer-matrix families).** Over BISH, the
following are equivalent:

(1) LPO

(2) For every non-decreasing sequence (Jₙ)ₙ with Jₙ ∈ [J₀, J₁]
    (0 < J₀ < J₁), the function

      F(N) := -log(2 · cosh(β · Jₙ))

    has a limit.

Wait — F(N) = -log(2·cosh(β·Jₙ)) is just a composition of cosh
with Jₙ. If Jₙ converges, F(N) converges (by continuity of cosh).
And Jₙ converges iff the underlying monotone bounded sequence
converges, which is BMC, which is LPO.

But this feels circular. The content is: "a monotone bounded real
sequence converges iff LPO," dressed in Ising clothing.

**The honest assessment:** The physical instantiation of Candidate 2
is essentially the observation that free energy density computation
reduces to BMC, and BMC ↔ LPO is known. The "encoding" is:

  α ↦ (Jₙ := J₀ + (J₁-J₀)·s(n)) ↦ (free energy of chain with
  coupling Jₙ at bond n)

The backward direction (convergence → LPO) works because:
1. The coupling sequence Jₙ is bounded and monotone.
2. If the free energy converges, the coupling must have a limit
   (invertibility of the free energy as a function of J).
3. The limit of Jₙ decides α.

Let me make this precise.

---

## 5. Clean Proof of the Backward Direction

**Theorem 5.1.** Over BISH:

If for every bounded non-decreasing sequence (Jₙ)ₙ in [J₀, J₁]
(with 0 < J₀ < J₁ rationals and β > 0 rational), the sequence

  F_α(N) := -log(2 · cosh(β · J_N))

converges, then LPO holds.

**Proof.**

Let α : ℕ → {0,1} be arbitrary. Define:

  s(N) := max(α(0), ..., α(N))    (∈ {0,1}, non-decreasing)
  J(N) := J₀ + (J₁ - J₀) · s(N)  (∈ {J₀, J₁}, non-decreasing)
  F(N) := -log(2 · cosh(β · J(N))) (bounded, monotone)

By hypothesis, L := lim F(N) exists.

**Claim:** L decides α.

The function g(J) := -log(2·cosh(β·J)) is continuous and strictly
decreasing on (0, ∞) (since cosh is strictly increasing on (0,∞) and
log is increasing).

  g(J₀) = -log(2·cosh(β·J₀))
  g(J₁) = -log(2·cosh(β·J₁))

  g(J₁) < g(J₀) since J₁ > J₀.

Set δ := g(J₀) - g(J₁) > 0.

Since F(N) ∈ {g(J₀), g(J₁)} for all N (because J(N) ∈ {J₀, J₁}),
and F is non-decreasing... wait. g is *decreasing* in J, and J(N) is
non-decreasing, so F(N) = g(J(N)) is *non-increasing*. So F is
bounded and *monotone non-increasing*.

L = lim F(N) exists by hypothesis. Since F(N) ∈ {g(J₀), g(J₁)} and
g(J₁) < g(J₀), and F is non-increasing:

Case 1: If α ≡ 0, then J(N) = J₀ for all N, so F(N) = g(J₀) for
all N, so L = g(J₀).

Case 2: If ∃n₀, α(n₀) = 1, then J(N) = J₁ for all N ≥ n₀, so
F(N) = g(J₁) for all N ≥ n₀, so L = g(J₁).

Now: L is a constructive real. g(J₀) and g(J₁) are constructive
rationals (for rational β, J₀, J₁). δ = g(J₀) - g(J₁) > 0 is a
constructive positive rational.

Approximate L to within δ/3: find q ∈ ℚ with |L - q| < δ/3.

Compare q with t := (g(J₀) + g(J₁))/2 (rational comparison, decidable).

If q > t: then L > t - δ/3 > g(J₁) + δ/2 - δ/3 = g(J₁) + δ/6,
so L ≠ g(J₁), hence L = g(J₀), hence α ≡ 0.
Output: ∀n, α(n) = 0.

If q ≤ t: then L < t + δ/3 < g(J₀) - δ/2 + δ/3 = g(J₀) - δ/6,
so L ≠ g(J₀), hence L = g(J₁), hence ∃n₀, α(n₀) = 1.

To extract the witness n₀: Since L = g(J₁) and F(N) → g(J₁), and
F(N) ∈ {g(J₀), g(J₁)}, there exists N₁ with F(N₁) = g(J₁) (in
fact, F(N₁) < t for large enough N₁). Then J(N₁) = J₁, so s(N₁) = 1,
so ∃k ≤ N₁ with α(k) = 1. Bounded search finds k. ∎

---

## 6. Lean 4 Formalization Blueprint

### 6.1 Definitions

```lean
-- LPO
def LPO : Prop := ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

-- Bounded monotone convergence
def BoundedMonotoneConvergence : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    (∀ n, a n ≤ a (n + 1)) →  -- non-decreasing
    (∀ n, a n ≤ M) →          -- bounded above
    ∃ L : ℝ, ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, |a N - L| < ε

-- Running maximum of a binary sequence
def runMax (α : ℕ → Bool) (N : ℕ) : Bool :=
  (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩
    (fun i => α i)
-- Or more concretely:
def runMax' (α : ℕ → Bool) : ℕ → Bool
  | 0 => α 0
  | n + 1 => α (n + 1) || runMax' α n

-- The coupling sequence
noncomputable def couplingSeq (α : ℕ → Bool) (J₀ J₁ : ℝ) (N : ℕ) : ℝ :=
  if runMax' α N then J₁ else J₀

-- The free energy value at coupling J
noncomputable def freeEnergyAtCoupling (β J : ℝ) : ℝ :=
  -Real.log (2 * Real.cosh (β * J))

-- The encoded monotone sequence
noncomputable def encodedSeq (α : ℕ → Bool) (β J₀ J₁ : ℝ) (N : ℕ) : ℝ :=
  freeEnergyAtCoupling β (couplingSeq α J₀ J₁ N)
```

### 6.2 Key lemmas

```lean
-- runMax is non-decreasing
lemma runMax_mono (α : ℕ → Bool) :
    ∀ n, runMax' α n ≤ runMax' α (n + 1) := by sorry

-- runMax characterization
lemma runMax_eq_false_iff (α : ℕ → Bool) (N : ℕ) :
    runMax' α N = false ↔ ∀ k ≤ N, α k = false := by sorry

lemma runMax_eq_true_iff (α : ℕ → Bool) (N : ℕ) :
    runMax' α N = true ↔ ∃ k ≤ N, α k = true := by sorry

-- Coupling sequence is non-decreasing
lemma couplingSeq_mono (α : ℕ → Bool) (J₀ J₁ : ℝ)
    (hJ : J₀ ≤ J₁) :
    ∀ n, couplingSeq α J₀ J₁ n ≤ couplingSeq α J₀ J₁ (n + 1) := by sorry

-- freeEnergyAtCoupling is strictly decreasing in J (for β > 0)
lemma freeEnergyAtCoupling_strictAnti (β : ℝ) (hβ : 0 < β) :
    StrictAnti (freeEnergyAtCoupling β) := by sorry

-- encodedSeq is non-increasing (hence bounded monotone after negation)
lemma encodedSeq_anti (α : ℕ → Bool) (β J₀ J₁ : ℝ) (hβ : 0 < β)
    (hJ : J₀ < J₁) :
    ∀ n, encodedSeq α β J₀ J₁ (n + 1) ≤ encodedSeq α β J₀ J₁ n := by sorry

-- The gap between the two possible values
lemma freeEnergy_gap (β J₀ J₁ : ℝ) (hβ : 0 < β) (hJ : J₀ < J₁) :
    freeEnergyAtCoupling β J₀ - freeEnergyAtCoupling β J₁ > 0 := by sorry

-- Values of the encoded sequence
lemma encodedSeq_of_all_zero (α : ℕ → Bool) (β J₀ J₁ : ℝ) (N : ℕ)
    (h : ∀ n, α n = false) :
    encodedSeq α β J₀ J₁ N = freeEnergyAtCoupling β J₀ := by sorry

lemma encodedSeq_eventually_J₁ (α : ℕ → Bool) (β J₀ J₁ : ℝ) (n₀ : ℕ)
    (h : α n₀ = true) :
    ∀ N ≥ n₀, encodedSeq α β J₀ J₁ N = freeEnergyAtCoupling β J₁ := by sorry
```

### 6.3 Main theorem

```lean
-- Forward direction
theorem lpo_of_bmc : BoundedMonotoneConvergence → LPO := by
  intro hBMC α
  -- Construct the encoded sequence
  -- Apply BMC to get the limit
  -- Approximate the limit and compare with threshold
  -- Extract witness by bounded search if needed
  sorry

-- Backward direction (known, Bridges-Vîță)
theorem bmc_of_lpo : LPO → BoundedMonotoneConvergence := by
  sorry -- Standard, possibly axiomatize

-- The equivalence
theorem lpo_iff_bmc : LPO ↔ BoundedMonotoneConvergence :=
  ⟨bmc_of_lpo, lpo_of_bmc⟩

-- Physical instantiation
theorem lpo_iff_freeEnergy_convergence :
    LPO ↔ (∀ (J : ℕ → ℝ) (β : ℝ), 0 < β →
      (∀ n, J n ≤ J (n + 1)) →
      (∃ J₀ J₁ : ℝ, ∀ n, J₀ ≤ J n ∧ J n ≤ J₁) →
      ∃ L : ℝ, ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
        |freeEnergyAtCoupling β (J N) - L| < ε) := by
  sorry
```

### 6.4 Formalization strategy

**Module 1: BooleanSequences.lean** (~50 lines)
- `runMax'`, `runMax_mono`, characterization lemmas
- Bounded search on `Fin (N+1) → Bool`

**Module 2: CouplingEncoding.lean** (~80 lines)
- `couplingSeq`, monotonicity, value characterization
- `encodedSeq`, anti-monotonicity

**Module 3: FreeEnergyProperties.lean** (~100 lines)
- `freeEnergyAtCoupling`, strict anti-monotonicity
- `freeEnergy_gap` positivity
- Depends on Paper 8 infrastructure (cosh, log properties)

**Module 4: LPO_BMC_Equiv.lean** (~150 lines)
- `lpo_of_bmc`: the main backward direction
- Rational approximation and comparison
- Witness extraction by bounded search
- `bmc_of_lpo`: forward (may axiomatize initially)

**Module 5: Main.lean** (~30 lines)
- `lpo_iff_bmc`, `lpo_iff_freeEnergy_convergence`
- #print axioms verification

**Total estimate: ~400-500 lines**

### 6.5 Axiom targets

```
#print axioms lpo_of_bmc
-- Should show: NO classical axioms (the proof is constructive
-- modulo the BMC hypothesis)

#print axioms bmc_of_lpo
-- May show Classical.choice if using Bridges-Vîță classical
-- infrastructure; or may be axiomatized

#print axioms lpo_iff_bmc
-- Clean equivalence statement
```

---

## 7. What This Proves

If formalized, this gives the third calibrated rung:

| Physical Layer | Principle | Status |
|---|---|---|
| Finite-volume physics | BISH | Calibrated (trivial) |
| Finite-size approximations | BISH | Calibrated (Paper 8) |
| Bidual-gap witness | ≡ WLPO | Calibrated (Paper 2) |
| Free energy convergence | ≡ LPO | Calibrated (this paper) |
| Spectral gap | Undecidable | Established (Cubitt et al.) |

The specific new content is: the *existence of the thermodynamic
limit as a completed object* is equivalent to LPO. The *empirical
content* (finite-size bounds) is BISH (Paper 8). So the LPO cost
is real but dispensable for predictions.

---

## 8. Honesty Section: What Could Go Wrong

**Risk 1: BMC ↔ LPO direction might need careful handling.** The
Bridges-Vîță proof is constructive but involves careful use of
dependent choice. The Lean formalization needs to track this.

**Risk 2: The "physical instantiation" may be seen as trivial.** A
referee could object that encoding α into a coupling sequence and
composing with cosh is not "physical" — it's just BMC in disguise.
This is partly fair. The contribution is not a new mathematical
theorem but a new *interpretation*: the abstract BMC ↔ LPO
equivalence has direct physical content via the free energy.

**Risk 3: The non-translation-invariant encoding (§3) doesn't work
cleanly.** We switched to the translation-invariant version (§5) for
exactly this reason. The position-dependent approach has monotonicity
issues. The clean version passes through {g(J₀), g(J₁)}-valued
sequences, which is logically equivalent to {0,1}-valued sequences,
which is just BMC. Honest framing: the physical content is the
observation that BMC instantiates as free energy convergence; the
equivalence is the known BMC ↔ LPO result of Bridges-Vîță.

**Risk 4: The step "F(N) ∈ {g(J₀), g(J₁)}" uses that J(N) ∈ {J₀, J₁}
which requires deciding runMax.** But runMax(N) IS decidable for each
finite N — it's a finite computation. The point is we can't decide
lim runMax(N) without LPO. This is exactly right.

---

## 9. Relation to Paper 8

Paper 8 (1D Ising BISH bounds) provides the infrastructure for the
forward direction: once we have LPO (hence BMC), the fact that the
1D Ising free energy converges follows from BMC applied to the
bounded monotone sequence f_N(β). Paper 8 gives the BISH-valid
error bounds that make the empirical content accessible without LPO.

This paper (Paper 9) provides the *backward* direction: free energy
convergence implies LPO. Together they establish:

- LPO is the exact logical cost of asserting "the thermodynamic
  limit exists as a completed object."
- BISH is sufficient for "the finite system approximates the
  infinite-volume prediction within any given ε."

The combination is the payoff: the idealization costs exactly LPO,
but the physics doesn't need it.
