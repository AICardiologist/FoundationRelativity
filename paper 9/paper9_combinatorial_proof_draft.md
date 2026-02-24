# Formulation-Invariance Test: 1D Ising Free Energy via Direct Combinatorial Sums

## Proof Draft for Lean 4 Formalization

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose and Design Principles

This document provides a complete proof that the LPO equivalence of the
1D Ising thermodynamic limit is formulation-invariant: it persists in a
purely combinatorial framework that never invokes transfer matrices,
eigenvalues, linear operators, Banach spaces, or any functional-analytic
machinery.

**What this proves:** The same two results as Paper 9 — (A) BISH
dispensability of finite-size bounds, (B) LPO equivalence of the
thermodynamic limit — hold when the entire proof is conducted using only:

- Finite sums over explicit configuration spaces
- Elementary arithmetic on reals (exp, log, cosh, sinh, tanh)
- Combinatorial identities for spin sums
- The inequality log(1+x) ≤ x

If the axiom audit matches Paper 9 (Part A: no omniscience; Part B: 
exactly LPO), then the logical cost is a feature of the *physics*, not
the *formalism*.

**What this does NOT import from Paper 9:**

- `Matrix`, `Matrix.trace`, `Matrix.mul`, `Matrix.pow`
- `transferEigenPlus`, `transferEigenMinus`
- Any Mathlib module from `LinearAlgebra.*` or `Analysis.NormedSpace.*`
- The words "eigenvalue," "eigenvector," "spectral," "operator," "norm"

**What this MAY share with Paper 9:**

- `Real.exp`, `Real.log`, `Real.cosh`, `Real.sinh` (these are real
  analysis, not functional analysis — the shared substrate is arithmetic
  of reals, which is physics-independent infrastructure)
- LPO, BMC definitions (these are the logical principles under test)
- `log_one_add_le` (the inequality log(1+x) ≤ x)

The point: two formalizations share the unavoidable (real arithmetic)
but diverge on everything that constitutes a "formalism choice."

---

## 1. Setup: The 1D Ising Model (Combinatorial)

### 1.1 Configuration space

Fix N ≥ 1. The configuration space is the set of all functions
σ : Fin N → Bool, where Bool = {false, true} represents spins
{-1, +1}. The total number of configurations is 2^N.

**Notation.** For σ : Fin N → Bool, define the spin value:

  spin(σ, i) := if σ(i) = true then (1 : ℝ) else (-1 : ℝ)

This is a function Fin N → ℝ taking values in {-1, 1}.

### 1.2 Hamiltonian

With periodic boundary conditions (σ_{N} := σ_0):

  H_N(σ) := - Σ_{i=0}^{N-1} spin(σ, i) · spin(σ, (i+1) mod N)

Each term spin(σ,i) · spin(σ,j) ∈ {-1, +1} since each factor is ±1.
Each term equals +1 if σ(i) = σ(j) and -1 if σ(i) ≠ σ(j).

Define the "agreement function":

  agree(σ, i) := if σ(i) = σ((i+1) mod N) then (1 : ℤ) else (-1 : ℤ)

Then H_N(σ) = - Σ_{i=0}^{N-1} agree(σ, i).

**Constructive status:** For each finite N and each σ : Fin N → Bool,
H_N(σ) is a computable integer. No omniscience. ∎

### 1.3 Partition function and free energy

**Partition function:**

  Z_N(β) := Σ_{σ : Fin N → Bool} exp(-β · H_N(σ))
           = Σ_{σ : Fin N → Bool} exp(β · Σ_i agree(σ, i))

**Free energy density:**

  f_N(β) := -(1/N) · log(Z_N(β))

**Constructive status:** Z_N(β) is a finite sum (2^N terms) of
positive reals. For rational β > 0, each term exp(β · k) with k ∈ ℤ
is a well-defined positive real. The sum is positive. log of a positive
real is well-defined constructively. Division by N is trivial.

So f_N(β) is constructively computable for every finite N and rational
β > 0. No omniscience needed. ∎

### 1.4 Target (infinite-volume free energy)

**Definition.** The infinite-volume free energy density is defined by
closed form (NOT as a limit):

  f_∞(β) := -log(2 · cosh(β))

**Constructive status:** For rational β > 0, cosh(β) > 1 > 0, so
2·cosh(β) > 0, and log is well-defined. This is a constructively
computable real. ∎

---

## 2. The Combinatorial Identity

This is the heart of the formulation-invariance proof. We need to show
Z_N(β) = (2·cosh(β))^N + (2·sinh(β))^N without using transfer matrices.

### 2.1 Bond variables

For a configuration σ : Fin N → Bool with periodic boundary, define
the bond variables:

  b_i(σ) := agree(σ, i) ∈ {-1, +1}    for i = 0, ..., N-1

So -H_N(σ) = Σ_i b_i(σ) and:

  Z_N(β) = Σ_σ exp(β · Σ_i b_i(σ))
          = Σ_σ Π_i exp(β · b_i(σ))

Each factor exp(β · b_i(σ)) equals exp(β) if b_i = 1 (aligned neighbors)
or exp(-β) if b_i = -1 (anti-aligned neighbors).

### 2.2 Counting by bond pattern

**Key observation:** Not every assignment b : Fin N → {-1, +1} arises
from a configuration σ. The constraint is:

  Π_{i=0}^{N-1} b_i = 1    (the "cycle constraint")

This is because b_i = spin(σ,i) · spin(σ,(i+1) mod N), and the
telescoping product around the cycle gives:

  Π_i b_i = Π_i [spin(σ,i) · spin(σ,(i+1) mod N)]
           = [Π_i spin(σ,i)] · [Π_i spin(σ,(i+1) mod N)]
           = [Π_i spin(σ,i)]²
           = 1

(Each spin appears once as a "left" factor and once as a "right" factor
in the cyclic product, so the product is 1.)

**Lemma 2.1 (Bond-configuration correspondence).** Given a bond pattern
b : Fin N → {-1, +1} satisfying Π_i b_i = 1, the number of
configurations σ producing that pattern is exactly 2 (the two global
spin flips). Conversely, every configuration σ produces a bond pattern
satisfying Π_i b_i = 1.

*Proof.* Given b satisfying the constraint, fix σ(0) = +1 and determine
σ(1) = b_0 · σ(0), σ(2) = b_1 · σ(1), ..., σ(N-1) = b_{N-2} · σ(N-2).
The cycle constraint ensures σ(0) = b_{N-1} · σ(N-1) is consistent.
The other choice is σ(0) = -1, giving the globally flipped configuration.
So exactly 2 configurations per valid bond pattern. ∎

**Constructive note:** This is a finite combinatorial argument. The
constraint Π b_i = 1 is decidable (compute the product). The enumeration
is explicit. No omniscience.

### 2.3 Partition function via bond sums

**Lemma 2.2 (Bond decomposition).** 

  Z_N(β) = 2 · Σ_{b : Fin N → {-1,+1}, Π b_i = 1} Π_i exp(β · b_i)

*Proof.* Each σ contributes Π_i exp(β · b_i(σ)). Configurations that
share the same bond pattern contribute the same product. By Lemma 2.1,
each valid bond pattern has exactly 2 pre-images. ∎

### 2.4 Evaluating the constrained sum

**Lemma 2.3.** Let a = exp(β), c = exp(-β). For each bond variable:

  exp(β · b_i) = a if b_i = +1, c if b_i = -1

So Π_i exp(β · b_i) = a^k · c^{N-k} where k = #{i : b_i = +1}.

The constraint Π b_i = 1 means (-1)^{N-k} = 1, i.e., N-k is even,
i.e., k and N have the same parity.

Therefore:

  Z_N(β) = 2 · Σ_{k=0,2,4,...}^{N} (or k=1,3,...) C(N,k) · a^k · c^{N-k}

where the sum runs over k with the same parity as N, and C(N,k) is the
binomial coefficient (the number of ways to choose which k of the N bonds
are +1).

Wait — I need to be more careful about the parity.

The constraint is Π b_i = 1. Since b_i ∈ {-1, +1}, we have
Π b_i = (-1)^{number of b_i = -1} = (-1)^{N-k}. For this to equal 1,
we need N-k even, i.e., k ≡ N (mod 2).

So:

  Z_N(β) = 2 · Σ_{k ≡ N (mod 2)} C(N,k) · a^k · c^{N-k}

### 2.5 The parity extraction identity

**Lemma 2.4 (Parity sieve).** For any real numbers a, c:

  Σ_{k ≡ 0 (mod 2)} C(N,k) · a^k · c^{N-k} = [(a+c)^N + (a-c)^N] / 2
  
  Σ_{k ≡ 1 (mod 2)} C(N,k) · a^k · c^{N-k} = [(a+c)^N - (a-c)^N] / 2

*Proof.* By the binomial theorem:

  (a+c)^N = Σ_k C(N,k) · a^k · c^{N-k}
  (a-c)^N = Σ_k C(N,k) · a^k · (-c)^{N-k} = Σ_k C(N,k) · a^k · (-1)^{N-k} · c^{N-k}

Adding: (a+c)^N + (a-c)^N = Σ_k C(N,k) · a^k · c^{N-k} · [1 + (-1)^{N-k}]
The bracket is 2 when N-k is even, 0 when N-k is odd.

Subtracting: (a+c)^N - (a-c)^N = Σ_k C(N,k) · a^k · c^{N-k} · [1 - (-1)^{N-k}]
The bracket is 2 when N-k is odd, 0 when N-k is even.

Dividing by 2 gives the claimed identities. ∎

**Constructive note:** This is a purely algebraic identity (binomial
theorem + finite sum manipulation). No omniscience, no analysis, not
even real numbers — this holds in any commutative ring.

### 2.6 The partition function identity

**Theorem 2.5 (Combinatorial partition function formula).**

  Z_N(β) = (exp(β) + exp(-β))^N + (exp(β) - exp(-β))^N
          = (2·cosh(β))^N + (2·sinh(β))^N

*Proof.* Set a = exp(β), c = exp(-β).

**Case N even:** k ≡ N (mod 2) means k even. By Lemma 2.4:

  Z_N = 2 · [(a+c)^N + (a-c)^N] / 2 = (a+c)^N + (a-c)^N ✓

**Case N odd:** k ≡ N (mod 2) means k odd. By Lemma 2.4:

  Z_N = 2 · [(a+c)^N - (a-c)^N] / 2 = (a+c)^N - (a-c)^N

But wait: when N is odd, (a-c)^N = (a-c)^N with a-c > 0, and the
formula should give Z_N = (a+c)^N + (a-c)^N in all cases. Let me recheck.

Actually, there is a sign issue for odd N. Let me redo this carefully.

For N odd: N-k even means k is odd (same parity as N).

  Z_N = 2 · Σ_{k odd} C(N,k) · a^k · c^{N-k}
      = 2 · [(a+c)^N - (a-c)^N] / 2
      = (a+c)^N - (a-c)^N

Now (a-c)^N = (exp(β) - exp(-β))^N = (2·sinh(β))^N.

For N odd: (2·sinh(β))^N > 0, and:

  Z_N = (2·cosh(β))^N - (2·sinh(β))^N

Hmm, this differs from the transfer matrix result Z_N = λ₊^N + λ₋^N
by a sign in the second term when N is odd!

Let me recheck the transfer matrix derivation. With T = (a c; c a):

  T has eigenvalues λ₊ = a + c = 2cosh(β) and λ₋ = a - c = 2sinh(β)
  Z_N = Tr(T^N) = λ₊^N + λ₋^N = (2cosh)^N + (2sinh)^N

So the transfer matrix gives Z_N = (2cosh)^N + (2sinh)^N for ALL N.

But the combinatorial calculation gives:
- N even: Z_N = (2cosh)^N + (2sinh)^N ✓
- N odd: Z_N = (2cosh)^N - (2sinh)^N ✗

There must be an error in my parity analysis. Let me recheck.

### 2.7 Corrected parity analysis

The issue is with the cycle constraint. Let me recount.

For σ : Fin N → {±1} with periodic boundary σ_N = σ_0, define:
  b_i = σ_i · σ_{i+1}    for i = 0, ..., N-1    (where σ_N = σ_0)

The number of anti-aligned bonds (b_i = -1) is the number of "domain
walls." For a periodic chain, domain walls always come in pairs (you
must re-enter the domain you started in). So the number of b_i = -1
is always even, regardless of N.

This means N - k (number of b_i = -1) is always even, so k ≡ N (mod 2)
is always satisfied. Wait, that gives the same constraint. But the
even-ness of domain walls means specifically that #{b_i = -1} is even,
which means N - k is even, i.e., k has same parity as N. This is what
I had.

Let me recheck with a small example.

**N = 3, β arbitrary:**

Configurations σ ∈ {±1}^3, periodic (σ_3 = σ_0):

σ = (+,+,+): bonds (+·+, +·+, +·+) = (+,+,+). k = 3 (odd = N).
  Contribution: exp(3β)

σ = (+,+,-): bonds (+·+, +·-, -·+) = (+,-,-). k = 1 (odd).
  Contribution: exp(β)·exp(-β)·exp(-β) = exp(-β)

σ = (+,-,+): bonds (+·-, -·+, +·+) = (-,-,+). k = 1. Contribution: exp(-β)

σ = (+,-,-): bonds (+·-, -·-, -·+) = (-,+,-). k = 1. Contribution: exp(-β)

σ = (-,+,+): bonds (-·+, +·+, +·-) = (-,+,-). k = 1. Contribution: exp(-β)

σ = (-,+,-): bonds (-·+, +·-, -·-) = (-,-,+). k = 1. Contribution: exp(-β)

σ = (-,-,+): bonds (-·-, -·+, +·-) = (+,-,-). k = 1. Contribution: exp(-β)

σ = (-,-,-): bonds (-·-, -·-, -·-) = (+,+,+). k = 3. Contribution: exp(3β)

Z_3 = 2·exp(3β) + 6·exp(-β)

Now let's check: (2cosh)^3 + (2sinh)^3

  (2cosh β)^3 = (e^β + e^{-β})^3 = e^{3β} + 3e^β + 3e^{-β} + e^{-3β}
  (2sinh β)^3 = (e^β - e^{-β})^3 = e^{3β} - 3e^β + 3e^{-β} - e^{-3β}

  Sum = 2e^{3β} + 6e^{-β} ✓✓✓

And (2cosh)^3 - (2sinh)^3 = 6e^β + 2e^{-3β} ≠ Z_3.

So the transfer matrix result Z_N = (2cosh)^N + (2sinh)^N is correct.
My combinatorial parity sieve was WRONG. Let me find the error.

Going back: for N = 3, the valid bond patterns have k ∈ {1, 3}
(odd = same parity as N = 3). But:
  k = 3: C(3,3) = 1 pattern, weight a^3 · c^0 = e^{3β}
  k = 1: C(3,1) = 3 patterns, weight a^1 · c^2 = e^β · e^{-2β} = e^{-β}

  2 · [1 · e^{3β} + 3 · e^{-β}] = 2e^{3β} + 6e^{-β} ✓

And by the parity sieve (Lemma 2.4):
  Σ_{k odd} C(3,k) a^k c^{3-k} = [(a+c)^3 - (a-c)^3] / 2

  (a+c)^3 = e^{3β} + 3e^β + 3e^{-β} + e^{-3β}
  (a-c)^3 = e^{3β} - 3e^β + 3e^{-β} - e^{-3β}
  
  Difference = 6e^β + 2e^{-3β}
  Half = 3e^β + e^{-3β}

  Z_3 = 2 · (3e^β + e^{-3β}) = 6e^β + 2e^{-3β}

But this is WRONG — we computed Z_3 = 2e^{3β} + 6e^{-β} above.

So 6e^β + 2e^{-3β} ≠ 2e^{3β} + 6e^{-β}. The parity sieve gives
the wrong answer!

The error is in the parity constraint. Let me recheck.

For N = 3: k = number of b_i = +1 (aligned bonds).

σ = (+,+,+): all aligned. k = 3 (N - k = 0, even). ✓
σ = (+,+,-): bonds (+,-,-). k = 1, N-k = 2 (even). ✓
σ = (-,-,-): bonds (+,+,+). k = 3, N-k = 0 (even). ✓

All configurations have N - k even. So the constraint is k ≡ N (mod 2),
which for N = 3 means k is odd: k ∈ {1, 3}. ✓

Number of bond patterns with k = 3: C(3,3) = 1. Weight: a^3.
Number of bond patterns with k = 1: C(3,1) = 3. Weight: a · c^2.

Z_3 = 2 · [a^3 + 3 · a · c^2]
    = 2 · a · [a^2 + 3c^2]
    = 2 · e^β · [e^{2β} + 3e^{-2β}]
    = 2e^{3β} + 6e^{-β} ✓

Now the parity sieve (Lemma 2.4, k odd):

Σ_{k odd} C(3,k) a^k c^{3-k} = C(3,1)·a·c^2 + C(3,3)·a^3·c^0
                                = 3ac^2 + a^3

The parity sieve formula says this equals [(a+c)^3 - (a-c)^3]/2.

(a+c)^3 - (a-c)^3 = [a^3 + 3a^2c + 3ac^2 + c^3] - [a^3 - 3a^2c + 3ac^2 - c^3]
                   = 6a^2c + 2c^3

Half = 3a^2c + c^3 = c(3a^2 + c^2)

But Σ_{k odd} = a^3 + 3ac^2 = a(a^2 + 3c^2)

These are NOT equal! c(3a^2 + c^2) ≠ a(a^2 + 3c^2) in general.

The error is that my parity sieve formula is WRONG for the odd-k sum.

Let me redo the parity sieve more carefully.

  (a+c)^N = Σ_k C(N,k) a^k c^{N-k}
  (a-c)^N = Σ_k C(N,k) a^k (-c)^{N-k}
           = Σ_k C(N,k) a^k (-1)^{N-k} c^{N-k}

Adding:
  (a+c)^N + (a-c)^N = Σ_k C(N,k) a^k c^{N-k} [1 + (-1)^{N-k}]

The factor [1 + (-1)^{N-k}] is:
  2  when N-k is even (i.e., k ≡ N mod 2)
  0  when N-k is odd

So:
  (a+c)^N + (a-c)^N = 2 · Σ_{k ≡ N (mod 2)} C(N,k) a^k c^{N-k}

Therefore:
  Σ_{k ≡ N (mod 2)} C(N,k) a^k c^{N-k} = [(a+c)^N + (a-c)^N] / 2

Check for N=3 (k ≡ 1 mod 2, i.e., k odd):

[(a+c)^3 + (a-c)^3] / 2 = [(a^3 + 3a^2c + 3ac^2 + c^3) + (a^3 - 3a^2c + 3ac^2 - c^3)] / 2
                         = [2a^3 + 6ac^2] / 2
                         = a^3 + 3ac^2  ✓✓✓

I had the parity sieve formula backwards! The correct formula is:

  Σ_{k ≡ N (mod 2)} = [(a+c)^N + (a-c)^N] / 2    (ALWAYS the plus)
  Σ_{k ≢ N (mod 2)} = [(a+c)^N - (a-c)^N] / 2    (ALWAYS the minus)

This holds for ALL N, regardless of parity. My earlier "Lemma 2.4" was
wrong because I wrote the sums as "k even" and "k odd" instead of
tracking the relationship to N.

### 2.6 The partition function identity (CORRECTED)

**Theorem 2.5 (Combinatorial partition function formula).**
For all N ≥ 1 and β > 0:

  Z_N(β) = (2·cosh(β))^N + (2·sinh(β))^N

*Proof.* Set a = exp(β), c = exp(-β). By the bond decomposition
(Lemma 2.2):

  Z_N = 2 · Σ_{k ≡ N (mod 2)} C(N,k) · a^k · c^{N-k}

By the corrected parity sieve:

  Σ_{k ≡ N (mod 2)} C(N,k) · a^k · c^{N-k} = [(a+c)^N + (a-c)^N] / 2

Therefore:

  Z_N = 2 · [(a+c)^N + (a-c)^N] / 2 = (a+c)^N + (a-c)^N

Now a + c = exp(β) + exp(-β) = 2·cosh(β) and a - c = exp(β) - exp(-β)
= 2·sinh(β). So:

  Z_N(β) = (2·cosh(β))^N + (2·sinh(β))^N   ∎

**Constructive note:** Every step is BISH-valid:
- The bond decomposition uses only finite enumeration and counting
- The parity sieve is a binomial identity (algebraic, holds in ℤ[a,c])
- The identification a + c = 2cosh(β) is a definition
- No limits, no spectral theory, no linear algebra

---

## 3. Auxiliary Definitions and Identities

### 3.1 The ratio r

**Definition.** For β > 0, define:

  r(β) := (2·sinh(β)) / (2·cosh(β)) = tanh(β)

**Lemma 3.1.** For β > 0: 0 < r(β) < 1.

*Proof.* sinh(β) > 0 and cosh(β) > sinh(β) for β > 0 (since
cosh(β) - sinh(β) = exp(-β) > 0). So r = sinh/cosh ∈ (0, 1). ∎

### 3.2 Free energy decomposition

**Lemma 3.2.** For all N ≥ 1 and β > 0:

  f_N(β) = -log(2·cosh(β)) - (1/N)·log(1 + r^N)

where r = tanh(β).

*Proof.*

  f_N = -(1/N) · log(Z_N)
      = -(1/N) · log((2cosh)^N + (2sinh)^N)
      = -(1/N) · log((2cosh)^N · (1 + (2sinh/2cosh)^N))
      = -(1/N) · [N·log(2cosh) + log(1 + r^N)]
      = -log(2cosh) - (1/N)·log(1 + r^N)   ∎

**Constructive note:** The factoring step uses (2cosh)^N > 0 (since
cosh(β) > 0), so division is well-defined. log of the product is
sum of logs. All steps are BISH-valid.

### 3.3 Error formula

**Corollary 3.3.** For all N ≥ 1 and β > 0:

  f_N(β) - f_∞(β) = -(1/N)·log(1 + r^N)

  |f_N(β) - f_∞(β)| = (1/N)·log(1 + r^N)

*Proof.* f_∞ = -log(2cosh), so the difference is -(1/N)·log(1 + r^N).
Since 0 < r < 1, we have 0 < r^N < 1, so 1 < 1 + r^N < 2, so
log(1 + r^N) > 0. The error is negative (f_N < f_∞) with magnitude
(1/N)·log(1 + r^N). ∎

---

## 4. Part A: BISH Dispensability (Combinatorial)

### 4.1 The key inequality

**Lemma 4.1.** For all x > 0: log(1 + x) ≤ x.

*Proof.* Equivalent to 1 + x ≤ exp(x), which follows from the Taylor
series exp(x) = 1 + x + x²/2 + ... ≥ 1 + x. Constructively: for x > 0,
exp(x) - 1 - x = Σ_{k=2}^∞ x^k/k! > 0 (each term is positive and the
series converges). ∎

### 4.2 Error bound

**Theorem 4.2 (Combinatorial finite-size bound).** For all N ≥ 1 and
β > 0:

  |f_N(β) - f_∞(β)| ≤ (1/N) · tanh(β)^N

*Proof.* By Corollary 3.3 and Lemma 4.1:

  |f_N - f_∞| = (1/N)·log(1 + r^N) ≤ (1/N)·r^N = (1/N)·tanh(β)^N   ∎

### 4.3 Exponential decay rate

**Lemma 4.3.** For β > 0, let c(β) := -log(tanh(β)) > 0. Then:

  tanh(β)^N = exp(-c(β)·N)

and the cruder bound:

  tanh(β)^N ≤ exp(-2N/(exp(2β) + 1))

*Proof.* tanh(β)^N = exp(N·log(tanh(β))) = exp(-c(β)·N) with
c(β) = -log(tanh(β)) > 0 (since tanh(β) < 1).

For the cruder bound: 1 - tanh(β) = sech(β)² / (1 + tanh(β)) ... 
Actually, more directly: 1 - tanh(β) = 2exp(-β)/(exp(β) + exp(-β))
= 2/(exp(2β) + 1) =: δ(β). Using -log(1-δ) ≥ δ for 0 < δ < 1:
c(β) = -log(1-δ(β)) ≥ δ(β) = 2/(exp(2β)+1).

Wait. tanh(β) = 1 - δ(β) where δ = 2·exp(-β)/(exp(β)+exp(-β)).

Actually: 1 - tanh(β) = 1 - (e^β - e^{-β})/(e^β + e^{-β})
= 2e^{-β}/(e^β + e^{-β}) = 2/(e^{2β} + 1).

So c(β) = -log(tanh(β)) = -log(1 - 2/(e^{2β}+1)) ≥ 2/(e^{2β}+1).

Therefore tanh(β)^N = exp(-c(β)N) ≤ exp(-2N/(e^{2β}+1)).  ∎

### 4.4 Constructive N₀

**Corollary 4.4.** For every rational β > 0 and rational ε > 0, there
exists a constructively computable N₀ ∈ ℕ such that for all N ≥ N₀:

  |f_N(β) - f_∞(β)| < ε

*Proof.* We need (1/N)·tanh(β)^N < ε. Since tanh(β)^N decays
exponentially and 1/N decays polynomially, the product decreases to 0.

Constructive witness: N₀ := max(1, ⌈2/c(β) · (|log ε| + 1)⌉). For
N ≥ N₀:

  (1/N)·exp(-c(β)N) ≤ exp(-c(β)N/2)    (since 1/N ≤ exp(c(β)N/2) for
                                          N ≥ 2/c(β))
                     ≤ exp(-|log ε| - 1)
                     < ε

Alternatively: by bounded search. For N = 1, 2, 3, ..., compute the
rational upper bound (1/N)·r_approx^N where r_approx is a rational
approximation to tanh(β) from above with r_approx < 1, and check
whether this is less than ε. The search terminates because the bound
decreases to 0. The search is BISH-valid: decidable comparison of
rationals, known termination by the a priori decay estimate. ∎

### 4.5 Main dispensability theorem

**Theorem 4.5 (LPO-dispensability, combinatorial proof).** For the 1D
Ising model with periodic boundary conditions, the following is provable
in BISH (no omniscience principle required):

For every rational β > 0 and rational ε > 0, there exists N₀ ∈ ℕ
(constructively computable from β and ε) such that for all N ≥ N₀:

  |f_N(β) - f_∞(β)| < ε

where f_N(β) = -(1/N)·log(Z_N(β)) with Z_N a finite sum over {±1}^N,
and f_∞(β) = -log(2·cosh(β)).

*Proof.* Theorem 4.2 + Corollary 4.4. Every step uses only:
- Finite sums over {±1}^N (combinatorial)
- Binomial identities (algebraic)
- Properties of exp, log, cosh, sinh, tanh (real analysis)
- The inequality log(1+x) ≤ x (elementary)
- Bounded search on ℕ (BISH)

No use of:
- Transfer matrices or linear algebra
- Eigenvalues or spectral theory
- Banach spaces, norms, dual spaces
- Monotone convergence theorem (LPO)
- Any omniscience principle   ∎

**Axiom audit:** Identical to Paper 9, Part A. No omniscience. BISH only.

---

## 5. Part B: LPO Equivalence (Combinatorial)

### 5.0 Prefatory note

The encoding construction from Paper 9 Part B uses the function
g(J) = -log(2·cosh(β·J)). This is the infinite-volume free energy for
coupling J. In the transfer matrix proof, this was derived via eigenvalues
of the coupling-dependent transfer matrix.

In the combinatorial proof, we need to verify that f_∞(β, J) = -log(2·cosh(βJ))
follows from the combinatorial partition function as well.

**Lemma 5.0.** For the 1D Ising model with coupling J > 0, the
partition function is:

  Z_N(β, J) = Σ_{σ ∈ {±1}^N} exp(βJ · Σ_i σ_i σ_{i+1})
            = (2·cosh(βJ))^N + (2·sinh(βJ))^N

*Proof.* The combinatorial argument of §2 goes through identically with
β replaced by βJ throughout. The bond variable becomes b_i = σ_i σ_{i+1},
which is independent of J. The weight per bond becomes exp(βJ·b_i). The
parity constraint is unchanged. The binomial identity yields
(exp(βJ) + exp(-βJ))^N + (exp(βJ) - exp(-βJ))^N
= (2cosh(βJ))^N + (2sinh(βJ))^N.   ∎

Therefore f_∞(β, J) = -log(2·cosh(βJ)) is the combinatorial infinite-volume
free energy, without any reference to eigenvalues.

### 5.1 The encoding (same as Paper 9, Part B)

Let α : ℕ → {0,1} be an arbitrary binary sequence. Fix rationals
0 < J₀ < J₁ and β > 0.

**Step 1: Running maximum.**

  m(0) := α(0)
  m(n+1) := max(m(n), α(n+1))

Properties: m non-decreasing, m(n) = 0 ↔ ∀k ≤ n, α(k) = 0.

**Step 2: Coupling sequence.**

  J(n) := if m(n) = 0 then J₀ else J₁

Properties: J non-decreasing, bounded in [J₀, J₁].

**Step 3: Free energy sequence.**

  F(n) := f_∞(β, J(n)) = -log(2·cosh(β·J(n)))

where f_∞(β, J) is now justified combinatorially by Lemma 5.0.

Properties:
- F(n) ∈ {g(J₀), g(J₁)} where g(J) = -log(2·cosh(βJ))
- F is non-increasing (since g is strictly decreasing, proved in §5.2)
- Bounded: g(J₁) ≤ F(n) ≤ g(J₀)

### 5.2 Monotonicity of g (combinatorial proof)

**Lemma 5.1.** For β > 0, the function g(J) = -log(2·cosh(βJ)) is
strictly decreasing on (0, ∞).

*Proof.* For J₁ > J₂ > 0: βJ₁ > βJ₂ > 0 implies cosh(βJ₁) > cosh(βJ₂)
(cosh is strictly increasing on (0,∞)), which implies
log(2·cosh(βJ₁)) > log(2·cosh(βJ₂)), so g(J₁) < g(J₂).

**Combinatorial justification of cosh being increasing:** For x > y > 0,
cosh(x) - cosh(y) = 2·sinh((x+y)/2)·sinh((x-y)/2) > 0 since both
sinh factors are positive (their arguments are positive). This uses only
the identity cosh(a) - cosh(b) = 2sinh((a+b)/2)sinh((a-b)/2) (derivable
from the exponential definitions) and sinh(t) > 0 for t > 0 (from the
power series). No derivatives, no calculus, no functional analysis.  ∎

### 5.3 The gap

**Lemma 5.2 (Gap lemma).** Fix β > 0 and 0 < J₀ < J₁. Then:

  δ := g(J₀) - g(J₁) = log(cosh(βJ₁) / cosh(βJ₀)) > 0

*Proof.* Immediate from Lemma 5.1. ∎

### 5.4 BMC → LPO via the encoding

**Theorem 5.3 (Free energy convergence implies LPO, combinatorial proof).**
Over BISH: if every bounded monotone sequence of reals converges, then LPO.

*Proof.* Let α : ℕ → {0,1} be given. Construct F(n) as above. Define
G(n) := -F(n), which is non-decreasing and bounded above by -g(J₁).

By BMC, L_G := lim G(n) exists with a modulus of convergence.
Set L := -L_G = lim F(n).

**Decision procedure.** L ∈ {g(J₀), g(J₁)}, separated by δ > 0.
Compute a rational approximation q with |L - q| < δ/3. Set the
threshold t := (g(J₀) + g(J₁))/2.

Compare q with t (decidable, rational arithmetic).

**If q > t:** Suppose ∃n₀, α(n₀) = 1. Then F is eventually g(J₁),
so L = g(J₁). But |q - g(J₁)| < δ/3, so q < g(J₁) + δ/3 =
t - δ/2 + δ/3 = t - δ/6 < t. Contradiction. So ∀n, α(n) = 0.

(The step ¬∃n.α(n)=1 → ∀n.α(n)=0 is BISH-valid for decidable predicates.)

**If q ≤ t:** By the symmetric argument, L = g(J₁) (if L = g(J₀)
then q > t, contradicting q ≤ t). So ∃n₀, α(n₀) = 1.

Extract the witness: from the modulus of convergence, compute N₁ with
|F(N₁) - g(J₁)| < δ/3. Since F(N₁) ∈ {g(J₀), g(J₁)} (decidable) and
|g(J₀) - g(J₁)| = δ > δ/3, we must have F(N₁) = g(J₁). So J(N₁) = J₁,
so m(N₁) = 1, so ∃k ≤ N₁, α(k) = 1.

Bounded search over k = 0, ..., N₁ finds the witness. ∎

### 5.5 LPO → BMC

**Theorem 5.4.** LPO implies BMC.

*Proof.* [Bridges-Vîță 2006, Theorem 2.1.5]. Axiomatize as:

  axiom bmc_of_lpo : LPO → BMC

### 5.6 The combined theorem

**Theorem 5.5 (LPO ↔ BMC ↔ Combinatorial Free Energy Convergence).**
Over BISH, the following are equivalent:

(1) LPO
(2) BMC
(3) For every bounded non-decreasing coupling sequence J : ℕ → [J₀, J₁]
    and every rational β > 0, the sequence -log(2·cosh(β·J(N))) converges.

where condition (3) refers to the *combinatorially defined* free energy
(via finite sums over {±1}^N and the binomial parity identity, NOT via
transfer matrices).

*Proof.*
(1) → (2): Theorem 5.4 (Bridges-Vîță).
(2) → (3): -g(J(N)) is bounded monotone; BMC gives convergence.
(3) → (1): Theorem 5.3 (the encoding and decision procedure).

**Axiom audit:** Identical to Paper 9, Part B. Direction (3) → (1) uses
no omniscience. Direction (1) → (2) axiomatized citing [BV06]. The
equivalence is exactly LPO. ∎

---

## 6. Formulation-Invariance Verification

### 6.1 What was proved

**Paper 9 (transfer matrix formulation):**
- Part A: |f_N - f_∞| ≤ (1/N)·tanh(β)^N, provable in BISH
- Part B: BMC (≡ LPO) ↔ convergence of g(J(N)) for encoded sequences

**This document (combinatorial formulation):**
- Part A: |f_N - f_∞| ≤ (1/N)·tanh(β)^N, provable in BISH
- Part B: BMC (≡ LPO) ↔ convergence of g(J(N)) for encoded sequences

### 6.2 What differs

| Aspect | Paper 9 | This proof |
|---|---|---|
| Z_N derived via | Transfer matrix T, Tr(T^N) | Bond sums, parity sieve |
| f_∞ derived via | Eigenvalue λ₊ of T | Closed form of combinatorial sum |
| Key identity | Z_N = λ₊^N + λ₋^N (spectral) | Z_N = (2cosh)^N + (2sinh)^N (binomial) |
| Linear algebra | Matrix, trace, eigenvectors | None |
| Mathlib imports | LinearAlgebra.Matrix.* | None from LinearAlgebra |
| Error bound proof | Same | Same |
| Encoding construction | Same | Same (different justification for g(J)) |

### 6.3 What is shared

- LPO, BMC definitions (the logical principles under test)
- Real.exp, Real.log, Real.cosh (arithmetic of reals)
- The inequality log(1+x) ≤ x
- The encoding construction α ↦ m ↦ J ↦ F (identical)
- The decision procedure via rational comparison (identical)

### 6.4 The formulation-invariance claim

The logical cost of the 1D Ising thermodynamic limit is:
- Part A: BISH (no omniscience) in both formulations
- Part B: exactly LPO in both formulations

The shared infrastructure (real arithmetic, LPO/BMC definitions) is
formulation-independent — it is the language in which the question is
asked, not a feature of either answer. The formulation-specific
infrastructure (transfer matrices vs. binomial sums) is strictly
disjoint. The logical cost is identical.

**Conclusion:** For the 1D Ising model, the logical cost of the
thermodynamic limit is not an artifact of the transfer-matrix / 
functional-analytic formulation. It persists under reformulation. ∎

---

## 7. Lean 4 Formalization Guide

### 7.1 Suggested module structure

```
Paper9_Combinatorial/
├── Defs/
│   ├── SpinConfig.lean       -- Fin N → Bool, spin values
│   ├── Hamiltonian.lean      -- H_N(σ), agree function
│   ├── PartitionFn.lean      -- Z_N(β) as Finset.sum
│   └── FreeEnergy.lean       -- f_N, f_∞ definitions
├── Combinatorics/
│   ├── BondVariables.lean    -- b_i, cycle constraint
│   ├── BondConfigCorr.lean   -- 2 configs per valid bond pattern
│   ├── ParitySieve.lean      -- Binomial parity identity
│   └── PartitionIdentity.lean -- Z_N = (2cosh)^N + (2sinh)^N
├── Bounds/
│   ├── CoshMonotone.lean     -- cosh increasing on (0,∞)
│   ├── LogOnePlusX.lean      -- log(1+x) ≤ x
│   ├── ErrorBound.lean       -- |f_N - f_∞| ≤ (1/N)·r^N
│   └── ComputeN0.lean        -- Constructive N₀
├── LPO/
│   ├── Defs.lean             -- LPO, BMC
│   ├── Encoding.lean         -- α ↦ m ↦ J ↦ F
│   ├── GapLemma.lean         -- δ = g(J₀) - g(J₁) > 0
│   ├── Decision.lean         -- Rational comparison → case split
│   ├── WitnessExtraction.lean -- Bounded search for witness
│   └── Equivalence.lean      -- LPO ↔ BMC ↔ convergence
└── Main/
    ├── Dispensability.lean    -- Part A main theorem
    ├── Calibration.lean       -- Part B main theorem
    └── FormulationInvariance.lean -- Comparison statement
```

### 7.2 Mathlib dependencies

**REQUIRED (shared with Paper 9):**
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv` (or Exp) — Real.exp, Real.log
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — log properties
- `Mathlib.Data.Bool.Basic`, `Mathlib.Data.Fin.Basic`
- `Mathlib.Order.Basic` — monotonicity

**REQUIRED (new, combinatorial):**
- `Mathlib.Data.Nat.Choose.Basic` — binomial coefficients C(N,k)
- `Mathlib.Algebra.BigOperators.Basic` — Finset.sum
- `Mathlib.Data.Finset.Powerset` or `Fintype` — summing over subsets

**EXPLICITLY NOT IMPORTED (formulation-invariance constraint):**
- `Mathlib.LinearAlgebra.Matrix.*`
- `Mathlib.LinearAlgebra.Eigenspace.*`
- `Mathlib.Analysis.NormedSpace.*`
- `Mathlib.Analysis.InnerProductSpace.*`
- `Mathlib.Topology.Algebra.Module.*`

### 7.3 Key formalization challenges

**Challenge 1: The partition function as a Finset.sum.**

Z_N(β) = Σ_{σ : Fin N → Bool} exp(β · Σ_{i : Fin N} agree(σ, i))

In Lean:
```lean
def partitionFn (N : ℕ) (β : ℝ) : ℝ :=
  Finset.univ.sum fun (σ : Fin N → Bool) =>
    Real.exp (β * Finset.univ.sum fun (i : Fin N) =>
      if σ i == σ (Fin.cycle i) then (1 : ℝ) else (-1 : ℝ))
```

where `Fin.cycle i` maps i to (i+1) mod N. (This may need a custom
definition for the cyclic successor on Fin N.)

**Challenge 2: The bond-configuration correspondence.**

This requires showing that the map σ ↦ (b_0, ..., b_{N-1}) is a 2-to-1
surjection onto the set of bond patterns with Π b_i = 1. The proof is
combinatorial but involves careful counting with Finset.card.

One approach: instead of the correspondence, prove the partition function
identity Z_N = (2cosh)^N + (2sinh)^N directly by induction on N, using
the recurrence structure. This may be simpler to formalize.

**Alternative: Direct induction approach.**

**Lemma (Inductive partition function).** For the periodic 1D Ising chain:

For N = 1: Z_1(β) = exp(β) + exp(-β) + exp(-β) + exp(β) = 2(exp(β) + exp(-β))

Wait, N = 1 with periodic boundary: σ₁ with σ₂ = σ₁.
H_1(σ) = -σ₁·σ₁ = -1. So Z_1 = 2·exp(β).

Actually, for N = 1 periodic: one spin, σ₁ ∈ {±1}, σ₂ = σ₁.
Sum: Σ_{σ₁} exp(β · σ₁ · σ₁) = Σ_{σ₁} exp(β) = 2·exp(β).

And (2cosh)^1 + (2sinh)^1 = 2cosh(β) + 2sinh(β) = 2exp(β). ✓

For N = 2 periodic: σ₁, σ₂, with σ₃ = σ₁.
Bonds: σ₁σ₂ and σ₂σ₁.
Z_2 = Σ_{σ₁,σ₂} exp(β(σ₁σ₂ + σ₂σ₁)) = Σ exp(2β·σ₁σ₂)

(+,+): exp(2β). (+,-): exp(-2β). (-,+): exp(-2β). (-,-): exp(2β).
Z_2 = 2exp(2β) + 2exp(-2β) = 2·2cosh(2β) = 4cosh(2β).

And (2cosh)^2 + (2sinh)^2 = 4cosh²+4sinh² = 4(cosh²+sinh²) = 4cosh(2β). ✓

The induction approach is trickier because the periodic boundary means
the chain is a cycle, and induction on N for cyclic chains requires
conditioning on the first and last spin.

**Recommended approach for Lean:** Prove the identity Z_N = (2cosh)^N + (2sinh)^N
by the combinatorial route (bond variables + parity sieve), which is a
clean finite argument. The alternative (induction on N for open chains,
then close the chain) also works but requires more case analysis.

For the bond route, the key lemma to formalize is:

```lean
-- The parity sieve identity
theorem parity_sieve (a c : ℝ) (N : ℕ) :
    2 * (Finset.filter (fun k => k % 2 = N % 2) (Finset.range (N+1))).sum
        (fun k => Nat.choose N k * a ^ k * c ^ (N - k))
    = (a + c) ^ N + (a - c) ^ N := by
  sorry -- proved by binomial theorem + adding (a+c)^N and (a-c)^N
```

This is a standard identity. It may already be in Mathlib in some form
(related to `Commute.add_pow` or the binomial theorem).

**Challenge 3: Cyclic successor on Fin N.**

Need: `cyclicSucc : Fin N → Fin N` mapping `⟨i, hi⟩` to `⟨(i+1) % N, ...⟩`.
This should be straightforward with `Fin.mk ((i+1) % N) (Nat.mod_lt _ hN)`.

### 7.4 Formalization order

1. **Defs:** SpinConfig, Hamiltonian, PartitionFn (pure definitions, ~80 lines)
2. **ParitySieve:** The binomial identity (self-contained, ~100 lines)
3. **PartitionIdentity:** Z_N = (2cosh)^N + (2sinh)^N via bond argument (~200 lines)
   - BondVariables, BondConfigCorr, apply ParitySieve
   - OR: prove by direct algebraic manipulation after bond decomposition
4. **Bounds:** CoshMonotone, LogOnePlusX, ErrorBound, ComputeN0 (~150 lines)
   - These closely parallel Paper 9 Part A, but import from Combinatorics/ not Matrix/
5. **LPO:** Encoding, GapLemma, Decision, WitnessExtraction, Equivalence (~250 lines)
   - Encoding + decision procedure identical to Paper 9 Part B modulo g(J) justification
6. **Main:** Dispensability, Calibration, FormulationInvariance (~50 lines)

**Estimated total:** 800-900 lines.

### 7.5 The FormulationInvariance module

The final module should contain a statement like:

```lean
/-- The combinatorial free energy matches the transfer-matrix free energy.
    This is a sanity check: both formulations compute the same function. -/
theorem combinatorial_eq_spectral (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β) :
    partitionFn_combinatorial N β = partitionFn_spectral N β := by
  -- Both reduce to (2·cosh β)^N + (2·sinh β)^N
  sorry

/-- The dispensability result (Part A) holds in the combinatorial formulation. -/
theorem dispensability_combinatorial (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |freeEnergyDensity_combinatorial N β - freeEnergy_inf β| < ε := by
  sorry -- proved via combinatorial error bound

/-- The LPO equivalence holds in the combinatorial formulation. -/
theorem lpo_equiv_combinatorial :
    LPO ↔ BoundedMonotoneConvergence := by
  sorry -- proved via combinatorial encoding
```

Note: the first statement (combinatorial_eq_spectral) is NOT necessary
for the formulation-invariance claim. The claim is not that the two
formulations compute the same thing (they trivially do — same physics).
The claim is that the logical cost is the same. The first statement is
a sanity check; the second and third are the actual content.

If we want to be maximally clean, the FormulationInvariance module should
NOT import any module from Paper 9. The two formalizations should be
completely independent, and the identity of axiom profiles should be
verified by external audit (reading the Lean output for both), not by
a cross-referencing theorem.

---

## 8. Notes for the Agent

### 8.1 What to do

Formalize this proof in Lean 4 + Mathlib as a standalone project. The
project MUST NOT import any module from the Paper 9 transfer-matrix
formalization. It may import Mathlib (excluding LinearAlgebra and
NormedSpace modules — see §7.2 for the whitelist/blacklist).

### 8.2 Priority order

1. Get the parity sieve identity working (§2.5, corrected version)
2. Prove Z_N = (2cosh)^N + (2sinh)^N from the parity sieve
3. Derive the error bound |f_N - f_∞| ≤ (1/N)·r^N
4. Set up the encoding and prove BMC → LPO
5. State the main theorems (dispensability and LPO equivalence)
6. Fill in remaining sorry's

### 8.3 If the parity sieve is hard

The parity sieve (Lemma 2.4 corrected) is a standard identity but may
require nontrivial Mathlib binomial theorem infrastructure. If this
proves difficult, there is a fallback:

**Fallback: Prove Z_N = (2cosh)^N + (2sinh)^N by induction on N for
open chains, then close.**

Define the open-chain partition function (no periodic boundary):

  Z_N^open(β, s, s') = Σ_{σ₂,...,σ_{N-1}} Π exp(β · σ_i · σ_{i+1})

with σ₁ = s, σ_N = s' fixed. This satisfies a matrix recurrence:

  Z_1^open(β, s, s') = exp(β · s · s') = T(s,s')

where T is the 2×2 matrix — but we DON'T call it a "transfer matrix"
or import linear algebra. We just define T as a function
{±1} × {±1} → ℝ and prove the recurrence by unfolding the sum.

  Z_N^open(β, s, s') = Σ_{s''} Z_{N-1}^open(β, s, s'') · exp(β · s'' · s')

This is a convolution, provable by rearranging the finite sum.

Then Z_N(β) = Σ_s Z_N^open(β, s, s) (closing the chain).

And by induction: Z_N^open(β, s, s') can be computed explicitly, giving
the same (2cosh)^N + (2sinh)^N formula for the trace.

This is essentially the transfer matrix proof in disguise but using
ONLY finite sums and the convolution identity, with no import of
Matrix, LinearMap, or any algebra infrastructure beyond Finset.sum.

### 8.4 Axiom audit instructions

After completing the formalization, run:

```bash
grep -r "axiom\|sorry\|Classical\|Decidable\|byContradiction\|
         LinearAlgebra\|NormedSpace\|Matrix\b" Paper9_Combinatorial/
```

The audit should show:
- `axiom bmc_of_lpo : LPO → BMC` (the Bridges-Vîță direction, same as Paper 9)
- No `sorry` in completed modules
- No `Classical.*` in Part A modules (BISH)
- No imports from `LinearAlgebra`, `NormedSpace`, `Matrix`
- The `Classical.*` usage pattern should match Paper 9 Part B exactly

If the audit matches, formulation-invariance is verified.

