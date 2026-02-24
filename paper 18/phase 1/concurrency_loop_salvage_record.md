# Concurrency Loops in Johnson Graphs: Salvageable Results

## Paul C.-K. Lee — Record of Valid Results
## February 2026

---

## 0. Context and Purpose

Between March 2025 and early 2026, a series of AI-assisted
conversations developed a framework attempting to derive Standard
Model gauge groups and fermion masses from "concurrency loops" in
forced-merge causal sets. The framework contained a valid
combinatorial core embedded in an invalid physical interpretation.
This document records what is mathematically sound, what failed,
and what remains open.

**Authorship note:** The valid combinatorial results were developed
collaboratively between the author and AI assistants (Claude).
The invalid physical interpretations were also collaboratively
developed — the AI hallucinated plausible-sounding but false
"proofs" of gauge group correspondences, and the author did not
catch the errors until a critical review in February 2026.

**Lesson:** Natural-language mathematical reasoning lacks a
type-checker. A formal verification system (e.g., Lean 4) would
have caught the central error at the first step, preventing months
of wasted development. This experience motivates the CRM
formalization programme.

---

## 1. Setup: The Johnson-like Graph

### 1.1 Definition

Fix n ≥ 3. Define the graph G(n) as follows:

- **Vertices:** All binary strings of length n with exactly two
  bits set to 1. There are C(n,2) = n(n-1)/2 such strings.

- **Edges:** Two vertices are adjacent if and only if they share
  exactly one 1-bit. Equivalently, their bitwise AND has Hamming
  weight 1.

This is closely related to the **Johnson graph** J(n, 2), where
vertices are 2-element subsets of {1, ..., n} and edges connect
subsets sharing exactly one element.

### 1.2 Physical Motivation (Causal Sets)

In the forced-merge causal set framework:

- Each event [a] in the causal set is encoded as a binary string
  γ_b([a]) with exactly two bits set to 1 (the "two-bit rule").

- Two events are "mergeable" (causally related via forced merge)
  if they share at least one common bit: γ_b([a]) AND γ_b([b]) ≠ 0.

- A **concurrency loop** is a cycle in the adjacency graph where
  consecutive events share *exactly* one bit.

The graph G(n) encodes the adjacency structure of these events.
Concurrency loops are cycles in G(n).

### 1.3 Example: G(4)

For n = 4, the vertices are the C(4,2) = 6 binary strings:

```
v₁ = (1,1,0,0)    v₂ = (1,0,1,0)    v₃ = (1,0,0,1)
v₄ = (0,1,1,0)    v₅ = (0,1,0,1)    v₆ = (0,0,1,1)
```

Adjacency (sharing exactly one 1-bit):

```
v₁ — v₂  (share bit 1)
v₁ — v₃  (share bit 1)
v₁ — v₄  (share bit 2)
v₁ — v₅  (share bit 2)
v₂ — v₄  (share bit 3)
v₂ — v₆  (share bit 3)
v₂ — v₃  (share bit 1)
v₃ — v₅  (share bit 4)
v₃ — v₆  (share bit 4)
v₄ — v₅  (share bit 2)    — wait, v₄=(0,1,1,0), v₅=(0,1,0,1)
                              share bit 2, yes
v₄ — v₆  (share bit 3)
v₅ — v₆  (share bit 4)
```

A length-3 cycle: v₁=(1,1,0,0) — v₂=(1,0,1,0) — v₄=(0,1,1,0) — v₁.
Check: v₁∩v₂ = bit 1, v₂∩v₄ = bit 3, v₄∩v₁ = bit 2. ✓

---

## 2. Theorem: Loop Length Divisibility by 3

### 2.1 Statement

**Theorem (Loop Length Divisibility).** Every cycle in G(n) — i.e.,
every closed walk v₁, v₂, ..., v_k, v₁ where consecutive vertices
share exactly one 1-bit and no vertex is repeated — has length
k divisible by 3.

### 2.2 Proof

Let the cycle have vertices v₁, v₂, ..., v_k. Each vertex v_i has
exactly two bits set to 1; denote them as the *pair* {a_i, b_i}
where a_i < b_i (ordering is arbitrary but fixed).

Since consecutive vertices share exactly one bit, we can track
which bit is "shared forward" and which is "new" at each step.

**Labeling convention:** At vertex v_i, call the bit shared with
v_{i-1} the "inherited bit" and the other bit the "free bit."
(For v₁, this is defined by the closing edge from v_k.)

At each step from v_i to v_{i+1}:
- v_{i+1} shares exactly one bit with v_i.
- v_{i+1} must share the *free bit* of v_i (not the inherited bit).

**Why?** Suppose v_{i+1} shared the *inherited bit* of v_i instead.
The inherited bit of v_i is the bit shared between v_{i-1} and v_i.
So v_{i+1} would also share a bit with v_{i-1}. If additionally
v_{i+1} shares no other bit with v_{i-1}, this is allowed but
creates a "shortcut." If v_{i+1} shares both its bits with
v_{i-1}, then v_{i+1} = v_{i-1}, which is forbidden in a simple
cycle (no repeated vertices) unless k = 3 and i = 2.

For a *simple* cycle (no repeated vertices), the only consistent
pattern is: at each step, the free bit of v_i becomes the
inherited bit of v_{i+1}. The new free bit of v_{i+1} is fresh.

**Tracking the bit roles through the cycle:**

Define a function role: {steps} → {inherited, free} that tracks
which "slot" the shared bit occupies.

Step 1→2: v₁ has bits {a₁, b₁}. Say b₁ is shared with v₂.
  v₂ = {b₁, c₂} for some new c₂.
  Inherited bit of v₂: b₁. Free bit of v₂: c₂.

Step 2→3: Free bit c₂ is shared.
  v₃ = {c₂, a₃} for some new a₃.
  Inherited bit of v₃: c₂. Free bit of v₃: a₃.

Step 3→4: Free bit a₃ is shared.
  v₄ = {a₃, b₄} for some new b₄.
  Inherited bit of v₄: a₃. Free bit of v₄: b₄.

The pattern of bit-pair structure repeats with period 3:

```
v₁ = {a, b}       ← pair type (X, Y)
v₂ = {b, c}       ← pair type (Y, Z)
v₃ = {c, d}       ← pair type (Z, X')
v₄ = {d, e}       ← pair type (X', Y')
v₅ = {e, f}       ← pair type (Y', Z')
v₆ = {f, g}       ← pair type (Z', X'')
...
```

More precisely, define the "phase" φ(i) = i mod 3 ∈ {0, 1, 2}.
The bit-sharing pattern has a 3-step periodicity in its structural
role: each group of 3 consecutive vertices introduces 2 new bits
and cycles through the same pattern of inherited/free alternation.

For the cycle to close (v_k shares a bit with v₁), the phase
must return to its starting value: φ(k) ≡ φ(0) mod 3, i.e.,
k ≡ 0 mod 3.

**Formally:** Assign each vertex a label from ℤ/3ℤ based on
which "position" in the 3-cycle it occupies. The closing
condition forces k ≡ 0 (mod 3). ∎

### 2.3 Lean Formalization Notes

This theorem is formalizable in Lean 4 in approximately 100-150
lines. The key structures needed:

- `Fin n → Bool` with Hamming weight 2 (or `Finset.card = 2`)
- Adjacency predicate (shared bits = 1)
- Cycle as a list with adjacency between consecutive elements
  and between last and first
- The proof tracks the ℤ/3ℤ-valued phase around the cycle

**Expected axiom certificate:** [propext, Quot.sound] — no
Classical.choice. Pure finite combinatorics. BISH.

---

## 3. Corollary: Three Shortest Cycle Classes

### 3.1 Statement

**Corollary.** In G(n) for n ≥ 5, the three shortest possible
cycle lengths are 3, 6, and 9.

### 3.2 Proof Sketch

Length 3 exists: see §1.3 example.

Length 6 exists: take two triangles sharing an edge, forming a
hexagonal cycle. Explicitly constructible for n ≥ 5.

Length 9 exists: chain three triangles. Constructible for n ≥ 7.

No cycles of length 1 or 2 exist (trivially — need at least 3
distinct vertices). No cycles of length 4 or 5 exist by the
divisibility theorem. No cycles of length 7 or 8 exist by the
divisibility theorem.

### 3.3 Suppression of Longer Cycles

**Conjecture (Loop-Length Stability).** Under bounded local
complexity constraints (each bit participates in at most B
events), cycles of length k = 3m for m ≥ 4 are exponentially
suppressed relative to k = 3, 6, 9.

**Status:** Unproven. Supported by small-scale computational
experiments (n ≤ 500) but no rigorous proof exists. The
suppression mechanism, if real, likely depends on the specific
bounded-complexity model, not just the graph structure.

---

## 4. The Numerical Coincidence: 3, 6, 9 and Gauge Groups

### 4.1 Observation

The three shortest cycle classes in G(n) have lengths 3, 6, 9.
The Standard Model gauge group is U(1) × SU(2) × SU(3), with
dimensions 1, 3, 8 (or fundamental representation dimensions
1, 2, 3).

Several numerical patterns were noted:
- Loop lengths: 3 = 1×3, 6 = 2×3, 9 = 3×3.
  Multipliers: 1, 2, 3 — matching representation dimensions.
- Three classes — matching three gauge group factors.
- The pattern terminates naturally (longer loops suppressed) —
  matching the fact that no fourth gauge group is observed.

### 4.2 Why This Is Not a Theorem

The claim that "merge-preserving transformations on length-k loops
are isomorphic to U(1), SU(2), SU(3)" was the central assertion
of the original framework. **This claim is false.**

The actual automorphism groups of cycles in G(n) are:

- **Length-3 cycle:** The automorphism group (permutations of the
  3 vertices preserving adjacency) is the dihedral group D₃ ≅ S₃,
  which has 6 elements. This is NOT isomorphic to U(1), which is
  a compact connected Lie group with uncountably many elements.

- **Length-6 cycle:** The cycle automorphism group is D₆, a finite
  group with 12 elements. This is NOT isomorphic to SU(2), which
  is a 3-dimensional compact Lie group.

- **Length-9 cycle:** The cycle automorphism group is D₉, a finite
  group with 18 elements. This is NOT isomorphic to SU(3), which
  is an 8-dimensional compact Lie group.

**The fundamental error:** Discrete finite structures (graphs,
combinatorial cycles) have discrete finite automorphism groups.
Continuous Lie groups (U(1), SU(2), SU(3)) cannot arise as
automorphism groups of finite combinatorial objects without
additional continuous structure being introduced by hand. The
original framework introduced this continuous structure via
"extending to complex-valued fields," but this extension was
not derived from the causal set axioms — it was imposed to
match the desired conclusion.

### 4.3 What Would Be Needed

For a valid loop-gauge correspondence, one would need:

1. A *continuum limit* of the graph structure as n → ∞, in which
   the discrete automorphism groups enlarge to continuous groups.

2. A proof that this continuum limit yields specifically U(1),
   SU(2), SU(3) and not some other continuous groups.

3. An explanation of why the continuum limit of a D₃ symmetry
   becomes U(1) rather than SO(2) or any other 1-dimensional
   Lie group (these happen to be isomorphic, but the isomorphism
   would need to be derived, not assumed).

4. An explanation of why D₆ → SU(2) rather than SO(3) or U(2)
   or Sp(1) (SU(2) ≅ Sp(1), but why not SO(3) ≅ SU(2)/ℤ₂?).

None of these were provided. The gap between finite discrete
symmetry and continuous gauge symmetry was papered over with
hand-waving about "complex-valued fields."

---

## 5. The Koide Formula Connection

### 5.1 What Was Claimed

The framework proposed a mass formula:

  m_G = μ · (k_G / 3)^β · √C₂(G)

where k_G ∈ {3, 6, 9} are loop lengths, C₂(G) are quadratic
Casimir invariants of U(1), SU(2), SU(3), and β ≈ 5.3 is a
fitted parameter. It was claimed that this formula yields the
Koide ratio Q = 2/3.

### 5.2 Why This Failed

1. The Casimir invariants C₂(U(1)) = 1, C₂(SU(2)) = 3/4,
   C₂(SU(3)) = 4/3 were imported from standard physics, not
   derived from the loop structure. Without the loop-gauge
   correspondence (which is invalid — see §4.2), there is no
   reason to associate these specific Casimir values with loops
   of lengths 3, 6, 9.

2. The parameter β ≈ 5.3 was fitted to reproduce Q = 2/3.
   A formula with a free parameter that is fitted to one datum
   is not a derivation.

3. The "close to 5.5" observation (where 5.5 = d + n_G/2 =
   4 + 3/2 for "theoretical" reasons) differs from 5.3 by
   about 4%, which is not close enough to claim a match.

4. The Koide formula relates *charged lepton* masses (e, μ, τ),
   which are all in the *same* gauge representation (SU(2)
   doublet, U(1) charged). They differ by *generation*, not by
   gauge group. The loop-gauge framework associates different
   loop lengths with different gauge groups, not with different
   generations. This is a category error.

### 5.3 What Would Be Needed

A valid derivation of the Koide formula from causal sets would
need to explain *generations* (three copies of the same gauge
representation), not *gauge groups* (three different symmetries).
The loop-length divisibility theorem gives three size classes,
but these would need to correspond to generations, not to U(1),
SU(2), SU(3). This is a fundamentally different physical
interpretation that was never developed.

---

## 6. Open Questions (Honest Assessment)

### 6.1 Genuinely Open and Interesting

1. **Is the loop-length stability conjecture (§3.3) provable?**
   Under what bounded-complexity assumptions are loops of length
   ≥ 12 exponentially suppressed? This is a well-defined
   combinatorial question independent of any physical interpretation.

2. **Does the Johnson graph J(n,2) have other interesting cycle
   structure?** The divisibility-by-3 theorem constrains cycle
   lengths. Are there further constraints on which multiples of 3
   actually occur for given n?

3. **Is there ANY valid route from discrete graph symmetry to
   continuous gauge symmetry?** Lattice gauge theory achieves this
   (Wilson's formulation recovers continuous gauge groups in the
   continuum limit), but through a very different mechanism than
   the one proposed here. Could the Johnson graph structure feed
   into a lattice gauge construction?

4. **Can the "three shortest cycle classes" observation be given
   physical content through a mechanism that doesn't require
   the false loop-gauge correspondence?** For instance, if the
   three cycle classes correspond to three *generations* rather
   than three *gauge groups*, the numerology changes entirely
   and might or might not work.

### 6.2 Likely Dead Ends

1. Direct identification of cycle automorphism groups with Lie
   groups. The mathematical gap is unbridgeable without a
   continuum limit, and no natural continuum limit has been
   identified.

2. Deriving Casimir invariants from loop lengths. Without the
   gauge correspondence, there is no connection between loop
   combinatorics and representation theory.

3. Deriving absolute mass values from the framework. Even if
   a valid gauge correspondence existed, the framework has no
   mechanism for fixing the overall mass scale μ.

---

## 7. Relation to the CRM Programme

### 7.1 What Axiom Calibration Can Contribute

The Loop Length Divisibility Theorem is a BISH result (finite
combinatorics, no choice principles). This is confirmed by its
structure: the proof is a finite case analysis on ℤ/3ℤ-valued
labels around a cycle.

If formalized in Lean 4:
- **#print axioms** would return [propext, Quot.sound] — clean.
- The result would be a small but valid entry in the
  "finite combinatorics is BISH" column of the calibration table.

More importantly, **the failed loop-gauge correspondence would
have been caught by Lean at the first step.** The statement
"Aut(C₃ in J(n,2)) ≅ U(1)" is type-incorrect: the left side
is a finite group (Fintype), the right side is a topological
group (TopologicalGroup). Lean's type system would refuse to
state the isomorphism, let alone prove it. This is a concrete
example of formalization preventing hallucination.

### 7.2 Lesson for the Programme

AI-assisted mathematical reasoning without formal verification
is unreliable for claims that cross mathematical categories
(e.g., finite combinatorics → continuous Lie theory). The
present case is a cautionary example: the combinatorial layer
was valid, the categorical leap was invalid, and the error
propagated through dozens of conversations because natural
language doesn't enforce type constraints.

The CRM programme's insistence on Lean formalization is not
just methodological preference — it's a safeguard against
exactly this failure mode.

---

## 8. Summary

| Component | Status | Lean-able? |
|-----------|--------|------------|
| Two-bit rule, Johnson graph setup | Valid | Yes, ~50 lines |
| Loop Length Divisibility (k ≡ 0 mod 3) | Valid theorem | Yes, ~100-150 lines |
| Three shortest classes: 3, 6, 9 | Valid corollary | Yes, ~50 lines |
| Loop-length stability conjecture | Unproven conjecture | Open |
| Loop-Gauge Correspondence (D₃ ≅ U(1), etc.) | **FALSE** | Would fail in Lean |
| Casimir invariants from loops | **UNFOUNDED** | N/A |
| Mass formula m_G ~ μ(k/3)^β √C₂ | **UNFOUNDED** | N/A |
| Koide Q = 2/3 from loops | **UNFOUNDED** | N/A |
| Three cycle classes ↔ three generations | Open, unexplored | Possible if developed |

---

END OF RECORD
