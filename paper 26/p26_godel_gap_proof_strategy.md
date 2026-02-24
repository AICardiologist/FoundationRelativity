# Proof Strategy Document: P26 — The Gödel-Gap Correspondence, Formalized

## Paper Working Title
**The Gödel-Gap Correspondence: A Lean-Verified Lattice Isomorphism Between Arithmetic Incompleteness and Analytic Non-Reflexivity**

## Series Context
This is Paper 26 in the Constructive Reverse Mathematics (CRM) series (Lee 2024–2026). Paper 2 established that the bidual gap (ℓ∞/c₀) has exactly the logical strength of WLPO. This paper formalizes a deeper structural result: the bidual gap *contains* a lattice-isomorphic copy of arithmetic incompleteness. Specifically, the Lindenbaum algebra of Π⁰₁ sentences of PA embeds as a sublattice of ℓ∞/c₀ via an explicit, computable map.

This result appeared at paper level in earlier drafts (Paper 3/3A). This is the first machine-checked formalization.

## Central Theorem

**Gödel-Gap Correspondence**: The map

    Φ: Π⁰₁/∼_PA  →  L ⊂ ℓ∞/c₀
    Φ([φ])       :=  [v^φ]

is a lattice isomorphism, where:
- Π⁰₁/∼_PA is the Lindenbaum algebra of closed Π⁰₁ sentences modulo PA-provable equivalence
- L is the "logical gap sublattice" of ℓ∞/c₀
- v^φ is the "Gödel sequence" encoding the consistency status of φ

## Architecture Overview

```
P26_GodelGap/
├── Basic.lean              -- Foundational definitions
├── ArithmeticSide.lean     -- Π⁰₁ sentences, proof predicate, Lindenbaum algebra
├── AnalyticSide.lean       -- ℓ∞/c₀ sublattice L, lattice operations
├── GodelSequence.lean      -- The map v^φ and its properties
├── WellDefined.lean        -- Φ respects provable equivalence
├── Injective.lean          -- Φ is injective
├── Surjective.lean         -- Φ is surjective onto L
├── LatticeMorphism.lean    -- Φ preserves ∧ and ∨
├── GodelGapCorrespondence.lean  -- Main theorem assembling all parts
├── CalibrationLink.lean    -- Connection to WLPO calibration from Paper 2
├── Main.lean               -- Aggregator, axiom audit, documentation
```

---

## Phase 1: Arithmetic Side (`ArithmeticSide.lean`)

### The Proof Predicate

We need a decidable predicate representing "p is a proof of ψ in PA."

**Approach: Axiomatize with specified properties.**

Building Gödel numbering from scratch in Lean would be a multi-month project and is not the goal. Instead, axiomatize the proof predicate with exactly the properties needed:

```lean
/-- Axiomatized proof predicate for PA.
    `PrfPA p ψ` means "p is a PA-proof of the sentence with Gödel number ψ".
    We axiomatize the properties we need rather than building Gödel numbering. -/
axiom SentencePA : Type
axiom PrfPA : ℕ → SentencePA → Prop
axiom PrfPA_decidable : ∀ p ψ, Decidable (PrfPA p ψ)

/-- Negation of sentences -/
axiom negPA : SentencePA → SentencePA

/-- Conjunction and disjunction of sentences -/
axiom andPA : SentencePA → SentencePA → SentencePA
axiom orPA : SentencePA → SentencePA → SentencePA

/-- PA-provability: there exists a proof -/
def ProvablePA (ψ : SentencePA) : Prop := ∃ p, PrfPA p ψ

/-- PA-refutability: the negation is provable -/
def RefutablePA (ψ : SentencePA) : Prop := ProvablePA (negPA ψ)

/-- Consistency of a sentence: not refutable -/
def ConsistentPA (ψ : SentencePA) : Prop := ¬ RefutablePA ψ

/-- PA-provable equivalence -/
def PAEquiv (φ ψ : SentencePA) : Prop :=
  ProvablePA (andPA (implPA φ ψ) (implPA ψ φ))
```

**Axioms about PrfPA that we need (state as axioms, document as standard properties of PA):**

```lean
/-- Soundness for refutation: if PA proves ¬φ, there's a finite witness -/
axiom refutation_bounded : ∀ φ, RefutablePA φ → ∃ p, PrfPA p (negPA φ)
-- (This is just the definition unwrapped, but stating it makes the API clearer)

/-- Decidability of bounded proof search -/
axiom bounded_proof_search_decidable :
  ∀ φ (n : ℕ), Decidable (∃ p, p ≤ n ∧ PrfPA p (negPA φ))

/-- PAEquiv is an equivalence relation -/
axiom paEquiv_refl : ∀ φ, PAEquiv φ φ
axiom paEquiv_symm : ∀ φ ψ, PAEquiv φ ψ → PAEquiv ψ φ
axiom paEquiv_trans : ∀ φ ψ χ, PAEquiv φ ψ → PAEquiv ψ χ → PAEquiv φ χ
```

**Π⁰₁ sentences:**

```lean
/-- Marker for Π⁰₁ sentences. We axiomatize this as a subtype. -/
axiom isPi01 : SentencePA → Prop

/-- The type of Π⁰₁ sentences -/
def Pi01 := { φ : SentencePA // isPi01 φ }

/-- Closure properties of Π⁰₁ -/
axiom pi01_and : ∀ φ ψ, isPi01 φ → isPi01 ψ → isPi01 (andPA φ ψ)
axiom pi01_or : ∀ φ ψ, isPi01 φ → isPi01 ψ → isPi01 (orPA φ ψ)
```

### The Lindenbaum Algebra

```lean
/-- Lindenbaum algebra: Π⁰₁ sentences quotiented by PA-provable equivalence -/
def LindenbaumPi01 := Quotient (Setoid.mk PAEquiv ⟨paEquiv_refl, paEquiv_symm, paEquiv_trans⟩)
```

**Lattice structure on LindenbaumPi01:**

```lean
instance : Lattice LindenbaumPi01 where
  inf := Quotient.lift₂ (fun φ ψ => ⟦andPA φ ψ⟧) (sorry /- respects equivalence -/)
  sup := Quotient.lift₂ (fun φ ψ => ⟦orPA φ ψ⟧) (sorry /- respects equivalence -/)
  -- ... le, etc.
```

**Proof agent task**: The lattice instance requires showing that andPA and orPA respect PAEquiv. This needs axioms about PA: if PA ⊢ φ ↔ φ' and PA ⊢ ψ ↔ ψ', then PA ⊢ (φ ∧ ψ) ↔ (φ' ∧ ψ'). These are standard logical facts. Axiomatize them cleanly.

### Axiom Audit for Arithmetic Side

**Expected custom axioms**: SentencePA, PrfPA, PrfPA_decidable, negPA, andPA, orPA, isPi01, and their properties (~15-20 axioms total). These are all standard facts about PA that would require formalizing Gödel numbering to prove — which is out of scope.

**Document clearly**: These axioms encode "PA is a sound, recursively axiomatized theory with a decidable proof predicate." Any consistent first-order theory with these properties would work. The construction is not specific to PA.

---

## Phase 2: Analytic Side (`AnalyticSide.lean`)

### Infrastructure from Paper 2

Reuse or import ℓ∞ and c₀ definitions from the Paper 2 Lean bundle if possible. If not, redefine:

```lean
/-- ℓ∞: bounded sequences -/
def lInfty := { f : ℕ → ℝ // BddAbove (Set.range (fun n => |f n|)) }

/-- c₀: sequences converging to 0 -/
def c0 := { f : ℕ → ℝ // Filter.Tendsto f Filter.atTop (nhds 0) }

/-- The quotient ℓ∞/c₀ -/
def lInftyModc0 := lInfty ⧸ c0  -- or define via a setoid
```

**Proof agent note**: The exact Lean formulation depends on what Mathlib provides. Mathlib has `lp` spaces. Check if `lp ⊤ ℕ ℝ` gives ℓ∞ and whether c₀ is available. If so, use Mathlib's versions. If not, define custom versions — the Paper 2 bundle should have these.

### The Logical Gap Sublattice L

```lean
/-- Index partition: for each n, a canonical infinite subset of ℕ.
    We use the pairing function for canonicity: U_n = { ⟨n, m⟩ | m ∈ ℕ } -/
def indexPartition (n : ℕ) : Set ℕ := { k | k.unpair.1 = n }

/-- Characteristic function of a union of index sets -/
def charUnion (S : Set ℕ) : ℕ → ℝ :=
  fun k => if k.unpair.1 ∈ S then 1 else 0

/-- The logical gap sublattice: equivalence classes of characteristic
    functions of unions of index partition sets -/
def logicalGapSublattice : Set lInftyModc0 :=
  { q | ∃ S : Set ℕ, q = ⟦charUnion S⟧ }
```

**Lattice operations on L:**

```lean
/-- Meet in L corresponds to intersection of index sets -/
-- [charUnion S] ∧ [charUnion T] = [charUnion (S ∩ T)]
-- because min(χ_A, χ_B) = χ_{A∩B} for {0,1}-valued functions

/-- Join in L corresponds to union of index sets -/
-- [charUnion S] ∨ [charUnion T] = [charUnion (S ∪ T)]
-- because max(χ_A, χ_B) = χ_{A∪B} for {0,1}-valued functions
```

**Proof agent task**: Verify that these operations are well-defined on the quotient. The key fact: if two {0,1}-valued sequences agree except on finitely many indices, they define the same element of ℓ∞/c₀. Since our sequences are characteristic functions of unions of *infinite* partition sets, two such sequences are equal mod c₀ iff they correspond to the same union (up to finite sets). Make this precise.

---

## Phase 3: The Gödel Sequence (`GodelSequence.lean`)

### Definition

```lean
/-- The Gödel sequence of a Π⁰₁ sentence φ.
    v^φ_k = 1 if k is in the index set for [φ]'s lattice position
            AND no proof of ¬φ has been found up to k.
    v^φ_k = 0 otherwise. -/
def godelSeq (φ : SentencePA) : ℕ → ℝ :=
  fun k =>
    if k.unpair.1 ∈ latticePosition φ ∧
       ∀ p, p ≤ k → ¬ PrfPA p (negPA φ)
    then 1
    else 0
```

**Note on `latticePosition`**: This maps each Π⁰₁ sentence (or rather, its equivalence class) to the corresponding set of natural numbers in the Birkhoff representation. For the Lean formalization, the simplest approach may be to use the Gödel number of φ directly as the index, avoiding the full Birkhoff representation:

```lean
/-- Simplified: use Gödel number of φ as the index into the partition -/
def godelSeqSimple (φ : SentencePA) (godelNum : ℕ) : ℕ → ℝ :=
  fun k =>
    if k.unpair.1 = godelNum ∧
       ∀ p, p ≤ k → ¬ PrfPA p (negPA φ)
    then 1
    else 0
```

This simplification maps each sentence to a single row of the ℕ×ℕ grid (via the pairing function), with the row determined by its Gödel number. It's less general than the full Birkhoff representation but sufficient for the lattice isomorphism.

**Proof agent task**: Decide between the full lattice-position approach and the simplified Gödel-number approach. The simplified version is easier to formalize but may complicate the surjectivity argument. The full version is more faithful to the paper but requires formalizing Birkhoff's representation theorem for distributive lattices — which is a substantial side project.

**Recommendation**: Start with the simplified version. If surjectivity breaks, upgrade to the full version.

### Key Properties of godelSeq

```lean
/-- godelSeq φ is bounded (values in {0,1}) -/
theorem godelSeq_bdd (φ : SentencePA) : ∀ k, |godelSeq φ k| ≤ 1

/-- If φ is refutable, godelSeq φ is eventually zero (hence in c₀) -/
theorem godelSeq_refutable_in_c0 (φ : SentencePA) (h : RefutablePA φ) :
    godelSeq φ ∈ c0

/-- If φ is consistent, godelSeq φ is NOT in c₀ -/
theorem godelSeq_consistent_not_c0 (φ : SentencePA) (h : ConsistentPA φ) :
    godelSeq φ ∉ c0
```

**Proof sketches:**

*godelSeq_refutable_in_c0*: If PA ⊢ ¬φ, there exists a proof number p₀. For all k > p₀, the condition `∀ p, p ≤ k → ¬ PrfPA p (negPA φ)` fails (take p = p₀). So godelSeq φ k = 0 for k sufficiently large (specifically, for k ≥ p₀ or more precisely for k such that k.unpair.2 ensures we've passed p₀). Hence godelSeq φ ∈ c₀.

*godelSeq_consistent_not_c0*: If φ is consistent, then for ALL k, `∀ p, p ≤ k → ¬ PrfPA p (negPA φ)` holds (because no refutation proof exists at any length). So for k with k.unpair.1 = godelNum, we have godelSeq φ k = 1. Since the set {k | k.unpair.1 = godelNum} is infinite, the sequence does not converge to 0. Hence godelSeq φ ∉ c₀.

**Proof agent task**: These proofs should be straightforward given the axiomatized properties of PrfPA. The main Lean challenge is managing the unpair arithmetic and the decidability of bounded proof search.

---

## Phase 4: Well-Definedness (`WellDefined.lean`)

### Theorem

```lean
/-- Φ respects PA-provable equivalence:
    if PA ⊢ φ ↔ ψ, then [v^φ] = [v^ψ] in ℓ∞/c₀ -/
theorem godelGap_well_defined (φ ψ : SentencePA) (h : PAEquiv φ ψ) :
    ⟦godelSeq φ⟧ = ⟦godelSeq ψ⟧
```

### Strategy

If PA ⊢ φ ↔ ψ, then φ is refutable iff ψ is refutable (over PA). So:
- If both are refutable: both godelSeq φ and godelSeq ψ are in c₀, so [v^φ] = [0] = [v^ψ].
- If both are consistent: this is where it gets delicate. The sequences may differ pointwise (different Gödel numbers → different index rows), but they must define the same element of L.

**Wait — this reveals a design issue.** If we use the simplified encoding (Gödel number as index), then PA-equivalent sentences with *different* Gödel numbers produce sequences supported on *different* rows. These sequences are NOT equal mod c₀ — they're supported on disjoint infinite sets!

**This means the simplified encoding does NOT give a well-defined map on the Lindenbaum algebra.**

**Fix**: We need the map to depend only on the equivalence class, not on the representative sentence. Two approaches:

**Approach A — Canonical representatives**: Choose a canonical representative for each PA-equivalence class (e.g., the sentence with the smallest Gödel number). Then the map is defined on classes by applying godelSeq to the canonical representative. This requires a choice of canonical representative, which uses classical logic but is straightforward.

```lean
/-- Canonical representative: smallest Gödel number in the equivalence class -/
noncomputable def canonicalRep (cls : LindenbaumPi01) : SentencePA :=
  -- use Nat.find on the Gödel numbers of sentences in the class
  sorry

/-- The Gödel-Gap map on equivalence classes -/
noncomputable def godelGapMap (cls : LindenbaumPi01) : lInftyModc0 :=
  ⟦godelSeq (canonicalRep cls)⟧
```

**Approach B — Consistency-only encoding**: Instead of encoding the full sentence, encode only its *consistency status*. Since PA-equivalent sentences have the same consistency status, this is automatically well-defined.

```lean
/-- Consistency-based Gödel sequence: uses a canonical index for each
    equivalence class, not the Gödel number of a particular sentence -/
def godelSeqClass (classIndex : ℕ) (isConsistent : Prop) [Decidable isConsistent] : ℕ → ℝ :=
  fun k =>
    if k.unpair.1 = classIndex ∧ isConsistent
    then 1
    else 0
```

**Problem with B**: `isConsistent` is not decidable in general (that's the whole point!). So we can't use this directly.

**Approach C — The full Birkhoff encoding from the paper**: Use downward-closed sets in the join-irreducible elements of the Lindenbaum algebra. This is automatically well-defined on equivalence classes because it uses the lattice structure, not individual sentences. But it requires formalizing Birkhoff's representation theorem.

**Proof agent task — critical design decision**: Choose between approaches A, B, C. My recommendation:

Use **Approach A** (canonical representatives). It's the most Lean-natural approach. The `noncomputable` marker is fine — the map's *existence* is what we need for the isomorphism theorem, not its computability. The canonical representative is obtained by well-ordering of ℕ (taking the smallest Gödel number in each class), which is available classically.

The well-definedness proof then becomes: for any two sentences φ, ψ in the same class, canonicalRep selects the same sentence, so godelSeq produces the same sequence. This is trivially true by construction.

**Alternative**: If Approach A feels like cheating (the well-definedness is trivially true because we forced it), consider a hybrid: define godelSeq on individual sentences, then prove that PA-equivalent sentences produce sequences that agree mod c₀. This requires Approach C's insight (that the consistency status is an invariant of the class) but applies it directly:

```lean
/-- Core lemma: PA-equivalent Π⁰₁ sentences have the same consistency status -/
axiom paEquiv_consistent_iff (φ ψ : SentencePA) (h : PAEquiv φ ψ) :
    ConsistentPA φ ↔ ConsistentPA ψ
```

Then well-definedness follows: if φ and ψ are PA-equivalent and both consistent, their godelSeqs are both non-zero characteristic functions (on different rows but both non-zero mod c₀). If both refutable, both are in c₀.

**But**: "both non-zero mod c₀" does NOT mean they're equal mod c₀! Characteristic functions on different infinite sets are different elements of ℓ∞/c₀.

**This confirms: Approach A (canonical representatives) is necessary.** The map must factor through the equivalence class in a way that produces a single sequence, not just sequences with the same "type" (zero vs nonzero).

---

## Phase 5: Injectivity (`Injective.lean`)

### Theorem

```lean
theorem godelGap_injective : Function.Injective godelGapMap
```

### Strategy

Suppose [v^φ] = [v^ψ] in ℓ∞/c₀ (where φ, ψ are canonical representatives of different classes). Then v^φ - v^ψ ∈ c₀. Since v^φ and v^ψ are {0,1}-valued and supported on different rows (different canonical Gödel numbers), v^φ - v^ψ can only be in c₀ if both are in c₀ (both refutable) or... actually, if they're on different rows, v^φ - v^ψ is ±1 on two infinite sets, which is NOT in c₀ unless both are in c₀.

**Wait**: If φ and ψ are canonical representatives of *different* classes, they have different Gödel numbers, so their sequences are supported on disjoint rows. The difference v^φ - v^ψ has values in {-1, 0, 1}. On the row for φ, it equals v^φ. On the row for ψ, it equals -v^ψ. For this to be in c₀, both v^φ and v^ψ must be in c₀, meaning both are refutable. But if both are refutable, they're both PA-equivalent to ⊥ (falsum), which means they're in the same equivalence class — contradicting the assumption that they represent different classes.

So: if φ and ψ are canonical reps of *different* classes and at least one is consistent, [v^φ] ≠ [v^ψ] in ℓ∞/c₀. Injectivity follows.

**Proof agent task**: Formalize this argument. The key lemma is: for two {0,1}-valued sequences supported on disjoint infinite sets, their difference is in c₀ only if both sequences are in c₀. This is a straightforward analytical fact.

**Additional axiom needed**: 

```lean
/-- All refutable Π⁰₁ sentences are PA-equivalent (they're all equivalent to ⊥) -/
axiom refutable_pi01_equivalent (φ ψ : SentencePA)
    (hφ : isPi01 φ) (hψ : isPi01 ψ)
    (hrφ : RefutablePA φ) (hrψ : RefutablePA ψ) :
    PAEquiv φ ψ
```

**Note**: This axiom is actually too strong — not all refutable Π⁰₁ sentences are PA-equivalent. For example, "0=1" and "0=2" are both refutable but not identical, though they are both PA-equivalent to ⊥. The correct statement is that all refutable sentences are PA-equivalent to ⊥ (falsity), which makes them all equivalent to each other. This IS true for Π⁰₁ sentences: a refutable Π⁰₁ sentence is PA-provably equivalent to ⊥.

Actually, wait — this may not be true in general. A refutable Π⁰₁ sentence φ has PA ⊢ ¬φ, which means PA ⊢ φ → ⊥, but we also need PA ⊢ ⊥ → φ, which is trivially true (ex falso). So PA ⊢ φ ↔ ⊥. Yes, the axiom is correct.

---

## Phase 6: Surjectivity (`Surjective.lean`)

### Theorem

```lean
theorem godelGap_surjective : ∀ q ∈ logicalGapSublattice, ∃ cls, godelGapMap cls = q
```

### Strategy

By construction, L consists of equivalence classes [charUnion S] for sets S of natural numbers. For each such S, we need to find a Π⁰₁ sentence whose canonical representative maps to [charUnion S].

**With the simplified encoding**: The elements of L are classes [v] where v is 1 on some row(s) of ℕ×ℕ and 0 elsewhere. Each row corresponds to a Gödel number. So an element of L supported on row n corresponds to the Π⁰₁ sentence with Gödel number n (if it's consistent) or to [0] (if it's refutable).

**Proof agent task**: Surjectivity is essentially by construction of L. The sublattice L is *defined* as the image of the map. So surjectivity onto L is trivial. The content is in showing that L is the *right* sublattice — that it's closed under the lattice operations and contains meaningful elements.

**If L is defined as the image**: Surjectivity is immediate. Define L := Set.range godelGapMap. Then the theorem is trivial. The work shifts to showing that L has the lattice structure claimed (closed under min/max) and that it's a "natural" sublattice (not just an arbitrary image).

---

## Phase 7: Lattice Morphism (`LatticeMorphism.lean`)

### Theorems

```lean
/-- Φ preserves meets -/
theorem godelGap_preserves_inf (a b : LindenbaumPi01) :
    godelGapMap (a ⊓ b) = godelGapMap a ⊓ godelGapMap b

/-- Φ preserves joins -/
theorem godelGap_preserves_sup (a b : LindenbaumPi01) :
    godelGapMap (a ⊔ b) = godelGapMap a ⊔ godelGapMap b
```

### Strategy

On the logical side: a ⊓ b = [φ ∧ ψ], a ⊔ b = [φ ∨ ψ].
On the analytical side: [v] ⊓ [w] = [min(v,w)], [v] ⊔ [w] = [max(v,w)].

Need to show: v^{φ∧ψ} agrees with min(v^φ, v^ψ) modulo c₀, and similarly for joins.

**Key insight**: For Π⁰₁ sentences, consistency of (φ ∧ ψ) relates to consistency of φ and ψ:
- Con(φ ∧ ψ) ↔ Con(φ) ∧ Con(ψ) is NOT true in general (φ and ψ could each be consistent but mutually inconsistent)
- For the lattice morphism to work, we need the *encoding* to respect the operations, not just the consistency status.

**This is a genuine technical issue.** The simplified one-row-per-sentence encoding may not give a lattice morphism because the relationship between v^{φ∧ψ} and min(v^φ, v^ψ) depends on how the Gödel number of (φ ∧ ψ) relates to the Gödel numbers of φ and ψ — and they're on different rows!

**Resolution**: This is where the Birkhoff encoding (using downward-closed sets) was necessary in the paper-level proof. The lattice operations on downward-closed sets (intersection for meet, union for join) correspond directly to the pointwise min/max on characteristic functions. The simplified encoding loses this correspondence.

**Proof agent task — critical**: Either:
(a) Implement the Birkhoff encoding (downward-closed sets of join-irreducibles) and show the lattice morphism property holds, OR
(b) Redefine L and Φ to use a multi-row encoding where each equivalence class maps to a characteristic function on a union of rows, with the union determined by the downward-closed set in the Birkhoff representation, OR
(c) Simplify the theorem to an order-embedding (preserving ≤) rather than a full lattice isomorphism. An order-embedding is weaker but still significant and avoids the lattice-operation complications.

**Recommendation**: Try (c) first. An order-embedding Φ: Π⁰₁/∼_PA ↪ ℓ∞/c₀ that preserves the partial order (PA-provable implication maps to the natural order on ℓ∞/c₀) is already a strong result. If (c) works cleanly, attempt (a) or (b) for the upgrade to a lattice isomorphism.

---

## Phase 8: Main Theorem (`GodelGapCorrespondence.lean`)

### Assembly

```lean
/-- The Gödel-Gap Correspondence: Φ is an order-embedding of the
    Lindenbaum algebra into ℓ∞/c₀ -/
theorem godelGap_orderEmbedding :
    OrderEmbedding LindenbaumPi01 lInftyModc0 where
  toFun := godelGapMap
  inj' := godelGap_injective
  map_rel_iff' := godelGap_order_preserving_iff  -- φ ≤ ψ ↔ [v^φ] ≤ [v^ψ]

/-- Upgrade to lattice isomorphism onto L (if lattice morphism properties are proved) -/
theorem godelGap_latticeIso :
    LatticeHom LindenbaumPi01 lInftyModc0 where
  toFun := godelGapMap
  map_inf' := godelGap_preserves_inf
  map_sup' := godelGap_preserves_sup
```

---

## Phase 9: Calibration Link (`CalibrationLink.lean`)

### Connection to WLPO

The Gödel-Gap correspondence enriches the Paper 2 result (WLPO ↔ bidual gap). Specifically:

```lean
/-- Detecting whether a Gödel-Gap element is zero or nonzero
    is equivalent to deciding consistency of the corresponding Π⁰₁ sentence,
    which is equivalent to WLPO -/
theorem godelGap_detection_iff_wlpo :
    (∀ φ : Pi01, Decidable (godelGapMap ⟦φ⟧ = 0)) ↔ WLPO
```

**Proof sketch**: Deciding whether [v^φ] = 0 in ℓ∞/c₀ is equivalent to deciding whether v^φ ∈ c₀, which is equivalent to deciding whether φ is refutable (by godelSeq_refutable_in_c0 and godelSeq_consistent_not_c0). Deciding refutability of arbitrary Π⁰₁ sentences is equivalent to WLPO (this is essentially the content of Paper 2, rephrased).

**Proof agent task**: This theorem connects P26 back to the series. It shows that the WLPO calibration from Paper 2 is not just about abstract gap detection — it's about deciding arithmetic consistency. The logical and analytical calibrations coincide.

---

## Axiom Budget and Risk Assessment

### Expected custom axioms (~20):
- SentencePA, PrfPA, PrfPA_decidable, negPA, andPA, orPA, implPA (~7 type/function axioms)
- isPi01, pi01_and, pi01_or, pi01_neg (~4 closure axioms)
- paEquiv_refl, paEquiv_symm, paEquiv_trans (~3 equivalence axioms)
- paEquiv_consistent_iff, refutable_pi01_equivalent (~2 key logical axioms)
- bounded_proof_search_decidable (~1 computability axiom)
- Possibly 2-3 more for lattice operations respecting equivalence

**These are all standard facts about PA.** They encode "PA is a consistent recursively axiomatized theory" — nothing controversial. A full formalization of Gödel numbering would prove them, but that's a separate multi-month project.

### Risk assessment:

**High confidence (likely to succeed):**
- godelSeq definition and basic properties (bounded, refutable → c₀, consistent → not c₀)
- Well-definedness via canonical representatives
- Injectivity
- Surjectivity (by construction of L)
- Calibration link to WLPO

**Medium confidence:**
- Lattice morphism properties (may require upgrading from simplified to Birkhoff encoding)
- Clean axiom budget (may need more axioms than expected for lattice operations)

**Fallback if lattice morphism is too hard:**
- State the main result as an order-embedding rather than a lattice isomorphism
- This is still a strong result: the Lindenbaum algebra embeds order-preservingly into the bidual gap
- The lattice isomorphism can be recorded as a conjecture with paper-level proof sketch

### Time estimate: 2-3 weeks

- Week 1: Phases 1-3 (definitions, Gödel sequence, basic properties)
- Week 2: Phases 4-6 (well-definedness, injectivity, surjectivity)
- Week 3: Phases 7-9 (lattice morphism or order-embedding, main theorem, calibration link)

---

## Technical Warnings

1. **Approach A (canonical representatives) requires Classical.choice** to select the smallest Gödel number. This is fine — the map is noncomputable, and the theorem is about *existence* of the isomorphism, not its computability. The axiom profile will include Classical.choice. Document this.

2. **The unpair function** (`Nat.unpair`) is in Mathlib. Use it consistently for the ℕ×ℕ encoding.

3. **Quotient API in Lean 4**: Working with `Quotient` types requires careful use of `Quotient.lift`, `Quotient.ind`, `Quotient.sound`, etc. The proof agent should be comfortable with these.

4. **Do NOT attempt to formalize Gödel numbering.** Axiomatize PrfPA and move on. The paper's contribution is the *correspondence*, not the arithmetization.

5. **Keep the file count manageable.** If some phases merge naturally (e.g., well-definedness + injectivity), combine files. The architecture above is a guide, not a mandate. A single 500-line file that proves the main theorem is better than 10 files with interface complexity.

6. **AI hallucination risk**: The earlier Paper 3 attempts produced categorical constructions that sounded plausible but were mathematically empty. Every definition in this formalization must have a Lean type. Every theorem must compile. If something "should work" but doesn't compile, the construction is wrong — do not paper over it with sorry or hand-waving. Report what breaks and why.

---

## Success Criteria

**Full success**: An order-embedding (or lattice isomorphism) Φ: LindenbaumPi01 → ℓ∞/c₀ with:
- 0 sorry in the main theorem chain
- Custom axioms limited to standard PA properties (~20)
- Clean axiom profile: `[propext, Classical.choice, Quot.sound]` + PA axioms
- The calibration link to WLPO proved

**Partial success**: The Gödel sequence construction with basic properties (refutable → c₀, consistent → not c₀) fully proved, and the correspondence theorem stated with 1-2 sorries in the lattice morphism properties. Still publishable with honest documentation.

**Failure**: The quotient/encoding design doesn't work in Lean and the main theorem has structural sorries. In this case, document what broke — the information is valuable for understanding the limits of formalizing metamathematics in Lean 4.

## Deliverables

1. Clean Lean 4 build (0 errors)
2. Main theorem with explicit axiom audit
3. Documentation distinguishing proved content from axiomatized PA properties
4. Calibration link to WLPO (connecting P26 to Paper 2)
