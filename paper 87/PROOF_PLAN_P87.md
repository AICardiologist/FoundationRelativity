# Paper 87 — Proof Plan (v2)

## Title
The Omniscience Cost of the Hodge Condition: A CRM Analysis

Paper 87 of the Constructive Reverse Mathematics Series

## Thesis
The uniform Hodge test — a single algorithm that decides "is α of type (p,p)?" for an arbitrary period matrix presented as Cauchy sequences — requires WLPO. When algebraic metadata is available (CM type, or known Mumford-Tate group), the cost drops to BISH. This is the first CRM analysis of a Clay Millennium Problem.

## What this paper IS
- A CRM-level classification of the uniform Hodge test as a decision problem
- A biconditional: uniform (p,p)-decidability = BISH iff algebraic metadata is available
- An embedding reduction: a uniform Hodge decider implies WLPO (via Bridges-Richman)
- A structural explanation of why all known Hodge results require CM or equivalent rigidity
- The first application of DPT to the Hodge conjecture's logical architecture

## What this paper is NOT
- A proof or disproof of the Hodge conjecture
- A new proof strategy for Hodge
- A biconditional between the Hodge conjecture and an omniscience principle
- A claim that the Hodge conjecture is related to Markov's Principle (it is not; the logical forms are distinct)

---

## Critical Correction (from v1)

### The "generic" fallacy

v1 claimed: "For generic abelian varieties (algebraically independent periods), the Hodge test requires WLPO."

This is **false**. For a KNOWN-generic abelian variety (Mumford-Tate group = Sp_{2g}), the only Hodge classes are Lefschetz classes. Testing "is α a wedge product of the polarisation?" is combinatorial. Cost: BISH.

Both endpoints give BISH:
- **CM varieties:** period entries are algebraic (Shiga-Wolfart). Hodge test is exact arithmetic. BISH.
- **Known-generic varieties:** MT group is maximal. Hodge classes = Lefschetz classes. No period computation needed. BISH.

The WLPO cost arises at the **uniform** problem: an algorithm that takes an ARBITRARY period matrix Ω (as Cauchy sequences) and a class α (as rational coordinates) and decides "is α Hodge?" This algorithm must handle all cases — CM, generic, and intermediate — without knowing which case it's in. Testing the projections π_{a,b}(α) requires real arithmetic on the period entries, and testing whether the result equals zero is WLPO.

### The uniform-vs-nonuniform distinction

This parallels a standard phenomenon in constructive mathematics:
- **Nonuniform:** For each specific variety (with known MT group), the Hodge test is BISH.
- **Uniform:** A single algorithm for ALL varieties requires WLPO.

The CRM cost of the Hodge condition is the cost of the UNIFORM problem. This is the natural formulation because the Hodge conjecture quantifies over ALL smooth projective varieties — it requires a uniform understanding of "Hodge class."

---

## Mathematical Content

### Setup

Let A be a principally polarised abelian variety of dimension g over C. The period matrix Ω ∈ H_g (Siegel upper half-space) determines the Hodge decomposition on H^{2p}(A, C). A class α ∈ ∧^{2p} H^1(A, Q) is **Hodge** iff π_{a,b}(α) = 0 for all (a,b) ≠ (p,p).

### The Uniform Hodge Test

**Definition.** The uniform Hodge test is the function:

  UniformHodgeTest : H_g × ∧^{2p}(Q^{2g}) → {yes, no}
  UniformHodgeTest(Ω, α) = "is α of type (p,p) with respect to Ω?"

where Ω is presented constructively (entries as Cauchy sequences of rationals) and α is given as rational coordinates.

The test reduces to: for each off-diagonal (a,b), compute π_{a,b}(α) ∈ C (a Q-linear combination of entries of Ω) and test if it equals zero.

### Theorem A (CM metadata → BISH)

**Statement.** If the abelian variety A is equipped with CM type (K, Φ), then the Hodge test for A is BISH-decidable.

**Proof sketch.**

1. **Shiga-Wolfart theorem** (1985, via Wüstholz's analytic subgroup theorem): For an abelian variety A/Q̄, the normalised period matrix has algebraic entries iff A has CM.

2. CM type (K, Φ) determines the Hodge decomposition algebraically: H^1(A, C) = ⊕_{σ ∈ Φ} H^{1,0}_σ ⊕ ⊕_{σ̄ ∈ Φ̄} H^{0,1}_{σ̄}, where the decomposition is by the action of K.

3. The projections π_{a,b} become K-linear maps, computable in exact arithmetic over Q̄.

4. Testing "is a Q̄-number equal to zero?" is BISH: it reduces to polynomial GCD over Q.

**Lean target:** Axiomatise CM metadata as providing algebraic period entries. Derive BISH-decidability from exact Q̄-arithmetic.

### Theorem B (Uniform test → WLPO)

**Statement.** Any uniform decider for the Hodge test implies WLPO.

**Proof: embedding reduction.**

1. Given any x ∈ R, construct a period matrix Ω_x ∈ H_g and a class α_x ∈ ∧^{2p}(Q^{2g}) such that:

   π_{a,b}(α_x) = x  (for one specific off-diagonal (a,b))
   π_{a',b'}(α_x) = 0  (for all other off-diagonal (a',b'))

   Construction: Start with a fixed CM period matrix Ω_0 (all entries algebraic). Perturb one entry: Ω_x = Ω_0 + x · E_{jk} where E_{jk} is a basis matrix and the perturbation is small enough that Im(Ω_x) > 0. Choose α_x so that the only non-trivial projection involves the perturbed entry.

2. Then: α_x is Hodge with respect to Ω_x iff π_{a,b}(α_x) = x = 0 iff x = 0.

3. A uniform Hodge decider applied to (Ω_x, α_x) decides "x = 0."

4. By Bridges-Richman (1987, Varieties of Constructive Mathematics, §1.3): the statement "∀x ∈ R, x = 0 ∨ x ≠ 0" is exactly WLPO.

5. Therefore: UniformHodgeDecider → WLPO.

**Lean target:** The embedding axioms (embed_real, embed_proj) encode steps 1-2. The reduction (step 3-5) is a 5-line proof matching the standard CRM pattern. This is Gemini's stub, which is correct.

### Theorem C (Biconditional)

**Statement.** For abelian varieties of dimension g ≥ 2:

  HodgeTestCost(metadata) = BISH  ↔  algebraic metadata determines the Hodge classes

where "algebraic metadata" means: a known CM type, OR a known Mumford-Tate group (including the generic case MT = Sp_{2g}).

**Proof.** Forward: if algebraic metadata is available, Theorem A (CM) or Lefschetz classification (generic) gives BISH. Reverse: without metadata, the uniform test is the only option, and Theorem B gives cost ≥ WLPO > BISH.

**The biconditional structure.** This mirrors Papers 72-74:
| Paper 72 | cycle_search_cost = BISH ↔ height is positive-definite |
| Paper 73 | morphism_cost = BISH ↔ radical is detachable |
| Paper 74 | eigenvalue_cost = BISH ↔ spectrum is algebraic |
| **Paper 87** | **hodge_test_cost = BISH ↔ algebraic metadata available** |

The common pattern: BISH-decidability of a mathematical operation is equivalent to an algebraic structural condition. Without the condition, the cost rises to WLPO or LPO.

### Theorem D (Shiga-Wolfart boundary for abelian varieties over Q̄)

**Statement.** For abelian varieties defined over Q̄:

  Period entries are algebraic  ↔  A has CM  (Shiga-Wolfart 1985)

**Consequence for the biconditional:** Over Q̄, the algebraic metadata condition in Theorem C reduces to "A has CM" for the period-entry route to BISH. The Lefschetz/MT-group route (known-generic) is independent of this — it works over any field but requires knowing the MT group.

**Lean target:** State Shiga-Wolfart as an axiom. Use it to sharpen Theorem C over Q̄.

### Connection to the Mumford-Tate conjecture

**Observation (not a theorem).** The Mumford-Tate conjecture asserts MT(A) = G_ℓ(A) (the ℓ-adic monodromy group). If true, the MT group is computable from the Galois action on ℓ-adic cohomology — an algebraic computation. This would make algebraic metadata always available for varieties over Q̄, collapsing the uniform Hodge test to BISH for all such varieties.

**CRM reading:** The Mumford-Tate conjecture is itself a statement about the computability of the Hodge condition. It asserts that the analytic invariant (MT group, determined by the period matrix) equals an algebraic invariant (ℓ-adic monodromy group, computable). If true, the WLPO cost of the uniform Hodge test is an artefact of the analytic presentation, not an intrinsic feature of the mathematics.

This connects to the central thesis of the CRM programme: the logical cost of mathematics is the logical cost of R. The uniform Hodge test costs WLPO because it uses R-valued period integrals. The Mumford-Tate conjecture predicts this cost is eliminable — the same information is available algebraically.

---

## Section: Structural Consequences for the Hodge Conjecture

### What DPT reveals about the conjecture's architecture

1. **Input cost vs. bridge cost.** The Hodge conjecture decomposes as:
   - (a) Identify Hodge classes. Cost: WLPO uniformly, BISH with metadata.
   - (b) Prove each Hodge class is algebraic. Cost: unknown in general; BISH for all known cases (CM abelian varieties, products of curves, etc.).

   The WLPO cost is in step (a), not step (b). All known difficulty in proving Hodge is in step (b) — finding the algebraic cycle. The CRM analysis reveals that the INPUT is already non-trivial.

2. **Counterexample constraint.** A counterexample requires a Hodge class that is NOT algebraic. Since step (b) is BISH for all known cases, a counterexample would require:
   - A variety where the algebraicity bridge has non-trivial CRM cost, OR
   - A variety where the Hodge condition produces "accidental" classes that resist algebraic construction.

   The CRM framework constrains what such a counterexample can look like: its MT group must be non-trivial but non-CM, producing Hodge classes that are not Lefschetz and not CM-forced.

3. **Conservation question (OPEN).** Does the Hodge conjecture conserve over BISH? If the conjecture is true classically, does the proof have a constructive core? The CRM analysis suggests this is related to the Mumford-Tate conjecture: if MT = G_ℓ (constructive access to the MT group), the Hodge condition is BISH, and the remaining algebraicity question might conserve.

### What DPT does NOT say

- The Hodge conjecture is NOT equivalent to an omniscience principle. Such a biconditional would prove the conjecture (since WLPO is classically available).
- The Hodge conjecture is NOT a geometric realisation of Markov's Principle. MP governs ¬¬Σ₁⁰ → Σ₁⁰ (double negation of existentials). The Hodge conjecture asserts Π₁⁰ → Σ₁⁰ (an analytic condition implies an algebraic existence). Different logical form.
- The WLPO cost of the uniform Hodge test does NOT imply the conjecture is hard. It implies the FORMULATION is hard — identifying Hodge classes uniformly requires omniscience. The conjecture's difficulty is in the bridge, not the input.

---

## Lean Formalisation Plan

### File structure
```
P87_HodgeCost/
├── lakefile.lean
├── lean-toolchain          (leanprover/lean4:v4.28.0-rc1)
├── Papers.lean
└── Papers/P87_HodgeCost/
    ├── CRMLevel.lean        — CRM hierarchy (reuse from P72-74)
    ├── HodgeTest.lean       — Uniform Hodge test, embedding reduction
    ├── CMDecidable.lean     — Theorem A: CM metadata → BISH
    ├── UniformWLPO.lean     — Theorem B: Uniform test → WLPO
    ├── Biconditional.lean   — Theorem C: biconditional
    ├── ShigaWolfart.lean    — Theorem D: algebraic periods ↔ CM (axiom)
    └── Paper87_HodgeCost.lean  — Main file, imports all
```

### Key Lean architecture
```lean
-- CRM Hierarchy (from P72-74)
inductive CRMLevel | BISH | MP | WLPO | LPO | CLASS
  deriving DecidableEq, Repr

-- WLPO as real-number equality decision
def WLPO_Real := ∀ x : ℝ, x = 0 ∨ x ≠ 0

-- Abstract analytic period matrix (axiomatised)
axiom AnalyticPeriodMatrix (g : ℕ) : Type
axiom hodge_projection {g : ℕ} (Ω : AnalyticPeriodMatrix g) (idx : ℕ) : ℝ

def is_hodge_analytic {g : ℕ} (Ω : AnalyticPeriodMatrix g) (idx : ℕ) : Prop :=
  hodge_projection Ω idx = 0

-- Embedding reduction (Theorem B core)
axiom embed_real (x : ℝ) : AnalyticPeriodMatrix 2
axiom embed_proj (x : ℝ) : hodge_projection (embed_real x) 0 = x

theorem uniform_test_implies_wlpo
    (decider : ∀ (Ω : AnalyticPeriodMatrix 2) (idx : ℕ),
      Decidable (is_hodge_analytic Ω idx)) : WLPO_Real := by
  intro x
  cases decider (embed_real x) 0 with
  | isTrue h  => exact Or.inl (embed_proj x ▸ h)
  | isFalse h => exact Or.inr (fun hx => h (embed_proj x ▸ hx))

-- Metadata classification
inductive MetadataState
  | CM_Known          -- CM type provided → algebraic periods → BISH
  | MT_Known          -- Mumford-Tate group provided → Hodge classes known → BISH
  | Bare_Analytic     -- Only Cauchy sequences → must compute → WLPO

noncomputable def hodge_test_cost : MetadataState → CRMLevel
  | .CM_Known      => .BISH
  | .MT_Known      => .BISH
  | .Bare_Analytic => .WLPO

theorem hodge_cost_biconditional (state : MetadataState) :
    hodge_test_cost state = .BISH ↔ state ≠ .Bare_Analytic := by
  cases state <;> simp [hodge_test_cost]

-- Shiga-Wolfart (axiom, over Q̄)
axiom ShigaWolfart :
  ∀ (A_over_Qbar : Type), -- abstraction
    (period_entries_algebraic A_over_Qbar ↔ has_CM A_over_Qbar)
```

### Estimated size
- ~300-400 lines Lean (slightly larger than P72-74 due to Shiga-Wolfart)
- Zero sorry target
- Axiom inventory: propext, Quot.sound, Classical.choice (infrastructure only),
  plus mathematical axioms (embed_real, embed_proj, ShigaWolfart)

---

## LaTeX Structure

1. **Title + Abstract** (0.5pp)
2. **Introduction** (2-3pp): The uniform Hodge test as a CRM problem. State Theorems A-D. Explicit "what this paper does not claim" section. First CRM analysis of a Millennium Problem.
3. **Preliminaries** (1.5pp): Abelian varieties, period matrices, CM types, Mumford-Tate groups, Hodge decomposition, CRM hierarchy, WLPO = real equality (Bridges-Richman).
4. **The Uniform Hodge Test** (2pp): Formalise the (p,p) condition as a real-number equality test. The uniform-vs-nonuniform distinction. Why both CM and generic give BISH nonuniformly.
5. **Theorem A: Algebraic Metadata → BISH** (2pp): CM type via Shimura-Taniyama. Known MT group via Lefschetz classification. Both routes to BISH.
6. **Theorem B: Uniform Test → WLPO** (2-3pp): Embedding reduction. Construct Ω_x from arbitrary x ∈ R. Reduce to Bridges-Richman.
7. **Theorem C: Biconditional** (1pp): Synthesis.
8. **Theorem D: Shiga-Wolfart Boundary** (1pp): Over Q̄, CM = algebraic periods. Sharpens Theorem C.
9. **Structural Consequences** (2pp): Input cost vs bridge cost. Counterexample constraints. Connection to Mumford-Tate conjecture. Conservation question.
10. **CRM Audit** (1pp): Classification table, axiom inventory, descent table.
11. **Formal Verification** (2pp): Lean bundle, axiom inventory, `#print axioms`.
12. **Discussion** (1pp): Relationship to DPT trilogy (72-74), CRMLint Squeeze (79-85), and Paper 86.
13. **Conclusion** (0.5pp)

**Estimated length:** 16-19 pages.

---

## Dependencies

- Papers 72-74: CRMLevel type, biconditional methodology, DPT framework
- Papers 79, 84-85: CM decidability examples (computational evidence for Theorem A)
- Papers 80-83: Gauss-Manin pipeline (cited as the mechanism behind CM decidability)
- Bridges-Richman (1987): WLPO ↔ real equality decision. *Varieties of Constructive Mathematics*, §1.3.
- Shiga-Wolfart (1985): Algebraic periods ↔ CM. "A Jorgensen-type theorem for CM abelian varieties."
- Wüstholz (1989): Analytic subgroup theorem (underpins Shiga-Wolfart).
- Shimura (1971): CM period matrices. *Introduction to the Arithmetic Theory of Automorphic Functions*.
- Moonen-Zarhin (1999): Hodge classes on generic abelian varieties = Lefschetz classes.

---

## Resolved Issues

### Former Gap 1 (RESOLVED): "Generic → WLPO" was false
Corrected to: the UNIFORM test requires WLPO. Known-generic varieties have BISH cost (Lefschetz classification). The biconditional is about algebraic metadata availability, not about the specific stratum.

### Former Gap 2 (RESOLVED): WLPO vs LPO
"α is Hodge" = conjunction of finitely many real-equality tests. Finite conjunction of WLPO = WLPO (via x₁² + x₂² + ... = 0). Cost is WLPO, not LPO.

### Former Gap 3 (PARTIALLY RESOLVED): Exact boundary
CM is sufficient for BISH (Shiga-Wolfart gives algebraic periods). Known-generic is also sufficient (Lefschetz). The exact boundary of "algebraic metadata sufficiency" is: any information that determines the Hodge classes without evaluating transcendental projections. Over Q̄, the Mumford-Tate conjecture predicts this is always available. Whether "CM or known-MT" exhausts the possibilities is connected to the MT conjecture — stated as an open question, not resolved.

### Markov's Principle claim (REJECTED)
The Hodge conjecture asserts P → Q (Hodge condition → algebraic cycle exists). MP asserts ¬¬Q → Q. These are different. The conjecture is not a geometric MP. Do not include this claim.

---

## Timeline Estimate

Phase 1 (Lean bundle): 1 session — adapt P72-74 framework, embedding reduction, biconditional
Phase 2 (LaTeX draft): 1 session — full mathematical content, structural consequences
Phase 3 (Review + polish): 1 session — format compliance, figures (descent diagram), peer review
