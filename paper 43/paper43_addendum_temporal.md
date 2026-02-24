# Paper 43 — Addendum: The Structural Characterisation of MP

## Instructions for Lean Investigation and Write-Up

---

## A. What to Investigate

The constructive hierarchy contains two kinds of principles:

- **Decision principles** (LPO, WLPO, LLPO): given a binary sequence α, produce a disjunction (A ∨ B) with no prior information. These are *oracular* — they survey the entire sequence and return a verdict.

- **Extraction principles** (MP): given a binary sequence α *and a hint* (¬∀n, α(n) = false), produce a witness (∃n, α(n) = true). This is *sequential* — the only known general method is to search 0, 1, 2, ... until the witness is found.

The hypothesis: MP is the unique principle in the standard hierarchy whose computational content is irreducibly sequential. LPO, WLPO, and LLPO can all be implemented by an oracle that inspects the whole sequence at once. MP cannot — it requires stepping through ℕ in order, with no bound on when the search terminates.

The key decomposition (Ishihara): WLPO + MP = LPO. This means: decision (WLPO: can you decide ¬¬∀ vs ¬∀?) plus extraction (MP: given ¬∀, find the witness) equals full omniscience (LPO: decide ∀ vs ∃ outright). The gap between MP and LPO is exactly the decision component.

---

## B. Lean Formalisations to Build

### B.1 Definitions (in Defs/Principles.lean or extend existing file)

```lean
/-- Limited Principle of Omniscience. --/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∃ n, α n = true) ∨ (∀ n, α n = false)

/-- Weak Limited Principle of Omniscience. --/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (¬¬(∀ n, α n = false)) ∨ (¬(∀ n, α n = false))
-- Note: WLPO is sometimes stated as:
-- ∀ α, (∀ n, α n = false) ∨ ¬(∀ n, α n = false)
-- Check which formulation Ishihara uses. The ¬¬ version is weaker
-- and may not be the standard one. The standard WLPO is:
-- ∀ α, (∀ n, α n = false) ∨ ¬(∀ n, α n = false)
-- which is LEM restricted to Π₁⁰ statements.
-- IMPORTANT: Verify against Bridges-Richman and Ishihara before coding.

/-- Standard WLPO (LEM for Π₁⁰ statements). --/
def WLPO_std : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- Markov's Principle. --/
def MP : Prop :=
  ∀ (α : ℕ → Bool), ¬(∀ n, α n = false) → ∃ n, α n = true

/-- Lesser Limited Principle of Omniscience. --/
def LLPO : Prop :=
  ∀ (α β : ℕ → Bool),
    ¬((∃ n, α n = true) ∧ (∃ n, β n = true)) →
    (∀ n, α n = false) ∨ (∀ n, β n = false)
```

### B.2 The Ishihara Decomposition: WLPO + MP = LPO

This is the central formalisation. It makes precise the claim that LPO decomposes into a decision component (WLPO) and an extraction component (MP).

```lean
/-- Forward: LPO implies WLPO. --/
theorem lpo_implies_wlpo : LPO → WLPO_std := by
  intro lpo α
  rcases lpo α with ⟨n, hn⟩ | hall
  · right
    intro hall
    exact absurd (hall n) (by simp [hn])
  · left
    exact hall

/-- Forward: LPO implies MP. (Already in main proof document.) --/
theorem lpo_implies_mp : LPO → MP := by
  intro lpo α h_not_all_false
  rcases lpo α with ⟨n, hn⟩ | hall
  · exact ⟨n, hn⟩
  · exact absurd hall h_not_all_false

/-- Reverse: WLPO + MP implies LPO. This is the key theorem. --/
theorem wlpo_mp_implies_lpo : WLPO_std → MP → LPO := by
  intro wlpo mp α
  rcases wlpo α with hall | h_not_all
  · right
    exact hall
  · left
    exact mp α h_not_all

/-- The decomposition: LPO ↔ WLPO + MP. --/
theorem lpo_iff_wlpo_and_mp : LPO ↔ (WLPO_std ∧ MP) := by
  constructor
  · intro lpo
    exact ⟨lpo_implies_wlpo lpo, lpo_implies_mp lpo⟩
  · intro ⟨wlpo, mp⟩
    exact wlpo_mp_implies_lpo wlpo mp
```

### B.3 MP is Strictly Weaker than LPO

The forward direction (LPO → MP) is proved above. The converse fails. This is a model-theoretic separation — in the computable model (Kleene's function realisability), MP holds but LPO fails. This cannot be proved in Lean (it's about models, not theorems within a model). State it as a comment:

```lean
/-- MP does not imply LPO.
    Separation: In Kleene's function realisability model,
    Church's Thesis holds, which implies MP (every total computable
    function that isn't all-zero has a computable witness via
    unbounded search). But LPO fails (no computable procedure
    decides whether an arbitrary computable sequence is all-zero).
    Reference: Bridges-Richman 1987, §3.4. --/
-- This is a model-theoretic fact, not formalisable in Lean.
```

### B.4 MP is Strictly Weaker than WLPO + MP (i.e., MP does not imply WLPO)

```lean
/-- MP does not imply WLPO.
    Separation: There exist models where MP holds but WLPO fails.
    In the effective topos with Church's Thesis and
    extended Church's Thesis (ECT), MP holds but WLPO fails.
    Reference: Ishihara 2006; Bridges-Vita 2006.
    VERIFY THIS CLAIM against the actual literature before citing. --/
-- Model-theoretic, not formalisable in Lean.
```

### B.5 Decision vs Extraction — Structural Characterisation

This is the conceptual formalisation. State what each principle "does":

```lean
/-- LPO is a decision principle: it produces A ∨ B with no prior information. --/
-- LPO : ∀ α, (∃ n, α n = true) ∨ (∀ n, α n = false)
-- Input: α only. Output: a disjunction.

/-- WLPO is a decision principle: it decides ∀ vs ¬∀ with no prior information. --/
-- WLPO : ∀ α, (∀ n, α n = false) ∨ ¬(∀ n, α n = false)
-- Input: α only. Output: a disjunction.

/-- MP is an extraction principle: given a refutation, it finds a witness. --/
-- MP : ∀ α, ¬(∀ n, α n = false) → ∃ n, α n = true
-- Input: α AND a proof of ¬∀. Output: a witness.

/-- The structural difference: MP requires a hint (the ¬∀ hypothesis).
    LPO and WLPO require no hint.
    The Ishihara decomposition shows that the hint is exactly
    what WLPO provides: WLPO decides whether ¬∀ holds,
    and MP extracts the witness once ¬∀ is known.
    Together they reconstruct LPO. --/
```

### B.6 The Temporal Observation (Comment Only)

```lean
/-- PHILOSOPHICAL OBSERVATION (not a theorem):
    
    MP's computational content, in models where Church's Thesis holds,
    is unbounded search: check α(0), α(1), α(2), ... until a witness
    is found. The ¬∀ hypothesis guarantees termination but provides
    no bound on the number of steps.
    
    This is the only principle in the hierarchy whose computational
    realiser is intrinsically sequential and unbounded:
    - BISH computations terminate in bounded (computable) time.
    - LPO's realiser (if it existed computably) would be an oracle
      that inspects the whole sequence simultaneously.
    - WLPO's realiser (if it existed computably) would similarly
      be an oracle for ∀ statements.
    - LLPO's realiser involves choosing between two sequences,
      again oracle-like.
    - MP's realiser is: run the search. Wait. It will stop.
    
    The sequential, unbounded, guaranteed-to-terminate character
    of MP's computational content is structurally analogous to
    temporal processes in physics: processes that definitely end
    but whose endpoint cannot be computed in advance.
    
    Whether this analogy is deep or superficial is a philosophical
    question that formal verification cannot answer. --/
```

---

## C. What to Write About

### C.1 Add to Paper 43 essay: new subsection in §7

**Title suggestion:** "Decision, Extraction, and the Logical Skeleton of Time"

**Content (approximately 400–600 words):**

The constructive hierarchy contains two structural types of principle. Decision principles (LPO, WLPO, LLPO) produce a disjunction from no prior information. They are oracular — in any computational model, their realiser would need to inspect an entire infinite sequence and return a verdict. Extraction principles (MP) produce a witness from a hint. The hint is a refutation (¬∀), and the witness is found by sequential search through ℕ.

The Ishihara decomposition (WLPO + MP = LPO) makes this precise. LPO decomposes into a decision component and an extraction component. The decision component (WLPO) determines whether a universal statement holds. The extraction component (MP) finds the counterexample once you know one exists. Neither component alone suffices for LPO.

The extraction component has a distinctive computational character. In any model where functions are computable (Church's Thesis), MP is realised by unbounded search: enumerate the natural numbers in order, test each one, stop when the predicate is satisfied. The ¬∀ hypothesis guarantees the search terminates. No bound on when.

This is the only principle in the standard hierarchy with this character. BISH computations have computable bounds. Decision principles are oracular (non-sequential). MP alone requires stepping through an ordered structure, one element at a time, with guaranteed but unknown termination.

This structural property is formally analogous to temporal processes in physics: radioactive decay terminates but has no computable deadline. Poincaré recurrence is guaranteed but unbounded. Vacuum tunnelling is certain but unscheduled. In each case, the physical process has the same logical shape as MP's computational realiser: sequential, ordered, guaranteed, unbounded.

The programme cannot determine whether this analogy is deep or superficial. It can state it precisely: MP is the unique principle in the hierarchy whose computational content matches the structure of physical processes with unbounded termination guarantees. And LPO's implication of MP means that any physical system with spatial infinity (thermodynamic limits, LPO) automatically possesses the logical resources for temporal open-endedness (unbounded but guaranteed termination, MP).

[End with observation, not claim. Flag as interpretive, not result.]

### C.2 What NOT to write

Do not claim:
- "MP is time." (Too strong. MP is a logical principle. Time is physical.)
- "The programme proves that time emerges from space." (The programme proves LPO ⟹ MP. The spatial/temporal gloss is interpretation.)
- "Sequential search is equivalent to temporal experience." (Equivocation between mathematical sequence and physical time.)

Do claim:
- MP is structurally unique in the hierarchy (extraction, not decision).
- Its computational content is sequential and unbounded.
- This matches the logical shape of physical processes with unbounded termination.
- LPO ⟹ MP means spatial commitments subsidise temporal ones.
- Whether this correspondence is deep remains open.

---

## D. Lean Module Additions

Add to the Paper 43 module structure:

```
Paper43_Actualisation/
├── ...existing modules...
├── Decomposition/
│   ├── WLPO_MP_LPO.lean        -- Ishihara decomposition (§B.2)
│   ├── StrictSeparations.lean   -- Comments on model-theoretic separations (§B.3, B.4)
│   └── StructuralTypes.lean     -- Decision vs extraction characterisation (§B.5, B.6)
```

**Additional lines: ~80–100.**

**New total estimate: ~630–650 lines.**

---

## E. References to Add

- Ishihara, H. (2006). "Reverse mathematics in Bishop's constructive mathematics." *Philosophia Scientiae*, Cahier spécial 6, 43–59. [WLPO + MP = LPO]
- Bridges, D., Richman, F. (1987). *Varieties of Constructive Mathematics*. Cambridge. [Model separations: MP does not imply LPO]
- Troelstra, A.S., van Dalen, D. (1988). *Constructivism in Mathematics*, Vol. 1. North-Holland. [Realisability models, Church's Thesis + MP]
- Kohlenbach, U. (2008). *Applied Proof Theory*. Springer. [Proof mining, computational content of classical principles]

**VERIFY** the Ishihara reference. The decomposition WLPO + MP = LPO is widely attributed to Ishihara but the specific paper and year should be confirmed against the actual publication. The 2006 *Philosophia Scientiae* reference is commonly cited but may not be the original source.

---

## F. Summary

The Lean investigation adds ~80–100 lines formalising the Ishihara decomposition (WLPO + MP = LPO) and characterising the structural difference between decision principles and extraction principles. The essay adds ~400–600 words observing that MP's computational content (sequential unbounded search) matches the logical shape of physical processes with unbounded termination, and that LPO ⟹ MP means spatial logical commitments automatically subsidise temporal ones. Both additions are flagged as observations, not results. The formal content is the decomposition theorem. The interpretation is the essay's contribution.
