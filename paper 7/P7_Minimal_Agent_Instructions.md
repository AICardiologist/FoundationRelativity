# P7_Minimal: Dependency-Free Logical Skeleton for Paper 7

## Instructions for Coding Agent

**Goal:** Build a minimal, Mathlib-free Lean 4 artifact (`P7_Minimal`) that captures the logical reduction at the heart of Paper 7. This artifact certifies that the core reasoning — "if a Banach space contains a non-reflexive closed subspace, then the space itself is non-reflexive, and therefore any non-reflexivity witness implies WLPO" — uses no classical axioms beyond what the WLPO content demands.

**This is NOT a rewrite of Paper 7.** The existing P7_Full (754 lines, Mathlib-based, zero sorry) remains the main formalization. P7_Minimal is a supplementary artifact — analogous to P2_Minimal in Paper 2 — that provides a clean constructive-purity certificate for the logical structure.

---

## Context: What Paper 7 Proves

Paper 7 establishes: Over BISH, "S₁(H) is non-reflexive with witness" ↔ WLPO.

The proof has three logical steps:

1. **ℓ¹ is non-reflexive with witness ↔ WLPO** (from Paper 2)
2. **ℓ¹ embeds isometrically as a closed subspace of S₁(H)** (mathematical fact about trace-class operators)
3. **If Y is a non-reflexive closed subspace of X, then X is non-reflexive** (Lemma B — the key technical step, proved via Hahn-Banach)

Steps 1 and 2 are imported (as axiom and interface assumption respectively). Step 3 is the original contribution. The logical skeleton of the entire argument is:

```
NonReflexive(ℓ¹) → NonReflexive(S₁(H))   [by Step 3, using Step 2]
NonReflexive(ℓ¹) ↔ WLPO                    [by Step 1]
∴ NonReflexive(S₁(H)) → WLPO              [by Step 1, backward]
∴ WLPO → NonReflexive(S₁(H))              [by Step 1 forward + Step 3]
```

## What P7_Minimal Must Capture

The abstract logical pattern — **independent of Banach spaces, Hahn-Banach, or any analysis** — is:

```
Given:
  - Types X, Y
  - A notion of "non-reflexive with witness" for each
  - Y embeds into X as a "closed subspace" (abstract assumption)
  - NonReflexive(Y) ↔ WLPO (imported from Paper 2)
  - If X is "reflexive" and Y is a "closed subspace" of X, then Y is "reflexive"
    (the Lemma B skeleton)

Conclude:
  NonReflexive(X) ↔ WLPO
```

This is a purely logical argument. It doesn't need real numbers, norms, functionals, or Hahn-Banach. It needs the *structure* of the reduction.

---

## File Structure

```
Papers/P7_PhysicalBidualGap/P7_Minimal/
├── Defs.lean           -- Abstract definitions (no Mathlib)
├── LemmaB.lean         -- Reflexivity descends to closed subspaces (abstract)
├── Reduction.lean       -- The full reduction: NonReflexive(X) ↔ WLPO
└── Main.lean           -- Top-level theorem + #print axioms
```

**Total target: 100-200 lines.**

---

## Module 1: `Defs.lean` (~40-60 lines)

Define everything abstractly at Prop level. No Mathlib imports.

```lean
/-
  P7_Minimal: Dependency-free logical skeleton for Paper 7
  (The Physical Bidual Gap)
  
  This artifact captures the logical reduction without Mathlib.
  All Banach space concepts are abstracted to Prop-level predicates.
  The mathematical content (Hahn-Banach, norm estimates) lives in P7_Full.
-/

-- No imports from Mathlib. Only Lean core.

/-- Abstract predicate: "X is reflexive" -/
class Reflexive (X : Type*) : Prop where
  is_reflexive : True  -- Placeholder; the content is in the axioms below

/-- Abstract predicate: "X is non-reflexive with witness" 
    (there exists Φ ∈ X** \ J(X)) -/
class NonReflexiveWitness (X : Type*) : Prop where
  has_witness : True

/-- Abstract predicate: "Y is a closed subspace of X" -/
class ClosedSubspaceOf (Y X : Type*) : Prop where
  is_closed_subspace : True

/-- WLPO: For any binary sequence α : ℕ → Bool, 
    either ∀ n, α n = false, or ¬(∀ n, α n = false) -/
def WLPO : Prop :=
  ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- Reflexive and NonReflexiveWitness are contradictory -/
axiom reflexive_not_witness (X : Type*) :
  Reflexive X → NonReflexiveWitness X → False
```

**IMPORTANT NOTES FOR AGENT:**
- Do NOT import any Mathlib files.
- The `Reflexive`, `NonReflexiveWitness`, and `ClosedSubspaceOf` predicates are abstract — they carry no mathematical content in this artifact. Their content is in P7_Full.
- WLPO must be defined concretely (as above), not as an axiom. This is the one definition that has real logical content.

---

## Module 2: `LemmaB.lean` (~30-50 lines)

State the abstract version of Lemma B (reflexivity descends to closed subspaces) as an axiom in P7_Minimal. The proof lives in P7_Full (where it uses Hahn-Banach).

```lean
import Papers.P7_PhysicalBidualGap.P7_Minimal.Defs

/-- Lemma B (abstract skeleton): If X is reflexive and Y is a closed 
    subspace of X, then Y is reflexive.
    
    PROOF JUSTIFICATION: In P7_Full, this is proved using two applications 
    of the Hahn-Banach theorem (geometric separation + norm-preserving 
    extension). The proof is 174 lines in ClosedSubspace.lean, zero sorry.
    Here we axiomatize it to keep the minimal artifact Mathlib-free. -/
axiom reflexive_closedSubspace_of_reflexive 
    (X Y : Type*) [ClosedSubspaceOf Y X] :
  Reflexive X → Reflexive Y

/-- Contrapositive (what we actually use): If Y is a non-reflexive 
    closed subspace of X, then X is not reflexive. -/
theorem not_reflexive_of_closedSubspace_not_reflexive
    (X Y : Type*) [ClosedSubspaceOf Y X]
    (hY : ¬ Reflexive Y) : ¬ Reflexive X :=
  fun hX => hY (reflexive_closedSubspace_of_reflexive X Y hX)
```

**KEY DESIGN DECISION:** Lemma B is axiomatized here, NOT proved. This is the correct choice because:
- The proof requires Hahn-Banach, which requires Mathlib
- P7_Full already has the sorry-free proof (174 lines in ClosedSubspace.lean)
- P7_Minimal's job is to certify the *logical reduction*, not re-prove functional analysis

The axiom is tagged with a comment pointing to the P7_Full proof.

---

## Module 3: `Reduction.lean` (~40-60 lines)

The core logical argument. This is where the actual certification happens.

```lean
import Papers.P7_PhysicalBidualGap.P7_Minimal.Defs
import Papers.P7_PhysicalBidualGap.P7_Minimal.LemmaB

/-- Interface assumption: ℓ¹ embeds as a closed subspace of S₁(H).
    Witness: the diagonal embedding ι : (λₙ) ↦ Σ λₙ |eₙ⟩⟨eₙ|.
    In P7_Full this is the HasTraceClassContainer typeclass. -/
axiom ell1_closed_subspace_of_S1 : 
  ClosedSubspaceOf ℓ¹_Type S1H_Type
  -- ℓ¹_Type and S1H_Type are opaque types standing for ℓ¹ and S₁(H)

/-- Paper 2 result: NonReflexiveWitness(ℓ¹) ↔ WLPO -/
axiom paper2_forward : NonReflexiveWitness ℓ¹_Type → WLPO
axiom paper2_reverse : WLPO → NonReflexiveWitness ℓ¹_Type

/-- NonReflexiveWitness implies ¬Reflexive -/
axiom witness_implies_not_reflexive (X : Type*) :
  NonReflexiveWitness X → ¬ Reflexive X

/-- ¬Reflexive implies NonReflexiveWitness for separable Banach spaces
    (this is the non-trivial direction; in P7_Full it uses Hahn-Banach
    to construct a witness from the failure of surjectivity) -/
axiom not_reflexive_implies_witness_S1 :
  ¬ Reflexive S1H_Type → NonReflexiveWitness S1H_Type

-- ============================================================
-- THE REDUCTION
-- ============================================================

/-- Forward: NonReflexiveWitness(S₁(H)) → WLPO
    
    Proof: A witness for S₁(H) gives ¬Reflexive(S₁(H)).
    By Lemma B contrapositive + ℓ¹ ↪ S₁(H), ¬Reflexive(S₁(H)) 
    implies ¬Reflexive(ℓ¹). Extract an ℓ¹ witness, apply Paper 2. 
    
    BUT NOTE: This chain goes through ¬Reflexive, not through 
    witness transfer. The cleaner path is direct:
    Any NonReflexiveWitness for S₁(H) can be restricted to ℓ¹ 
    (via the diagonal embedding) to give a witness for ℓ¹.
    Then apply Paper 2 forward.
    
    For the minimal artifact we take the simpler abstract route. -/
theorem S1H_witness_implies_WLPO :
    NonReflexiveWitness S1H_Type → WLPO := by
  intro h_S1
  -- S₁(H) has witness → S₁(H) not reflexive
  have h_not_ref_S1 := witness_implies_not_reflexive S1H_Type h_S1
  -- S₁(H) not reflexive → ℓ¹ not reflexive (Lemma B contrapositive)
  have h_not_ref_ell1 : ¬ Reflexive ℓ¹_Type := by
    exact not_reflexive_of_closedSubspace_not_reflexive S1H_Type ℓ¹_Type 
      (by { intro h_ref_ell1; sorry })
    -- AGENT NOTE: This step needs care. The contrapositive goes:
    -- "if ℓ¹ not reflexive then S₁(H) not reflexive"
    -- We need the other direction here. 
    -- Actually, re-examine: we have ¬Reflexive(S₁(H)), and we want 
    -- ¬Reflexive(ℓ¹). Lemma B says Reflexive(S₁(H)) → Reflexive(ℓ¹).
    -- Contrapositive: ¬Reflexive(ℓ¹) → ¬Reflexive(S₁(H)).
    -- That gives us the WRONG direction!
    -- 
    -- The correct argument is: we don't derive ¬Reflexive(ℓ¹) from 
    -- ¬Reflexive(S₁(H)). We already KNOW ℓ¹ is not reflexive from 
    -- Paper 2 (WLPO → witness for ℓ¹ is one direction, but we don't 
    -- have WLPO yet — that's what we're trying to prove).
    --
    -- CORRECTION: The forward direction is actually simpler.
    -- Paper 7's actual forward proof uses the Ishihara kernel directly:
    -- given ANY Ψ ∈ X** \ J(X), construct the WLPO decision.
    -- This is what WLPOFromWitness.lean does (196 lines in P7_Full).
    -- It doesn't go through ℓ¹ at all.
    --
    -- So the forward direction should be axiomatized as the Ishihara 
    -- kernel construction, not derived from Lemma B.
  sorry -- SEE CORRECTION BELOW

/-- Reverse: WLPO → NonReflexiveWitness(S₁(H))
    
    Proof: WLPO → NonReflexiveWitness(ℓ¹)  [Paper 2 reverse]
           → ¬Reflexive(ℓ¹)                 [witness_implies_not_reflexive]
           → ¬Reflexive(S₁(H))              [Lemma B contrapositive]
           → NonReflexiveWitness(S₁(H))     [not_reflexive_implies_witness_S1]
-/
theorem WLPO_implies_S1H_witness :
    WLPO → NonReflexiveWitness S1H_Type := by
  intro h_wlpo
  -- Step 1: WLPO → ℓ¹ has witness
  have h_ell1_witness := paper2_reverse h_wlpo
  -- Step 2: ℓ¹ witness → ℓ¹ not reflexive
  have h_ell1_not_ref := witness_implies_not_reflexive ℓ¹_Type h_ell1_witness
  -- Step 3: ℓ¹ not reflexive → S₁(H) not reflexive (Lemma B contrapositive)
  have h_S1_not_ref : ¬ Reflexive S1H_Type :=
    not_reflexive_of_closedSubspace_not_reflexive S1H_Type ℓ¹_Type h_ell1_not_ref
  -- Step 4: S₁(H) not reflexive → S₁(H) has witness
  exact not_reflexive_implies_witness_S1 h_S1_not_ref
```

### CRITICAL CORRECTION FOR THE AGENT

**Read this carefully.** The forward direction (`S1H_witness → WLPO`) does NOT use Lemma B. I made an error in the initial sketch above, and the inline comments explain why.

The correct structure of the proof in Paper 7 is:

**Forward direction:** Given ANY Ψ ∈ X** \ J(X) for ANY Banach space X, the Ishihara kernel construction produces a WLPO decision. This is a *general* result — it works for X = S₁(H), X = ℓ¹, X = anything. It's proved in `WLPOFromWitness.lean` (196 lines in P7_Full), adapted from Paper 2's Ishihara.lean.

**Reverse direction:** WLPO → witness for ℓ¹ (Paper 2) → ℓ¹ not reflexive → S₁(H) not reflexive (Lemma B contrapositive) → witness for S₁(H).

So the correct minimal artifact structure is:

```
Forward: axiomatize the Ishihara kernel
  "for any space X, NonReflexiveWitness(X) → WLPO"
  (proved in P7_Full's WLPOFromWitness.lean)

Reverse: derive via Lemma B chain
  WLPO → witness(ℓ¹) → ¬Reflexive(ℓ¹) → ¬Reflexive(S₁(H)) → witness(S₁(H))
  (Lemma B is used only here)
```

The agent should restructure accordingly. The forward direction is a single axiom (backed by the 196-line proof in P7_Full). The reverse direction is a derivation using Lemma B, Paper 2's reverse, and the witness extraction.

---

## Module 4: `Main.lean` (~20-30 lines)

```lean
import Papers.P7_PhysicalBidualGap.P7_Minimal.Reduction

/-- Main theorem (P7_Minimal): 
    NonReflexiveWitness(S₁(H)) ↔ WLPO -/
theorem P7_main : NonReflexiveWitness S1H_Type ↔ WLPO :=
  ⟨S1H_witness_implies_WLPO, WLPO_implies_S1H_witness⟩

-- Axiom audit
#print axioms P7_main
-- Expected output:
--   'P7_main' depends on axioms: 
--   [propext, Quot.sound,
--    reflexive_closedSubspace_of_reflexive,  -- Lemma B (proved in P7_Full)
--    ell1_closed_subspace_of_S1,             -- Interface (ℓ¹ ↪ S₁(H))
--    paper2_forward,                          -- Paper 2 Ishihara kernel
--    paper2_reverse,                          -- Paper 2 WLPO → gap
--    witness_implies_not_reflexive,           -- Structural
--    not_reflexive_implies_witness_S1,        -- Structural (needs Hahn-Banach in full)
--    reflexive_not_witness]                   -- Structural
--
-- NOTABLY ABSENT: Classical.choice
-- 
-- The axioms fall into three categories:
-- 1. Lean foundational: propext, Quot.sound (unavoidable)
-- 2. Paper 2 imports: paper2_forward, paper2_reverse (proved in P2_Full)
-- 3. Paper 7 content: reflexive_closedSubspace_of_reflexive (proved in P7_Full),
--    ell1_closed_subspace_of_S1 (mathematical fact, sorry-backed in Instance.lean),
--    not_reflexive_implies_witness_S1 (proved in P7_Full via Hahn-Banach)
-- 4. Structural: reflexive_not_witness, witness_implies_not_reflexive (trivial)
```

---

## Build Configuration

Add to the project's `lakefile.lean`:

```lean
lean_lib P7_Minimal where
  srcDir := "Papers/P7_PhysicalBidualGap/P7_Minimal"
  -- No Mathlib dependency
```

Or if using a separate lakefile target:

```
lake build Papers.P7_PhysicalBidualGap.P7_Minimal.Main
```

The build must succeed with **zero errors, zero sorry, zero warnings**.

---

## Verification Checklist

After building, verify:

1. **`#print axioms P7_main` shows NO `Classical.choice`.** This is the whole point.

2. **All axioms are traceable.** Every axiom in the output should map to either:
   - A Lean foundational axiom (propext, Quot.sound)
   - A result proved in P7_Full (with file and line reference)
   - A result proved in P2_Full (with reference)
   - The interface assumption (ℓ¹ ↪ S₁(H))

3. **No Mathlib imports anywhere in P7_Minimal.** Grep the directory:
   ```bash
   grep -r "import Mathlib" Papers/P7_PhysicalBidualGap/P7_Minimal/
   ```
   Must return nothing.

4. **Zero sorry.** Grep:
   ```bash
   grep -r "sorry" Papers/P7_PhysicalBidualGap/P7_Minimal/
   ```
   Must return nothing (comments containing "sorry" are OK; proof terms containing `sorry` are not).

---

## What This Artifact Certifies

P7_Minimal certifies: **The logical reduction from "S₁(H) non-reflexivity witness" to WLPO uses no classical reasoning beyond what is contained in the explicitly listed axioms (Ishihara kernel, Lemma B, embedding, Paper 2).** The classical content (if any) is isolated in those axioms, which are proved in P7_Full and P2_Full.

Combined with P2_Minimal (which certifies the Paper 2 core without classical axioms) and the P7_Full proofs (which certify the mathematical content), the three artifacts together provide a complete certificate chain:

```
P2_Minimal  →  certifies WLPO ↔ bidual gap (abstract)
P7_Minimal  →  certifies S₁(H) non-reflexivity reduces to abstract bidual gap
P7_Full     →  certifies the mathematical content (Hahn-Banach, embedding)
```

---

## Estimated Effort

This should take 1-2 hours for the coding agent. The file is ~150 lines total, no Mathlib, no complex tactic proofs. The main work is getting the types and axiom signatures right so that the reduction type-checks cleanly.

**Do NOT spend time on:**
- Proving Lemma B (that's in P7_Full)
- Defining Banach spaces, norms, or functionals (everything is abstract)  
- Importing or depending on Mathlib in any way
- Making the definitions mathematically meaningful (they're Prop-level placeholders)

**DO spend time on:**
- Getting the forward/reverse asymmetry right (forward uses Ishihara kernel directly, reverse uses Lemma B chain)
- Making `#print axioms` output clean and interpretable
- Adding documentation comments that point to the corresponding P7_Full proofs
- Ensuring zero sorry, zero errors, zero warnings
