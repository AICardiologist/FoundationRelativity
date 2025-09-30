# Strategic Tactical Plan for Alternation Theorem Completion

**Date:** September 29, 2025
**Re:** Resolving Phase 3 bottlenecks (timeouts and structural mismatch)
**To:** Alternation Theorem Implementation Team
**From:** Senior Professor

## Executive Summary

Your analysis is precise. The mathematical infrastructure—including the diagonal collapse and folding lemmas—is complete and sound. The persistent issues in Phase 3 stem from two distinct tactical bottlenecks:

1. **Structural Mismatch (Memo 5):** The goal state does not syntactically match the patterns of your helper lemmas, causing simp to report "no progress."

2. **Goal Complexity (Memo 4, Unnumbered Memo):** The goal state is too complex for simp to navigate efficiently, leading to deterministic timeouts.

We must address these sequentially: first ensure the lemmas can fire (resolve the mismatch), and then manage the resources required to apply them (resolve the complexity).

## 1. Diagnostics: The Crucial First Step

We must inspect the exact shape of the goal after Phase 2 to understand the structural mismatch. Standard InfoView settings might hide crucial details.

**Action Plan:**

1. **Enable Detailed Pretty-Printing:** Before the theorem definition, set these options:

```lean
set_option pp.all true       -- Show all implicit arguments and details
set_option pp.explicit true  -- Show metavariables explicitly
set_option pp.max_depth 1000 -- Prevent truncation of deep structures
```

2. **Inspect the Goal:** Place your cursor immediately after Phase 2 finishes. Analyze the Tactic State in the InfoView. Pay meticulous attention to the parenthesization and the order of the sumIdx terms.

## 2. Resolving "No Progress" (Structural Mismatch)

The "no progress" error confirms that the goal does not match the patterns of lemmas like `sumIdx_fold_add_pairs_sub`. This is typically due to variations in Associativity and Commutativity (AC). We must normalize the goal into a canonical form.

### Strategy A: Normalize with `abel` (Highly Recommended)

The `abel` tactic is specifically designed to normalize additive structures. It is often far more effective than simp with AC lemmas.

```lean
-- Phase 3a: Normalize additive structure
abel

-- Phase 3b: Apply folding and collapse (if abel succeeded, these should now fire)
simp only [sumIdx_right_diag, sumIdx_left_diag,
           add_sub_add_sub_assoc', sub_sub_eq_sub_add_sub',
           sumIdx_fold_add_pairs_sub]
```

### Strategy B: Control Phase 2 Output

A proactive approach is to prevent Phase 2 from creating an unfavorable structure. Aggressive normalization in Phase 2 (using `add_comm`, `add_assoc`) can rearrange terms unpredictably.

```lean
-- In Phase 2:
-- Remove generic normalization lemmas and rely only on specific transformations.
simp only [dCoord_g_via_compat, Christoffel_symm]
-- AVOID including: add_comm, add_left_comm, add_assoc
```

### Strategy C: Manual Rearrangement

If the above fails, use the insights from Step 1 to manually rewrite the goal to match the expected pattern.

```lean
-- Example: If the goal is (A - C) + (B - D) and you need (A + B) - (C + D)
try { rw [add_comm (sumIdx A - sumIdx C)] }
try { rw [← add_sub_assoc] }
-- Now the folding lemma will fire:
rw [sumIdx_fold_add_pairs_sub]
```

## 3. Resolving "Timeouts" (Complexity Management)

If you resolve the "no progress" issue but the proof begins timing out again, the complexity is exceeding Lean's resources. We must now manage that complexity.

### Primary Recommendation: Intermediate Lemma Extraction (Isolation Strategy)

This is the most robust solution (your Question 3). By isolating the algebraic identity, you can allocate specific resources locally without affecting the main project build.

**Action Plan:**

1. **Extract the Identity:** Define a standalone lemma proving the equality required by Phase 3.

2. **Isolate Resources and Prove:**

```lean
lemma alternation_phase3_identity (M r θ : ℝ) (μ ν ρ σ : Idx) :
  [Exact LHS pattern after Phase 2] = [Canonical RHS] := by
  -- Increase resources significantly just for this lemma
  set_option maxHeartbeats 2000000 -- e.g., 10x default, or use 0 for unlimited

  -- Apply the full tactical sequence (including normalization if needed)
  abel
  simp only [sumIdx_right_diag, sumIdx_left_diag]
  simp only [add_sub_add_sub_assoc', sub_sub_eq_sub_add_sub',
             sumIdx_fold_add_pairs_sub]
  ring

-- In the main alternation theorem proof, after Phase 2:
rw [alternation_phase3_identity]
```

### Secondary Recommendation: Surgical Rewriting (conv Mode)

If you prefer an inline proof, use `conv` mode (your Question 1) to apply transformations precisely, avoiding the broad search space of simp.

```lean
-- Phase 3 (Surgical Approach):

-- Step 1: Surgical Diagonal Collapse
conv_lhs =>
  -- Navigate to the specific subterms based on your inspection in Step 1.
  -- Example (adjust navigation paths as needed):
  enter [1, 2, 1] -- Navigate to a specific subterm
  rw [sumIdx_right_diag]
  -- Repeat for other terms...

-- Step 2: Controlled Folding
abel -- Normalize the structure
rw [sumIdx_fold_add_pairs_sub] -- Apply folding manually

-- Step 3: Final Normalization Inside the Binder
conv_lhs =>
  enter [i] -- Descend into the 'sumIdx (fun i => ...)' binder
  -- Now we are dealing with scalar arithmetic.
  try { ring }
```

## 4. Answers to Specific Questions

1. **Conv Mode Approach?** **Yes.** As detailed in Section 3, conv mode is essential for surgical rewriting when simp times out. It allows targeted application of lemmas like `sumIdx_right_diag`.

2. **Term Mode Construction?** **I strongly advise against this.** For complex algebraic identities, term mode proofs are brittle, unreadable, and extremely difficult to maintain.

3. **Intermediate Lemma Extraction?** **Yes.** This is the most robust strategy for isolating complexity and managing resources (Section 3, Primary Recommendation).

4. **Phase 2 Decomposition?** **Yes.** As discussed in Section 2 (Strategy B), controlling the normalization in Phase 2 (by removing AC lemmas from simp) is crucial for producing a predictable goal state for Phase 3.

## Conclusion

By systematically applying these strategies—**Inspect, Normalize, and then Isolate or Surgically Rewrite**—you will be able to overcome these tactical bottlenecks and complete the proof.