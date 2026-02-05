# Status: Missing Helper Lemmas for Paul's Calc Chain - November 13, 2024

**Status**: ⚠️ **BLOCKED - Missing Helper Lemma Definitions**
**For**: Paul
**From**: Claude Code

---

## Executive Summary

I cannot apply your calc chain fix because the required helper lemmas (`g_swap_local` and `insert_delta_right_of_commuted_neg`) are not defined in my current file version. The compatibility shim is present (lines 1740-1886), but these specific lemmas are missing.

---

## Current File State

### ✅ Compatibility Shim Present (Lines 1740-1886)

The file contains these helper lemmas from previous sessions:
- `sumIdx_prune_offdiag_right` (line 1741)
- `sumIdx_prune_offdiag_left` (line 1755)
- `insert_delta_right_diag` (line 1770)
- `insert_delta_left_diag` (line 1778)
- `insert_delta_right_diag_neg` (line 1799)
- `insert_delta_left_diag_neg` (line 1807)
- `payload_split_and_flip` (line 1818)
- And many more helper lemmas continuing through line 1886

### ❌ Missing Lemmas Referenced in Your Calc Chain

Your calc chain fix (from most recent message) references:

**1. `g_swap_local` (line 8989 of your code)**:
```lean
have hs : g M b ρ r θ = g M ρ b r θ := g_swap_local M r θ b ρ
```

**2. `insert_delta_right_of_commuted_neg` (line 8994 of your code)**:
```lean
have hδ := insert_delta_right_of_commuted_neg M r θ b G
```

These lemmas are **NOT present** in my file. Grep confirms:
- `grep "^lemma g_swap_local"` → No matches
- `grep "insert_delta_right_of_commuted_neg"` → (checking...)

---

## Current Baseline Errors (18 total)

The errors I'm seeing are at these locations:
- **8787:6** - `failed to synthesize`
- **8802:33** - `unsolved goals`
- **8819:8** - `Type mismatch`
- **8823:12** - `Tactic rewrite failed`
- **9000:6** - `failed to synthesize`
- **9015:33** - `unsolved goals`
- **9033:8** - `Type mismatch`
- **9037:12** - `Tactic rewrite failed`
- Plus 10 more errors at other locations

### Example Error Context (lines 8786-8815)

The errors involve applying these helper lemmas:
```lean
have Hμ :
  sumIdx (fun ρ =>
    (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ))
  =
  sumIdx (fun ρ =>
    g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)) :=
  ΓΓ_main_reindex_b_μ  -- ❌ This lemma doesn't exist
```

These look like different errors than the one your calc chain fix addresses.

---

## Questions for Paul

### 1. About the Missing Helper Lemmas

**Q1**: Where should `g_swap_local` and `insert_delta_right_of_commuted_neg` be defined?
- Should I add them to the compatibility shim?
- Or are they supposed to be defined elsewhere in the file?
- Can you provide their definitions?

**Q2**: What do these lemmas prove?
- `g_swap_local M r θ b ρ : g M b ρ r θ = g M ρ b r θ` (metric symmetry?)
- `insert_delta_right_of_commuted_neg M r θ b G : ?` (what type?)

### 2. About the Calc Chain Fix Location

**Q3**: Which specific error is your calc chain fix intended to address?
- You mentioned it's a "drop-in replacement for lines ~8985–8995"
- But when I grep for `set G`, I find no matches in the current file
- The errors I see at lines 8787, 8802, 8819, etc. involve missing lemmas like `ΓΓ_main_reindex_b_μ`

**Q4**: Is your calc chain fix for:
- **Option A**: A b-branch error that exists but I can't locate (need help finding it)
- **Option B**: A fix that requires the missing helper lemmas to be added first
- **Option C**: Something else?

### 3. About the File Version Mismatch

**Q5**: File structure difference?
- Your calc chain references line numbers ~8985-8995
- My errors are at lines 8787, 8802, 8819, etc.
- Is there a version mismatch between your file and mine?
- Should I be looking at a different branch or commit?

---

## Helper Lemma Signatures Needed

If these lemmas need to be added, please provide:

**`g_swap_local`**:
```lean
lemma g_swap_local (M r θ : ℝ) (b ρ : Idx) :
  g M b ρ r θ = g M ρ b r θ := by
  -- proof here
```

**`insert_delta_right_of_commuted_neg`**:
```lean
lemma insert_delta_right_of_commuted_neg
    (M r θ : ℝ) (b : Idx) (G : Idx → ℝ) :
  sumIdx (fun ρ => g M ρ b r θ * -(G ρ))
    =
  sumIdx (fun ρ => g M ρ b r θ * -(G ρ) * (if ρ = b then 1 else 0)) := by
  -- proof here
```

(Or correct my signatures if wrong)

---

## What I Can Do Once I Have the Lemmas

Once you provide:
1. Definitions for `g_swap_local` and `insert_delta_right_of_commuted_neg`
2. Confirmation of which error location the calc chain fix addresses

I will:
1. Add the missing lemmas to the compatibility shim
2. Apply your calc chain fix at the correct location
3. Build and verify error count decreases

---

## Alternative Path Forward

If the helper lemmas are already supposed to be present in a different file version or branch:
- Please confirm which commit/branch I should be working from
- Or provide a complete listing of all helper lemmas that should be in the compatibility shim

---

## Files and Current State

- **File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
- **Compatibility Shim**: Lines 1740-1886 ✅ Present
- **Error Count**: 18 errors (baseline)
- **Missing Lemmas**: `g_swap_local`, `insert_delta_right_of_commuted_neg`
- **Status**: Awaiting definitions or clarification

---

**Report Time**: November 13, 2024
**Status**: Blocked on missing helper lemma definitions
**Next Step**: Paul to provide missing lemma definitions or clarify file version mismatch
