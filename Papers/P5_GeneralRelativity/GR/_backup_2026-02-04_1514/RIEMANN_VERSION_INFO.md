# Riemann.lean Version Information

**Date:** October 5, 2025
**For:** Junior Professor

## File Snapshot: Riemann_commit_851c437_current.lean

This is the **current working version** of Riemann.lean as of commit 851c437.

### File Stats
- **Lines:** 5364
- **Sorrys:** 7 (Riemann pair exchange symmetries)
- **Errors:** 17 (3 core + 14 cascading)
- **Commit:** 851c437 "Add type annotations to stabilize typeclass inference"

### Key Locations in THIS version

| Feature | Line Number |
|---------|-------------|
| `differentiableAt_Γ_t_tr_r` | 394 |
| `differentiableAt_Γ_r_tt_r` | 421 |
| Error A1 location | 427 |
| `R_trtr_eq` (Error A2) | 1196 |
| `R_rθrθ_eq` (Error A3) | 1222 |
| `nabla_g_eq_dCoord_sub_C` | 1772 |
| First sorry (Riemann_pair_exchange) | 5035 |

### Changes Applied From Your Patch

✅ **Successfully applied:**
1. Line 400: `exact differentiableAt_const (M : ℝ)` 
2. Line 427: `exact differentiableAt_const (M : ℝ)`
3. Line 1775: `simp only [sumIdx_add]` (was `simp [sumIdx_add]`)

❌ **Could not apply (failed):**
4. `ring_nf` before `ring` in R_trtr_eq and R_rθrθ_eq
   - Error: "ring_nf made no progress on goal"
   - Reverted to original `field_simp` + `ring`

### The 3 Core Errors (A1, A2, A3)

**Error A1 - Line 427:**
```
error: typeclass instance problem is stuck, it is often due to metavariables
  NormedSpace ?m.49 ℝ
```
Location: `differentiableAt_Γ_r_tt_r`, line `exact differentiableAt_const (M : ℝ)`
Status: Type annotation applied but error persists

**Error A2 - Line 1197:**
```
error: unsolved goals
⊢ Riemann M r θ Idx.t Idx.r Idx.t Idx.r = (2 * M) / r^3
```
Location: `R_trtr_eq` lemma
Status: Proof tactics don't close the goal

**Error A3 - Line 1223:**
```
error: unsolved goals
⊢ Riemann M r θ Idx.r Idx.θ Idx.r Idx.θ = M / (r * f M r)
```
Location: `R_rθrθ_eq` lemma
Status: Proof tactics don't close the goal

### Version Comparison

Your patch referenced:
- Line 314 → Now at 394 (+80 lines)
- Line 347 → Now at 421 (+74 lines)
- Line 1008 → Now at 1772 (+764 lines)
- Line 1127 → Now at 1196 (+69 lines)
- Line 1159 → Now at 1222 (+63 lines)

Likely cause: File has grown significantly since your source version.

### How to Use This File

If you want to generate a new patch based on this version:

1. Work from `Riemann_commit_851c437_current.lean`
2. Use the line numbers from the table above
3. Test your fixes on this exact version
4. The file has all recent work including Patch M (diagonal Ricci cases)

### Current Git State

```
Commit: 851c437
Branch: feat/p0.2-invariants
Status: 3 changes applied from your patch (partial success)
```

---

**Note:** This is the active working version. Any patches should target these line numbers, not the older version you may have been working from.

Generated: October 5, 2025
