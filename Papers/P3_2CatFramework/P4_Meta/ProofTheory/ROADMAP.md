# Paper 3B – Roadmap (Updated: 2025-08-31)

> **Prime directive:** Keep the scaffold green and reduce the Paper-3B axiom budget without destabilizing interfaces.

## ✅ Recently completed

- **PR-1**: Discharged arithmetization propagation (→ **26 total axioms** now).
- **PR-4**: Discharged WLPO/LPO *upper* bounds by aligning with `ClassicalitySteps`.
- **PR-3**: Collision-lite refactor (docs, guards, helper lemmas; **no budget change**).
- **PR-7**: CI guard hardened (per-file reports, GA annotations, override env var, macOS+Linux matrix).

## 📊 Axiom budget

- **Locked** at **26** total (17 Paper-3B + 9 base infra). Enforced by `.ci/check_axioms.sh`.

### Remaining Paper-3B axioms by category

| Category                                   | Count | Discharge path (planned)                              | PR label |
|--------------------------------------------|------:|--------------------------------------------------------|:--------:|
| Tag–semantics bridge                       | 2     | Parametric tags (defeq to semantics) or semantic proof | **PR-2** |
| Collision – cross-ladder bridge            | 2     | Falls after PR-2 via `RFN→Con` + tag equivalences      | PR-2→PR-3b |
| Collision – height comparison              | 2     | Likely **permanent** (ordinal analysis)                | —        |
| Classical lower bounds                     | 5     | **Permanent** (independence results)                   | —        |
| Hierarchy strictness (cons/refl proper)    | 2     | Likely permanent unless we internalize OA              | —        |
| Core definability/arithmetization          | 3     | "Small" internalizations; see PR-5/PR-8                | PR-5/8   |
| Limit behavior (`LClass_omega_eq_PA`)      | 1     | Likely permanent (OA)                                  | —        |

**Total Paper-3B axioms:** 17  → *near-term target*: **15** after PR-2  
**Total including base infra:** 26 → *near-term target*: **24**

## 🎯 Near-term plan (low-risk first)

### 1) **PR-2A – Parametric tags (mechanical)**  
**Goal:** Remove both tag–semantics bridge axioms by definition.
- Change signatures:  
  `ConTag : Theory → Nat → Formula`, `RfnTag : Theory → Nat → Formula`  
  and make them **defeq** to the corresponding semantic formulas.
- Update call sites: `consFormula n` ↦ `ConTag T0 n`, `reflFormula n` ↦ `RfnTag T0 n`.  
  Provide local abbreviations if helpful to minimize churn.
- Adjust `RealizesCons/RealizesRFN` to use defeq (no axioms).
- **Acceptance criteria:**  
  - Build green, **axiom budget drops 26 → 24**, `#print axioms` on impacted theorems shows no Ax. usage.  
  - `AXIOM_INDEX.md` updated; CI budget auto-parses to 24.

*Fallback:* If refactor is too noisy, switch to **PR-2B** (semantic proof) after drafting a small expansion of `HasArithmetization` (Σ₁-definability of `Prov_T`, diagonalization hooks).

### 2) **PR-5 – Core definability mini-pass** *(1–2 axioms)*  
- Targets: `Sigma1_Bot` and/or `Bot_is_FalseInN` via existing encodings.  
- Keep scope tight; avoid large meta-theory changes.
- **Acceptance criteria:** budget −1/−2 with no API breakage.

### 3) **PR-8 – CI "delta-aware" budget guard** *(no budget change)*  
- Add a mode that flags **new** Ax. lines introduced by the PR (diff-based).  
- Keep current total-budget guard as the primary gate.

## 🧪 Guardrails & checks

- CI:  
  - **Axiom guard** (budget + Ax. namespace) — macOS + Ubuntu.  
  - **No-sorries** pass with per-file reporting.  
  - `#print axioms` guards in `test/ProofTheory_Sanity.lean` for collision and classicality theorems.

## 🧭 Long-range (deeper work)

- Ordinal-analysis layer to potentially address the height-comparison pair and limit behavior.  
- Full semantic PR-2B path (if parametric tags are deferred), including Σ₁-definability of provability, numerals, diagonal lemma utilities.

## Next PR cards (ready to open)

### PR-2A — Parametric tags (budget 26 → 24) 

**Goal:** Remove the two tag–semantics bridge axioms by making tags theory-indexed and definitionally equal to their semantic formulas.

**Why now:** We already discharged WLPO/LPO by definitional alignment. Doing the same for tags is the fastest way to drop two axioms with minimal proof work.

#### Implementation Plan (surgical diffs)

**Step 1: Make tags parametric and defeq to semantics**

In `Papers/P3_2CatFramework/P4_Meta/ProofTheory/Progressions.lean`:
```lean
/-! ## Parametric tags (definitional semantics) -/

/-- Consistency tag at stage `n` for base theory `T0`. -/
abbrev ConTag (T0 : Theory) (n : Nat) : Formula :=
  ConsistencyFormula (LCons T0 n)

/-- Σ₁-Reflection tag at stage `n` for base theory `T0`. -/
abbrev RfnTag (T0 : Theory) (n : Nat) : Formula :=
  RFN_Sigma1_Formula (LReflect T0 n)

/-- Notation for readability. -/
scoped notation "ConTag[" T0 "] " n => ConTag T0 n
scoped notation "RfnTag[" T0 "] " n => RfnTag T0 n
```

**Step 2: Replace global, non-parametric usages**
- Search/replace `ConTag n` → `ConTag[T0] n` and `RfnTag n` → `RfnTag[T0] n`
- Redefine helper aliases:
  ```lean
  abbrev consFormula (T0 : Theory) (n : Nat) := ConTag[T0] n
  abbrev reflFormula (T0 : Theory) (n : Nat) := RfnTag[T0] n
  ```

**Step 3: Delete bridge axioms and simplify instances**
- Remove the two "tag means semantics" axioms from Progressions.lean
- In RealizesCons/RealizesRFN, refinement proofs become:
  ```lean
  have h' := h
  simpa [ConTag, ConsistencyFormula] using h'
  ```

**Step 4: Update collision stubs to parametric tags**
In `Collisions.lean`:
```lean
axiom collision_tag (T0 : Theory) (n : Nat) :
  (LReflect T0 (n+1)).Provable (RfnTag[T0] n) →
  (LReflect T0 (n+1)).Provable (ConTag[T0] n)
```

**Step 5: Tests & CI**
- Update `test/ProofTheory_Sanity.lean` for new parametric names
- Run `.ci/check_axioms.sh` → expect 24
- Update AXIOM_INDEX.md banner to "BUDGET LOCKED AT 24"

**Definition of Done:**
- Build green, 0 sorries
- `./.ci/check_axioms.sh` reports 24 total
- No remaining references to non-parametric tags
- AXIOM_INDEX.md + P3B_STATUS.md updated

**Files to modify:**
- `P4_Meta/ProofTheory/Progressions.lean` — tag definitions and Realizes*
- `P4_Meta/ProofTheory/Collisions.lean` — signatures mentioning tags
- `P4_Meta/ProofTheory/Core.lean` — ExtendIter_arithmetization instances
- `test/ProofTheory_Sanity.lean` — #print axioms confirmations
- `documentation/AXIOM_INDEX.md` — update banner to 24

### PR-5 — Core definability mini-pack (budget 24 → 22-23)

**Goal:** Replace 1–2 "Core definability" axioms with straightforward lemmas.

**Candidates (pick easiest first):**
1. **Sigma1_Bot** — Define Bot as Σ₁ (e.g., ∃x. x ≠ x or standard Δ₀ contradiction)
   - Prove `IsSigma1 Bot` from existing Σ₁ constructors
2. **Bot_is_FalseInN** (stretch) — Show ℕ ⊨ Bot is false by evaluation

**Definition of Done:**
- Axiom count drops by 1–2
- `#print axioms` for new lemmas is empty or restricted to base theory

### PR-8 — CI polish (no budget change)

**Goal:** Keep the guard future-proof and fast.

**Enhancements:**
- Add Lake cache step to workflow for faster rebuilds
- Add "changed-files only" mode (env var) for PR scans
- Make axiom guard step required in branch protections

**Optional extras:**
- Delta-aware guard: flag new `^axiom` lines in PRs
- Performance: limit scans to touched `*.lean` under ProofTheory/

## 🔎 Risks & Mitigations

### API churn from parametric tags
**Mitigation:** Add scoped notation `ConTag[T] n`, `RfnTag[T] n` and provide local `abbrev consFormula/reflFormula` wrappers. Touches are mechanical and confined to Progressions.lean, Collisions.lean, and nearby instances/tests.

### Typeclass resolution for arithmetization at each stage
**Mitigation:** Keep existing pattern: `letI : HasArithmetization (LCons T0 n) := LCons_arithmetization n` (same for LReflect). This is already in place and documented.

## 📊 Status Recap & Targets

- **Now:** 26 total axioms = 17 (Paper-3B) + 9 (base infra)
- **Next milestone:** 24 (PR-2A parametric tags)
- **Near-term stretch:** 22-23 (PR-5 definability mini-pack)
- **Likely permanent:** ~10 axioms (collision height-comparison, classical lower bounds, ω-limit behavior)