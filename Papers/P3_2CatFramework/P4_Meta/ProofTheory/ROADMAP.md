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

### PR-2A — Parametric tags (defeq → semantics)
- **Edits:** Progressions/Heights/Collisions/test modules where ConTag/RfnTag occur.
- **API:**
  - `def ConTag (T : Theory) (n : Nat) : Formula := ConsistencyFormula (LCons T n)`
  - `def RfnTag (T : Theory) (n : Nat) : Formula := RFN_Sigma1_Formula (LReflect T n)`
  - Local abbrev for backward-compatible notation if needed.
- **Tests:**
  - `#print axioms` for RealizesCons/RealizesRFN → no Ax. deps.
  - Derived collision semantic step follows from bridge removal.
- **Docs/CI:**
  - AXIOM_INDEX.md → 26 → 24
  - CI budget auto-updates, guard passes.

### PR-5 — Core definability mini-pass
- **Target:** Sigma1_Bot, Bot_is_FalseInN (whichever is feasible first).
- **Approach:** Use existing encoding hooks; keep proofs local to Core.lean.
- **Tests:** `#print axioms` show no new Ax.; CI budget decrements accordingly.

### PR-8 — CI delta guard
- **Idea:** In CI, compute `git diff --unified=0` on changed files and count newly added `^axiom` lines.
- **Fail if:** total budget OK but new Ax. lines > 0 (unless label `allow-axiom-add` is present).
- **Keeps:** contributors honest while allowing explicit exceptions.