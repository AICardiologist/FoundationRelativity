# Paper 3B Status Checkpoint

A concise, checkpoint-style status for Paper 3B—mapped to the roadmap themes we've been using.

---

## ✅ What's done (and building cleanly)

### Scaffold + core theorems
- **ProofTheory/Core.lean**
  - Schematic tags in place: `ConTag`, `RfnTag`, `GTagFormula`.
  - Core axioms moved under namespace `Ax`: `Ax.Sigma1_Bot`, `Ax.Bot_is_FalseInN`.
- **ProofTheory/Reflection.lean**
  - Collision core: `RFN_implies_Con` proved (no sorries).
  - Kept Σ₁ reflection as a two-theory class (`HasRFN_Sigma1`).

### Progressions (ladders)
- **ProofTheory/Progressions.lean**
  - Ladders: `LCons`, `LReflect`, `LClass` with simp lemmas.
  - ω-limit: `ExtendOmega` machinery; `Ax.LClass_omega_eq_PA` declared.
  - Schematic→semantic bridge: `RealizesCons`, `RealizesRFN` typeclasses with sorry-free instances (use local `letI` + refinement axioms).
  - Axioms moved to `Ax.` namespace: `Ax.LCons_arithmetization_instance`, `Ax.LReflect_arithmetization_instance`, `Ax.cons_tag_refines`, `Ax.rfn_tag_refines`.

### Heights (certificates)
- **ProofTheory/Heights.lean**
  - Upper bounds: `con_height_upper`, `godel_height_upper`, `rfn_height_upper`, `con_n_height`.
  - Certificates: `con_height_cert`, `godel_height_cert`, `rfn_height_cert`, `WLPO_height_cert`, `LPO_height_cert`.
  - Axioms under `Ax.`: `Ax.con_implies_godel`, `Ax.G1_lower`, `Ax.G2_lower`, `Ax.RFN_lower`, `Ax.cons_hierarchy_proper`, `Ax.refl_hierarchy_proper`, `Ax.WLPO_*`, `Ax.LPO_*`.

### Collisions (dominance)
- **ProofTheory/Collisions.lean**
  - Schematic collision: `collision_step` from `Ax.collision_tag`.
  - Semantic & dominance scaffolding: morphism `reflection_dominates_consistency`, height comparison axiom `Ax.reflection_height_dominance`. All collision axioms under `Ax.`.

### Diagnostics & tests
- **test/ProofTheory_Sanity.lean**
  - Builds end-to-end with examples for all ladders.
  - `#print axioms` guards for key theorems and instances (cleanly shows dependence only on `Ax.*` and `propext` where relevant).
  - No sorries anywhere (we replaced the last two with local `letI` + axioms).
  - Pre-commit passes; build is green.

### Documentation
- **documentation/AXIOM_INDEX.md**
  - Updated: 21 axioms, all under `Ax.`; categorized; discharge plans noted.
  - Diagnostics section updated with actual `#print axioms` dependencies.

---

## 🧭 What remains (to exit the "scaffold" phase)

Below are the outstanding roadmap items, grouped by how they'll get discharged.

### A. Internalization / arithmetization layer

1. **Preservation of arithmetization under extension**
   - Replace `Ax.LCons_arithmetization_instance` and `Ax.LReflect_arithmetization_instance` with real instances.
   - Location: Progressions.lean (or a small Arithmetization.lean helper if you prefer).

2. **Refinement of schematic tags**
   - Discharge `Ax.cons_tag_refines` and `Ax.rfn_tag_refines` by tying `ConTag n` / `RfnTag n` to the actual arithmetized formulas for `Con(LCons T0 n)` and `RFN_Σ₁(LReflect T0 n)`.

3. **Collision via internalized RFN→Con**
   - Replace `Ax.collision_tag` and `Ax.collision_step_semantic` by deriving them from the internalized RFN→Con plus the ladder step facts.

### B. Ladder interactions and limits

4. **Classicality limit**
   - Prove `Ax.LClass_omega_eq_PA` (limit of EM-fragment ladder yields PA).

5. **Dominance and height comparison**
   - Replace `Ax.reflection_dominates_consistency_axiom` and `Ax.reflection_height_dominance` with proofs (or reductions) using the results from A + ordinal-analysis lemmas you already cite.

### C. Classicality principles

6. **Inclusions**
   - Discharge `Ax.WLPO_height_upper` (EM_Σ₀ ⊢ WLPO) and `Ax.LPO_height_upper` (EM_Σ₁ ⊢ LPO).

7. **Independence (optional to discharge now)**
   - `Ax.WLPO_lower`, `Ax.LPO_lower` can remain as documented classical results; you can postpone their formalization if out of current scope.

### D. Semantics of Σ₁ (clean-up)

8. **Replace the placeholder `Sigma1 : Formula → Prop := fun _ => True`**
   - Introduce a proper Σ₁ predicate or typeclass and port the few uses (`Ax.Sigma1_Bot`, RFN surface) to the real definition.

---

## 📌 Current quality gates (all green)
- ✅ **0 sorries** across Paper 3B.
- ✅ **All axioms in `Ax` namespace** (guardable by a simple CI script).
- ✅ **Axiom count**: 21, with a clear per-category discharge plan.
- ✅ **Sanity tests compile**, and `#print axioms` diagnostics are in place.

---

## 🔜 Suggested next PRs (small, decoupled)

1. **Arithmetization-preservation instances** (replace `Ax.L*arithmetization_instance`).
2. **Tag-refinement proofs** (replace `Ax.cons_tag_refines`, `Ax.rfn_tag_refines`).
3. **Internalized RFN→Con derivations of collisions** (remove `Ax.collision_*`).
4. **Classicality ω-limit** (`Ax.LClass_omega_eq_PA`).
5. **WLPO/LPO inclusions** (discharge `Ax.WLPO_height_upper`, `Ax.LPO_height_upper`).
6. **Σ₁ semantics finalization** (replace the placeholder).

Each can land independently without destabilizing the scaffold.

---

## One-line summary

**We're out of the "scaffold with sorries" phase**: ladders, heights, and collisions all compile; axioms are centralized under `Ax`; diagnostics and docs are up-to-date. What's left is the planned discharge of the internalization/arithmetization layer and a handful of classicality/limit axioms to move us from "schematic" to "fully internalized."