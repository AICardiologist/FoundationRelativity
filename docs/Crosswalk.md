# Paper ↔ Lean Crosswalk: WLPO ↔ BidualGap

**Purpose**: Map paper labels to Lean constants for seamless reviewer navigation  
**Paper**: Paper 2 - WLPO ↔ BidualGap Equivalence  
**Status**: Forward direction (Gap → WLPO) axiom-clean ✅  

## Blueprint File Structure

| Paper Section | Lean File | Status |
|---------------|-----------|--------|
| **§2: Finite Cesàro Theory** | `Papers/P2_BidualGap/Basics/FiniteCesaro.lean` | 🔧 Extracted |
| **§3: Boolean Sublattice** | `Papers/P2_BidualGap/Gap/BooleanSubLattice.lean` | 🔧 Extracted |
| **§3: Finite Embedding** | `Papers/P2_BidualGap/Gap/FiniteEmbedding.lean` | 🔧 Extracted |
| **Core Implementation** | `Papers/P2_BidualGap/Constructive/Ishihara.lean` | ✅ **Axiom-Clean** |
| **API Stability** | `Papers/P2_BidualGap/Basics/ApiShims.lean` | 🔧 Extracted |

---

## Forward Direction: Gap → WLPO (Axiom-Clean) ✅

### Core Theorems

| Paper Label | Lean Constant | File | Status |
|-------------|---------------|------|--------|
| **Main Theorem** | `Papers.P2.Constructive.WLPO_of_gap` | `Ishihara.lean` | ✅ **0 sorries** |
| **Helper Lemma A** | `Papers.P2.Constructive.exists_on_unitBall_gt_half_opNorm` | `Ishihara.lean` | ✅ **0 sorries** |
| **Helper Lemma B** | `Papers.P2.Constructive.hasOpNorm_CLF` | `Ishihara.lean` | ✅ **0 sorries** |

**Axiom Status**: Uses only `[propext, Classical.choice, Quot.sound]` 

### Finite Cesàro Theory (§2)

| Paper Label | Lean Constant | File | Status |
|-------------|---------------|------|--------|
| **Thm 2.1a** (Norm bounds) | `Papers.P2.Basics.FiniteCesaro.fn_basics_norm` | `FiniteCesaro.lean` | 🔧 To extract |
| **Thm 2.1b** (Vanishing) | `Papers.P2.Basics.FiniteCesaro.fn_basics_vanishing` | `FiniteCesaro.lean` | 🔧 To extract |
| **Thm 2.1c** (Calibration) | `Papers.P2.Basics.FiniteCesaro.fn_basics_calibration` | `FiniteCesaro.lean` | 🔧 To extract |
| **Lem 2.2** (Uniqueness) | `Papers.P2.Basics.FiniteCesaro.fn_uniqueness` | `FiniteCesaro.lean` | 🔧 To extract |
| **Lem 2.3** (Dyadic jump) | `Papers.P2.Basics.FiniteCesaro.dyadic_jump_bound` | `FiniteCesaro.lean` | 🔧 To extract |

### Boolean Sublattice Theory (§3)

| Paper Label | Lean Constant | File | Status |
|-------------|---------------|------|--------|
| **Thm 3.1** (Indicator equiv) | `Papers.P2.Gap.BooleanSubLattice.indicator_mod_c0` | `BooleanSubLattice.lean` | 🔧 To extract |
| **Def 3.1** (Embedding ι) | `Papers.P2.Gap.BooleanSubLattice.iota` | `BooleanSubLattice.lean` | 🔧 To extract |
| **Thm 3.2a** (Injectivity) | `Papers.P2.Gap.BooleanSubLattice.iota_injective` | `BooleanSubLattice.lean` | 🔧 To extract |  
| **Thm 3.2b** (Lattice hom) | `Papers.P2.Gap.BooleanSubLattice.iota_lattice_hom` | `BooleanSubLattice.lean` | 🔧 To extract |
| **Lem 3.3** (Partition) | `Papers.P2.Gap.BooleanSubLattice.finite_partition_construction` | `BooleanSubLattice.lean` | 🔧 To extract |

### Finite Embedding Construction (§3 cont.)

| Paper Label | Lean Constant | File | Status |
|-------------|---------------|------|--------|
| **Def 3.2** (E_L embedding) | `Papers.P2.Gap.FiniteEmbedding.E_L` | `FiniteEmbedding.lean` | 🔧 To extract |
| **Thm 3.4** (E_L injective) | `Papers.P2.Gap.FiniteEmbedding.E_L_injective` | `FiniteEmbedding.lean` | 🔧 To extract |
| **Thm 3.5a** (Preserves ∨) | `Papers.P2.Gap.FiniteEmbedding.E_L_preserves_sup` | `FiniteEmbedding.lean` | 🔧 To extract |
| **Thm 3.5b** (Preserves ∧) | `Papers.P2.Gap.FiniteEmbedding.E_L_preserves_inf` | `FiniteEmbedding.lean` | 🔧 To extract |
| **Thm 3.5c** (Preserves ¬) | `Papers.P2.Gap.FiniteEmbedding.E_L_preserves_compl` | `FiniteEmbedding.lean` | 🔧 To extract |
| **Cor 3.6** (Main result) | `Papers.P2.Gap.FiniteEmbedding.finite_boolean_algebra_embeds` | `FiniteEmbedding.lean` | 🔧 To extract |

---

## Reverse Direction: WLPO → Gap (Pending) 🔧

| Paper Label | Lean Constant | File | Status |
|-------------|---------------|------|--------|
| **Main Reverse** | `Papers.P2.wlpo_implies_gap` | `WLPO_Equiv_Gap.lean` | 🔧 **1 sorry** |
| **Bridge Lemma 1** | `Papers.P2.Constructive.hasOperatorNorm_to_hasOpNorm` | `DualStructure.lean` | 🔧 **1 sorry** |
| **Bridge Lemma 2** | `Papers.P2.Constructive.hasOpNorm_to_hasOperatorNorm` | `DualStructure.lean` | 🔧 **3 sorries** |
| **WLPO → LUB** | `Papers.P2.Constructive.lub_exists_for_valueSet_of_WLPO` | `DualStructure.lean` | 🔧 **1 sorry** |

**Strategy Options**:
- **Track A**: WLPO ⇒ nontrivial class in ℓ∞/c₀ (human proof + Lean stub)
- **Track B**: WLPO ⇒ non-surjectivity of canonical embedding (full formalization)

---

## API Stability Layer

| Purpose | Lean Constant | File | Status |
|---------|---------------|------|--------|
| **Unit normalization** | `Papers.P2.Basics.ApiShims.unitSphere_normalize` | `ApiShims.lean` | 🔧 Extracted |
| **Op norm bounds** | `Papers.P2.Basics.ApiShims.opNorm_pointwise_bound` | `ApiShims.lean` | 🔧 Extracted |  
| **Half-bound contradiction** | `Papers.P2.Basics.ApiShims.opNorm_half_bound_zero` | `ApiShims.lean` | 🔧 Extracted |
| **Norm bridges** | `Papers.P2.Basics.ApiShims.abs_eq_norm` | `ApiShims.lean` | 🔧 Extracted |
| **Stable op norm** | `Papers.P2.Basics.ApiShims.le_opNorm'` | `ApiShims.lean` | 🔧 Extracted |
| **Classical LUB** | `Papers.P2.Basics.ApiShims.bounded_nonempty_has_sSup` | `ApiShims.lean` | 🔧 Extracted |

---

## Build Commands

### Individual Components
```bash
# Core axiom-clean theorem
lake build Papers.P2_BidualGap.Constructive.Ishihara

# Blueprint sections (after extraction)  
lake build Papers.P2_BidualGap.Basics.FiniteCesaro
lake build Papers.P2_BidualGap.Gap.BooleanSubLattice
lake build Papers.P2_BidualGap.Gap.FiniteEmbedding

# API stability
lake build Papers.P2_BidualGap.Basics.ApiShims

# Main equivalence  
lake build Papers.P2_BidualGap.WLPO_Equiv_Gap
```

### Axiom Verification
```bash
# Check axiom-clean status
lake env lean Scripts/AxiomCheck.lean

# Expected output for key theorems:
# 'Papers.P2.Constructive.WLPO_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Paper + Build Integration (Future)
```bash
# Integrated build (when Makefile added)
make paper    # builds LaTeX + runs lake build + axiom check
```

---

## Usage Notes for Reviewers

1. **Start with Ishihara.lean** - Contains the complete axiom-clean proof
2. **Check crosswalk entries** - Each paper theorem maps to specific Lean constant  
3. **Verify blueprint structure** - New files organize proofs by paper sections
4. **Test build commands** - All ✅ entries should build without sorries
5. **Review API shims** - Stable patterns replace ad hoc proofs

**Navigation Pattern**: Paper Thm X.Y → Look up in crosswalk → Jump to Lean file → Find constant with `[Paper Thm X.Y]` docstring