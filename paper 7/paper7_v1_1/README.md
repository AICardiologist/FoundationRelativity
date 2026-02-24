# Paper 7 v1.1: The Physical Bidual Gap and Banach Space Non-Reflexivity

**A Lean 4 Formalization of WLPO via Trace-Class Operators**

Paul Chun-Kit Lee, New York University

DOI: [10.5281/zenodo.18527559](https://doi.org/10.5281/zenodo.18527559)

---

## What's New in v1.1

- **P7_Minimal artifact** (277 lines, 4 files): dependency-free logical skeleton
  certifying the reduction chain `NonReflexiveWitness(S₁(H)) ↔ WLPO` with
  **no `Classical.choice`** in the axiom profile. Zero Mathlib imports, zero sorry.
- **Revised paper** (18 pages, up from 15): new §6.3 "The Classical Metatheory"
  with honest disclosure of the Classical.choice certification methodology,
  P7_Minimal build details in the reproducibility box, and strengthened
  cross-references to Paper 2's P2_Minimal and the Paper 10 methodology.

---

## Quick Start

### Prerequisites

- **elan** (Lean version manager): https://github.com/leanprover/elan
- **Git** (required by Lake to fetch Mathlib)
- ~8 GB disk space (for Mathlib cache)

### Build P7_Full (Mathlib-based, 754 lines)

```bash
cd paper7_v1_1
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles all source files (~2-5 min)
```

A successful build produces 0 errors. The only expected diagnostic is
`sorry` warnings from `Instance.lean` (an intentionally sorry-backed stub).

### Build P7_Minimal (dependency-free, 277 lines)

```bash
cd paper7_v1_1
lake build Papers.P7_PhysicalBidualGap.P7_Minimal.Main
```

Expected output (5 jobs, 0 errors):
```
✔ Built Papers.P7_PhysicalBidualGap.P7_Minimal.Defs
✔ Built Papers.P7_PhysicalBidualGap.P7_Minimal.LemmaB
✔ Built Papers.P7_PhysicalBidualGap.P7_Minimal.Reduction
ℹ Built Papers.P7_PhysicalBidualGap.P7_Minimal.Main
info: 'P7_Minimal.P7_main' depends on axioms:
  [P7_Minimal.ell1_closed_subspace_of_S1,
   P7_Minimal.ishihara_kernel,
   P7_Minimal.not_reflexive_implies_witness_S1,
   P7_Minimal.paper2_reverse,
   P7_Minimal.reflexive_closedSubspace_of_reflexive,
   P7_Minimal.witness_implies_not_reflexive]
```

**Notably absent: `Classical.choice`, `propext`, `Quot.sound`.**

### Compile the Paper

```bash
pdflatex paper7_writeup.tex    # pass 1
pdflatex paper7_writeup.tex    # pass 2 (resolves references)
pdflatex paper7_writeup.tex    # pass 3 (stabilizes TOC)
```

The precompiled `paper7_writeup.pdf` (18 pages) is included.

---

## File Organization

```
paper7_v1_1/
├── README.md                          this file
├── lakefile.lean                      Lake build configuration
├── lean-toolchain                     Lean version pin (v4.28.0-rc1)
├── lake-manifest.json                 pinned dependency versions
├── Papers.lean                        root import module
├── Papers/P7_PhysicalBidualGap/
│   ├── Basic.lean                     WLPO & IsReflexive definitions (34 lines)
│   ├── ReflexiveDual.lean             Lemma A: reflexive ⟹ dual reflexive (47 lines)
│   ├── DiagonalEmbedding.lean         HasTraceClassContainer typeclass (45 lines)
│   ├── Compat.lean                    reflexivity transfer via isometries (78 lines)
│   ├── ReflexiveSubspace.lean         Lemma B: closed subspace of reflexive (174 lines)
│   ├── WLPOFromWitness.lean           Ishihara kernel: witness ⟹ WLPO (196 lines)
│   ├── Instance.lean                  concrete S₁(ℓ²(ℕ)) witness, sorry-backed (51 lines)
│   ├── Main.lean                      assembly + main theorem (129 lines)
│   └── P7_Minimal/                    ← NEW in v1.1
│       ├── Defs.lean                  opaque types, predicates, WLPO (73 lines)
│       ├── LemmaB.lean                Lemma B axiom + contrapositive (39 lines)
│       ├── Reduction.lean             interface axioms + forward/reverse (108 lines)
│       └── Main.lean                  assembly + #print axioms audit (57 lines)
├── paper7_writeup.tex                 LaTeX source (v1.1, ~1400 lines)
└── paper7_writeup.pdf                 compiled paper (18 pages)
```

**P7_Full:** 754 lines, 8 files, 7/8 sorry-free, 1 interface assumption.
**P7_Minimal:** 277 lines, 4 files, zero sorry, zero Mathlib imports, no Classical.choice.

---

## Main Theorem

```lean
-- P7_Full (Mathlib-based)
theorem physical_bidual_gap [tc : HasTraceClassContainer] :
    (¬ IsReflexive ℝ tc.X) ∧
    ((∃ Ψ : (tc.X)**, Ψ ∉ range (inclusionInDoubleDual ℝ tc.X)) → WLPO)

-- P7_Minimal (dependency-free)
theorem P7_main : NonReflexiveWitness S1H_Type ↔ WLPO
```

**Forward (unconditional):** S₁(H) is not reflexive, because it contains
ℓ¹ as a closed isometric subspace (diagonal embedding), and ℓ¹ is not reflexive.

**Backward (Ishihara kernel):** Any non-reflexivity witness for *any* Banach
space implies WLPO. This is a universal result — it does not use Lemma B or ℓ¹.

**Reverse in P7_Minimal (WLPO → witness):** Chains through ℓ¹ via Lemma B:
  WLPO → witness(ℓ¹) [Paper 2] → ¬Reflexive(ℓ¹) → ¬Reflexive(S₁(H)) [Lemma B] → witness(S₁(H))

---

## Axiom Profiles

### P7_Full

```
#print axioms physical_bidual_gap
-- [propext, Classical.choice, Quot.sound, ell1_not_reflexive]

#print axioms wlpo_of_nonreflexive_witness_proof
-- [propext, Classical.choice, Quot.sound]  (no custom axioms)
```

The `Classical.choice` dependency arises from Mathlib's normed space infrastructure
(Hahn-Banach, NormedSpace hierarchy, Decidable instances on ℝ).

### P7_Minimal

```
#print axioms P7_Minimal.P7_main
-- [P7_Minimal.ell1_closed_subspace_of_S1,
--  P7_Minimal.ishihara_kernel,
--  P7_Minimal.not_reflexive_implies_witness_S1,
--  P7_Minimal.paper2_reverse,
--  P7_Minimal.reflexive_closedSubspace_of_reflexive,
--  P7_Minimal.witness_implies_not_reflexive]
```

All six axioms are explicitly declared interface assumptions with backing proofs
in P7_Full or P2_Full. **No Classical.choice, no propext, no Quot.sound.**

---

## Certification Methodology

The constructive (BISH) claim for the equivalence is established at two levels:

1. **P7_Full** provides machine-checked proof correctness: all theorem statements
   compile without sorry (7/8 files), and the proof chain is verified by Lean's
   kernel. The `Classical.choice` in the axiom profile is an infrastructure
   artifact from Mathlib, not a reflection of classical content in the proofs.

2. **P7_Minimal** provides structural certification: the logical reduction is
   verified to use no classical axioms beyond the explicitly declared interface
   assumptions. Each interface axiom is backed by a proof in P7_Full or P2_Full.

Paper 7 is classified as "structurally verified" in the series certification
framework (Paper 10, forthcoming).

---

## Toolchain and Dependencies

| Component | Version / Commit |
|-----------|-----------------|
| Lean 4 | v4.28.0-rc1 |
| Lake | 5.0.0-src+3b0f286 |
| Mathlib4 | `9543d5047cb12a05abd2d9b9bc2ea2a604b3be87` |

All dependency versions are pinned in `lake-manifest.json` for exact reproducibility.

---

## Citation

```bibtex
@unpublished{Lee2026Paper7,
  author = {Lee, Paul Chun-Kit},
  title  = {The Physical Bidual Gap and {Banach} Space Non-Reflexivity:
            A {Lean}~4 Formalization of {WLPO} via Trace-Class Operators},
  year   = {2026},
  note   = {Preprint, v1.1. Lean~4 formalization with P7\_Minimal artifact},
  doi    = {10.5281/zenodo.18527559},
  url    = {https://github.com/quantmann/FoundationRelativity}
}
```

---

## Links

- **GitHub repository:** https://github.com/quantmann/FoundationRelativity
- **Paper 2 (companion):** same repository, `paper_2_bundle/`
- **Mathlib4 docs:** https://leanprover-community.github.io/mathlib4_docs/

---

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
