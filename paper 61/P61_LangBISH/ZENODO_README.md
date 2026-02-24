# Paper 61: Lang's Conjecture as the MP → BISH Gate

**The Decidability Hierarchy for Mixed Motives**

Series: Constructive Reverse Mathematics and Physics
Author: Paul C.-K. Lee, February 2026

## Quick Start

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (installed via `elan`)
- Internet connection (for Mathlib cache download)

### Build and Verify
```bash
cd P61_LangBISH
lake exe cache get    # downloads prebuilt Mathlib (~5 min)
lake build            # compiles all source files (~1 min on cache hit)
```

**Expected output:** 0 errors, 0 warnings, 0 `sorry`.

## Main Results

| Theorem | Lean Name | Statement |
|---------|-----------|-----------|
| A (Lang → BISH) | `lang_implies_bish` | Effective Lang + Minkowski + Northcott gives computable height bound |
| B (BISH ⟹̸ Lang) | `bish_does_not_imply_lang` | Witness: family c(n)=1/(n+2), each bounded but inf→0 |
| C (X₀(389)) | `generators_within_bound` | Both generators ĥ(Pᵢ) ≤ ĥ_max ≈ 10.54 |
| D (No Northcott ↔ LPO) | `no_northcott_iff_lpo` | Infinite lattice completeness ↔ LPO (explicit reduction) |
| E (Uniform Lang) | `uniform_lang_analytic_bish` | Under Uniform Lang, L-function is universal BISH certificate |

## DPT Hierarchy

```
BISH  ⊊  MP  ⊊  LPO
        ↑          ↑
     Lang's     Northcott
    conjecture  property
```

- **Gate 1 (Northcott):** Controls LPO → MP. Abelian varieties pass; K3 surfaces fail.
- **Gate 2 (Lang):** Controls MP → BISH. Minkowski covolume → individual vector bound.
- Both implications are strict (one-way).

## Axiom Audit

| Theorem | Axioms |
|---------|--------|
| `lang_implies_bish` | `propext`, `Classical.choice`, `Quot.sound` |
| `bish_does_not_imply_lang` | `propext`, `Classical.choice`, `Quot.sound` |
| `generators_within_bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `no_northcott_iff_lpo` | `propext`, `Quot.sound` |
| `uniform_lang_analytic_bish` | `propext`, `Classical.choice`, `Quot.sound`, `UniformLang` |

- `Classical.choice` appears via Mathlib's ℚ arithmetic infrastructure (implementation artifact).
- `UniformLang` is the only open-conjecture axiom, used exclusively for Theorem E.
- Zero `sorry`. Zero custom axioms beyond the above.

## File Organization

```
P61_LangBISH/
├── lakefile.lean
├── lean-toolchain
├── Papers.lean
├── paper61.tex
├── paper61.pdf
├── ZENODO_README.md
└── Papers/P61_LangBISH/
    ├── Main.lean                    -- Root module & axiom audit
    ├── Basic/
    │   ├── Decidability.lean        -- BISH, MP, LPO definitions
    │   ├── Heights.lean             -- Canonical height, Northcott property
    │   └── Lattices.lean            -- Hermite constants, Minkowski axiom
    ├── Forward/
    │   ├── LangToBISH.lean          -- Theorem A: Lang → BISH
    │   └── Explicit389.lean         -- Theorem C: X₀(389) verification
    ├── Converse/
    │   └── BISHNotLang.lean         -- Theorem B: BISH ⟹̸ Lang
    ├── Northcott/
    │   └── EscalationLPO.lean       -- Theorem D: No Northcott ↔ LPO
    └── Uniform/
        └── UniformLang.lean         -- Theorem E: Uniform Lang → analytic BISH
```

## Toolchain and Dependencies

| Component | Version |
|-----------|---------|
| Lean 4 | v4.29.0-rc1 |
| Mathlib | latest (via `lake exe cache get`) |
| LaTeX | pdfTeX (any recent distribution) |

## Citation

```bibtex
@misc{lee2026langbish,
  author = {Lee, Paul C.-K.},
  title  = {Lang's Conjecture as the {MP} $\to$ {BISH} Gate:
            The Decidability Hierarchy for Mixed Motives},
  year   = {2026},
  note   = {Paper 61 in the Constructive Reverse Mathematics and Physics series.
            Lean 4 formalization with Mathlib.}
}
```

## License

MIT License. See individual files for details.
