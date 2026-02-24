# Paper 13: The Event Horizon as a Logical Boundary

**Schwarzschild Interior Geodesic Incompleteness and LPO in Lean 4**

Paul Chun-Kit Lee, New York University

DOI: [10.5281/zenodo.18529007](https://doi.org/10.5281/zenodo.18529007)

---

## Overview

This paper formalizes in Lean 4 a decomposition of Schwarzschild interior
physics into constructive content layers. The explicit cycloid geodesic
r(eta) = M(1 + cos eta) reaches r = 0 at proper time tau* = pi*M
constructively (BISH, Height 0). The abstract principle that every bounded
monotone decreasing sequence in [0, 2M) converges to a definite real
limit---the completed-limit formulation of geodesic incompleteness---is
equivalent to the Limited Principle of Omniscience (LPO).

The event horizon at r = 2M thus demarcates not only a causal boundary but
a logical boundary: the exterior geometry (Paper 1) and the interior's
finite-time physics are BISH, while the singularity assertion as a
completed-limit principle requires exactly LPO.

Paper 13 in the Constructive Reverse Mathematics Series.

---

## Quick Start

### Prerequisites

- **elan** (Lean version manager): https://github.com/leanprover/elan
- **Git** (required by Lake to fetch Mathlib)
- ~8 GB disk space (for Mathlib cache)

### Build and Verify

```bash
cd paper13_v1
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 13 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, 0 sorry.

### Compile the Paper

```bash
pdflatex paper13_writeup.tex    # pass 1
pdflatex paper13_writeup.tex    # pass 2
pdflatex paper13_writeup.tex    # pass 3
```

The precompiled `paper13_writeup.pdf` (15 pages) is included.

---

## File Organization

```
paper13_v1/
├── README.md                              this file
├── lakefile.lean                          Lake build configuration
├── lean-toolchain                         Lean version pin (v4.28.0-rc1)
├── lake-manifest.json                     pinned dependency versions
├── Papers.lean                            root import module
├── Papers/P13_EventHorizon/
│   ├── Basic.lean                         LPO, BMC, Schwarzschild f(M,r) (168 lines)
│   ├── RadialGeodesic.lean                cycloid r(eta), tau(eta), monotonicity (250 lines)
│   ├── Incompleteness.lean                geodesic incompleteness definition (167 lines)
│   ├── LPO_Forward.lean                   incompleteness → LPO (91 lines)
│   ├── LPO_Reverse.lean                   LPO → incompleteness (57 lines)
│   ├── BISH_Content.lean                  Kretschmann scalar computability (128 lines)
│   ├── Certificates.lean                  axiom audit via #print axioms (85 lines)
│   └── Main.lean                          assembly + main theorem (75 lines)
├── paper13_writeup.tex                    LaTeX source
└── paper13_writeup.pdf                    compiled paper (15 pages)
```

**Total formalization:** 1,021 lines, 8 modules, zero sorry, zero errors.

---

## Main Results

**Part A --- BISH Content (Height 0):**
- Cycloid geodesic r(eta) = M(1 + cos eta) reaches r = 0 at tau* = pi*M (constructive).
- Kretschmann scalar K = 48M^2/r^6 is constructively computable for any r > 0.
- For any epsilon > 0, there exists explicit eta with r(eta) < epsilon.

**Part B --- LPO Equivalence (Height 1):**
- Schwarzschild interior geodesic incompleteness (every bounded monotone
  decreasing sequence in [0, 2M) converges) is equivalent to LPO.
- Forward: incompleteness implies LPO.
- Reverse: LPO implies incompleteness (via BMC, imported from Paper 8).

**Main Theorem:**
```
schwarzschild_interior_geodesic_incompleteness_iff_LPO
```

---

## Axiom Profile

```
#print axioms schwarzschild_interior_geodesic_incompleteness_iff_LPO
-- [propext, Classical.choice, Quot.sound, bmc_of_lpo]
```

**Interface assumption:** `bmc_of_lpo` axiomatizes the Bridges-Vita equivalence
BMC <-> LPO (formally proved in Paper 8).

**BISH results only:**
```
#print axioms r_cycloid_at_pi
-- [propext, Classical.choice, Quot.sound]
```

The `Classical.choice` dependency enters through Mathlib's typeclass infrastructure
(Decidable instances on R/C), not from the mathematical content.

---

## Toolchain

| Component | Version / Commit |
|-----------|-----------------|
| Lean 4 | v4.28.0-rc1 |
| Mathlib4 | `2d9b14086f3a61c13a5546ab27cb8b91c0d76734` |

---

## Citation

```bibtex
@unpublished{Lee2026Paper13,
  author = {Lee, Paul Chun-Kit},
  title  = {The Event Horizon as a Logical Boundary:
            {Schwarzschild} Interior Geodesic Incompleteness
            and {LPO} in {Lean}~4},
  year   = {2026},
  note   = {Preprint},
  doi    = {10.5281/zenodo.18529007},
  url    = {https://github.com/quantmann/FoundationRelativity}
}
```

---

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
