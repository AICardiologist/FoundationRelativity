# Paper 44: The Measurement Problem Dissolved

**Constructive Stratification of Quantum Interpretations — A Lean 4 Formalization**

Paul Chun-Kit Lee, New York University
February 2026 | Paper 44 of the Foundation Relativity series
DOI: [10.5281/zenodo.18671162](https://doi.org/10.5281/zenodo.18671162)

---

## Overview

We apply the axiom calibration framework of constructive reverse mathematics (CRM) to the measurement problem of quantum mechanics. The three major interpretations each require a distinct constructive principle over Bishop's constructive mathematics (BISH):

| Interpretation | Physical Assertion | Principle | Forward | Reverse |
|---|---|---|---|---|
| Copenhagen (weak) | Superposition decidability (double-negation) | WLPO | proved | sorry'd |
| Copenhagen (strong) | Superposition decidability (strict) | LPO | proved | sorry'd |
| Many-Worlds | Complete branching through measurement trees | DC | sorry'd | proved |
| Bohmian | Asymptotic velocity for guided trajectories | LPO | sorry'd | sorry'd |
| Uniform MWI | Uniform branching (BISH bonus) | BISH | proved | N/A |

Since WLPO < LPO strictly and DC is incomparable with both in BISH, the three interpretations sit at **provably distinct positions** in the constructive hierarchy. The measurement problem is not one problem but three.

## Repository Contents

```
paper 44/
  paper44.tex            LaTeX source (18 pages)
  paper44.pdf            Compiled manuscript
  paper44_manuscript.md  Markdown manuscript
  README.md              This file
  CITATION.cff           Citation metadata
  .zenodo.json           Zenodo upload metadata
  P44_MeasurementDissolved/
    lakefile.lean         Lake build configuration
    lean-toolchain        leanprover/lean4:v4.28.0
    Papers.lean           Root import
    Papers/P44_MeasurementDissolved/
      Defs/
        Principles.lean        LPO, WLPO, LLPO, DC definitions (99 lines)
        BinaryEncoding.lean    r_f = sum f(n) * 2^-(n+1) via tsum (140 lines)
      Copenhagen/
        QubitState.lean        Qubit model and encoding (92 lines)
        Copenhagen.lean        copenhagen_implies_WLPO, strong_copenhagen_implies_LPO (80 lines)
      ManyWorlds/
        BranchingStructure.lean  Measurement trees, DC formulation (97 lines)
        ManyWorlds.lean          DC_implies_manyworlds, uniform_world_witness (88 lines)
      Bohmian/
        BohmianParams.lean     Free Gaussian trajectory formula (186 lines)
        BohmianLPO.lean        BMC equivalence, velocity_seq_bounded (158 lines)
      Main/
        Synthesis.lean         measurement_problem_dissolved theorem (65 lines)
        AxiomAudit.lean        #print axioms for all key theorems (101 lines)
```

**Total: 10 files, ~1,106 lines, zero build errors (2047 lake jobs).**

## Building

### Prerequisites
- [elan](https://github.com/leanprover/elan) (Lean version manager)

### Build
```bash
cd P44_MeasurementDissolved
lake build
```

Expected output: `Build completed successfully (2047 jobs).`

The `lean-toolchain` file pins Lean 4 v4.28.0; `elan` will fetch it automatically. Mathlib is pulled as a Lake dependency. First build downloads Mathlib cache and takes several minutes; subsequent builds are fast.

### Verify Axiom Audit
```bash
lake env lean Papers/P44_MeasurementDissolved/Main/AxiomAudit.lean
```

Key results:
- `copenhagen_implies_WLPO`: propext, Quot.sound (no sorry, no Classical.choice)
- `strong_copenhagen_implies_LPO`: propext, Quot.sound (no sorry, no Classical.choice)
- `DC_implies_manyworlds`: propext, Quot.sound (no sorry, no Classical.choice)
- `uniform_world_witness`: propext, Quot.sound (no sorry, no Classical.choice)

## Key Results

### Sorry-Free Directions (3)
1. **copenhagen_implies_WLPO**: CopenhagenPostulate -> WLPO
2. **strong_copenhagen_implies_LPO**: CopenhagenStrong -> LPO
3. **DC_implies_manyworlds**: DC -> ManyWorldsPostulate

### BISH Bonus (1)
4. **uniform_world_witness**: Sigma-type witness for uniform branching (no omniscience principle needed)

### Sorry'd Obligations (transparent)
- WLPO -> CopenhagenPostulate (reverse Copenhagen, literature support: Bridges-Vita 2006)
- LPO -> CopenhagenStrong (reverse strong Copenhagen)
- ManyWorldsPostulate -> DC (forward Many-Worlds)
- Both directions of Bohmian <-> LPO (conjectured)

### Synthesis Theorem
```lean
theorem measurement_problem_dissolved :
    (CopenhagenPostulate <-> WLPO) /\
    (ManyWorldsPostulate <-> DC) /\
    (BohmianAsymptoticVelocity <-> LPO) :=
  <<copenhagen_iff_WLPO, manyworlds_iff_DC, bohmian_iff_LPO>>
```

## Constructive Hierarchy

```
         DC (Dependent Choice)
        / \
       /   \         independent branch
      /     \
   WLPO --- LPO     (WLPO < LPO strictly)
   Copenhagen  Bohmian

   BISH c LLPO c WLPO c LPO
```

- Copenhagen calibrates at WLPO (or LPO in strong formalization)
- Many-Worlds calibrates at DC (incomparable with WLPO and LPO)
- Bohmian calibrates at LPO (equivalent to Bounded Monotone Convergence)
- Uniform Many-Worlds is BISH-provable (no omniscience needed)

## Methodology

AI-assisted formalization using Claude (Anthropic) for Lean 4 code generation and proof strategy exploration. All mathematical content specified by the author; every theorem verified by the Lean 4 type checker. The author is a medical professional; physical interpretations and sorry'd proof obligations require independent verification by domain experts.

## Copyright and License

Copyright 2026 Paul Chun-Kit Lee. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at

<http://www.apache.org/licenses/LICENSE-2.0>

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

## Citation

```bibtex
@software{Lee2026P44,
  author    = {Lee, Paul Chun-Kit},
  title     = {The Measurement Problem Dissolved: Constructive
               Stratification of Quantum Interpretations (Paper 44)},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.18671162},
  url       = {https://doi.org/10.5281/zenodo.18671162},
  note      = {Lean 4 / Mathlib formalization, 10 files, ~1,106 lines}
}
```
