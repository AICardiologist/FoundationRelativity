# Paper 43: What the Ceiling Means

**Paper 43 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

DOI: [10.5281/zenodo.18665418](https://doi.org/10.5281/zenodo.18665418)

## Overview

This Lean 4 formalization interprets the BISH+LPO ceiling established in
Paper 40 through the lens of three constructive schools --- Bishop, Brouwer,
and Markov --- identifying exactly where they disagree about physics.

The key finding: Markov's Principle (MP) governs *physical actualisation* ---
the step from "the probability of non-occurrence is zero" to "the event
actually occurs." This step requires Cournot's Principle (a physical postulate)
plus MP. The three schools disagree about this step specifically.

LPO strictly implies MP (five-line proof), so the BISH+LPO ceiling already
contains MP. The ceiling does not extend.

## Main Results

| Theorem | Statement | CRM Status |
|---------|-----------|------------|
| `lpo_implies_mp` | LPO strictly implies MP | Pure logic (propext only) |
| `detection_time_bish` | Detection time t0 = (log(1/eps)+1)/rate is BISH | BISH |
| `poincare_nonreturn_measure_zero` | Non-return set has measure zero | BISH |
| `not_eternal_survival` | Cournot: atom does not survive forever | Cournot |
| `atom_decays_mp` | BISH + Cournot + MP implies atom decays | Cournot + MP |
| `not_never_return` | Cournot: orbit does not never return | Cournot |
| `orbit_returns_mp` | BISH + Cournot + MP implies orbit returns | Cournot + MP |
| `vacuum_decays_mp` | False vacuum decays (reuses atom_decays_mp) | Cournot + MP |
| `fine_structure` | Assembly: hierarchy + BISH detection time | BISH |
| `lpo_subsidizes_actualisation` | LPO implies MP (re-export) | Pure logic |

## Significance

Paper 43 does not extend the ceiling. It interprets it:

- **Three schools, three readings:** Bishop (BISH alone), Brouwer (rejects LPO
  and MP), Markov (accepts MP). The programme reports where all three lines fall.
- **MP is uniquely disputed:** The only principle where all three schools have
  different positions (accept / reject / abstain).
- **Physical actualisation = Cournot + MP:** The same three-step chain
  (BISH computation -> Cournot exclusion -> MP witness extraction) governs
  radioactive decay, Poincare recurrence, and false vacuum decay.
- **Paper 22 correction:** LPO -> MP was always implicit but not stated.
  Detection time is BISH for known positive rate. MP enters through
  physical interpretation, not mathematics.

## Axiom Profile

```
#print axioms fine_structure
-- [propext, Classical.choice, Quot.sound]

#print axioms atom_decays_mp
-- [propext, Classical.choice, Quot.sound, cournot, survival_prob_zero]

#print axioms lpo_implies_mp
-- [propext]
```

- 2 custom axioms: `cournot` (physical postulate), `survival_prob_zero` (model bridge)
- MarkovPrinciple appears as a hypothesis, NOT as an axiom
- 3 Lean infrastructure (`propext`, `Classical.choice`, `Quot.sound`)

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper43.pdf`). To recompile:

```bash
pdflatex paper43.tex
pdflatex paper43.tex   # second pass for cross-references
```

### Lean 4 Formalization

**Prerequisites:** Lean 4 (v4.28.0) with elan.

```bash
cd P43_Actualisation
lake exe cache get
lake build
```

**Expected output:** 0 errors, 0 warnings, 0 sorry.

### Module Structure (12 modules, ~770 lines)

```
Defs/
  Principles.lean         -- MP, LPO, WLPO, LLPO, AtMostOne
  Cournot.lean            -- Bridge axiom: Cournot's Principle
  Decay.lean              -- survivalProb, detectionTime, eternalSurvival
Hierarchy/
  LPOImpliesMP.lean       -- Theorem 1: LPO -> MP + full hierarchy
BISHContent/
  ExponentialWitness.lean -- Theorem 2: detection time is BISH
  PoincareMeasure.lean    -- Theorem 3: non-return set measure zero
Actualisation/
  RadioactiveDecay.lean   -- Three-step chain: BISH -> Cournot -> MP -> exists
  PoincarePointwise.lean  -- Poincare recurrence actualisation
  FalseVacuum.lean        -- False vacuum decay (reuses RadioactiveDecay)
Assembly/
  FineStructure.lean      -- Assembly theorem + lpo_subsidizes_actualisation
  AxiomAudit.lean         -- Comprehensive #print axioms audit
Main.lean                 -- Root import
```

## Toolchain

- Lean: `leanprover/lean4:v4.28.0`
- Mathlib4 (pinned via `lake-manifest.json`)

## License

Creative Commons Attribution 4.0 International (CC BY 4.0).

## Citation

```bibtex
@misc{Lee2026P43,
  author = {Lee, Paul Chun-Kit},
  title  = {What the Ceiling Means: Constructive Schools, Physical
            Actualisation, and the Fine Structure of BISH+LPO},
  year   = {2026},
  doi    = {10.5281/zenodo.18665418},
  note   = {Paper~43 of the Constructive Reverse Mathematics Programme}
}
```
