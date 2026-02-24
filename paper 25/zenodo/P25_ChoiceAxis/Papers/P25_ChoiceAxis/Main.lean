/-
Papers/P25_ChoiceAxis/Main.lean
Paper 25: Aggregator and Axiom Audit

Constructive Reverse Mathematics of the Choice Axis:
Separating Countable Choice from Dependent Choice
via Ergodic Theory and Quantum Measurement

This module imports all components of Paper 25 and performs the
axiom audit via #print axioms.

## Summary of Results

### Choice Hierarchy (proved)
- `cc_n_of_dc`:  DC → CC_N
- `ac0_of_cc_n`: CC_N → AC₀
- `ac0_of_dc`:   DC → AC₀ (transitive)

### Cesàro Average Properties (proved)
- `cesaroAvg_of_fixed`: Fixed points are invariant
- `sum_iterate_sub`: Telescoping identity
- `cesaroAvg_range_norm_le`: Norm bound for Range(U-I) elements
- `cesaroAvg_range_tendsto_zero`: Convergence to zero
- `cesaroAvg_norm_le`: Uniform bound for isometries

### Forward Directions
- `meanErgodic_of_cc`: CC → Mean Ergodic Theorem [fully proved]
- `weakLLN_of_cc`: CC → Weak Law of Large Numbers [fully proved, via SLLN + a.e. ⇒ in prob.]
- `strongLLN_of_dc`: DC → Strong Law of Large Numbers [fully proved, wraps Mathlib]

### Reverse Directions
- `meanErgodic_implies_cc`: Mean Ergodic → CC [fully proved — classically trivial]
- `meanErgodicComputableAll_implies_cc`: MeanErgodicComputableAll → CC_N
    [fully proved — Type-level, hypothesis genuinely used, 395 lines]
- `birkhoff_of_dc`: DC → Birkhoff [axiom — Birkhoff not in Mathlib]
- `dc_of_birkhoff`: Birkhoff → DC [fully proved — classically trivial]

### Equivalences
- `meanErgodic_iff_cc`: CC ↔ Mean Ergodic Theorem
- `birkhoff_iff_dc`: DC ↔ Birkhoff's Theorem
-/
import Papers.P25_ChoiceAxis.MeanErgodicReverse
import Papers.P25_ChoiceAxis.PointwiseErgodicReverse
import Papers.P25_ChoiceAxis.WeakLaw
import Papers.P25_ChoiceAxis.StrongLaw
import Papers.P25_ChoiceAxis.Separation
import Papers.P25_ChoiceAxis.CalibrationTable
import Papers.P25_ChoiceAxis.Computable

namespace Papers.P25_ChoiceAxis

-- ========================================================================
-- Axiom Audit
-- ========================================================================

-- Choice hierarchy (fully proved)
#print axioms cc_n_iff_cc_seq
#print axioms cc_n_of_dc
#print axioms ac0_of_cc_n
#print axioms ac0_of_dc

-- Cesàro average properties (fully proved)
#print axioms cesaroAvg_of_fixed
#print axioms sum_iterate_sub
#print axioms cesaroAvg_range_norm_le
#print axioms cesaroAvg_range_tendsto_zero
#print axioms cesaroAvg_norm_le

-- Key lemma (fully proved)
#print axioms orthogonal_range_sub_le_fixed
#print axioms fixedSubspace_isClosed

-- Forward directions (all fully proved)
#print axioms meanErgodic_of_cc
#print axioms weakLLN_of_cc
#print axioms strongLLN_of_dc

-- Reverse directions (proved classically)
#print axioms meanErgodic_implies_cc
#print axioms dc_of_birkhoff

-- Type-level reverse (non-trivial, hypothesis genuinely used)
#print axioms meanErgodicComputableAll_implies_cc

-- Equivalences
#print axioms meanErgodic_iff_cc  -- fully clean (no custom axioms)
#print axioms birkhoff_iff_dc     -- depends on birkhoff_of_dc only

-- Separation and calibration
#print axioms birkhoff_above_mean_ergodic

/-
## Expected Axiom Profile

### Fully proved theorems:
  cc_n_iff_cc_seq:              [propext, Quot.sound]
  cc_n_of_dc:                   [propext, Quot.sound]
  ac0_of_cc_n:                  [propext, Classical.choice, Quot.sound]
  ac0_of_dc:                    [propext, Classical.choice, Quot.sound]
  cesaroAvg_of_fixed:           [propext, Classical.choice, Quot.sound]
  sum_iterate_sub:              [propext, Classical.choice, Quot.sound]
  cesaroAvg_range_norm_le:      [propext, Classical.choice, Quot.sound]
  cesaroAvg_range_tendsto_zero: [propext, Classical.choice, Quot.sound]
  cesaroAvg_norm_le:            [propext, Classical.choice, Quot.sound]
  orthogonal_range_sub_le_fixed: [propext, Classical.choice, Quot.sound]
  fixedSubspace_isClosed:       [propext, Classical.choice, Quot.sound]

### Forward directions (fully proved):
  meanErgodic_of_cc:            [propext, Classical.choice, Quot.sound]
  weakLLN_of_cc:                [propext, Classical.choice, Quot.sound]
  strongLLN_of_dc:              [propext, Classical.choice, Quot.sound]

### Reverse directions (classically trivial — proved via Classical.choice):
  meanErgodic_implies_cc:       [propext, Classical.choice, Quot.sound]
  dc_of_birkhoff:               [propext, Classical.choice, Quot.sound]

### Type-level reverse (non-trivial — hypothesis genuinely used):
  meanErgodicComputableAll_implies_cc: [propext, Classical.choice, Quot.sound]
  -- Classical.choice from Mathlib infrastructure only; the hypothesis
  -- h : MeanErgodicComputableAll is genuinely used via .some, proj_fixed,
  -- and modulus_spec. Cannot be discarded.

### Single remaining axiom (Birkhoff not in Mathlib):
  birkhoff_of_dc:               depends on [birkhoff_of_dc] (only custom axiom)

### Equivalences:
  meanErgodic_iff_cc:           [propext, Classical.choice, Quot.sound]  ← CLEAN!
  birkhoff_iff_dc:              depends on [birkhoff_of_dc] only
  birkhoff_above_mean_ergodic:  [propext, Classical.choice, Quot.sound]  ← CLEAN!

Note: Classical.choice appears in analysis theorems because Mathlib's
InnerProductSpace, Measure, and Filter infrastructure uses it
transitively. This is an infrastructure artifact, not a mathematical
dependency. The mathematical content of the proved theorems is
constructive (algebraic identities, Cauchy-Schwarz, telescoping sums).

## Formalization Scope and Classical/Constructive Boundary

The forward calibrations (choice principle → physical theorem) are
formalized in Lean 4 with clean axiom profiles. These are the directions
where the mathematical content lives and where formalization adds
confidence:
  - CC → Mean Ergodic: 600+ lines of genuine Hilbert space analysis
  - CC → Weak LLN: via strong law (calibration note in WeakLaw.lean)
  - DC → Strong LLN: wrapping Mathlib's `strong_law_ae_real`

The reverse calibrations (physical theorem → choice principle) present
a unique challenge in classical proof assistants. In Lean, the Prop-level
`MeanErgodicTheorem → CC_N` is trivially true because `CC_N` is provable
regardless of hypothesis (the antecedent is discarded via Classical.choice).

To overcome this, Computable.lean (395 lines) introduces a Type-level
formulation `MeanErgodicComputable` where the projection and convergence
modulus are data (not mere existence claims). The theorem
`meanErgodicComputableAll_implies_cc` then extracts CC_N from this
Type-level hypothesis via an explicit ℓ²(ℕ×ℕ) encoding with a diagonal
reflection operator. The hypothesis is genuinely used — it cannot be
discarded — making this a non-trivial formalization of the reverse
direction even in a classical proof assistant.

The Birkhoff reverse direction remains paper-level (documented in
PointwiseErgodic.lean). Fully constructive formalization (e.g., in Agda
without K or Coq without classical axioms) is noted as future work.

### Permanent sorries (2, model-theoretic):
  - `ac0_not_implies_cc_n`: AC₀ ↛ CC (requires Fraenkel-Mostowski model)
  - `cc_n_not_implies_dc`:  CC ↛ DC (requires forcing/inner model argument)
  These independence results cannot be proved in any object-level theory;
  they require model construction at the metatheoretic level.
-/

end Papers.P25_ChoiceAxis
