# Paper 3C: DC_ω Axis Calibration

**Status**: Early Development  
**Target**: DC_ω → Baire formal proof

## Overview

Paper 3C extends the AxCal framework with a third orthogonal axis based on Dependent Choice (DC_ω). This axis captures principles related to sequential construction and completeness properties.

## Key Results

1. **DC_ω → Baire**: Formal proof that countable dependent choice implies the Baire category theorem for ℕ^ℕ
2. **Orthogonality**: DC_ω axis is independent of WLPO and FT axes
3. **Height Calibration**: Baire principle has profile (WLPO, FT, DC_ω) = (0, 0, 1)

## Module Structure

```
P3C_DCwAxis/
├── README.md                 # This file
├── Paper3C_Main.lean        # Main aggregator
└── Core/
    ├── DCw_Definition.lean  # DC_ω principle definition
    ├── Baire_Space.lean     # Baire space formalization
    └── DCw_Baire_Proof.lean # Main theorem

P3_2CatFramework/P4_Meta/    # Shared with 3A/3B
├── DCw_Frontier.lean        # DC_ω axis API
├── DCw_Baire.lean          # DC_ω → Baire proof
└── DCwPortalWire.lean      # Height transport
```

## Development Status

- [x] DC_ω axis definition
- [x] Baire space formalization  
- [ ] Step relation for closed balls
- [ ] Main theorem proof
- [ ] Height certificate
- [ ] Integration with profile machinery

## Building

```bash
lake build Papers.P3C_DCwAxis.Paper3C_Main
```

## Key Theorems

```lean
-- DC_ω principle
def DCω : Prop :=
  ∀ (X : Type) [Inhabited X] (R : X → X → Prop),
    (∀ x, ∃ y, R x y) →
    ∃ f : ℕ → X, ∀ n, R (f n) (f (n + 1))

-- Main calibration
theorem dcω_implies_baire : DCω → Baire

-- Height profile
theorem baire_profile : 
  getProfile oracle BaireWitness = ⟨0, 0, 1⟩
```

## References

- Kohlenbach (2008): Applied Proof Theory, Chapter 3
- Simpson (2009): Subsystems of Second Order Arithmetic, Chapter V.4
- Standard reverse mathematics proof via nested closed balls