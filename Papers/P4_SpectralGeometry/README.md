# Paper 4: Axiom Calibration for Quantum Spectra

## Status: New Direction - Planning Phase

**Transition Date**: September 4, 2025  
**New Direction Defined**: September 4, 2025

### Overview
Paper 4 applies the Axiom Calibration (AxCal) framework to quantum spectral theory, identifying which spectral results are constructively provable (height 0) and which require additional logical principles like WLPO, DCω, or Markov's Principle.

### Key Results (S0-S4)
1. **S0**: ε-spectral approximations for compact operators (height 0)
2. **S1**: Spec_approx = Spec equivalence requires Markov's Principle
3. **S2**: Locale spatiality needs DCω (upper bound)
4. **S3**: WLPO portal for separation-based proofs
5. **S4**: Quantum harmonic oscillator at height 0

### Previous Work
The original Paper 4 (Spectral Geometry - Undecidable eigenvalue problems) has been archived to `archive/old_spectral_geometry_2025/`. It contained ~75 sorries and was suspended from active development.

### New Direction: Quantum Spectra & Axiom Calibration
This paper connects quantum mechanics to the AxCal framework, showing how different spectral properties require different logical axioms.

### Lean Verification Strategy

#### Phase 1: Infrastructure (Reuse from Paper 3A)
```lean
-- Import AxCal framework from Paper 3A
import Papers.P3_2CatFramework.P4_Meta.AxCalFramework

-- Axiom tokens (already in Paper 3A)
class HasWLPO (F : Foundation) : Prop
class HasFT (F : Foundation) : Prop  
class HasDCω (F : Foundation) : Prop
class HasMP (F : Foundation) : Prop  -- New for Markov's Principle
class HasACω (F : Foundation) : Prop -- Countable choice
```

#### Phase 2: Spectral Witness Families
```lean
-- S0: Compact spectral approximation (height 0)
structure CompactSpectralApprox_W : WitnessFamily

-- S1: Spec_approx = Spec (requires MP)
structure SpecApproxEqSpec_W : WitnessFamily

-- S2: Locale spatiality (upper bound DCω)
structure LocaleSpatiality_W : WitnessFamily  

-- S3: WLPO portal for separation
structure SeparationRoute_W : WitnessFamily
```

#### Phase 3: Main Theorems
1. **Height 0 results** (S0, S4): Constructive spectral approximations
2. **Markov frontier** (S1): Characterize exact spectrum membership
3. **DCω upper bound** (S2): Locale point extraction
4. **WLPO portal** (S3): Connect to Paper 2's bidual gap

### Implementation Priorities
1. ✅ Define axiom tokens for extended axes (MP, ACω, etc.)
2. ⬜ Formalize spectral witness families S0-S4
3. ⬜ Prove height 0 results (S0, S4)
4. ⬜ Connect S3 to Paper 2's WLPO ↔ Gap equivalence
5. ⬜ Literature axiomatization for S1 reversal

### Physics Connection
The calibration reveals which quantum mechanical results are:
- **Computational** (height 0): Numerical methods, finite approximations
- **Semi-computational** (MP): Decidable but potentially unbounded search
- **Non-computational** (DCω, WLPO): Require genuine choice principles

### Structure
```
P4_SpectralGeometry/
├── README.md                    # This file
├── Paper4_QuantumSpectra.tex    # Main LaTeX document
├── TRANSITION_NOTICE.md         # Historical record
├── Spectral/                    # New Lean modules (to be created)
│   ├── Basic.lean              # Hilbert space setup
│   ├── CompactApprox.lean      # S0: Height 0 approximations
│   ├── MarkovSpectrum.lean     # S1: MP frontier
│   ├── LocaleSpatiality.lean   # S2: DCω upper bound
│   ├── WLPOPortal.lean         # S3: Separation route
│   └── QHO.lean                # S4: Quantum harmonic oscillator
└── archive/
    └── old_spectral_geometry_2025/  # Previous work (preserved)