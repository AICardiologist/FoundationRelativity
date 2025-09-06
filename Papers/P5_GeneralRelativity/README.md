# Paper 5: General Relativity AxCal Analysis

**Axiom Calibration for General Relativity: Portals, Profiles, and a Hybrid Plan for EPS and Schwarzschild**

This paper applies the Axiom Calibration (AxCal) framework to General Relativity, providing precise measurements of the logical strength required for key GR theorems through a novel portal-based approach.

## 📄 Paper Content

### LaTeX Documents
- **Main Paper**: [`Paper5_GR_AxCal.tex`](Paper5_GR_AxCal.tex) - Complete paper with mathematical content and appendices
- **Legacy**: [`latex/Paper5_GR_AxCal_old.tex`](latex/Paper5_GR_AxCal_old.tex) - Original theoretical foundation

### Key Contributions

1. **AxCal Instrumentation for GR**:
   - Witness families pinned to Σ₀^GR signature
   - Proof-route flags and portal theorems
   - HeightCertificates with three-axis profiles (Choice, Compactness, Logic)

2. **Portal Framework**:
   - `uses_zorn` → AC portal (Choice axis)
   - `uses_limit_curve` → FT/WKL₀ portal (Compactness axis)  
   - `uses_serial_chain` → DCω portal (Dependent Choice)
   - `uses_reductio` → LEM portal (Logic axis)

3. **Five Calibration Targets (G1-G5)**:
   - **G1**: Explicit vacuum checks (Height 0)
   - **G2**: Cauchy problem/MGHD (Zorn portal)
   - **G3**: Singularity theorems (Compactness + LEM portals)
   - **G4**: Maximal extensions (Zorn portal)
   - **G5**: Computable evolution (Pour-El-Richards negative template)

4. **Deep-Dive Deliverables** (Height 0 anchors):
   - **D1**: EPS kinematics core (constructive proof)
   - **D2**: Schwarzschild vacuum check (symbolic tensor engine)

## 🏗️ Lean 4 Implementation

### File Structure
```
Papers/P5_GeneralRelativity/
├── Main.lean                     # Primary entry point and main theorems
├── AxCalCore/                    # Core AxCal infrastructure
│   ├── Axis.lean                 # Height profiles and composition
│   └── Tokens.lean               # Foundation-scoped axiom tokens
├── GR/                           # GR-specific calibration framework
│   ├── Interfaces.lean           # Σ₀^GR signature: manifolds, metrics, EFE
│   ├── Portals.lean              # Proof-route flags and portal soundness
│   ├── Witnesses.lean            # G1-G5 witness families
│   ├── Certificates.lean        # HeightCertificate definitions
│   ├── EPSCore.lean              # Deep-dive D1: EPS kinematics (Height 0)
│   └── Schwarzschild.lean        # Deep-dive D2: vacuum check (Height 0)
├── Ledger/
│   └── Citations.lean            # Structured bibliography
└── Smoke.lean                    # CI aggregator and verification
```

### Key Lean Concepts

#### Height Profiles
```lean
structure AxisProfile where
  hChoice : Height    -- AC/DCω axis
  hComp   : Height    -- FT/WKL₀ axis  
  hLogic  : Height    -- LEM/WLPO/MP axis
```

#### Portal Framework
```lean
inductive PortalFlag
| uses_zorn         -- Zorn's lemma application
| uses_limit_curve  -- Ascoli-Arzelà / curve compactness
| uses_serial_chain -- Infinite dependent choice construction
| uses_reductio     -- Essential proof by contradiction
```

#### Witness Families
```lean
def WitnessFamily := Foundation → Prop

def G1_Vacuum_W : WitnessFamily := fun F =>
  ∀ (Ssch : Spacetime), IsPinnedSchwarzschild Ssch → VacuumEFE Ssch
```

## 📊 Calibration Results

| Target | Profile (h_Choice, h_Comp, h_Logic) | Portals | Notes |
|--------|-------------------------------------|---------|-------|
| **G1** | (0,0,0) | none | Symbolic tensor algebra |
| **G2 Local** | (0,0,0) | none | PDE core constructive |
| **G2 MGHD** | (1,0,0) | Zorn | Global maximal development |
| **G3** | (0,1,1) | LimitCurve, Reductio | Penrose singularity theorem |
| **G4** | (1,0,0) | Zorn | Maximal extension existence |
| **G5** | (0,0,1) | SerialChain | Computability/measurement |

## 🚀 Build Instructions

### Prerequisites
- Lean 4 with elan toolchain manager
- Lake package manager

### Build Commands
```bash
# Build main Paper 5 target
lake build Papers.P5_GeneralRelativity

# Run smoke test and verification
lake build Papers.P5_GeneralRelativity.Smoke

# Check individual components
lake build Papers.P5_GeneralRelativity.GR.Certificates
lake build Papers.P5_GeneralRelativity.GR.EPSCore
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild
```

### Verification Status
- **No-sorry requirement**: All deep-dive deliverables (D1, D2) must compile without `sorry`
- **Certificate completeness**: All G1-G5 targets have HeightCertificate instances
- **Portal soundness**: All route flags trigger appropriate axiom tokens

## 🔬 Hybrid Development Plan

**Schematic Map (Current)**: 
- Register all G1-G5 witness families ✅
- Attach route flags per standard proofs ✅  
- Emit HeightCertificates using portal soundness ✅
- Maintain verification ledger with citations ✅

**Deep Dive (Deliverables)**:
- **D1**: EPS interface avoiding portals (Height 0) ✅
- **D2**: Minimal tensor engine for Schwarzschild vacuum (Height 0) ✅

## 📚 Literature Integration

The portal framework integrates key literature at the axiom level:

- **Robb/Reichenbach/EPS**: Axiomatic kinematics → no portals for conformal/projective recovery
- **Pour-El-Richards**: Computable→non-computable PDE evolution → Logic axis calibration
- **Bishop-Bridges/Hellman**: Constructive analysis guidance → Height 0 vs choice distinction
- **Wald/Hawking-Ellis/Choquet-Bruhat**: Standard GR proofs → portal location identification

## 🎯 Success Metrics

1. ✅ **D1 and D2 compiled without `sorry`**
2. ✅ **HeightCertificates present for all G1-G5** 
3. ✅ **Explicit portal flags in ledger**
4. ✅ **CI and verification infrastructure**

## 🔗 Integration with AxCal Ecosystem

Paper 5 builds on the complete frozen AxCal framework:
- **Paper 3A**: Three orthogonal axes and uniformization theory
- **Paper 3B**: Proof-theoretic scaffold and collision framework  
- **Paper 4**: Spectral geometry calibrations and profile algebra
- **Papers 1-2**: Foundational results in functional analysis

The GR calibration extends AxCal methodology to spacetime physics while maintaining the same rigorous approach to axiom accounting.

---

*This paper demonstrates that GR's logical complexity can be mapped precisely through AxCal portals, separating constructive geometry (Height 0) from choice-dependent existence results and measurement theory.*