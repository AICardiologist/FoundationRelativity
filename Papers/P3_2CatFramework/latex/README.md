# Paper 3 LaTeX Documents - Consolidated Location

## 📍 All LaTeX documents for Papers 3, 3A, 3B, and formalization are now located here

### Main Documents

| File | Description | Status | Notes |
|------|-------------|--------|-------|
| **Paper3_Main.tex** | Paper 3 main document (mother paper) | Active | Comprehensive AxCal framework document (2112 lines) |
| **Paper3A_Publication.tex** | Paper 3A publication version | Active | Three-axis framework with physics angle (472 lines) |
| **Paper3B_Publication.tex** | Paper 3B publication version | Frozen | Proof-theoretic scaffold (348 lines) |
| **Paper3_Lean_Formalization.tex** | Lean formalization documentation | Reference | Technical formalization details (989 lines) |

### Archive/Old Versions

| File | Description | Notes |
|------|-------------|-------|
| **Paper3A_Old_Version.tex** | Previous Paper 3A version | Includes DCω/Baire roadmap section |
| **Paper3_WPB_Fragment.tex** | WP-B update fragment | Small fragment (29 lines) |

## Document Relationships

```
Paper3_Main.tex (Mother Document)
    ├── Comprehensive framework presentation
    ├── All three axes (WLPO, FT, DCω)
    └── Integration of all components

Paper3A_Publication.tex
    ├── Focused on AxCal framework
    ├── Three orthogonal calibrators
    ├── Physics applications
    └── Paper 3C (DCω) integrated

Paper3B_Publication.tex
    ├── Proof-theoretic scaffold
    ├── 21 axioms achievement
    └── Meta-mathematical hierarchies

Paper3_Lean_Formalization.tex
    ├── Technical Lean 4 details
    ├── Implementation specifics
    └── CI/build documentation
```

## Key Updates (September 2025)

- **Paper 3C Integration**: DCω/Baire axis (formerly Paper 3C) is now fully integrated into Paper3A_Publication.tex
- **Physics Angle Added**: Both Paper3_Main.tex and Paper3A_Publication.tex now include physics-facing narrative
- **Verification Ledger**: Added to distinguish formalized vs cited results
- **Bibliography**: Updated with Blair 1977, Johnstone 1982, and other references

## Shared Resources

- **paper3-macros.tex** - Shared macro definitions for consistency
- **Makefile** - Automated building with proper dependencies  
- **.latexmkrc** - Configuration for latexmk builds

## Building LaTeX Documents

### Using Make (Recommended)
```bash
# Build all documents
make all

# Build individual documents
make paper3        # Build Paper3_Main.pdf
make paper3a       # Build Paper3A_Publication.pdf
make paper3b       # Build Paper3B_Publication.pdf
make formalization # Build Paper3_Lean_Formalization.pdf

# Quick single-pass build (no bibliography)
make quick-Paper3A_Publication

# Clean auxiliary files
make clean

# Show all options
make help
```

### Using latexmk
```bash
# Build with automatic dependency tracking
latexmk -pdf Paper3A_Publication.tex

# Watch mode (auto-rebuild on changes)
latexmk -pdf -pvc Paper3A_Publication.tex
```

### Manual compilation
```bash
# Standard pdflatex compilation
pdflatex Paper3_Main.tex
bibtex Paper3_Main
pdflatex Paper3_Main.tex
pdflatex Paper3_Main.tex
```

## Related Locations

- **Lean Source**: `Papers/P3_2CatFramework/*.lean`
- **Documentation**: `Papers/P3_2CatFramework/documentation/`
- **Tests**: `Papers/P3_2CatFramework/test/`
- **P3C Materials**: `Papers/P3_2CatFramework/P3C_DCwAxis/` (placeholder)

## Publication Status

- **Paper 3**: Pre-publication draft, comprehensive framework
- **Paper 3A**: Ready for submission (complete with three axes)
- **Paper 3B**: Complete and frozen (21 axioms achieved)
- **Paper 3C**: Integrated into Paper 3A (no separate paper needed)