# Paper 5: General Relativity - GR Module

This directory contains the Schwarzschild vacuum solution formalization and supporting infrastructure.

## 📚 Documentation Hub

### Core Development Roadmap
- **[ROADMAP_Schwarzschild_Vacuum.md](ROADMAP_Schwarzschild_Vacuum.md)** - Main development roadmap with sprint breakdown
- **[Riemann.lean](Riemann.lean)** - Primary implementation file (alternation identity, Stage-1 infrastructure)

### Activation Infrastructure
- **[ACTIVATION_TRACKING.md](ACTIVATION_TRACKING.md)** - Live status matrix, decision points, and DoD checklists
- **[ACTIVATION_QUICKREF.md](ACTIVATION_QUICKREF.md)** - Quick reference with copy-paste commands
- **[PR_TEMPLATES.md](PR_TEMPLATES.md)** - Ready-to-use PR descriptions for activation phases
- **[ISSUES_TO_OPEN.md](ISSUES_TO_OPEN.md)** - Decision issue templates (sumIdx, gInv strategies)

## 🔧 Quality Gates & Automation

### Make Targets
```bash
make check      # Run all Riemann quality gates
make baseline   # Verify 51-error baseline
make activation # Check activation status
make audit      # Run Riemann-specific audits
```

### Scripts
- `scripts/check.sh` - Main quality gate runner
- `scripts/check-baseline.sh` - Baseline verification (expects 51 errors)
- `scripts/check-activation.sh` - Activation status verification
- `scripts/set-activation.sh` - One-command activation mode switcher
- `scripts/audit-riemann.sh` - Guards against global [simp], RHS/gInv consistency

## 📊 Current Status

### Baseline
- **51 errors** (all intentional geometry placeholders)
- **Activation mode:** `baseline` (ready to switch)
- **Stage-1 LHS:** 4 lemmas proven and ready
- **Bridge lemmas:** Complete (enables local sumIdx expansion)

### Decision Points (Open)
- [ ] **Issue A:** sumIdx_expand strategy (Option A: definitional vs B: finite-type)
- [ ] **Issue B:** gInv domain strategy (A: hypothesis-gated vs B: chart-restricted)
- [ ] **Issue C:** Activation mode (stage1-lhs-first vs stage1-lhs-both)

## 🚀 Quick Start

### To Open Decision Issues
```bash
# Copy templates from ISSUES_TO_OPEN.md to GitHub Issues
cat ISSUES_TO_OPEN.md
```

### To Create Activation PR
```bash
# Create branch
git checkout -b feat/p5-activate-lhs-splits

# Set activation mode
./scripts/set-activation.sh stage1-lhs-both

# Verify gates
make check

# Use PR template from PR_TEMPLATES.md
```

### To Test Locally
See the `ActivationDemo` section (lines 995-1045) in Riemann.lean for exact wiring patterns.

## 📈 Progress Tracking

### Completed ✅
- [x] Calculus infrastructure (`dCoord` operator)
- [x] Local Clairaut theorem
- [x] Stage-1 LHS lemmas (all 4 proven)
- [x] Helper infrastructure (`dCoord_add4_flat`)
- [x] Bridge lemmas for local sumIdx
- [x] Quality gates and automation
- [x] Comprehensive documentation

### Next Steps
1. Team decides on Issue A (sumIdx strategy)
2. Execute PR-A (LHS activation)
3. Team decides on Issue B (gInv strategy)
4. Execute PR-B (RHS activation)

## 🔗 Integration Points

### CI/CD
- Pre-commit hooks enforce no global `[simp]` on sumIdx_expand
- GitHub Actions can run `make audit` (non-blocking initially)
- PR template includes Paper 5 activation checklist

### Related Files
- Parent roadmap: [Papers/P5_GeneralRelativity/README.md](../README.md)
- LaTeX document: [Papers/P5_GeneralRelativity/Paper5_GR_AxCal.tex](../Paper5_GR_AxCal.tex)
- Makefile targets: [/Makefile](/Makefile) (root level)

---

**Maintainer Note:** All activation work should maintain the 51-error baseline until the math lands. Use the quality gates (`make check`) before any PR.