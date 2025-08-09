# Foundation-Relativity Documentation

This directory contains comprehensive documentation for the Foundation-Relativity project, a Lean 4 formalization exploring how mathematical pathologies behave differently under various foundational assumptions.

> **🎯 AXIOM-CLEAN BREAKTHROUGH**: Gap → WLPO completed with zero sorries and minimal axiom usage! (August 2025)

## 📁 Documentation Organization

### 📋 Planning & Status
- **[`planning/project-status.md`](planning/project-status.md)** - Current project status across all papers
- **[`planning/ROADMAP-v3.2.md`](planning/ROADMAP-v3.2.md)** - Current roadmap with axiom-clean achievements
- **[`planning/paper4-status.md`](planning/paper4-status.md)** - Detailed status of Paper 4 implementation
- **[`planning/paper4-roadmap-enhanced.md`](planning/paper4-roadmap-enhanced.md)** - Fast-track roadmap for Paper 4

### 📚 Papers & LaTeX Sources
- **[`papers/`](papers/)** - LaTeX sources for all academic papers
  - [`P1-GBC.tex`](papers/P1-GBC.tex) - Gödel-Banach Correspondence ✅
  - [`P2-BidualGap.tex`](papers/P2-BidualGap.tex) - Bidual Gap Construction ✅ (Legacy)
  - **NEW**: [`../Papers/P2_BidualGap/documentation/paper-v3.2.tex`](../Papers/P2_BidualGap/documentation/paper-v3.2.tex) - Current Paper 2 with Lean results
  - [`P3-2CatFramework.tex`](papers/P3-2CatFramework.tex) - 2-Categorical Framework 📋
  - [`P4-SpectralGeometry.tex`](papers/P4-SpectralGeometry.tex) - Spectral Geometry 🔧

### 🔬 Analysis & Insights  
- **[`analysis/`](analysis/)** - Formalization insights and comparisons
  - [`lean-latex-alignment-p1.md`](analysis/lean-latex-alignment-p1.md) - Paper 1 Lean/LaTeX comparison
  - [`lean-latex-complete-alignment.md`](analysis/lean-latex-complete-alignment.md) - Complete alignment analysis
  - [`lean-mathAI-insights.md`](analysis/lean-mathAI-insights.md) - Insights from AI collaboration

### 🏃 Sprint Reports
- **[`sprints/`](sprints/)** - Recent sprint completion reports
  - [`sprint50-summary.md`](sprints/sprint50-summary.md) - Final sprint completing Paper 1
  - [`audit-response-2025-08-03.md`](sprints/audit-response-2025-08-03.md) - QA audit response

### 📦 Historical Archive
- **[`archive/`](archive/)** - Historical documentation and completed sprints
  - [`sprint35/`](archive/sprint35/) through [`sprint50/`](archive/sprint50/) - Detailed sprint reports
  - [`obsolete-2025-08/`](archive/obsolete-2025-08/) - Recently archived outdated docs

### 🛠️ Developer Reference
- **[`reference/`](reference/)** - Development guides and technical documentation
  - [`DEV_GUIDE.md`](reference/DEV_GUIDE.md) - Developer setup and workflows
  - [`TOOLCHAIN_UPGRADE.md`](reference/TOOLCHAIN_UPGRADE.md) - Lean toolchain management

## 🎯 Current Project Status

### ✅ Completed Papers
1. **Paper 1: Gödel-Banach Correspondence** - Complete with 0 sorries ✅
2. **Paper 2: Gap → WLPO** - **AXIOM-CLEAN BREAKTHROUGH** ✅
   - Forward direction mathematically complete (0 sorries)
   - Uses only standard classical axioms
   - Direct Prop-level proof avoiding extraction issues

### 🔧 Active Development
3. **Paper 2: WLPO → Gap** - Reverse direction pending 🔧
   - Classical construction needed
   - Bridge lemmas in progress

4. **Paper 3: 2-Categorical Framework** - Framework ready 📋
   - 6 sorries remaining (infrastructure complete)
   - Pseudo-functor theory implementation needed

5. **Paper 4: Spectral Geometry** - Discrete CPW model 🔧
   - 61 sorries in discrete implementation
   - 85% complete, active development

## 🔍 Key Documentation Highlights

### For New Contributors
1. Start with [`onboarding.md`](onboarding.md) for quick orientation
2. Read [`planning/project-status.md`](planning/project-status.md) for current status
3. Review [`reference/DEV_GUIDE.md`](reference/DEV_GUIDE.md) for development setup
4. Check [`planning/ROADMAP-v3.2.md`](planning/ROADMAP-v3.2.md) for current priorities

### For Understanding the Axiom-Clean Achievement
1. **Main Implementation**: [`../Papers/P2_BidualGap/Constructive/Ishihara.lean`](../Papers/P2_BidualGap/Constructive/Ishihara.lean)
2. **Paper Documentation**: [`../Papers/P2_BidualGap/documentation/`](../Papers/P2_BidualGap/documentation/)
3. **LaTeX Paper**: [`../Papers/P2_BidualGap/documentation/paper-v3.2.tex`](../Papers/P2_BidualGap/documentation/paper-v3.2.tex)
4. **Technical Details**: [`../Papers/P2_BidualGap/README.md`](../Papers/P2_BidualGap/README.md)

### For Researchers
1. **Current Papers**: [`../Papers/P2_BidualGap/documentation/paper-v3.2.tex`](../Papers/P2_BidualGap/documentation/paper-v3.2.tex)
2. **Implementation Analysis**: [`analysis/`](analysis/) documents Lean insights
3. **Project Evolution**: Sprint reports show development history

## 📊 Documentation Statistics

| Category | Files | Status | Current Focus |
|----------|-------|--------|---------------|
| Planning | 4 active | 🔄 **Current** | Roadmap v3.2 reflects axiom-clean achievement |
| Papers | 4 papers + v3.2 | ✅ **Up to Date** | Paper 2 v3.2 includes Lean results |
| Analysis | 3 files | ✅ **Current** | Comprehensive insights preserved |
| Archives | 50+ files | 📦 **Archived** | Historical development preserved |
| Reference | 6 files | ✅ **Current** | Developer guides updated |

## 🔄 Recent Major Updates (August 2025)

### 🎯 **AXIOM-CLEAN BREAKTHROUGH**
- ✅ **Gap → WLPO theorem complete** with zero sorries
- ✅ **Axiom-clean verification** - only standard classical axioms
- ✅ **Paper v3.2** - LaTeX updated with Lean results
- ✅ **Documentation updated** - All READMEs reflect achievement

### Architecture & Infrastructure
- ✅ **API stabilization** - Robust proof patterns for mathlib drift
- ✅ **Universe polymorphism** - Clean kernel design
- ✅ **Direct Prop-level proofs** - Avoiding extraction complexity

## 🤝 Contributing to Documentation

### Documentation Structure
- **Active docs**: Current status and planning documents
- **Paper-specific docs**: In respective `Papers/*/documentation/` folders  
- **Historical docs**: Preserved in `archive/` with clear dating

### Updating Guidelines
1. Keep current versions in main folders
2. Update cross-references when moving files
3. Maintain consistency with actual implementation status
4. Archive outdated versions with clear timestamps

## 🔗 Quick Links

- **Main Project README**: [`../README.md`](../README.md) - Project overview with axiom-clean status
- **Paper 2 (Current)**: [`../Papers/P2_BidualGap/`](../Papers/P2_BidualGap/) - Axiom-clean implementation
- **Current Roadmap**: [`planning/ROADMAP-v3.2.md`](planning/ROADMAP-v3.2.md) - Next steps and priorities
- **Axiom Verification**: [`../Scripts/AxiomCheck.lean`](../Scripts/AxiomCheck.lean) - Check axiom usage

---

This documentation provides comprehensive coverage of the Foundation-Relativity project, with special emphasis on the recent **axiom-clean breakthrough** in Paper 2's Gap → WLPO direction. The project demonstrates both mathematical depth and technical innovation in proof assistant formalization.