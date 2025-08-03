# Contributing to Foundation-Relativity

Thank you for your interest in contributing to Foundation-Relativity! This project formalizes foundation-relative mathematics in Lean 4, and we welcome contributions from mathematicians, formal methods experts, and anyone interested in constructive mathematics.

> **⚠️ CRITICAL QA NOTICE**: Papers 1-3 have significant formalization issues despite "0 sorries" claims. See [CRITICAL_QA_NOTICE.md](CRITICAL_QA_NOTICE.md) and [roadmap-corrective-action.md](docs/planning/roadmap-corrective-action.md) for details. All contributors must follow the **No-Shortcuts Rules** below.

**Current Status**: QA audit revealed Unit/() tricks used instead of real formalization. 12-week corrective action plan in progress.

## ⚠️ MANDATORY READING: No-Shortcuts Policy

**QA Audit Finding**: The repository has been using deceptive Unit/() tricks to achieve "0 sorries" without real formalization.

**This is now FORBIDDEN. All contributors must:**
1. Use `sorry` for incomplete work - NEVER use Unit stubs
2. Write real mathematical definitions - NEVER use `dummy : Unit`
3. Create genuine proofs - NEVER use `exact ⟨()⟩` tricks
4. Follow the detailed No-Shortcuts Rules below

**Violations will result in PR rejection.**

## 🚀 Quick Start

1. **Fork** the repository
2. **Clone** your fork: `git clone https://github.com/yourusername/FoundationRelativity.git`
3. **Install** Lean 4.22.0-rc3 and VS Code with the lean4 extension
4. **Build** the project: `lake build`
5. **Run tests**: `lake exe testFunctors && lake exe AllPathologiesTests`
6. **Check quality**: `bash scripts/verify-no-sorry.sh`
7. **NEW - Check for shortcuts**: `lake exe cheap_proofs && python scripts/check_struct_stubs.py`

## 🎯 Types of Contributions

### 🧮 Mathematical Content
- **Formal proofs** of foundation-relative theorems
- **New pathologies** and their characterizations
- **Classical principle requirements** (WLPO, LPO, etc.)
- **Cross-foundation comparisons**

### 🔧 Technical Infrastructure
- **Proof automation** tactics and meta-programs
- **Test coverage** improvements
- **Performance optimizations**
- **CI/CD enhancements**

### 📚 Documentation
- **Mathematical explanations** for complex proofs
- **Tutorials** for newcomers to constructive mathematics
- **Code comments** and API documentation
- **Examples** demonstrating key concepts

## 📋 Development Guidelines

### 🚨 No-Shortcuts Rules (CRITICAL - QA MANDATED)

These rules prevent the deceptive practices identified in QA audit:

#### Golden Rules
1. **Only two acceptable states for any theorem:**
   - Work-in-progress: contains `sorry`
   - Finished: no `sorry` AND uses real mathematical definitions

2. **FORBIDDEN patterns:**
   - ❌ Single-field structures with `Unit` or `True`
   - ❌ Defining `Prop` as `True`
   - ❌ Proofs using only `trivial`, `⟨()⟩`, or pattern matching on Unit
   - ❌ Theorems proved by `exact ⟨()⟩` or similar Unit tricks
   - ❌ Hidden axioms outside `src/Extra/Axioms.lean`

3. **Every finished theorem MUST:**
   - ✅ Depend on non-trivial definitions from the project or mathlib
   - ✅ Have a proof that actually uses mathematical content
   - ✅ Include `-- (LaTeX Theorem X.Y)` reference if from a paper

#### Examples of Violations
```lean
-- ❌ FORBIDDEN: Unit stub
structure BidualGap where
  dummy : Unit

-- ❌ FORBIDDEN: Vacuous proof
theorem main_result : BidualGap := ⟨()⟩

-- ❌ FORBIDDEN: Trivial-only proof
lemma key_lemma : ImportantProperty := by trivial
```

#### Correct Approach
```lean
-- ✅ CORRECT: Real definition or sorry
def BidualGap : Prop := 
  ∃ (X : BanachSpace ℝ), ¬Isometric (canonicalEmbedding X)

-- ✅ CORRECT: Incomplete work marked with sorry
theorem main_result : BidualGap := by
  sorry -- TODO: Implement using Goldstine theorem

-- ✅ CORRECT: Real proof using mathematical content
lemma key_lemma : ImportantProperty := by
  apply fundamental_theorem
  exact mathematical_construction
```

### Code Standards

#### No Sorry Policy (Updated)
- **Zero sorry** allowed in core modules (`Found/`, `Gap2/`, `APFunctor/`, `RNPFunctor/`)
- Test files may use `sorry` for incomplete test cases (clearly marked)
- CI enforces this with `LEAN_ABORT_ON_SORRY=1`
- **NEW**: CI also enforces no cheap proofs via `lake exe cheap_proofs`

#### Style Guidelines
```lean
-- Good: Clear, descriptive names
def Gap₂_requires_WLPO : requiresWLPO Gap₂ := by
  -- proof here

-- Good: Explicit type annotations for public APIs  
def pathologyFunctor (α : Type) : Foundation ⥤ Cat := 
  -- implementation

-- Avoid: Generic names without context
def helper_lemma : Prop := sorry
```

#### Documentation Standards
```lean
/-!
# Module Purpose

Brief description of what this module accomplishes.

## Main Definitions

- `Definition1`: What it does
- `Definition2`: What it does

## Main Theorems

- `theorem_name`: Statement and significance
-/

/-- 
Brief description of the definition.

More detailed explanation if needed, including:
- Mathematical intuition
- Relationship to other definitions
- Usage examples
-/
def important_definition : Type := sorry
```

### Testing Requirements

#### Required Tests
- **Unit tests** for all public functions
- **Property tests** for mathematical statements
- **Integration tests** for functor behavior
- **Migration tests** when refactoring APIs

#### Test Naming
```lean
-- Test file structure
test/
├── FunctorTest.lean          # Core functor behavior
├── NonIdMorphisms.lean       # Morphism handling
├── AllPathologiesTest.lean   # Comprehensive validation
└── Gap2MigrationTest.lean    # Specific migrations
```

### Git Workflow

#### Branch Naming
- `feat/description` - New features
- `fix/description` - Bug fixes  
- `docs/description` - Documentation updates
- `test/description` - Test improvements

#### Commit Messages
```
type(scope): brief description

Longer explanation if needed.

- List specific changes
- Reference issues: Fixes #123
- Note breaking changes

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: [Your Name] <email@example.com>
```

#### Pull Request Process
1. **Create feature branch** from latest `main`
2. **Implement changes** following style guidelines AND no-shortcuts rules
3. **Verify code quality** with our tools:
   ```bash
   # Required checks before PR
   lake build                         # Must build successfully
   LEAN_ABORT_ON_SORRY=1 lake build  # Zero sorry policy
   bash scripts/verify-no-sorry.sh   # CI verification  
   bash scripts/check-no-axioms.sh   # Axiom audit
   
   # NEW QA-MANDATED CHECKS:
   lake exe cheap_proofs              # No Unit/() trick proofs
   python scripts/check_struct_stubs.py  # No Unit stub structures
   python scripts/check_alignment.py     # LaTeX theorems properly formalized
   ```
4. **Run relevant tests**:
   ```bash
   lake exe AllPathologiesTests      # Integration tests
   lake exe Gap2ProofTests           # If modifying Gap₂
   lake exe RNP3ProofTests           # If modifying RNP₃
   ```
5. **Add/update tests** to maintain coverage
6. **Update documentation** if needed
7. **Create PR** with clear description and test plan

## 🚧 Corrective Action Plan (Active)

Due to QA findings, we are implementing a 12-week corrective action plan:

### Current Priorities
1. **Paper 1** (Weeks 1-3): Fix 12 cheap proofs, implement OrdinalRho
2. **Paper 2** (Weeks 4-8): Complete implementation from scratch (currently 0%)
3. **Paper 3** (Weeks 6-12): Complete implementation from scratch (currently <5%)

### How to Contribute
- **Pick a missing module** from [roadmap-corrective-action.md](docs/planning/roadmap-corrective-action.md)
- **Follow the No-Shortcuts Rules** strictly
- **Use `sorry`** for incomplete work - never use Unit tricks
- **Reference LaTeX theorems** with comments like `-- (LaTeX Theorem 3.4)`

### Priority Modules Needing Implementation
- `Cat/OrdinalRho.lean` - Ordinal-valued 2-functor (Paper 1)
- `Analysis/WeakStar.lean` - Weak* topology (Paper 2)
- `Analysis/Goldstine.lean` - Goldstine theorem (Paper 2)
- `Cat/Bicategory/GPS.lean` - Gordon-Power-Street coherence (Paper 3)
- See full list in corrective action roadmap

## 🧪 Testing Your Changes

### Local Testing
```bash
# Full build
lake build

# Run specific tests
lake exe testFunctors
lake exe AllPathologiesTests

# Verify no sorry
bash scripts/verify-no-sorry.sh

# Check style (if linter available)
lake exe lint

# NEW: Run QA-mandated checks
lake exe cheap_proofs
python scripts/check_struct_stubs.py
python scripts/check_alignment.py
```

### CI Testing
All PRs automatically run:
- **Build verification** on Ubuntu with Lean 4.3.0
- **Complete test suite** including new tests
- **Sorry verification** with `LEAN_ABORT_ON_SORRY=1`
- **Dependency checks** for mathlib compatibility
- **NEW**: Cheap proof detection
- **NEW**: Unit stub detection
- **NEW**: LaTeX-Lean alignment verification

## 📖 Mathematical Background

### Key Concepts

#### Foundations
- **BISH**: Bishop's constructive mathematics (no LEM, no AC)
- **ZFC**: Classical set theory with choice
- **Interpretation morphisms**: How foundations relate

#### Pathologies  
- **Gap₂**: Requires WLPO (Weak Limited Principle of Omniscience)
- **AP_Fail₂**: Approximate pathology
- **RNP_Fail₂**: Real number pathology

#### Witness Types
```lean
def WitnessType (α : Type) : Foundation → Type
  | bish => Empty    -- Pathology fails constructively
  | zfc => PUnit     -- Works classically
```

### Proof Patterns

#### Typical Theorem Structure
```lean
theorem pathology_requires_principle (P : PathologyType) : 
  requiresPrinciple P := by
  -- 1. Show witness is empty in BISH
  have h1 : IsEmpty (WitnessType P bish) := by sorry
  -- 2. Show witness is non-empty in ZFC  
  have h2 : Nonempty (WitnessType P zfc) := by sorry
  -- 3. Deduce classical principle needed
  sorry
```

## 🤝 Community Guidelines

### Code Review Process
- **Be constructive**: Focus on improving the code
- **Be specific**: Point to exact lines and suggest alternatives
- **Be patient**: Complex mathematical proofs take time to review
- **Ask questions**: Better to clarify than assume

### PR Approval Criteria (QA Mandated)
PRs will NOT be approved if they contain:
- 🚫 Unit stub structures (`structure X where dummy : Unit`)
- 🚫 Vacuous proofs (`exact ⟨()⟩`, `by trivial` for non-trivial claims)
- 🚫 Theorems that don't use real mathematical definitions
- 🚫 Missing LaTeX cross-references for paper theorems

PRs MUST pass:
- ✅ All standard CI checks
- ✅ `lake exe cheap_proofs` (no output)
- ✅ `python scripts/check_struct_stubs.py`
- ✅ `python scripts/check_alignment.py` (if modifying paper content)

### Communication
- **Issues**: Use for bug reports and feature requests
- **Discussions**: Use for mathematical questions and design discussions  
- **PRs**: Keep focused on single logical changes
- **Commit messages**: Explain the "why" not just the "what"

### Recognition
All contributors are recognized in:
- **AUTHORS.md**: List of project contributors
- **Release notes**: Highlighting major contributions
- **Academic publications**: Co-authorship for significant mathematical contributions

## 🎓 Learning Resources

### Lean 4 Resources
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)

### Constructive Mathematics
- Bishop's "Foundations of Constructive Analysis"
- Bridges & Richman's "Varieties of Constructive Mathematics"
- [Constructive Mathematics Wiki](https://ncatlab.org/nlab/show/constructive+mathematics)

### Category Theory in Lean
- [Mathlib Category Theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory.html)
- ["Category Theory in Context" formalization](https://github.com/rwbarton/lean-category-theory)

## 🆘 Getting Help

### Common Issues

#### Build Failures
```bash
# Clean build
lake clean
lake build

# Update dependencies  
lake update
```

#### Test Failures
```bash
# Run specific test with verbose output
lake exe testFunctors --verbose

# Check for sorry in your changes
grep -r "sorry" YourChangedFiles/
```

#### Proof Stuck
- **Simplify**: Break complex proofs into smaller lemmas
- **Check types**: Use `#check` to verify intermediate steps
- **Use tactics**: `simp`, `ring`, `omega` for automation
- **Ask for help**: Create a discussion with minimal example

### Getting Support
1. **Search existing issues** first
2. **Create a minimal reproducible example**
3. **Provide context**: What are you trying to prove/implement?
4. **Tag appropriately**: `bug`, `question`, `help wanted`, etc.

---

## 📄 License

By contributing, you agree that your contributions will be licensed under the Apache 2.0 License.

---

**Happy formalizing!** 🎉

*Questions? Open an issue or start a discussion. We're here to help!*