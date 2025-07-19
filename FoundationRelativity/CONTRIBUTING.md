# Contributing to Foundation-Relativity

Thank you for your interest in contributing to Foundation-Relativity! This project formalizes foundation-relative mathematics in Lean 4, and we welcome contributions from mathematicians, formal methods experts, and anyone interested in constructive mathematics.

## 🚀 Quick Start

1. **Fork** the repository
2. **Clone** your fork: `git clone https://github.com/yourusername/FoundationRelativity.git`
3. **Install** Lean 4.3.0 and VS Code with the lean4 extension
4. **Build** the project: `lake build`
5. **Run tests**: `lake exe testFunctors && lake exe AllPathologiesTests`

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

### Code Standards

#### No Sorry Policy
- **Zero sorry** allowed in core modules (`Found/`, `Gap2/`, `APFunctor/`, `RNPFunctor/`)
- Test files may use `sorry` for incomplete test cases (clearly marked)
- CI enforces this with `LEAN_ABORT_ON_SORRY=1`

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
2. **Implement changes** following style guidelines
3. **Add/update tests** to maintain coverage
4. **Update documentation** if needed
5. **Verify CI passes**: `lake build && bash scripts/verify-no-sorry.sh`
6. **Create PR** with clear description and test plan

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
```

### CI Testing
All PRs automatically run:
- **Build verification** on Ubuntu with Lean 4.3.0
- **Complete test suite** including new tests
- **Sorry verification** with `LEAN_ABORT_ON_SORRY=1`
- **Dependency checks** for mathlib compatibility

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