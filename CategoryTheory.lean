-- Core 2-categorical infrastructure  
import Papers.P3_2CatFramework.Core.FoundationBasic
import CategoryTheory.GapFunctor  
import CategoryTheory.Obstruction

/-!
# CategoryTheory Module - Sprint 42 2-Categorical Layer

This module implements the 2-categorical framework for foundation-relative mathematics,
providing the infrastructure for systematic analysis of mathematical pathologies
across different foundational systems.

## Architecture

```
CategoryTheory/
├── Found.lean          -- 2-category of foundations
├── GapFunctor.lean     -- Contravariant 2-functor Gap⟂  
└── Obstruction.lean    -- Functorial-Obstruction theorem
```

## Mathematical Content

- **2-Category of Foundations**: Objects (BISH, ZFC, etc.), 1-cells (interpretations), 2-cells (coherence)
- **Gap⟂ Functor**: Contravariant mapping Foundation^op × Foundation → Cat
- **Obstruction Theory**: Systematic classification of foundation-relative pathologies

## Sprint 42 Goals

1. **Repository Structure** ✅: CategoryTheory/ directory with core modules
2. **Minimal Compilation**: All files compile without errors
3. **Integration**: Proper lakefile.lean wiring for build system
4. **Documentation**: Clear module structure and mathematical content
5. **CI Integration**: Green builds with new CategoryTheory infrastructure

This provides the foundation for implementing the full 2-categorical theory
from Paul Lee's research papers, particularly Paper 3 on 2-categorical frameworks.
-/

-- Export the new Foundation types globally  
-- Note: These are available directly since FoundationBasic doesn't use a namespace