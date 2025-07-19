# Foundation-Relativity Developer Guide

## Adding a New Pathology

To add a new pathology functor, you need approximately 40 lines of code:

### 1. Define Your Pathology Type (5 lines)

```lean
-- NewPathology/Types.lean
structure MyPathology where
  -- pathology-specific data
```

### 2. Implement PathologyWitness Instance (15 lines)

```lean
-- NewPathology/Witness.lean
import Found.Witness
import NewPathology.Types

instance : PathologyWitness MyPathology where
  witness := fun
    | bish => Empty    -- No constructive witnesses (ρ > 0)
    | zfc  => PUnit    -- Classical witnesses exist (ρ = 0)
  witness_bish_empty := inferInstance
  witness_zfc_inhabited := inferInstance
```

### 3. Define the Functor (20 lines)

```lean
-- NewPathology/Functor.lean
import Found.Lift
import NewPathology.Witness

open CategoryTheory Foundation

def MyPathology_Functor : Foundation ⥤ Cat where
  obj F := Cat.of (Discrete (PathologyWitness.witness MyPathology F))
  map φ := liftTransport φ
  map_id := liftTransport_id
  map_comp := liftTransport_comp
```

### 4. Add Tests

```lean
-- test/MyPathologyTest.lean
import NewPathology.Functor

#eval MyPathology_Functor.obj bish  -- Empty category
#eval MyPathology_Functor.obj zfc   -- Singleton category
```

## ρ-Degree Guidelines

- **ρ = 0**: Classical theorems (work in ZFC)
- **ρ = 1**: Require WLPO (Weak Limited Principle of Omniscience)
- **ρ = 2**: Require DC_ω (Dependent Choice for sequences)
- **ρ = 3+**: Higher computational principles (research frontier)

## CI and Testing

Before submitting:
1. Run `lake build` locally
2. Ensure `scripts/verify-no-sorry.sh` passes
3. Add your pathology to `PathologyTests.lean`
4. Update `README.md` with a description of your pathology

## Code Style

- Use descriptive names (e.g., `BanachTarski_Fail₃` not `BT3`)
- Document the classical theorem that fails constructively
- Include citations to relevant papers
- Keep witness definitions simple (Empty or PUnit variants)