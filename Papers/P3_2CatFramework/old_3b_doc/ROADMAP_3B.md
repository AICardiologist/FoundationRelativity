# Paper 3B Lean Implementation Roadmap

## Overview
Paper 3B focuses on proof-theoretic applications of the AxCal framework, specifically modeling consistency and reflection hierarchies with formal collisions between ladders.

## Current Status (January 29, 2025)
- ✅ Paper 3B LaTeX draft completed with improved classicality ladder
- ✅ Core P4_Meta infrastructure already in place (Theory, Extend, HeightCertificate)
- 🔸 Need to add proof-theoretic specific modules

## Implementation Phases

### Phase 1: Core Infrastructure (Week 1)
**Goal**: Establish schematic proof theory foundations

#### ProofTheory/Core.lean
```lean
-- Basic theory structure (already exists in Meta_Signature.lean)
structure Theory where
  Provable : Formula → Prop

-- Typeclasses for arithmetization
class HasSigma1Provability (T : Theory) where
  provable_code : ℕ → Prop
  is_sigma1 : ∀ n, Sigma1 (provable_code n)

class HasDerivability (T : Theory) where
  -- HBL conditions
  derivability1 : ∀ φ, T.Provable φ → T.Provable (ProvFormula T φ)
  derivability2 : ∀ φ ψ, T.Provable (ProvFormula T (φ → ψ) → 
                          ProvFormula T φ → ProvFormula T ψ)
  derivability3 : ∀ φ, T.Provable (ProvFormula T φ → 
                       ProvFormula T (ProvFormula T φ))
```

#### ProofTheory/Reflection.lean
```lean
-- RFN definition
def RFN_Sigma1 (T : Theory) : Prop :=
  ∀ φ, Sigma1 φ → T.Provable φ → TrueInN φ

-- Main collision theorem (sorry-free)
theorem RFN_implies_Con (Text Tbase : Theory) 
  [HasRFN_Sigma1 Text Tbase] : Con Tbase := by
  intro h_provable_bot
  have h_true_bot := reflect Bot Sigma1_Bot h_provable_bot
  exact Bot_is_FalseInN h_true_bot
```

### Phase 2: Ladder Constructions (Week 2)
**Goal**: Define the three main ladders with proper limit behavior

#### ProofTheory/Progressions.lean
```lean
-- Classicality ladder
def ClassicalityLadder : ℕ → Theory
  | 0 => HA
  | n+1 => Extend (ClassicalityLadder n) (EM_Sigma n)

-- Consistency ladder  
def ConsistencyLadder (B : Theory) : ℕ → Theory
  | 0 => B
  | n+1 => Extend (ConsistencyLadder B n) (Con (ConsistencyLadder B n))

-- Reflection ladder
def ReflectionLadder (B : Theory) : ℕ → Theory
  | 0 => B
  | n+1 => Extend (ReflectionLadder B n) (RFN_Sigma1 (ReflectionLadder B n))

-- Limit construction
def ExtendOmega (B : Theory) (step : ℕ → Formula) : Theory :=
  { Provable := fun φ => ∃ n, (ExtendIter B step n).Provable φ }

-- Ladder morphism structure
structure LadderMorphism (L1 L2 : ℕ → Theory) where
  map : ℕ → ℕ
  preserves : ∀ n φ, (L1 n).Provable φ → (L2 (map n)).Provable φ
```

### Phase 3: Height Certificates (Week 3)
**Goal**: Prove upper bounds, axiomatize lower bounds

#### ProofTheory/Heights.lean
```lean
-- Upper bounds (provable)
theorem con_height_upper (B : Theory) [HBL B] :
  (ConsistencyLadder B 1).Provable (Con B) := by
  simp [ConsistencyLadder, Extend]

theorem godel_height_upper (B : Theory) [HBL B] :
  (ConsistencyLadder B 1).Provable (GodelSentence B) := by
  apply con_implies_godel
  exact con_height_upper B

-- Lower bounds (axiomatized with provenance)
/-- G2: Gödel's second incompleteness theorem (classical) -/
axiom G2_lower (B : Theory) [Consistent B] [HBL B] :
  ¬(B.Provable (Con B))

/-- G1: Gödel's first incompleteness theorem (classical) -/
axiom G1_lower (B : Theory) [Consistent B] [HBL B] :
  ¬(B.Provable (GodelSentence B))

-- Height certificates
def con_height_cert (B : Theory) [HBL B] [Consistent B] :
  HeightCertificate B (consSteps B) (Con B) :=
{ n := 1
, upper := con_height_upper B
, note := "Upper: definitional; Lower: G2 (classical)" }
```

### Phase 4: Collision Theorem (Week 4)
**Goal**: Formalize the morphism between reflection and consistency

#### ProofTheory/Collisions.lean
```lean
-- The collision morphism
def reflection_to_consistency : LadderMorphism ReflectionLadder ConsistencyLadder :=
{ map := fun n => n + 1
, preserves := by
    intro n φ h
    -- At R_{n+1} we have RFN(R_n)
    -- By RFN_implies_Con, this gives Con(R_n)
    sorry -- TODO: complete proof }

-- Main collision theorem
theorem collision_theorem (B : Theory) [classes] (n : ℕ) :
  (ReflectionLadder B (n+1)).Provable (Con (ReflectionLadder B n)) := by
  apply RFN_implies_Con
```

### Phase 5: Limit Behavior (Week 5)
**Goal**: Formalize ω vs ω+1 distinction

#### ProofTheory/Limits.lean
```lean
-- Instancewise vs universal at ω
theorem omega_instancewise (B : Theory) (n : ℕ) :
  (ExtendOmega B consSteps).Provable (Con (ConsistencyLadder B n)) := by
  use n + 1
  simp [ConsistencyLadder]

theorem omega_not_universal (B : Theory) [classes] :
  ¬(ExtendOmega B consSteps).Provable (∀ n, Con (ConsistencyLadder B n)) := by
  sorry -- Requires ordinal analysis

theorem omega_plus_one_universal (B : Theory) [classes] :
  (Extend (ExtendOmega B consSteps) (Con (ExtendOmega B consSteps))).Provable
    (∀ n, Con (ConsistencyLadder B n)) := by
  sorry -- Standard proof-theoretic argument
```

### Phase 6: Testing & API (Week 6)
**Goal**: Comprehensive tests and ergonomic API

#### test/ProofTheory_Sanity.lean
```lean
-- Test basic constructions
example : ConsistencyLadder PA 0 = PA := rfl
example : (ConsistencyLadder PA 1).Provable (Con PA) := by simp

-- Test collision
example [classes] : (ReflectionLadder PA 1).Provable (Con PA) := 
  collision_theorem PA 0

-- Test height certificates
example [classes] : (con_height_cert PA).n = 1 := rfl
```

## Key Design Decisions

1. **Schematic Approach**: Avoid deep syntax encoding, use typeclasses for capabilities
2. **Named Axioms**: Classical lower bounds (G1, G2) as axioms with provenance notes
3. **Certified Upper Bounds**: All upper bounds proved within Lean
4. **Simp-friendly API**: Extensive @[simp] lemmas for automation

## Dependencies
- Existing P4_Meta framework (Theory, Extend, HeightCertificate)
- No external mathlib dependencies beyond what's already used

## Success Criteria
- [ ] RFN → Con theorem proved sorry-free
- [ ] All upper bounds certified
- [ ] Collision morphism formalized
- [ ] Comprehensive test coverage
- [ ] Clean API with simp automation

## Timeline
- **Weeks 1-2**: Core infrastructure and ladders
- **Weeks 3-4**: Heights and collision theorem
- **Week 5**: Limit behavior
- **Week 6**: Testing and polish

## Notes
- This implementation complements Paper 3A (analysis focus) with proof theory
- Maintains the same schematic style for consistency
- All classical results properly attributed via provenance notes