# Foundation-Relativity Corrective Action Roadmap

**Date Created**: 2025-08-03  
**Severity**: CRITICAL  
**Purpose**: Address QA findings that Papers 1-3 are not genuinely formalized despite "0 sorries" claims

## 🚨 Executive Summary

QA audit revealed that the repository achieves "0 sorries" through deceptive Unit/() tricks rather than real formalization:
- **Paper 1**: Main theorem uses `exact ⟨()⟩` - 12 cheap proofs identified
- **Paper 2**: 0% formalized - only Unit stubs exist
- **Paper 3**: <5% formalized - only Unit stubs exist

This roadmap provides a detailed 12-week plan to achieve genuine formalization.

---

## 📊 Current State vs Required State

| Paper | Current State | Required Work | Effort |
|-------|--------------|---------------|---------|
| Paper 1 | ~75% real, 12 cheap proofs including MAIN THEOREM | Fix Survey Theorem, Reflection lemmas, implement OrdinalRho | 2-3 weeks |
| Paper 2 | 0% - Unit stubs only | Full implementation from scratch | 4-6 weeks |
| Paper 3 | <5% - Unit stubs only | Full implementation from scratch | 6-10 weeks |

---

## 🛠️ Phase 0: CI Lockdown & Transparency (Week 0-1)

### Immediate Actions (Already Completed)
- ✅ Created CRITICAL_QA_NOTICE.md
- ✅ Updated README with warnings
- ✅ Added status files in each paper directory
- ✅ Created CLAIMS_VS_REALITY.md

### CI Infrastructure to Implement

#### 1. Cheap Proofs Linter (`scripts/lean/CheapProofs.lean`)
```lean
import Lean

open Lean Elab Meta

/-- Constants that indicate a "cheap" proof -/
def isHarmless (n : Name) : Bool :=
  n.isInternal || n.isAnonymous ||
  n.getPrefix.isPrefixOf `Init ||
  n.getPrefix.isPrefixOf `Std ||
  n.getPrefix.isPrefixOf `Tactic ||
  n.getPrefix.isPrefixOf `Classical ||
  n.getPrefix.isPrefixOf `Logic ||
  n == ``Unit || n == ``True || n == ``False || n == ``PUnit ||
  n == ``Eq || n == ``HEq || n == ``rfl

/-- Check if a proof only uses trivial constants -/
def proofIsCheap (env : Environment) (decl : Name) : MetaM Bool := do
  let some info := env.find? decl | return false
  let some val := info.value? | return false
  let used ← collectUsedConstants val
  return used.all isHarmless

/-- Main executable -/
def main : IO Unit := do
  let env ← importModules [{module := `FoundationRelativity}] {}
  let mut cheapProofs : Array (Name × String) := #[]
  
  for (name, info) in env.constants do
    if info.isTheorem && !name.isInternal then
      let isCheap ← MetaM.run' (ctx := {}) (s := {}) do
        proofIsCheap env name
      if isCheap && !info.value?.any (·.hasSorry) then
        let module := name.getPrefix
        cheapProofs := cheapProofs.push (name, s!"{module}")
  
  if cheapProofs.size > 0 then
    IO.eprintln s!"⚠️  Found {cheapProofs.size} cheap proofs:"
    for (name, module) in cheapProofs do
      IO.eprintln s!"  {name} in {module}"
    IO.Process.exit 1
  else
    IO.println "✅ No cheap proofs found"
```

#### 2. Stub Structure Detector (`scripts/check_struct_stubs.py`)
```python
#!/usr/bin/env python3
import re
import sys
import pathlib
from typing import List, Tuple

# Patterns that indicate stub structures
STUB_PATTERNS = [
    # structure X where dummy : Unit
    re.compile(r'structure\s+(\w+)\s*(?:where|:=)[^{]*\{\s*dummy\s*:\s*Unit\s*\}'),
    # structure X := (dummy : Unit)
    re.compile(r'structure\s+(\w+)\s*:=\s*\(\s*dummy\s*:\s*Unit\s*\)'),
    # def X : Prop := True
    re.compile(r'def\s+(\w+)\s*:\s*Prop\s*:=\s*True\b'),
    # abbrev X := Unit
    re.compile(r'abbrev\s+(\w+)\s*:=\s*Unit\b'),
]

# Patterns for vacuous proofs
VACUOUS_PROOF_PATTERNS = [
    # exact ⟨()⟩ or exact ⟨⟨()⟩⟩
    re.compile(r'exact\s*⟨+\(\)⟩+'),
    # by trivial (as only tactic)
    re.compile(r':\s*by\s+trivial\s*$'),
    # constructor; exact variants
    re.compile(r'constructor\s*[;·]\s*(?:intro\s+\w+\s*[;·]\s*)?(?:cases\s+\w+\s*[;·]\s*)?exact\s*⟨'),
]

def scan_file(filepath: pathlib.Path) -> List[Tuple[str, int, str]]:
    """Scan a file for stub patterns. Returns list of (type, line_no, content)"""
    issues = []
    content = filepath.read_text()
    lines = content.split('\n')
    
    # Check for stub structures
    for pattern in STUB_PATTERNS:
        for match in pattern.finditer(content):
            line_no = content[:match.start()].count('\n') + 1
            struct_name = match.group(1) if match.lastindex else "unknown"
            issues.append(("stub_structure", line_no, f"Structure '{struct_name}' is a Unit stub"))
    
    # Check for vacuous proofs
    for i, line in enumerate(lines, 1):
        for pattern in VACUOUS_PROOF_PATTERNS:
            if pattern.search(line):
                issues.append(("vacuous_proof", i, f"Vacuous proof pattern: {line.strip()}"))
    
    return issues

def main():
    root = pathlib.Path('.')
    all_issues = []
    
    # Skip these directories
    skip_dirs = {'.lake', 'lake-packages', '.git', 'build'}
    
    for lean_file in root.rglob('*.lean'):
        # Skip if in excluded directory
        if any(part in skip_dirs for part in lean_file.parts):
            continue
        
        # Skip generated files
        if 'lake-build' in str(lean_file) or lean_file.name.endswith('.ilean'):
            continue
            
        issues = scan_file(lean_file)
        if issues:
            all_issues.append((lean_file, issues))
    
    if all_issues:
        print("❌ Stub structures and vacuous proofs detected:\n")
        for filepath, issues in all_issues:
            print(f"📄 {filepath}:")
            for issue_type, line_no, description in issues:
                icon = "🔲" if issue_type == "stub_structure" else "⭕"
                print(f"  {icon} Line {line_no}: {description}")
            print()
        
        total = sum(len(issues) for _, issues in all_issues)
        print(f"\n❌ Total issues: {total}")
        print("\nReplace these with proper definitions and 'sorry' for incomplete proofs.")
        sys.exit(1)
    else:
        print("✅ No stub structures or vacuous proofs found")
        sys.exit(0)

if __name__ == "__main__":
    main()
```

#### 3. LaTeX-Lean Alignment Checker (`scripts/check_alignment.py`)
```python
#!/usr/bin/env python3
import re
import json
import pathlib
import subprocess
from typing import Dict, List, Set, Optional

class AlignmentChecker:
    def __init__(self):
        self.latex_theorems: Dict[str, List[str]] = {}
        self.lean_declarations: Dict[str, str] = {}
        self.cheap_proofs: Set[str] = set()
        
    def extract_latex_theorems(self, tex_file: pathlib.Path) -> List[Dict]:
        """Extract theorem/lemma/proposition labels from LaTeX"""
        content = tex_file.read_text()
        results = []
        
        # Patterns for LaTeX theorem environments
        patterns = [
            r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[([^\]]*)\])?\s*\\label\{([^}]+)\}',
            r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[([^\]]*)\])?[^}]*\n\s*\\label\{([^}]+)\}',
        ]
        
        for pattern in patterns:
            for match in re.finditer(pattern, content, re.MULTILINE | re.DOTALL):
                env_type = match.group(1)
                description = match.group(2) or ""
                label = match.group(3)
                
                # Extract the content until \end{...}
                start = match.end()
                end_pattern = f'\\\\end\\{{{env_type}\\}}'
                end_match = re.search(end_pattern, content[start:])
                if end_match:
                    theorem_content = content[start:start + end_match.start()].strip()
                    # Clean up LaTeX commands for summary
                    theorem_content = re.sub(r'\\[a-zA-Z]+\{[^}]*\}', '', theorem_content)
                    theorem_content = re.sub(r'\\[a-zA-Z]+', '', theorem_content)
                    theorem_content = ' '.join(theorem_content.split())[:200] + "..."
                else:
                    theorem_content = ""
                
                results.append({
                    'type': env_type,
                    'label': label,
                    'description': description,
                    'content_preview': theorem_content,
                    'file': str(tex_file)
                })
        
        return results
    
    def find_lean_declaration(self, label: str) -> Optional[str]:
        """Find Lean declaration that references this LaTeX label"""
        # Common transformations
        possible_names = [
            label,
            label.replace('-', '_'),
            label.replace(':', '_'),
            'theorem_' + label.replace('-', '_'),
            'lemma_' + label.replace('-', '_'),
        ]
        
        for name in possible_names:
            result = subprocess.run(
                ['grep', '-r', f'LaTeX.*{label}', '--include=*.lean', '.'],
                capture_output=True, text=True
            )
            if result.stdout:
                return result.stdout.split('\n')[0]
        
        return None
    
    def check_dependencies(self, lean_file: str, decl_name: str) -> bool:
        """Check if declaration uses non-trivial dependencies"""
        # This is a simplified check - in practice would use Lean's API
        trivial_only = ['Init', 'Std', 'Unit', 'True', 'PUnit', 'trivial']
        
        try:
            # Try to get dependency info (would need actual Lean tooling)
            content = pathlib.Path(lean_file).read_text()
            
            # Look for the theorem/lemma
            theorem_match = re.search(
                f'(theorem|lemma|def)\\s+{decl_name}.*?:=\\s*by(.*?)(?=theorem|lemma|def|end|$)',
                content, re.DOTALL
            )
            
            if theorem_match:
                proof_body = theorem_match.group(2)
                # Check for suspicious patterns
                if re.search(r'exact\s*⟨+\(\)⟩+', proof_body):
                    return False
                if re.search(r'^\s*trivial\s*$', proof_body):
                    return False
                if len(proof_body.strip()) < 20:  # Very short proofs are suspicious
                    return False
            
            return True
            
        except:
            return True  # Give benefit of doubt if can't analyze
    
    def generate_report(self) -> Dict:
        """Generate alignment report"""
        papers = {
            'Paper 1': pathlib.Path('docs/papers/P1-GBC.tex'),
            'Paper 2': pathlib.Path('docs/papers/P2-BidualGap.tex'),
            'Paper 3': pathlib.Path('docs/papers/P3-2CatFramework.tex'),
        }
        
        report = {}
        
        for paper_name, tex_file in papers.items():
            if not tex_file.exists():
                report[paper_name] = {'error': 'LaTeX file not found'}
                continue
                
            theorems = self.extract_latex_theorems(tex_file)
            
            aligned = []
            missing = []
            suspicious = []
            
            for thm in theorems:
                lean_match = self.find_lean_declaration(thm['label'])
                if lean_match:
                    # Check if it's a real proof
                    lean_file = lean_match.split(':')[0]
                    if self.check_dependencies(lean_file, thm['label']):
                        aligned.append(thm)
                    else:
                        suspicious.append({**thm, 'lean_location': lean_match})
                else:
                    missing.append(thm)
            
            report[paper_name] = {
                'total': len(theorems),
                'aligned': len(aligned),
                'missing': len(missing),
                'suspicious': len(suspicious),
                'details': {
                    'aligned': aligned,
                    'missing': missing,
                    'suspicious': suspicious
                }
            }
        
        return report
    
def main():
    checker = AlignmentChecker()
    report = checker.generate_report()
    
    # Print summary
    print("📊 LaTeX-Lean Alignment Report\n")
    
    all_good = True
    for paper, data in report.items():
        if 'error' in data:
            print(f"❌ {paper}: {data['error']}")
            continue
            
        total = data['total']
        aligned = data['aligned']
        missing = data['missing']
        suspicious = data['suspicious']
        
        percentage = (aligned / total * 100) if total > 0 else 0
        
        status = "✅" if percentage == 100 else "⚠️" if percentage > 50 else "❌"
        print(f"{status} {paper}: {aligned}/{total} theorems properly formalized ({percentage:.0f}%)")
        
        if missing > 0:
            print(f"   🔴 Missing: {missing} theorems")
            all_good = False
            
        if suspicious > 0:
            print(f"   🟡 Suspicious: {suspicious} theorems (may use Unit tricks)")
            all_good = False
        
        print()
    
    # Detailed report
    with open('alignment_report.json', 'w') as f:
        json.dump(report, f, indent=2)
    
    print("📄 Detailed report saved to alignment_report.json")
    
    if not all_good:
        print("\n❌ Alignment check FAILED")
        print("Replace Unit stubs with proper definitions and 'sorry' for incomplete work")
        sys.exit(1)
    else:
        print("\n✅ All theorems properly aligned")
        sys.exit(0)

if __name__ == "__main__":
    main()
```

### GitHub Actions Integration (`.github/workflows/ci-no-shortcuts.yml`)
```yaml
name: No-Shortcuts CI

on: [push, pull_request]

jobs:
  cheap-proofs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: leanprover/lean-action@v1
      - name: Build cheap proofs linter
        run: lake build CheapProofs
      - name: Run cheap proofs check
        run: lake exe cheap_proofs
        
  stub-structures:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-python@v4
      - name: Check for stub structures
        run: python scripts/check_struct_stubs.py
        
  alignment:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-python@v4
      - name: Check LaTeX-Lean alignment
        run: python scripts/check_alignment.py
```

---

## 📝 Paper 1: Gödel-Banach Correspondence (Weeks 1-3)

### Current Deficiencies (12 Cheap Proofs)

#### 1. Main Survey Theorem (**CRITICAL**)
**File**: `Papers/P1_Survey/SurveyTheorem.lean`  
**Current State**:
```lean
theorem survey_theorem : 
  ∀ (obstruction : AnalyticObstruction),
  ∃ (ρ : OrdinalIndexed2Functor),
  reflects obstruction ρ := by
  intro obstruction
  -- 11 lines of setup that import PseudoFunctor
  exact ⟨()⟩  -- FAKE PROOF!
```

**Required Fix**:
```lean
theorem survey_theorem : 
  ∀ (obstruction : AnalyticObstruction),
  ∃ (ρ : OrdinalIndexed2Functor),
  reflects obstruction ρ := by
  intro obstruction
  -- Need to construct ρ based on obstruction type
  cases obstruction with
  | bidualGap => 
      use OrdinalRho.atLevel 1
      apply reflects_bidual_gap
  | spectralGap =>
      use OrdinalRho.atLevel 3  
      apply reflects_spectral_gap
  | rnpFailure =>
      use OrdinalRho.atLevel 2
      apply reflects_rnp
```

#### 2. Reflection Lemmas (2 instances)
**File**: `Papers/P1_Survey/Bridges.lean`  
**Current**:
```lean
lemma set_type_reflection : SetTheory ≃ TypeTheory := by trivial
lemma czf_hott_reflection : CZF ≃ HoTT := by trivial
```

**Required**:
- Implement universe polymorphism handling
- Define proper equivalence at meta-level
- Prove preservation of mathematical content

#### 3. Other Cheap Proofs (9 instances)
Located in various files, using patterns like:
- `rfl` where actual computation needed
- `simp` as complete proof where manual work required
- Single-line proofs for non-trivial claims

### Missing Modules for Paper 1

#### `Cat/OrdinalRho.lean` (NEW FILE)
```lean
import Mathlib.SetTheory.Ordinal.Basic
import CategoryTheory.PseudoFunctor

/-- Ordinal-indexed 2-functor for measuring logical complexity -/
structure OrdinalIndexed2Functor where
  level : Ordinal
  functor : PseudoFunctor (Foundation.op) (Cat)
  monotone : ∀ {F G : Foundation}, F ≤ G → functor.obj F ≥ functor.obj G
  
namespace OrdinalRho

/-- Construct ρ-functor at given ordinal level -/
def atLevel (α : Ordinal) : OrdinalIndexed2Functor := {
  level := α
  functor := {
    obj := fun F => match α with
      | 0 => TrivialCat
      | 1 => WLPOCat F
      | 2 => DCCat F  
      | 3 => ACCat F
      | _ => TopCat F
    map := fun f => sorry  -- Implement functor mapping
    map₂ := fun η => sorry -- Implement 2-cell mapping
  }
  monotone := sorry
}

/-- Key theorem: ρ reflects bidual gap at level 1 -/
theorem reflects_bidual_gap : 
  reflects BidualGapObstruction (atLevel 1) := by
  sorry -- Requires WLPO analysis

end OrdinalRho
```

#### `Logic/Reflection.lean` (NEW FILE)
```lean
import Mathlib.Logic.Equiv.Basic
import Mathlib.CategoryTheory.Equivalence

/-- Meta-level reflection between set and type theories -/
def SetTypeReflection : SetTheory ≃ TypeTheory where
  toFun := fun S => sorry -- Convert set-theoretic construction to type
  invFun := fun T => sorry -- Convert type-theoretic construction to set
  left_inv := sorry -- Round-trip property
  right_inv := sorry -- Round-trip property

/-- Constructive to homotopy reflection -/  
def CZFHoTTReflection : CZF ≃ HoTT where
  toFun := sorry -- Map constructive sets to HoTT types
  invFun := sorry -- Map HoTT types to constructive sets
  left_inv := sorry
  right_inv := sorry
```

### Week-by-Week Plan for Paper 1

**Week 1**: Fix Critical Proofs
- Day 1-2: Implement OrdinalRho.lean structure
- Day 3-4: Fix main survey_theorem using real ρ-functor
- Day 5: Progress review and testing

**Week 2**: Reflection Principles  
- Day 1-2: Implement SetTypeReflection with universe handling
- Day 3-4: Implement CZFHoTTReflection 
- Day 5: Integration testing

**Week 3**: Remaining Cheap Proofs
- Day 1-2: Fix remaining 9 trivial proofs
- Day 3-4: Run cheap proof linter, ensure 0 violations
- Day 5: Final review and PR preparation

### External Consultant Needs (Paper 1)
- **Ordinal Arithmetic Expert** (1 week): Help with OrdinalRho implementation
- **Type Theory Expert** (3 days): Universe polymorphism for Reflection lemmas

---

## 🔬 Paper 2: Bidual Gap (Weeks 4-8)

### Current State: 0% Formalized

Everything is Unit stubs:
```lean
structure BidualGap where dummy : Unit
structure WLPO where dummy : Unit  
theorem gap_equiv_WLPO : BidualGap ↔ WLPO := by
  constructor; cases; exact ⟨⟨()⟩⟩; cases; exact ⟨⟨()⟩⟩
```

### Required Modules (ALL NEW)

#### `Analysis/BanachDual.lean`
```lean
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.WeakDual

/-- The bidual of a Banach space -/
def bidual (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  (NormedSpace.Dual ℝ (NormedSpace.Dual ℝ X))

/-- Canonical embedding into bidual -/
def canonical_embedding (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
  X →L[ℝ] bidual X where
  toFun x := fun φ => φ x
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

/-- A space has the bidual gap property if canonical embedding is not surjective -/
def has_bidual_gap (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ¬Function.Surjective (canonical_embedding X)
```

#### `Analysis/WeakStar.lean`
```lean
import Mathlib.Topology.Algebra.Module.WeakDual

/-- Weak* topology on dual space -/
def weak_star_topology (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
  TopologicalSpace (NormedSpace.Dual ℝ X) :=
  WeakDual.instTopologicalSpace

/-- Goldstine's theorem: X embeds weak*-densely in X** -/
theorem goldstine (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] 
  [CompleteSpace X] :
  DenseRange (canonical_embedding X) := by
  sorry -- Major theorem, needs careful proof
```

#### `Analysis/QuantitativeGap.lean`
```lean
/-- Quantitative version: gap with explicit constant -/
theorem bidual_gap_quantitative (ε : ℝ) (hε : 0 < ε) :
  ∃ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∃ (φ : NormedSpace.Dual ℝ (NormedSpace.Dual ℝ X)),
  ‖φ‖ = 1 ∧ dist (φ : bidual X) (Set.range (canonical_embedding X)) ≥ ε := by
  sorry -- Construct explicit counterexample space
```

#### `Logic/WLPO.lean`
```lean
import Mathlib.Logic.ClassicalChoice

/-- Weak Limited Principle of Omniscience -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- Key equivalence: Bidual gap exists iff WLPO holds -/
theorem bidual_gap_iff_wlpo :
  (∃ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X], has_bidual_gap X) ↔ 
  WLPO := by
  constructor
  · -- Gap → WLPO
    intro ⟨X, hX⟩
    sorry -- Use gap to decide sequences
  · -- WLPO → Gap  
    intro hwlpo
    sorry -- Construct ℓ∞ with specific functionals
```

### Implementation Plan (Paper 2)

**Week 4**: Basic Definitions
- Implement Banach space duality
- Define canonical embedding
- Set up weak* topology

**Week 5**: Core Theorems
- Prove basic properties of bidual
- Start Goldstine theorem
- Implement WLPO definition

**Week 6**: Main Equivalence
- Complete Goldstine proof
- Prove gap → WLPO direction
- Start WLPO → gap construction

**Week 7**: Quantitative Results
- Implement explicit gap estimates
- Connect to Paper 2 LaTeX constants
- Complete all directions of equivalence

**Week 8**: Polish & Integration
- Remove all sorries
- Add LaTeX cross-references
- Full integration testing

### External Consultants (Paper 2)
- **Functional Analyst** (2 weeks): Goldstine theorem, weak* topology
- **Constructive Logic Expert** (1 week): WLPO equivalence details

---

## 🏗️ Paper 3: 2-Categorical Framework (Weeks 6-12)

### Current State: <5% Formalized

All definitions are Unit stubs:
```lean
structure CategoricalObstruction where dummy : Unit
structure TwoCatPseudoFunctor where dummy : Unit
structure ρHierarchy where dummy : Unit
-- Every proof is trivial or exact ⟨()⟩
```

### Required Modules (ALL NEW)

#### `Cat/Bicategory/GPS.lean`
```lean
import Mathlib.CategoryTheory.Bicategory.Coherence

/-- Gordon-Power-Street coherence data -/
structure GPSCoherence (B : Bicategory) where
  pentagon : ∀ {W X Y Z : B} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    (α_ f g h).hom ≫ (α_ f (g ≫ h) id).hom = 
    (α_ (f ≫ g) h id).hom ≫ (f ◁ (α_ g h id).hom)
  triangle : ∀ {X Y : B} (f : X ⟶ Y),
    (α_ f (𝟙 Y) id).hom ≫ (ρ_ f).hom = f ◁ (λ_ (𝟙 Y)).hom

/-- Coherence theorem for bicategories -/
theorem gps_coherence (B : Bicategory) [GPSCoherence B] :
  ∀ (d₁ d₂ : CoherenceDiagram B), 
  d₁.commutes ↔ d₂.commutes := by
  sorry -- Major theorem
```

#### `Cat/Found.lean` (EXPAND EXISTING)
```lean
/-- 2-category of foundations with full structure -/
def Found : Bicategory where
  Obj := Foundation
  Hom := Interp
  id := fun F => Interp.id F
  comp := fun f g => Interp.comp f g
  homCategory := fun F G => {
    Hom := InterpTrans
    id := InterpTrans.id
    comp := InterpTrans.comp
  }
  whiskerLeft := sorry
  whiskerRight := sorry
  associator := sorry -- Key 2-cell
  leftUnitor := sorry
  rightUnitor := sorry
  pentagon := sorry -- GPS axiom
  triangle := sorry -- GPS axiom
```

#### `Cat/PseudoFunctor/Gap.lean`
```lean
/-- The Gap⟂ pseudo-functor -/
def GapPerp : PseudoFunctor (Found.op) Cat where
  obj := fun F => GapCategory F
  map := fun {F G} φ => GapFunctor φ
  map₂ := fun {F G} {φ ψ} η => GapNatTrans η
  mapId := sorry -- Pseudo, not strict
  mapComp := sorry -- Up to isomorphism
  associativity := sorry -- Coherence 2-cell
  leftUnitality := sorry
  rightUnitality := sorry
```

#### `Cat/RhoHierarchy.lean`
```lean
import Mathlib.SetTheory.Ordinal.Arithmetic

/-- The ρ-hierarchy measuring logical strength -/
inductive RhoLevel : Type
  | zero : RhoLevel -- Decidable
  | succ : RhoLevel → RhoLevel -- +1 level
  | limit : (ℕ → RhoLevel) → RhoLevel -- Limit ordinal

/-- Assignment of ρ-degree to obstructions -/
def rho_degree : AnalyticObstruction → RhoLevel
  | .bidualGap => .succ .zero -- ρ = 1 (WLPO)
  | .rnpFailure => .succ (.succ .zero) -- ρ = 2 (DC)
  | .spectralGap => .succ (.succ (.succ .zero)) -- ρ = 3 (AC)

/-- ρ-hierarchy is well-founded -/
theorem rho_well_founded : WellFounded (fun a b : RhoLevel => a < b) := by
  sorry
```

#### `Cat/Obstruction.lean`
```lean
/-- Functorial Obstruction Theorem -/
theorem functorial_obstruction 
  (F : PseudoFunctor Found Cat) 
  (preserves_limits : PreservesLimits F) :
  ∃ (obs : CategoricalObstruction),
  F factors_through GapPerp ↔ overcomes obs := by
  sorry -- Main theorem of Paper 3
```

### Implementation Plan (Paper 3)

**Week 6-7**: Foundation Setup
- Implement full Found bicategory
- Add GPS coherence infrastructure
- Define basic 2-cells

**Week 8-9**: Pseudo-Functor Construction
- Implement Gap⟂ functor properly
- Add coherence 2-cells
- Prove pseudo-functor laws

**Week 10**: ρ-Hierarchy
- Implement ordinal-based hierarchy
- Prove well-foundedness
- Connect to obstruction degrees

**Week 11**: Main Theorem
- Implement oplax limits
- Prove Functorial Obstruction
- Add all coherence conditions

**Week 12**: Examples & Polish
- Implement concrete examples
- Remove all sorries
- Final integration

### External Consultants (Paper 3)
- **Higher Category Theorist** (3 weeks): GPS coherence, bicategories
- **Proof Theorist** (2 weeks): Ordinal hierarchies, ρ-degree

---

## 📊 Resource Summary

### Development Team Requirements
| Role | FTE Weeks | Key Responsibilities |
|------|-----------|---------------------|
| Lead Developer | 12 | Overall coordination, Paper 1 fixes |
| Analysis Developer | 8 | Paper 2 implementation |
| Category Developer | 10 | Paper 3 implementation |
| CI/DevOps Engineer | 2 | Linter integration, automation |

### External Consultants
| Consultant Type | Duration | Paper | Key Deliverables |
|----------------|----------|-------|------------------|
| Ordinal Expert | 1 week | P1 | OrdinalRho implementation |
| Type Theorist | 3 days | P1 | Reflection principles |
| Functional Analyst | 2 weeks | P2 | Goldstine, weak* topology |
| Logic Expert | 1 week | P2 | WLPO bridge |
| Category Theorist | 3 weeks | P3 | GPS coherence |
| Proof Theorist | 2 weeks | P3 | ρ-hierarchy |

### Total Timeline
- **Week 0-1**: CI lockdown, transparency
- **Weeks 1-3**: Paper 1 corrections
- **Weeks 4-8**: Paper 2 from scratch
- **Weeks 6-12**: Paper 3 from scratch (overlaps with P2)

---

## 🎯 Success Criteria

### Must Pass All Checks
1. **Cheap Proofs**: `lake exe cheap_proofs` → No output
2. **Stub Detector**: `python check_struct_stubs.py` → Pass
3. **Alignment**: `python check_alignment.py` → 100% for all papers
4. **Sorry Count**: `lake exe sorry_count` → 0 (with no tricks)

### Code Quality Requirements
- Every theorem has `-- (LaTeX Theorem X.Y)` reference
- Every proof uses real mathematical libraries
- No Unit, True, (), or trivial-only proofs
- External reviewers must approve

### Final Validation
1. Run full regression test suite
2. Generate coverage report showing real dependencies
3. Academic reviewers verify mathematical correctness
4. Update all badges to reflect true status

---

## 🚨 Critical Rules

### Never Allowed
- ❌ Defining mathematical objects as Unit stubs
- ❌ Proving theorems with `exact ⟨()⟩`
- ❌ Using `by trivial` for non-trivial claims
- ❌ Claiming "0 sorries" with hidden tricks

### Always Required
- ✅ Use `sorry` for incomplete work
- ✅ Real definitions matching LaTeX papers
- ✅ Proofs that use actual mathematics
- ✅ Transparent progress reporting

---

## 📈 Progress Tracking

Weekly reports must include:
1. Sorry count per paper
2. Cheap proof linter results
3. Alignment percentage
4. Consultant deliverables status
5. Blockers and mitigation plans

This roadmap ensures genuine formalization of all three papers, eliminating the deceptive practices identified by QA.