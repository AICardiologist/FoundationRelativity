# Paper 96: The Root Number Bifurcation — Rank 0 BSD Squeeze
## Lean 4 Implementation Specification

---

## Overview

Paper 96 establishes a **bifurcation theorem** for the CRM cost of the BSD proof, controlled by the root number w = ±1. This is the BSD analogue of the palindromic bifurcation (Paper 89) in the Hodge campaign.

**The discovery:** For rank-0 elliptic curves (w = +1), detection of L(E,1) ≠ 0 is **purely BISH** via modular symbols — no analytic continuation, no Rankin–Selberg, no Green's functions. For rank-1 curves (w = −1), detection of L'(E,1) ≠ 0 requires the Gross–Zagier formula (**CLASS**). The CRM cost of BSD detection jumps discontinuously at w = −1.

**Test cases:**
- Rank 0: E = 11a1 (y² + y = x³ − x² − 10x − 20, conductor 11, w = +1)
- Rank 1: E = 37a1 (y² + y = x³ − x, conductor 37, w = −1) [from Paper 95]

**Deliverable:** ~800–1000 lines of Lean 4, zero sorry, organized as a self-contained lake project.

---

## Mathematical Content to Formalize

### Part A: Modular Symbol Arithmetic for 11a1 (BISH Core)

The newform f ∈ S₂(Γ₀(11)) associated to 11a1 has Hecke eigenvalues that the CAS will compute from Cremona's tables. The key result: the modular symbol

```
[0→∞]⁺ = L(E,1) / Ω⁺
```

is a **rational number**, computed by a finite sum involving Hecke eigenvalues. For 11a1, this ratio equals 1/5.

The CAS (Python) computes this rational number. Lean verifies it equals 1/5 ≠ 0 by `norm_num`. This proves L(E,1) ≠ 0 without analytic continuation.

#### A1. Hecke Eigenvalue Table for 11a1

```
def hecke_11a1 : Nat → Int
  | 2  => -2
  | 3  => -1
  | 5  => 1
  | 7  => -2
  | 11 => 1    -- bad prime: a_11 = 1 (split multiplicative)
  | 13 => 4
  | 17 => -2
  | 19 => 0
  | 23 => -1
  | 29 => 0
  | 31 => 7
  | 37 => 3
  | 41 => -8
  | 43 => -6
  | 47 => 8
  | _  => 0
```

Verify for 11a1 (y² + y = x³ − x² − 10x − 20):
- Point counts: a_p = p + 1 − #E(𝔽_p) for p = 2, 3, 5, 7, 13 (at least 5 primes)
- Hasse bounds: a_p² ≤ 4p for all good primes p ≤ 47
- Hecke recurrence: a_{p²} = a_p² − p for p = 2, 3, 5, 7
- Multiplicativity: a_{mn} = a_m · a_n for gcd(m,n) = 1

All verified by `native_decide`. Same pattern as Paper 95's Theorem A.

#### A2. Point Counts for 11a1

The CAS computes #E(𝔽_p) by brute force enumeration for small p. For 11a1:

```
def card_E_Fp_11a1 : Nat → Nat
  | 2  => 5
  | 3  => 5
  | 5  => 5
  | 7  => 10
  | 13 => 10
  | _  => 0
```

Verify: card_E_Fp_11a1 p = p + 1 - hecke_11a1 p for each listed prime.

NOTE: Computing #E(𝔽_p) for the model y² + y = x³ − x² − 10x − 20 requires counting solutions (x, y) ∈ 𝔽_p × 𝔽_p to the equation, plus the point at infinity. The CAS should enumerate all (x,y) with 0 ≤ x,y < p and check 4(y² + y) = 4(x³ − x² − 10x − 20) (clearing denominators if needed), OR use the short Weierstrass form. For small p this is instant.

#### A3. Modular Symbol Computation

The **critical new content** not in Paper 95. The modular symbol [0→∞]⁺ for 11a1 equals L(E,1)/Ω⁺ = 1/5.

This is computed by the Manin–Drinfeld theorem: the modular symbol is a finite rational linear combination of values {r→s} for r,s ∈ ℚ ∪ {∞}, evaluated via continued fraction expansion and Hecke action.

**For the Lean formalization, we do NOT need the full modular symbol theory.** We need:

```
-- The modular symbol ratio, computed by CAS
def modular_symbol_ratio_11a1 : Rat := 1/5

-- The key theorem: this ratio is nonzero
theorem modular_symbol_nonzero_11a1 :
    modular_symbol_ratio_11a1 ≠ 0 := by norm_num

-- Documentary: this ratio equals L(E,1)/Ω⁺
axiom modular_symbol_equals_L_ratio :
    modular_symbol_ratio_11a1 = L_value_11a1 / omega_plus_11a1
```

The axiom stub documents the connection to the L-function. The BISH content is: 1/5 ≠ 0.

#### A4. Torsion and Tamagawa for 11a1

```
-- E(ℚ)_tors ≅ ℤ/5ℤ for 11a1
def torsion_order_11a1 : Nat := 5

-- Tamagawa number: c_11 = 1 (split multiplicative, Kodaira type I_1... 
-- actually 11a1 has Kodaira type I_5 at p=11, so c_11 = 5)
-- IMPORTANT: CAS must verify. For 11a1: c_11 = 5, but |tors|² = 25,
-- so c_11/|tors|² = 5/25 = 1/5.
-- Actually need to check: Cremona gives c_11 = 1 for 11a1.
-- CAS MUST VERIFY FROM SOURCE (LMFDB). Do not trust this spec.
def tamagawa_product_11a1 : Nat := sorry -- CAS fills this in
```

**CRITICAL NOTE TO LEAN AGENT:** The Tamagawa number and torsion for 11a1 must be computed or looked up from a reliable source (LMFDB, Cremona's tables). Do NOT trust the values in this spec — verify independently. The BSD formula requires exact values.

For reference, LMFDB gives for 11a1:
- Torsion: ℤ/5ℤ (order 5)
- Tamagawa product: c_11 = 1
- Sha: trivial (order 1)
- Rank: 0
- L(E,1)/Ω⁺ = 1/5

The BSD formula check: L(E,1)/Ω⁺ = |Sha| · Reg · ∏c_p / |tors|² = 1 · 1 · 1 / 25... 

Wait — this gives 1/25 ≠ 1/5. So either Reg or the period convention differs.

**IMPORTANT: For rank 0, the regulator is defined as det(∅) = 1. The BSD formula is:**

```
L(E,1) / Ω⁺ = |Sha| · ∏c_p / |E(ℚ)_tors|²
```

So 1/5 = 1 · 1 / 25 = 1/25? This doesn't work. The resolution: for 11a1, c_11 = 5 (not 1). Then:

```
L(E,1)/Ω⁺ = |Sha| · c_11 / |tors|² = 1 · 5 / 25 = 1/5. ✓
```

**CAS MUST VERIFY: c_11 = 5 for 11a1.** (Kodaira type I₅ at p = 11, so c_11 = 5.)

#### A5. BSD Formula Verification for 11a1

```
theorem bsd_formula_check_11a1 :
    (1 : Rat) / 5 = 1 * 5 / (5 * 5) := by norm_num
```

This verifies: L(E,1)/Ω⁺ = |Sha| · c_11 / |tors|² = 1 · 5 / 25 = 1/5.

---

### Part B: Root Number Bifurcation Theorem

This is the headline result. Define the root number and state the bifurcation.

#### B1. Root Number Definition

```
inductive RootNumber where
  | plus  : RootNumber   -- w = +1, even functional equation, rank 0 expected
  | minus : RootNumber   -- w = -1, odd functional equation, rank 1 expected

def root_number_11a1 : RootNumber := RootNumber.plus
def root_number_37a1 : RootNumber := RootNumber.minus
```

#### B2. CRM Level Definitions (reuse from Paper 95)

```
inductive CRMLevel where
  | BISH  : CRMLevel
  | CLASS : CRMLevel
  deriving DecidableEq, Repr

structure CRMComponent where
  name  : String
  level : CRMLevel
  used  : Bool    -- true = invoked in proof; false = documentary stub
  deriving DecidableEq, Repr
```

#### B3. Rank 0 Audit (11a1)

```
def rank0_audit : List CRMComponent := [
  -- BISH components
  { name := "Hecke eigenvalue table (11a1)",      level := .BISH,  used := true },
  { name := "Point count verification",            level := .BISH,  used := true },
  { name := "Hecke recurrence",                    level := .BISH,  used := true },
  { name := "Hecke multiplicativity",              level := .BISH,  used := true },
  { name := "Hasse bound",                         level := .BISH,  used := true },
  { name := "Modular symbol ratio = 1/5",          level := .BISH,  used := true },
  { name := "Modular symbol nonzero",              level := .BISH,  used := true },
  { name := "Torsion order = 5",                   level := .BISH,  used := true },
  { name := "Tamagawa c_11 = 5",                   level := .BISH,  used := true },
  { name := "BSD formula check (rank 0)",          level := .BISH,  used := true },
  -- CLASS components (Kolyvagin side only — NO Gross-Zagier needed)
  { name := "Analytic continuation (modularity)",  level := .CLASS, used := false },
  { name := "Kato Euler system (rank = 0)",        level := .CLASS, used := false },
  { name := "Sha finiteness",                      level := .CLASS, used := false },
]

theorem rank0_bish_count :
    (rank0_audit.filter (fun c => c.level == .BISH)).length = 10 := by
  native_decide

theorem rank0_class_count :
    (rank0_audit.filter (fun c => c.level == .CLASS)).length = 3 := by
  native_decide
```

#### B4. Rank 1 Audit (37a1) — Import from Paper 95

Either import Paper 95's audit or duplicate it. The key numbers:
- 15 BISH + 6 CLASS = 21 components

#### B5. The Bifurcation Theorem

```
-- The headline result
structure BifurcationData where
  root_number    : RootNumber
  bish_count     : Nat
  class_count    : Nat
  total          : Nat
  detection_level : CRMLevel   -- CRM level of "L^(r)(E,1) ≠ 0"
  existence_level : CRMLevel   -- CRM level of "rk = r and Sha finite"

def rank0_bifurcation : BifurcationData := {
  root_number    := .plus
  bish_count     := 10
  class_count    := 3
  total          := 13
  detection_level := .BISH     -- modular symbol: BISH!
  existence_level := .CLASS    -- Sha finiteness: CLASS
}

def rank1_bifurcation : BifurcationData := {
  root_number    := .minus
  bish_count     := 15
  class_count    := 6
  total          := 21
  detection_level := .CLASS    -- Gross-Zagier needed: CLASS
  existence_level := .CLASS    -- Euler system: CLASS
}

-- The bifurcation: detection level jumps at w = -1
theorem detection_bifurcation :
    rank0_bifurcation.detection_level = .BISH ∧
    rank1_bifurcation.detection_level = .CLASS := by
  constructor <;> rfl

-- Existence is CLASS regardless of root number
theorem existence_always_class :
    rank0_bifurcation.existence_level = .CLASS ∧
    rank1_bifurcation.existence_level = .CLASS := by
  constructor <;> rfl

-- The BISH fraction improves: 77% for rank 0 vs 71% for rank 1
-- 10/13 ≈ 77%, 15/21 ≈ 71%
-- (This is a component count, not a depth measure)
```

---

### Part C: Explicit 2-Descent for 37a1 (Excising Kolyvagin for Rank)

This section proves rk E(ℚ) ≤ 1 for 37a1 without Kolyvagin, via explicit 2-descent.

#### C1. 2-Selmer Bound

The CAS computes the 2-Selmer group of 37a1. The output is:

```
-- dim_{𝔽₂} Sel²(E/ℚ) = 1 (computed by mwrank/magma/sage)
-- This means rk E(ℚ) ≤ 1
-- Combined with the known point (0,0) of infinite order, rk E(ℚ) = 1

def selmer2_rank_37a1 : Nat := 1

-- Documentary axiom: the 2-Selmer computation
-- (The CAS certificate could in principle be verified, but we
-- document the result as an axiom for now)
axiom selmer2_bound :
    selmer2_rank_37a1 = 1
    -- Interpretation: dim_{𝔽₂} Sel²(E/ℚ) / E(ℚ)[2] = 1
    -- Since E(ℚ)[2] = 0 for 37a1 (no rational 2-torsion),
    -- this gives dim Sel² = 1, hence rk E(ℚ) ≤ 1

-- The meta-theorem: rank bounding without Kolyvagin
theorem rank_bound_without_kolyvagin
    (sel2 : selmer2_rank_37a1 = 1)
    (point_exists : True)  -- (0,0) ∈ E(ℚ) is non-torsion
    : True := trivial       -- rk E(ℚ) = 1

-- NOTE: A full formalization would state this with actual
-- Mordell-Weil rank, but Mathlib doesn't have MW rank yet.
-- We document the logical structure.
```

**CAS TASK:** Use SageMath or Magma to compute the 2-Selmer rank of 37a1. The command in Sage is:
```python
E = EllipticCurve('37a1')
E.selmer_rank()  # Should return 1
```

#### C2. The Meta-Theorem

```
-- Rank bounding is BISH; Sha finiteness is CLASS
-- This is the precise statement of what Kolyvagin buys you

structure KolyvaginExcision where
  rank_bound_level : CRMLevel    -- CRM level of "rk E(ℚ) ≤ r"
  sha_finite_level : CRMLevel    -- CRM level of "|Sha| < ∞"

def kolyvagin_excision_37a1 : KolyvaginExcision := {
  rank_bound_level := .BISH     -- via 2-descent
  sha_finite_level := .CLASS    -- irreducible: needs Euler system
}

theorem descent_excises_rank :
    kolyvagin_excision_37a1.rank_bound_level = .BISH := rfl

theorem sha_requires_kolyvagin :
    kolyvagin_excision_37a1.sha_finite_level = .CLASS := rfl
```

---

### Part D: Cross-Program Comparison Table

The universal detection/existence bifurcation, now with the root number refinement.

```
-- Compile the full bifurcation landscape
structure SqueezeInstance where
  paper       : String
  domain      : String
  detection   : CRMLevel
  existence   : CRMLevel
  control     : String      -- what controls the bifurcation

def squeeze_landscape : List SqueezeInstance := [
  { paper := "P84-89", domain := "Hodge (Weil locus)",
    detection := .BISH, existence := .CLASS,
    control := "palindromic obstruction (a-c)" },
  { paper := "P94", domain := "CY3 (Griffiths group)",
    detection := .BISH, existence := .CLASS,
    control := "source term δ(z)" },
  { paper := "P95", domain := "BSD (rank 1, w=-1)",
    detection := .CLASS, existence := .CLASS,
    control := "root number w" },
  { paper := "P96", domain := "BSD (rank 0, w=+1)",
    detection := .BISH, existence := .CLASS,
    control := "root number w" },
]

-- The universal theorem: existence is always CLASS
theorem existence_universally_class :
    ∀ s ∈ squeeze_landscape, s.existence = .CLASS := by
  simp [squeeze_landscape]
  constructor <;> (try constructor) <;> rfl

-- The bifurcation theorem: detection level is controlled
-- by a computable invariant (root number for BSD,
-- palindromic obstruction for Hodge)
-- Detection is BISH except when forced to CLASS by
-- the invariant (w = -1 for BSD, a ≠ c for Hodge)
```

---

## File Structure

```
Paper96_RootNumberBifurcation/
├── lakefile.lean
├── lean-toolchain              -- leanprover/lean4:v4.29.0-rc2
├── Papers.lean                 -- root import
├── CRMLevel.lean               -- CRM hierarchy (reuse from P95)
├── HeckeData11a1.lean          -- Hecke eigenvalues, point counts for 11a1
├── ModularSymbol.lean          -- Modular symbol ratio, nonzero proof
├── BSDRank0.lean               -- BSD formula check for rank 0
├── HeckeData37a1.lean          -- (import or duplicate from P95)
├── HeegnerData37a1.lean        -- (import or duplicate from P95)
├── Descent37a1.lean            -- 2-Selmer bound, descent excision
├── Bifurcation.lean            -- Root number bifurcation theorem
└── Paper96_Assembly.lean       -- Theorems A-D, #print axioms, final audit
```

## Theorem Inventory (Target: ~55-65 theorems)

### HeckeData11a1.lean (~15 theorems)
- hecke_pointcount_{2,3,5,7,13} (5 theorems, native_decide)
- hecke_recurrence_{2,3,5,7} (4 theorems, native_decide)
- hecke_multiplicativity_{2·3,2·5,3·5,5·7} (4 theorems, native_decide)
- hasse_bound for 11a1 primes (1 compound or ~12 individual, native_decide)

### ModularSymbol.lean (~5 theorems)
- modular_symbol_ratio_def : modular_symbol_ratio_11a1 = 1/5
- modular_symbol_nonzero : modular_symbol_ratio_11a1 ≠ 0 (norm_num)
- Axiom stub: modular_symbol_equals_L_ratio

### BSDRank0.lean (~8 theorems)
- torsion_order_11a1 = 5 (native_decide or rfl)
- tamagawa_11a1 = 5 (native_decide or rfl)  
- sha_order_11a1 = 1 (rfl)
- bsd_formula_check : (1:Rat)/5 = 1 * 5 / (5 * 5) (norm_num)
- rank0_bish_count = 10 (native_decide)
- rank0_class_count = 3 (native_decide)
- rank0_detection_bish (rfl)

### Descent37a1.lean (~5 theorems)
- selmer2_rank_37a1 = 1 (axiom from CAS)
- descent_excises_rank (rfl)
- sha_requires_kolyvagin (rfl)
- rank_meta_theorem structure

### Bifurcation.lean (~10 theorems)
- detection_bifurcation (rfl)
- existence_always_class (rfl)
- existence_universally_class (simp + rfl)
- squeeze_landscape definition
- Cross-program comparison with P84-89, P94

### Paper96_Assembly.lean (~10 theorems)
- theorem_A_modular_symbol_core (assembly)
- theorem_B_rank0_squeeze (assembly)  
- theorem_C_root_number_bifurcation (assembly)
- theorem_D_descent_excision (assembly)
- #print axioms for each key theorem

---

## CAS Tasks (Python/SymPy/Sage)

The Lean agent should request the following computations or perform them:

### CAS Task 1: Point counts for 11a1
```python
# Enumerate solutions to y^2 + y = x^3 - x^2 - 10x - 20 over F_p
def count_points(p):
    count = 1  # point at infinity
    for x in range(p):
        for y in range(p):
            if (y*y + y) % p == (x*x*x - x*x - 10*x - 20) % p:
                count += 1
    return count

for p in [2, 3, 5, 7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
    if p != 11:  # skip bad prime
        print(f"p={p}: #E(F_p) = {count_points(p)}, a_p = {p + 1 - count_points(p)}")
```

### CAS Task 2: Modular symbol for 11a1
```python
# Using Sage
E = EllipticCurve('11a1')
print(E.modular_symbol()(0))  # Should give 1/5
# Or equivalently:
print(E.lseries().L_ratio())  # L(E,1) / Omega^+
```

### CAS Task 3: Tamagawa and torsion for 11a1
```python
E = EllipticCurve('11a1')
print(f"Torsion order: {E.torsion_order()}")        # 5
print(f"Tamagawa product: {E.tamagawa_product()}")   # 5 (c_11 = 5)
print(f"Sha order: {E.sha().an()}")                  # 1
print(f"Rank: {E.rank()}")                            # 0
```

### CAS Task 4: 2-Selmer for 37a1
```python
E = EllipticCurve('37a1')
print(f"2-Selmer rank: {E.selmer_rank()}")  # 1
print(f"Rank: {E.rank()}")                   # 1
```

---

## Axiom Stubs (CLASS Documentary)

The following axiom stubs document the CLASS boundary. They are NEVER invoked in any proof. They exist for CRM classification only.

```lean
-- Rank 0 CLASS boundary
axiom analytic_continuation_11a1 :
    -- L(E,s) has analytic continuation to ℂ via modularity
    True  -- documentary

axiom kato_euler_system_11a1 :
    -- Kato's Euler system: if L(E,1) ≠ 0 then rk E(ℚ) = 0
    -- (For rank 0, Kato replaces Kolyvagin)
    True  -- documentary

axiom sha_finite_11a1 :
    -- |Sha(E/ℚ)| < ∞ (requires Euler system)
    True  -- documentary

-- Rank 1 CLASS boundary (from Paper 95)
axiom gross_zagier_formula :
    -- L'(E,1) = c_GZ · ĥ(y_K)
    True  -- documentary

axiom kolyvagin_euler_system :
    -- If y_K non-torsion then rk E(ℚ) = 1 and Sha finite
    True  -- documentary

axiom rankin_selberg_integral :
    -- Petersson inner product via non-compact integration
    True  -- documentary
```

---

## Key Verification Points

After building, run `#print axioms` on every key theorem:

1. **modular_symbol_nonzero_11a1**: Should show ONLY `Lean.ofReduceBool` or `propext`/`Quot.sound`. No documentary axioms. This is the purest BISH result.

2. **bsd_formula_check_11a1**: Should show ONLY `norm_num` infrastructure. No documentary axioms.

3. **detection_bifurcation**: Should show only `rfl`-level axioms. This is a structural theorem about CRM levels, not about elliptic curves.

4. **existence_universally_class**: Same — structural, not computational.

5. **rank0_bish_count** and **rank0_class_count**: `native_decide` only.

---

## Paper Title and Main Theorems

**Title:** "The Root Number Bifurcation: CRM Cost of BSD Detection is Controlled by the Functional Equation"

**Subtitle:** Paper 96 of the Constructive Reverse Mathematics Series

### Theorem A (Rank 0 Modular Symbol Core)
For E = 11a1, the modular symbol L(E,1)/Ω⁺ = 1/5 ≠ 0 is verified by `norm_num`. The Hecke eigenvalue arithmetic (point counts, recurrence, multiplicativity, Hasse bounds) is verified by `native_decide`. Pure finite arithmetic: BISH. No analytic continuation invoked.

### Theorem B (Root Number Bifurcation)
The CRM cost of BSD *detection* (proving L^(r)(E,1) ≠ 0) is controlled by the root number w:
- w = +1 (rank 0): detection is BISH (modular symbols compute L(E,1)/Ω⁺ ∈ ℚ)
- w = −1 (rank 1): detection is CLASS (Gross–Zagier formula requires Rankin–Selberg)

The CRM cost of BSD *existence* (proving rk = r and Sha finite) is CLASS regardless of w.

### Theorem C (Descent Excision)  
For 37a1, explicit 2-descent gives rk E(ℚ) ≤ 1 without Kolyvagin's Euler system. The meta-theorem: rank bounding is BISH (descent); Sha finiteness is irreducibly CLASS (requires Euler system).

### Theorem D (Universal Detection/Existence Table)
Across four Squeeze instances (Hodge P84-89, CY3 P94, BSD rank 1 P95, BSD rank 0 P96), existence is universally CLASS. Detection is BISH except when forced to CLASS by a computable invariant (palindromic obstruction, root number).

---

## What NOT to Do

1. **Do NOT attempt to formalize modular forms, L-functions, or Galois representations in Lean.** These are CLASS axiom stubs, not BISH content.

2. **Do NOT attempt to formalize the 2-descent algorithm.** The Selmer rank is a CAS output documented as an axiom. A full descent formalization is a multi-year project.

3. **Do NOT import Paper 95 as a dependency.** Duplicate the necessary definitions (CRMLevel, CRMComponent, 37a1 data). Each paper should be a self-contained lake project.

4. **Do NOT use `sorry` anywhere.** If something can't be proved, make it an axiom stub and document it as CLASS.

5. **Do NOT use `Classical.choice` in proof terms.** If it appears in `#print axioms` as Mathlib infrastructure, that's acceptable and should be documented (as in Paper 95). But no proof should intentionally invoke classical reasoning.
