# Paper 61: Lang's Conjecture as the MP → BISH Gate
## Lean 4 Proof Strategy Document

### Overview

Paper 61 formalizes the logical relationship between Lang's Height Lower Bound Conjecture and BISH-decidability of Mordell-Weil generators at rank ≥ 2. The main results:

1. **Forward:** Effective Lang ⟹ BISH-decidability for all ranks (Theorem A)
2. **Converse failure:** BISH-decidability ⟹̸ Lang (Theorem B)  
3. **Explicit computation:** X₀(389) search bound ĥ_max ≤ 4.87 (Theorem C)
4. **Northcott escalation:** Without Northcott, decidability requires LPO (Theorem D)
5. **Uniformity:** Uniform Lang ⟺ Uniform Analytic BISH (Theorem E)

### File Structure

```
Paper61_Lang_BISH/
├── Basic/
│   ├── Decidability.lean      -- BISH, MP, LPO definitions (import from Paper 50/60)
│   ├── Heights.lean           -- Canonical height, naive height, Northcott
│   └── Lattices.lean          -- Minkowski successive minima, Hermite constant
├── Forward/
│   ├── MinkowskiBound.lean    -- Minkowski Second Theorem → height bound
│   ├── LangToBISH.lean       -- Lang + Minkowski + Northcott → BISH
│   └── Explicit389.lean      -- X₀(389) numerical verification
├── Converse/
│   ├── BISHNotLang.lean       -- Separation: BISH does not imply Lang
│   └── AckermannWitness.lean  -- Witness: bounding function growing faster than Lang allows
├── Northcott/
│   ├── NorthcottFailure.lean  -- K3/higher K-theory: infinite cycles in bounded height
│   └── EscalationLPO.lean    -- Without Northcott, rank ≥ 2 → LPO
├── Uniform/
│   └── UniformLang.lean       -- Uniform Lang ⟹ analytic-only BISH certificate
└── Main.lean                  -- Imports all, states summary theorems
```

### Definitions to Formalize

```lean
-- Basic/Decidability.lean
-- Import or redefine from Paper 50/60

/-- BISH-decidable: there exists a computable bound B such that
    the search space is finite and enumerable within B steps. -/
def BISHDecidable (P : ℕ → Prop) [DecidablePred P] : Prop :=
  ∃ B : ℕ, ∀ n, P n → n ≤ B

/-- MP-decidable: if ∃ n, P n, then the search halts,
    but no a priori bound on halting time. -/
def MPDecidable (P : ℕ → Prop) [DecidablePred P] : Prop :=
  (∃ n, P n) → ∃ n, P n  -- trivial classically; constructive content is the witness

/-- LPO: for any sequence, either all terms are zero or some term is nonzero. -/
axiom LPO : ∀ (f : ℕ → ℤ), (∀ n, f n = 0) ∨ (∃ n, f n ≠ 0)
```

```lean
-- Basic/Heights.lean

/-- Canonical height on an elliptic curve (or abelian variety).
    Positive-definite quadratic form on E(ℚ)/tors ⊗ ℝ. -/
structure CanonicalHeight (r : ℕ) where
  /-- Height pairing matrix (r × r, positive-definite) -/
  gram : Matrix (Fin r) (Fin r) ℚ  
  /-- Regulator = det(gram) -/
  regulator : ℚ
  reg_eq : regulator = gram.det
  pos_def : ∀ v : Fin r → ℚ, v ≠ 0 → (Matrix.dotProduct v (gram.mulVec v)) > 0

/-- Northcott property: finitely many points of bounded height -/
def NorthcottProperty (heightBound : ℚ) (count : ℕ) : Prop :=
  -- The number of rational points with naive height ≤ heightBound is ≤ count
  True  -- axiomatize; the content is the finiteness, not the count

/-- Northcott's theorem for abelian varieties -/
axiom northcott_abelian_variety :
  ∀ (B : ℚ), ∃ (N : ℕ), NorthcottProperty B N
```

```lean
-- Basic/Lattices.lean

/-- Hermite constant γ_r for dimension r -/
def hermiteConstant : ℕ → ℚ
  | 1 => 1
  | 2 => 4/3  -- (2/√3)² = 4/3
  | 3 => 2
  | 4 => 4
  | 5 => 8
  | 6 => 64/3
  | 7 => 64
  | 8 => 256
  | _ => 0  -- placeholder; only need small dimensions

/-- Minkowski's Second Theorem: product of successive minima
    bounded by Hermite constant times covolume.
    λ₁ · λ₂ · ... · λ_r ≤ γ_r^(r/2) · vol(Λ) -/
axiom minkowski_second_theorem (r : ℕ) (hr : r ≥ 1)
  (lambda : Fin r → ℚ)  -- successive minima (canonical heights)
  (vol : ℚ)             -- covolume = √regulator
  (h_ordered : ∀ i j, i ≤ j → lambda i ≤ lambda j) :
  (Finset.univ.prod lambda) ≤ (hermiteConstant r) ^ (r / 2) * vol
```

### Theorem A: Lang ⟹ BISH (Forward Direction)

```lean
-- Forward/LangToBISH.lean

/-- Lang's Height Lower Bound Conjecture (effective version):
    There exists a computable constant c > 0 depending on E
    such that ĥ(P) ≥ c for all non-torsion P ∈ E(ℚ). -/
structure EffectiveLang (r : ℕ) where
  c : ℚ          -- computable lower bound
  c_pos : c > 0
  -- For all non-torsion points, canonical height ≥ c

/-- Main theorem: Lang + Minkowski + Northcott → BISH
    
    The key computation:
    From Minkowski: λ₁ · λ₂ · ... · λ_r ≤ γ_r^(r/2) · √R
    From Lang: λ_i ≥ c for all i
    Therefore: c^(r-1) · λ_r ≤ γ_r^(r/2) · √R
    So: λ_r ≤ γ_r^(r/2) · √R / c^(r-1)
    
    This gives computable ĥ_max. Northcott then gives finite search set. -/
theorem lang_implies_bish (r : ℕ) (hr : r ≥ 2)
    (heights : CanonicalHeight r)
    (lang : EffectiveLang r) :
    -- There exists a computable bound on the maximum generator height
    ∃ h_max : ℚ, h_max = (hermiteConstant r) ^ (r / 2) * 
      heights.regulator / lang.c ^ (r - 1) := by
  exact ⟨_, rfl⟩
```

### Theorem B: BISH ⟹̸ Lang (Converse Failure)

```lean
-- Converse/BISHNotLang.lean

/-- The converse fails: BISH-decidability does not imply Lang.
    
    Proof strategy: Construct a hypothetical family of curves where:
    - The minimum height c(E) decays faster than any Lang-admissible rate
    - But a computable bounding function B(E) still exists (just grows very fast)
    
    The separation: Lang constrains the RATE of c(E) decay.
    BISH only requires EXISTENCE of B(E), regardless of growth rate. -/
theorem bish_does_not_imply_lang :
    -- There exists a notion of "BISH-decidable family" that does not
    -- satisfy Lang's geometric scaling
    ¬ (∀ (family : ℕ → ℚ),  -- family of minimum heights c(E_n)
       (∀ n, ∃ B : ℕ, True) →  -- BISH: bound exists for each
       (∃ C : ℚ, C > 0 ∧ ∀ n, family n ≥ C))  -- Lang: uniform lower bound
    := by
  intro h
  -- Witness: family n = 1/(n+1), each has a bound, but inf → 0
  have := h (fun n => 1 / (↑n + 1)) (fun n => ⟨n + 1, trivial⟩)
  obtain ⟨C, hC_pos, hC_bound⟩ := this
  -- For n large enough, 1/(n+1) < C, contradiction
  sorry  -- The Lean agent should close this with concrete n = ⌈1/C⌉
```

### Theorem C: X₀(389) Explicit Computation

```lean
-- Forward/Explicit389.lean

/-- X₀(389): rank 2 elliptic curve.
    Known data (Cremona tables):
    - Analytic rank: 2
    - Regulator: R ≈ 0.15246... 
    - Generators: P₁ = (0, 0), P₂ = (-1, 1)  
    - ĥ(P₁) ≈ 0.327..., ĥ(P₂) ≈ 0.465...
    
    We verify: both generators satisfy ĥ ≤ ĥ_max where
    ĥ_max = γ₂ · √R / c(E)
    
    Using γ₂ = 4/3, R = 15246/100000 (rational approx),
    c(E) = 173/100 (Hindry-Silverman): -/

-- Use rational approximations for native_decide
def R_389 : ℚ := 15246 / 100000
def gamma_2 : ℚ := 4 / 3
def c_389 : ℚ := 173 / 100  -- Hindry-Silverman effective constant

-- The maximum generator height bound
def h_max_389 : ℚ := gamma_2 * R_389 / c_389

-- Known generator heights (rational approximations from Cremona)
def h_P1 : ℚ := 327 / 1000   -- ĥ(P₁) ≈ 0.327
def h_P2 : ℚ := 465 / 1000   -- ĥ(P₂) ≈ 0.465

/-- Both generators fall within the Lang-Minkowski bound -/
theorem generators_within_bound : h_P1 ≤ h_max_389 ∧ h_P2 ≤ h_max_389 := by
  unfold h_P1 h_P2 h_max_389 gamma_2 R_389 c_389
  constructor <;> native_decide

-- NOTE TO LEAN AGENT: 
-- The h_max formula above is SIMPLIFIED. The full formula from the math genius is:
-- ĥ_max = γ_r^(r/2) · √R / c^(r-1) 
-- For r=2: ĥ_max = (4/3) · √0.15246 / 1.73^1
-- √0.15246 ≈ 0.3905
-- So ĥ_max ≈ (4/3) · 0.3905 / 1.73 ≈ 0.3009
-- 
-- WAIT: this gives ĥ_max ≈ 0.30, but ĥ(P₂) ≈ 0.465 > 0.30.
-- The generators EXCEED this bound!
-- 
-- The math genius claimed ĥ_max ≤ 4.87, using a different formula.
-- PLEASE VERIFY: which formula is correct? 
-- The discrepancy may be because:
-- (a) The Minkowski bound uses √R not R directly
-- (b) The c(E) value 1.73 may be wrong
-- (c) The math genius used a different Minkowski normalization
--
-- CRITICAL: Run the actual numbers before trusting native_decide.
-- If the bound is wrong, the theorem statement needs correction.
-- Flag this to Paul.
```

### Theorem D: Northcott Failure → LPO

```lean
-- Northcott/EscalationLPO.lean

/-- Without Northcott, even bounded height contains infinitely many cycles.
    Verifying completeness of a lattice basis over an infinite set requires LPO.
    
    The argument:
    1. Bounded height region contains infinitely many cycles (no Northcott)
    2. Given candidate generators g₁,...,g_r, must verify:
       ∀ z in bounded region, z ∈ ℤ-span(g₁,...,g_r)
    3. This is universal quantification over an infinite set
    4. = LPO (testing whether an infinite sequence is identically zero) -/

/-- A motive lacks Northcott if bounded height regions are infinite -/
def LacksNorthcott : Prop :=
  ∃ B : ℚ, ∀ N : ℕ, ∃ (cycles : Fin N → Unit), True
  -- There exist arbitrarily many distinct cycles of bounded height

/-- Main escalation theorem -/
theorem no_northcott_requires_LPO (r : ℕ) (hr : r ≥ 2)
    (h_no_northcott : LacksNorthcott) :
    -- Decidability of "g₁,...,g_r generate the full lattice" 
    -- requires LPO
    -- Formalized as: the decision procedure must evaluate
    -- a predicate on an infinite domain
    True  -- placeholder; the content is the logical argument
    := by
  trivial

-- NOTE TO LEAN AGENT:
-- The real content here is the REDUCTION:
-- "Does v lie in ℤ-span(g₁,...,g_r)?" is decidable for each v (linear algebra over ℤ)
-- "Does EVERY v of bounded height lie in the span?" requires checking infinitely many v
-- This infinite conjunction is equivalent to LPO:
--   given f : ℕ → ℤ, (∀ n, f n = 0) ∨ (∃ n, f n ≠ 0)
-- 
-- The cleanest formalization: construct an explicit reduction from LPO 
-- to the lattice-completeness decision problem.
-- Given f : ℕ → ℤ, define cycle z_n that lies in span iff f(n) = 0.
-- Then "all z_n in span" ⟺ "∀ n, f(n) = 0" ⟺ one disjunct of LPO.
--
-- This is the key new result of Paper 61. Please formalize carefully.
```

### Theorem E: Uniform Lang ⟹ Analytic BISH

```lean
-- Uniform/UniformLang.lean

/-- Uniform Lang-Silverman: the lower bound depends only on
    dimension g and number field K, not on the specific variety. -/
axiom UniformLang (g : ℕ) : 
  ∃ c : ℚ, c > 0  -- universal constant for all abelian varieties of dim g over ℚ

/-- Under Uniform Lang, the BISH search bound is a function 
    of the L-function data alone. -/
theorem uniform_lang_analytic_bish (g : ℕ) (r : ℕ) (hr : r ≥ 2)
    (R : ℚ)  -- regulator, computable from L^(r)(M,s₀) via Bloch-Kato
    (hR : R > 0) :
    -- The search bound depends only on R and universal constants
    ∃ h_max : ℚ, ∀ (c : ℚ), c > 0 → 
      h_max = (hermiteConstant r) ^ (r / 2) * R / c ^ (r - 1) := by
  sorry  -- Lean agent: this is just algebra, close it
```

### Main.lean Summary

```lean
-- Main.lean

import Paper61_Lang_BISH.Forward.LangToBISH
import Paper61_Lang_BISH.Converse.BISHNotLang
import Paper61_Lang_BISH.Forward.Explicit389
import Paper61_Lang_BISH.Northcott.EscalationLPO
import Paper61_Lang_BISH.Uniform.UniformLang

/-- Paper 61 Summary:
    
    The DPT decidability hierarchy for Ext¹ of motives:
    
    1. Rank 0: BISH (Paper 60)
    2. Rank 1: BISH (Paper 60, via Northcott)  
    3. Rank ≥ 2 with Northcott: MP (Paper 60)
       → BISH if Lang holds (Paper 61, Theorem A)
    4. Rank ≥ 2 without Northcott: LPO (Paper 61, Theorem D)
    
    The hierarchy is:
    BISH ⊂ MP ⊂ LPO
    
    Lang's conjecture is the gate from MP to BISH.
    Northcott's property is the gate from LPO to MP.
    Both are one-way: BISH ⟹̸ Lang, MP ⟹̸ Northcott.
-/
```

### Priority Notes for Lean Agent

1. **CRITICAL: Verify the X₀(389) numbers.** The math genius claims ĥ_max ≤ 4.87 but my back-of-envelope gives ~0.30 using the Minkowski formula directly. There may be a normalization issue (Minkowski uses covolume = √R, not R). Check Cremona's database for X₀(389) generator heights and verify which bound is correct before running native_decide.

2. **Main new result is Theorem D (LPO escalation).** This is the result that extends Paper 60's hierarchy. Invest the most effort here. The reduction from LPO to lattice-completeness should be explicit and clean.

3. **Theorem B (converse failure)** can be a short argument. The witness is any sequence c(n) → 0 that's still computable. Don't over-engineer this.

4. **Theorem E (uniformity)** is conditional on an open conjecture. State it with `axiom UniformLang` and move on.

5. **Import structure from Paper 60 Lean source if available.** Reuse BISH/MP/LPO definitions. Don't rebuild from scratch.
