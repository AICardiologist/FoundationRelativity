# Paper 28 Extension: Hamiltonian Formulation

## Proof Strategy Document for Lean 4 Agent

**Context:** Paper 28 currently proves Newton (BISH) vs Lagrange (FT) stratification for the discrete harmonic oscillator with N=2. This extension adds the Hamiltonian formulation and the Legendre transform, completing the triad.

**Depends on:** Existing Paper 28 infrastructure (Defs.lean, BISHHalf.lean, FTHalf.lean, Stratification.lean)
**Target:** ~80–120 additional lines Lean 4, zero sorries
**Date:** 2026-02-11

---

## 1. WHAT WE ARE ADDING

Three new results, all BISH:

1. **Discrete Hamilton's equations** for the harmonic oscillator at N=2 have a unique explicit solution. (BISH)
2. **Discrete Legendre transform** mapping (q, qdot) ↔ (q, p) is an explicit invertible map. (BISH)
3. **Consistency**: the Hamiltonian EL solution, pulled back through the Legendre transform, equals the Lagrangian EL solution from BISHHalf.lean.

One result invoking FT:

4. **Hamiltonian variational principle**: asserting that the Hamiltonian action attains its minimum on [0,1] requires FT. (This follows immediately from the existing FTHalf.lean — the action is the same physical quantity in different variables.)

The punchline becomes a **three-way stratification**:

```
BISH:  Euler-Lagrange eqn  ←—Legendre (BISH)—→  Hamilton's eqns
                    ↕                                    ↕
 FT:   Lagrangian min ∃     ←— same action —→    Hamiltonian min ∃
```

All equation-solving is BISH. All optimization is FT. The bridge between formulations is BISH.

---

## 2. PHYSICS SETUP

### 2.1 Hamiltonian for the Harmonic Oscillator

Starting from L(q, qdot) = ½m·qdot² − ½k·q², the conjugate momentum is:

```
p = ∂L/∂qdot = m·qdot
```

The Hamiltonian is obtained by Legendre transform:

```
H(q, p) = p·qdot − L(q, qdot)    where qdot = p/m
         = p·(p/m) − ½m·(p/m)² + ½k·q²
         = p²/m − p²/(2m) + ½k·q²
         = p²/(2m) + ½k·q²
```

Hamilton's equations:

```
qdot = ∂H/∂p = p/m
pdot = −∂H/∂q = −kq
```

### 2.2 Discrete Hamilton's Equations at N=2

With N=2 time steps on [0,1], Δt = 1/2. Boundary conditions: q₀ = A, q₂ = B. Free variables: q₁ and p₁.

The discrete Hamilton's equations (symplectic Euler or equivalent) at the interior node are:

```
(q₁ − A) / Δt = p₁ / m          ... (i)   discrete qdot = p/m
(p₂ − p₁) / Δt = −k · q₁        ... (ii)  discrete pdot = −kq
```

But we also need the second leg:

```
(B − q₁) / Δt = p₂ / m          ... (iii)  discrete qdot at step 2
```

**IMPORTANT DESIGN DECISION:** There are multiple discretization schemes for Hamilton's equations (symplectic Euler, Störmer-Verlet, etc.). For consistency with the existing Lagrangian discretization, we should derive the discrete Hamiltonian equations FROM the discrete Lagrangian via the Legendre transform, not independently.

### 2.3 Derivation via Discrete Legendre Transform

The discrete Legendre transform maps discrete velocities to discrete momenta:

```
pᵢ⁺ = ∂₂Ld(qᵢ, qᵢ₊₁) = ∂/∂qᵢ₊₁ [L(qᵢ, (qᵢ₊₁−qᵢ)/Δt) · Δt]
pᵢ₊₁⁻ = −∂₁Ld(qᵢ, qᵢ₊₁) = −∂/∂qᵢ [L(qᵢ, (qᵢ₊₁−qᵢ)/Δt) · Δt]
```

For the harmonic oscillator at N=2 with Δt = 1/2:

**First leg (i=0):** Ld(q₀, q₁) = [½m·((q₁−A)/(½))² − ½k·A²] · ½ = m(q₁−A)² − kA²/4

```
p₁⁻ = ∂Ld/∂q₁ (q₀, q₁) = 2m(q₁ − A)
```

**Second leg (i=1):** Ld(q₁, q₂) = [½m·((B−q₁)/(½))² − ½k·q₁²] · ½ = m(B−q₁)² − kq₁²/4

```
p₁⁺ = −∂Ld/∂q₁ (q₁, q₂) = 2m(B − q₁) − (−kq₁/2) = 2m(B−q₁) + kq₁/2
```

Wait — let me be more careful. The discrete EL equation is p₁⁻ + ∂₁Ld(q₁,q₂) = 0, i.e., the matching condition p₁⁺ = p₁⁻ (momentum continuity). Let me recompute:

```
∂₂Ld(q₀, q₁) = ∂/∂q₁ [m(q₁−A)² − kA²/4] = 2m(q₁ − A)

∂₁Ld(q₁, q₂) = ∂/∂q₁ [m(B−q₁)² − kq₁²/4] = −2m(B−q₁) − kq₁/2
```

The discrete EL equation is:

```
∂₂Ld(q₀,q₁) + ∂₁Ld(q₁,q₂) = 0
2m(q₁−A) + [−2m(B−q₁) − kq₁/2] = 0
2m·q₁ − 2mA − 2mB + 2m·q₁ − kq₁/2 = 0
(4m − k/2)·q₁ = 2m(A+B)
(8m − k)·q₁ = 4m(A+B)  ✓  matches existing EL equation
```

Good. Now define the discrete momentum at node 1:

```
p₁ := ∂₂Ld(q₀, q₁) = 2m(q₁ − A)
```

This is the **discrete Legendre transform**: given the Lagrangian solution q₁ = q*, compute p₁ = 2m(q* − A).

### 2.4 Simplification for Lean

Rather than formalizing the full discrete Legendre transform framework (which would require partial derivatives of Ld as functions — heavy infrastructure), we can work with the **explicit formulas** for this specific system.

**Define:**
```
p* := 2 * m * (q* − A)     where q* = 4m(A+B)/(8m−k)
```

**Verify Hamilton's equations are satisfied:**
```
Hamilton eq 1:  (q* − A) / Δt = p* / m
  LHS = (q* − A) / (1/2) = 2(q* − A)
  RHS = 2m(q* − A) / m = 2(q* − A)  ✓

Hamilton eq 2:  (B − q*) / Δt relates to the momentum at the next step
  This is the consistency check — the discrete momentum matching condition
  is exactly the discrete EL equation, which we've already proved.
```

The cleanest approach: define the discrete Legendre transform as an explicit map, show it's invertible, show the Hamilton's equations are satisfied by (q*, p*), and show this is unique.

---

## 3. FILE STRUCTURE

### New file: `HamiltonBISH.lean` (~80–120 lines)

### Updated file: `Stratification.lean` (add ~20–30 lines for the three-way theorem)

---

## 4. DETAILED SPECIFICATIONS

### 4.1 Definitions to Add (in Defs.lean or HamiltonBISH.lean)

```lean
-- Discrete Legendre transform: maps EL solution to phase space point
noncomputable def discreteMomentum (p : HOParams) (q : ℝ) : ℝ :=
  2 * p.m * (q - p.A)

-- Inverse Legendre transform: recover q from (A, p₁)
noncomputable def legendreInverse (p : HOParams) (p₁ : ℝ) : ℝ :=
  p₁ / (2 * p.m) + p.A

-- The Hamiltonian
noncomputable def hamiltonian (p : HOParams) (q mom : ℝ) : ℝ :=
  mom ^ 2 / (2 * p.m) + p.k / 2 * q ^ 2

-- Phase space solution
noncomputable def elSolutionPhaseSpace (p : HOParams) : ℝ × ℝ :=
  (elSolution p, discreteMomentum p (elSolution p))
```

### 4.2 Theorems to Prove

#### Theorem 1: Legendre Transform is Invertible (BISH)

```lean
theorem legendre_invertible (p : HOParams) (q : ℝ) :
    legendreInverse p (discreteMomentum p q) = q := by
  unfold legendreInverse discreteMomentum
  field_simp
  ring

theorem legendre_invertible' (p : HOParams) (mom : ℝ) :
    discreteMomentum p (legendreInverse p mom) = mom := by
  unfold discreteMomentum legendreInverse
  field_simp
  ring
```

**Risk:** LOW. Pure algebra, `field_simp` + `ring` should handle it. The only subtlety is `p.m ≠ 0` which follows from `p.hm : 0 < p.m`. The agent will need `ne_of_gt p.hm` or similar.

#### Theorem 2: Discrete Hamilton's Equations Satisfied (BISH)

Define the discrete Hamilton's equations for N=2:

```lean
-- Discrete Hamilton's equation 1: (q₁ − A)/(1/2) = p₁/m
-- Equivalently: 2(q₁ − A) = p₁/m, or: 2m(q₁ − A) = p₁
def satisfiesHamiltonEq1 (p : HOParams) (q₁ p₁ : ℝ) : Prop :=
  p₁ = 2 * p.m * (q₁ - p.A)

-- Discrete Hamilton's equation 2: momentum matching (= discrete EL)
-- This is the condition that the EL equation holds, expressed in
-- phase space variables. For N=2 it reduces to the same algebraic
-- condition as the EL equation.
def satisfiesHamiltonEq2 (p : HOParams) (q₁ p₁ : ℝ) : Prop :=
  (8 * p.m - p.k) * q₁ = 4 * p.m * (p.A + p.B)
```

```lean
theorem hamilton_eqs_satisfied (p : HOParams) (hcfl : p.k < 8 * p.m) :
    let sol := elSolutionPhaseSpace p
    satisfiesHamiltonEq1 p sol.1 sol.2 ∧
    satisfiesHamiltonEq2 p sol.1 sol.2 := by
  constructor
  · -- Eq 1: follows from definition of discreteMomentum
    unfold elSolutionPhaseSpace satisfiesHamiltonEq1 discreteMomentum
    ring
  · -- Eq 2: this IS the EL equation, already proved
    exact elSolution_satisfies p hcfl
```

**Risk:** LOW. The first equation is true by definition (we defined p₁ = 2m(q₁−A), and Hamilton's eq 1 says exactly that). The second equation is the existing EL result.

#### Theorem 3: Uniqueness of Hamilton Solution (BISH)

```lean
theorem hamilton_unique_solution (p : HOParams) (hcfl : p.k < 8 * p.m) :
    ∃! qp : ℝ × ℝ,
      satisfiesHamiltonEq1 p qp.1 qp.2 ∧
      satisfiesHamiltonEq2 p qp.1 qp.2 := by
  refine ⟨elSolutionPhaseSpace p, hamilton_eqs_satisfied p hcfl, ?_⟩
  intro ⟨q', p'⟩ ⟨h1, h2⟩
  -- From h1: p' = 2m(q' − A)
  -- From h2: (8m−k)q' = 4m(A+B), so q' = elSolution p (by uniqueness from BISHHalf)
  -- Then p' = discreteMomentum p (elSolution p) by h1
  ext
  · -- q component: uniqueness from EL
    have := (el_unique_solution_N2 p hcfl).unique h2
    simp [elSolutionPhaseSpace, this]
  · -- p component: determined by q via h1
    simp [elSolutionPhaseSpace, discreteMomentum, satisfiesHamiltonEq1] at *
    linarith
```

**Risk:** MEDIUM. The `ext` tactic on `ℝ × ℝ` and the extraction of uniqueness from `∃!` may need some care. The agent should check whether `ExistsUnique.unique` or similar is available in Mathlib for extracting the uniqueness clause. Alternative: prove uniqueness directly without invoking `el_unique_solution_N2`, just by algebra on the two equations.

**Fallback approach if ∃! on pairs is awkward:**
```lean
-- Prove separately:
-- (a) q is uniquely determined by Hamilton eq 2 (= EL equation)
-- (b) p is uniquely determined by q via Hamilton eq 1
-- Package as: ∃! q, ∃! p, ...
-- Or just prove it as two separate uniqueness statements
```

#### Theorem 4: Legendre Consistency (BISH)

The Lagrangian solution and Hamiltonian solution are related by the Legendre transform:

```lean
theorem legendre_consistency (p : HOParams) (hcfl : p.k < 8 * p.m) :
    (elSolutionPhaseSpace p).2 = discreteMomentum p (elSolution p) := by
  unfold elSolutionPhaseSpace
  rfl
```

This is trivially true by definition. But it's worth stating as a theorem because the *paper* needs to assert that the two formulations are connected by the Legendre transform, and the connection is BISH.

### 4.3 Updated Stratification Theorem

```lean
theorem stratification_triad (p : HOParams) (hcfl : p.k < 8 * p.m) :
    -- Part 1: BISH solves the EL equation (Lagrangian)
    (∃! q : ℝ, (8 * p.m - p.k) * q = 4 * p.m * (p.A + p.B))
    ∧
    -- Part 2: BISH solves Hamilton's equations
    (∃! qp : ℝ × ℝ,
      satisfiesHamiltonEq1 p qp.1 qp.2 ∧ satisfiesHamiltonEq2 p qp.1 qp.2)
    ∧
    -- Part 3: Legendre transform is invertible (BISH bridge)
    (∀ q : ℝ, legendreInverse p (discreteMomentum p q) = q)
    ∧
    -- Part 4: Minimizer existence ↔ Fan Theorem
    ((∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
       ∃ x ∈ Set.Icc (0:ℝ) (1:ℝ), ∀ y ∈ Set.Icc (0:ℝ) (1:ℝ), f x ≤ f y)
     ↔ FanTheorem) :=
  ⟨el_unique_solution_N2 p hcfl,
   hamilton_unique_solution p hcfl,
   legendre_invertible p,
   minimizer_iff_ft⟩
```

---

## 5. AXIOM AUDIT

| Result | Expected Axioms | Notes |
|--------|----------------|-------|
| `legendre_invertible` | [propext, Classical.choice, Quot.sound] | Pure algebra over ℝ, BISH |
| `legendre_invertible'` | same | BISH |
| `hamilton_eqs_satisfied` | same | BISH, reuses `elSolution_satisfies` |
| `hamilton_unique_solution` | same | BISH, reuses `el_unique_solution_N2` |
| `legendre_consistency` | same (or possibly fewer — `rfl` might not need all) | BISH, definitional |
| `stratification_triad` | same | BISH ∧ FT |

All new theorems should show **no FanTheorem dependency**. They are all BISH. The FT dependence comes only through the existing `minimizer_iff_ft` in Part 4.

**CRITICAL CHECK:** Run `#print axioms hamilton_unique_solution` and verify FanTheorem does NOT appear. If it does, something is wrong — the Hamilton solution is computed by explicit algebra and should not require FT.

---

## 6. POTENTIAL PITFALLS

### 6.1 ∃! on Product Types
**Problem:** `∃! qp : ℝ × ℝ, ...` might be awkward in Lean. Uniqueness on pairs requires showing both components are equal.
**Mitigation:** If `∃!` on pairs is cumbersome, reformulate as two separate uniqueness claims:
```lean
(∃! q : ℝ, satisfiesHamiltonEq2 p q) ∧
(∀ q : ℝ, satisfiesHamiltonEq2 p q → ∃! mom : ℝ, satisfiesHamiltonEq1 p q mom)
```
This says: q is uniquely determined by the EL equation, and given q, the momentum is uniquely determined by Hamilton eq 1. Logically equivalent, easier to prove.

### 6.2 field_simp Needs m ≠ 0
**Problem:** `field_simp` will need `p.m ≠ 0` for the Legendre transform inversions.
**Mitigation:** Extract `have hm_ne : p.m ≠ 0 := ne_of_gt p.hm` at the top of each proof. Pass to `field_simp [hm_ne]`.

### 6.3 Definitional Unfolding
**Problem:** `elSolutionPhaseSpace` is defined in terms of `elSolution` and `discreteMomentum`. Lean may need explicit `unfold` or `simp only [elSolutionPhaseSpace]` to see through the definitions.
**Mitigation:** Use `simp only [elSolutionPhaseSpace, discreteMomentum, elSolution]` before `ring` or `field_simp`.

### 6.4 Don't Over-Engineer the Hamiltonian Action
**Problem:** It might be tempting to define a separate Hamiltonian action functional and prove its minimizer requires FT independently.
**Mitigation:** DON'T. The Hamiltonian action is the same physical action expressed in phase space variables. For N=2 with the Legendre constraint imposed, it reduces to the same function of q₁. The existing `minimizer_iff_ft` already covers it. Just note this in a docstring. The FT half does not need any new Lean code.

---

## 7. PROOF ORDER

1. Add definitions (`discreteMomentum`, `legendreInverse`, `hamiltonian`, `elSolutionPhaseSpace`, `satisfiesHamiltonEq1`, `satisfiesHamiltonEq2`) to Defs.lean or a new HamiltonDefs section.
2. Prove `legendre_invertible` and `legendre_invertible'` — pure ring lemmas, instant.
3. Prove `hamilton_eqs_satisfied` — unfold + ring for eq1, invoke existing result for eq2.
4. Prove `hamilton_unique_solution` — the hardest new lemma but still straightforward algebra.
5. Update `Stratification.lean` with `stratification_triad`.
6. Run axiom audit on all new theorems.

---

## 8. PAPER CHANGES NEEDED

### 8.1 New Subsection in §3 or §4

Add "§3.5 The Discrete Hamiltonian Formulation" or "§4.4 Hamiltonian Half":

- Define H(q,p) = p²/(2m) + kq²/2
- Define discrete Legendre transform: p₁ = 2m(q₁ − A)
- State discrete Hamilton's equations for N=2
- Show unique solution (q*, p*) exists in BISH
- Show Legendre transform connects Lagrangian and Hamiltonian solutions (BISH)

### 8.2 Updated Stratification Theorem

Theorem 5.1 (or wherever) becomes the three-way stratification:
- Euler-Lagrange: BISH
- Hamilton's equations: BISH
- Legendre transform: BISH
- Variational principle (either formulation): FT

### 8.3 Updated Stratification Diagram

```
      ┌─────────────────────────────────────────────────┐
  FT  │  Lagrangian min ∃  ←→  Hamiltonian min ∃       │
      │  (same action, different variables)              │
      ├─────────────────────────────────────────────────┤
      │              ↑ requires FT                       │
      ├─────────────────────────────────────────────────┤
 BISH │  EL equation  ←—Legendre (BISH)—→  Hamilton eqs │
      │  q* = 4m(A+B)/(8m−k)    p* = 2m(q*−A)         │
      └─────────────────────────────────────────────────┘
```

### 8.4 Updated Discussion

- Remove the Hamiltonian from the "open questions" list (§5.3 item 3)
- Add discussion of the result: all three textbook formulations of classical mechanics stratify identically. The equation-solving content is always BISH; the optimization content is always FT. The Legendre transform bridging Lagrangian and Hamiltonian is BISH. This strengthens the conclusion that variational principles carry logical overhead independent of which variables are used.

### 8.5 Updated Line Count and Module Table

Add HamiltonBISH.lean to the module table. Expected total: ~500–540 lines.

---

## 9. EXPECTED LINE COUNTS

| File | Current Lines | New Lines | Total |
|------|-------------|-----------|-------|
| Defs.lean | 81 | +15 (new defs) | ~96 |
| BISHHalf.lean | 87 | 0 | 87 |
| FTHalf.lean | 104 | 0 | 104 |
| HamiltonBISH.lean | — | ~80–100 | ~80–100 |
| Stratification.lean | 116 | +20 (triad theorem) | ~136 |
| Main.lean | 14 | +1 (import) | 15 |
| **Total** | **416** | **~116–136** | **~530–550** |

---

## 10. SUCCESS CRITERIA

1. ✅ All new theorems compile with zero sorries
2. ✅ `#print axioms hamilton_unique_solution` shows NO FanTheorem
3. ✅ `#print axioms legendre_invertible` shows NO FanTheorem
4. ✅ `stratification_triad` compiles, packaging all four parts
5. ✅ Existing theorems unchanged (BISHHalf, FTHalf still compile)
6. ✅ Axiom audit clean: all new results are BISH

---

## 11. SUMMARY FOR AGENT

**You are extending Paper 28** from a two-way (Newton vs Lagrange) to a three-way (Newton vs Lagrange vs Hamilton) stratification. The new results are all BISH — Hamilton's equations are solved by explicit algebra, and the Legendre transform is an explicit invertible map. No new FT results are needed; the existing `minimizer_iff_ft` covers both variational formulations since they involve the same physical action.

**The key insight to formalize:** the Legendre transform (BISH) bridges two equation-solving formulations (both BISH), while the variational interpretation (FT) sits above both. The logical overhead of optimization is independent of the choice of variables (configuration space vs phase space).

**Keep it concrete.** Everything is for the harmonic oscillator at N=2. The definitions are explicit formulas. The proofs are algebra. If you find yourself building abstract infrastructure for symplectic geometry or general Legendre transforms, you've gone too far. Back up and use the explicit formulas.
