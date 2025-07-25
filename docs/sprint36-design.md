# Sprint 36 Design Document – ρ = 4 Pathology
*(Borel‑Selector / Double‑Gap Operator)*

**Purpose.**  
Provide an analytic operator whose *two* separated spectral gaps force a selector
that is equivalent to **DC _{ω·2}** (strong Dependent Choice).  This will occupy
logical level ρ = 4 in the Foundation‑Relativity hierarchy.

---

## 0 Notation & Imports

* `L2Space`            – Hilbert space ℓ² (ℕ → ℂ) from `SpectralGap/HilbertSetup.lean`.
* `e n`                – standard basis vector.
* `χ b n`              – indicator (ℝ‐valued) of boolean sequence `b : ℕ → Bool`.
* `BoundedOp`          – continuous linear operator on `L2Space`.

We re‑use the boolean‑controlled diagonal pattern introduced for the Cheeger operator.

---

## 1 Operator Definition `ρ4 (β₀ β₁ β₂ : ℝ) (b : ℕ → Bool)`

ρ4 v := Σ n,  λ n ↦ (if b n then β₀ else β₂) • v n   – main diagonal
+   compact_shaft v                       – rank‑one compact bump

* **Parameters**

  | Symbol | constraint | role |
  |--------|------------|------|
  | `β₀`   | β₀ < β₁    | *low* eigenvalue when `b n = true` |
  | `β₁`   | gap anchor | value of rank‑one bump (affects only a fixed vector `u`) |
  | `β₂`   | β₁ < β₂    | *high* eigenvalue when `b n = false` |

  We fix `β₀ = 0`, `β₁ = ½`, `β₂ = 1` throughout the proofs; the inequalities create **two disjoint gaps**  
  `[β₀,β₀+¼]` and `[β₁+¼, β₂]`.

* **`compact_shaft`** – rank‑one operator  
  `compact_shaft v := ⟨inner v u⟩ • u`,  where `u := ∑_{n=0}^{∞} 2^{-(n+1)} e n`.  
  It pushes a single eigenvalue to `β₁`.

---

## 2 Analytic Lemmas (Day 2 targets)

| Lemma | Statement |
|-------|-----------|
| `rho4_selfAdjoint` | operator is self‑adjoint (diagonal + rank‑one Hermitian bump). |
| `rho4_bounded`     | ‖ρ4‖ ≤ `max {‖β₂‖, ‖β₁‖}`. |
| `rho4_has_two_gaps`| intervals `[β₀+¼, β₁-¼]` and `[β₁+¼, β₂-¼]` are spectral gaps. |
| `rho4_apply_basis` | explicit action on `e n` and on bump vector `u`. |

---

## 3 Logical Path (Days 3‑5)

1. **Selector ⇒ WLPO\+**  
   *Define `Sel₂` that must choose an *eigenspace representative from each gap*.  
   Boolean sequence controls *which* gap is empty.  Absence of an eigenvector in the
   "wrong" gap encodes a decision of the Π₀₂ sentence.*

2. **WLPO\+ ⇒ DC _{ω·2}**  
   *Reuse existing bridge `dcω2_of_wlpo_plus`.  Gives logical degree ρ = 4.*

3. **Classical Witness**  
   *Boolean stream `bTrue` (all `true`), vector `e 0` lies in low‐eigenvalue subspace.*

4. **Bridge Theorem**  

theorem Rho4_requires_DCω2 (hsel₂ : Sel₂) :
RequiresDCω2 ∧ witness_rho4

---

## 4 Sprint Schedule  (already mirrored in project board)

| Day | Deliverable | File |
|-----|-------------|------|
| 1 | Stub operator & section headers | `SpectralGap/Rho4.lean` |
| 2 | Analytic lemmas (self‑adjoint, bounded, two gaps) | same file |
| 3 | `wlpo_plus_of_sel₂` constructive impossibility | same |
| 4 | `witness_rho4_zfc` classical vector | same |
| 5 | Bridge theorem, 0 sorries | same |
| 6 | Lint, tests (`test/Rho4ProofTest.lean`) | tests |
| 7 | Docs (`docs/rho4-pathology.md`), update hierarchy table | docs |

---

## 5 File Layout Additions

* `SpectralGap/Rho4.lean`   – operator + proofs  
* `test/Rho4ProofTest.lean` – compile‑time #eval check  
* `docs/rho4-pathology.md` – explainer, diagrams  
* No new definitions outside `SpectralGap` namespace.

---

## 6 Dependencies & Risks

* **mathlib4** 4.22.0‑rc3 suffices; rank‑one compact operator is already there.
* Build time expected +6 s vs Cheeger.
* Ensure `compact_shaft` marked `noncomputable`.

---

*Prepared by **Math‑Coder AI**, Sprint 36 Day 1.*