# Paper 15: Noether's Theorem and the Logical Cost of Global Conservation Laws

Lean 4 formalization of Noether's theorem (energy conservation) calibrated against
constructive omniscience principles. Fourth domain (after statistical mechanics,
general relativity, and quantum decoherence) exhibiting the BMC ↔ LPO pattern.

**Zenodo DOI:** 10.5281/zenodo.18572494

## Main Theorems

### Part A — BISH Content (Level 0)

```lean
theorem noether_conservation (hN : 2 ≤ N) (φ π : Fin N → ℝ) (V' : ℝ → ℝ) :
    totalEnergyRate (by omega) φ π V' = 0

theorem energyDensity_nonneg (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hN : 0 < N) (s : LatticeState N) (i : Fin N) :
    0 ≤ energyDensity V hN s i

theorem partialEnergy_mono (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (φ : ℕ → ℝ) (π : ℕ → ℝ) :
    Monotone (partialEnergy V φ π)
```

The algebraic conservation identity (Noether's theorem on a finite periodic lattice)
is purely constructive. Energy density is non-negative (weak energy condition).
Partial energy is monotone increasing. No limits, no completeness, no LPO.

### Part B — LPO Equivalence (Level 1)

```lean
theorem npsc_iff_bmc : NPSC ↔ BMC     -- pure BISH, no custom axioms!

theorem global_energy_iff_LPO :
    (∀ (V : ℝ → ℝ), (∀ x, 0 ≤ V x) →
      ∀ (φ : ℕ → ℝ) (π : ℕ → ℝ) (M : ℝ), (∀ N, partialEnergy V φ π N ≤ M) →
      ∃ E : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |partialEnergy V φ π N - E| < ε)
    ↔ LPO
```

The assertion "for every bounded field configuration with V ≥ 0, the total energy
E = lim E_N exists" is equivalent to LPO. The abstract framework NPSC ↔ BMC is
pure BISH (no omniscience axioms).

## Four Domains, One Logical Structure

| Domain              | Paper | Bounded Monotone Sequence | LPO Content              |
|---------------------|-------|---------------------------|--------------------------|
| Stat. Mech.         | P8    | Free energy f_N           | f_∞ exists exactly       |
| Gen. Rel.           | P13   | Radial coordinate r(τ)    | r → 0 exactly            |
| Quantum Meas.       | P14   | Coherence c(N)            | c → 0 exactly (collapse) |
| **Conservation Laws** | **P15** | **Partial energy E_N**  | **E = lim E_N exists**   |

## Dependencies

- **Lean 4:** `leanprover/lean4:v4.28.0-rc1`
- **Mathlib4:** commit `7091f0f601d5aaea565d2304c1a290cc8af03e18` (pinned in `lake-manifest.json`)

## File Manifest

### Lean Source Files (`P15_Noether/Papers/P15_Noether/`)

| File | Lines | Role |
|------|-------|------|
| `Defs.lean` | 157 | Lattice types, energy density, fnext/fprev, non-negativity |
| `LocalConservation.lean` | 190 | Periodic BC shift lemmas, Noether's theorem (dE/dt = 0) |
| `Monotonicity.lean` | 68 | Partial energy recurrence, monotonicity |
| `LPO_BMC.lean` | 57 | LPO/BMC definitions + axiomatized equivalence |
| `GlobalEnergy.lean` | 200 | NPSC framework, npsc_iff_bmc, encoding, headline theorem |
| `Main.lean` | 100 | Assembly + `#print axioms` audit |

### Other Files

| File | Description |
|------|-------------|
| `paper15_writeup.tex` | LaTeX source for the paper |
| `paper15_writeup.pdf` | Compiled PDF (15 pages) |
| `README.md` | This file |

## Build

```bash
cd P15_Noether
lake exe cache get    # download prebuilt Mathlib oleans
lake build            # ~2 min with cache, ~45 min without
```

Expected output: 1955 jobs, 0 errors, 0 sorry, 0 warnings.

## Axiom Certificate

**BISH theorems** (`noether_conservation`, `energyDensity_nonneg`, `partialEnergy_mono`, `sum_shift`, etc.):
- `[propext, Classical.choice, Quot.sound]` — standard Mathlib infrastructure only
- Classical.choice traces to `Fin.fintype` and `Real.instField` (type infrastructure)
- No custom axioms, no omniscience principles

**Abstract framework** (`npsc_iff_bmc`):
- Fully proved, no custom axioms — NPSC ↔ BMC is pure BISH

**LPO theorems** (`global_energy_iff_LPO`, `npsc_iff_lpo`):
- Above + `bmc_of_lpo`, `lpo_of_bmc` (axiomatized, citing Bridges-Vîță 2006 and Paper 8)

**CRM Audit Details:**
- `by_cases` uses `instDecidableEqNat` (zero axioms), not `Classical.em`
- `Nat.eq_or_lt_of_le` and `Nat.succ_le_of_lt` are axiom-free
- No `Classical.em`, no `Classical.byContradiction` anywhere in source

## Architecture

```
Defs.lean
  ├── LocalConservation.lean              (Noether's theorem, BISH)
  ├── Monotonicity.lean                   (partial energy monotonicity, BISH)
  │     └── GlobalEnergy.lean             (NPSC ↔ LPO, headline theorem)
  ├── LPO_BMC.lean                        (axiomatized interface)
  │     └── GlobalEnergy.lean
  └── Main.lean                           (assembly + axiom audit)
```

## Mathematical Content

**Part A (BISH):** Scalar field on a 1D lattice with periodic boundary conditions.
The energy E_N = Σ [½π² + ½(Δφ)² + V(φ)] is conserved under Hamilton's equations
(Noether's theorem as algebraic identity). Each energy density term is non-negative.
The partial energy E_N is monotone increasing for V ≥ 0.

**Part B (LPO):** The assertion that E = lim E_N exists for ALL bounded configurations
with non-negative potential is equivalent to LPO. The abstract framework NPSC
(Nonnegative Partial Sum Convergence) is equivalent to BMC, which is equivalent to LPO.
The reverse direction encodes arbitrary bounded monotone sequences into lattice field
configurations via π_i = √(2·d_i) with V = 0, φ = 0.

**The sign trap:** The result applies only to positive-definite densities (energy).
Signed densities (electric charge) produce oscillating partial sums that do not
fit the BMC pattern.

## License

CC BY 4.0. See repository root for details.
