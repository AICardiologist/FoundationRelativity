# Paper 14: The Measurement Problem as a Logical Artefact

Lean 4 formalization of quantum decoherence calibrated against constructive
omniscience principles. Third domain (after statistical mechanics and general
relativity) exhibiting the BMC ↔ LPO pattern.

**Zenodo DOI:** 10.5281/zenodo.18569068

## Main Theorems

### Part A — BISH Content (Level 0)

```lean
theorem decoherence_epsilon_bound (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ)
    (hθ : 0 < θ ∧ θ < π) (hc : 0 < ‖ρ₀ 0 1‖) (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → coherence ρ₀ θ N < ε

theorem coherence_eq_geometric (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (N : ℕ) :
    coherence ρ₀ θ N = ‖ρ₀ 0 1‖ * |Real.cos (θ / 2)| ^ N
```

For any fixed interaction angle 0 < θ < π and any ε > 0, there is an
explicitly computable N₀ such that the coherence c(N) < ε for all N ≥ N₀.
The bound is constructive: N₀ depends only on the initial coherence, θ, and ε.
No limits, no completeness, no LPO.

### Part B — LPO Equivalence (Level 1)

```lean
theorem exact_decoherence_iff_LPO :
    (∀ (f : ℕ → ℝ), Antitone f → (∃ B : ℝ, ∀ n, B ≤ f n) →
      ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |f N - L| < ε)
    ↔ LPO
```

The assertion "every bounded antitone sequence converges exactly" is equivalent
to LPO. The coherence sequence is an instance (antitone, bounded below by 0).

### Verification Bonus

```lean
theorem decoherenceMap_eq_physical (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    decoherenceMap θ ρ = decoherenceMapPhysical θ ρ
```

The explicit decoherence formula equals the physical definition
(partial trace of conjugated Kronecker product): Φ(ρ) = Tr_E[U(θ)·(ρ⊗|0⟩⟨0|)·U†(θ)].
Proved by brute-force 4×4 matrix computation with Pythagorean identity in ℂ.

## Three Domains, One Logical Structure

| Domain              | Bounded Monotone Sequence | LPO Content            |
|---------------------|---------------------------|------------------------|
| Stat. Mech. (P8)    | Free energy f_N           | f_∞ exists exactly     |
| Gen. Rel. (P13)     | Radial coordinate r(τ)    | r → 0 exactly          |
| Quantum Meas. (P14) | Coherence c(N)            | c → 0 exactly (collapse)|

## Dependencies

- **Lean 4:** `leanprover/lean4:v4.28.0-rc1`
- **Mathlib4:** commit `7091f0f601d5aaea565d2304c1a290cc8af03e18` (pinned in `lake-manifest.json`)

## File Manifest

### Lean Source Files (`P14_Decoherence/Papers/P14_Decoherence/`)

| File | Lines | Role |
|------|-------|------|
| `Defs.lean` | 105 | Core definitions: controlledRotation, decoherenceMap, coherence |
| `PartialTrace.lean` | 37 | Partial trace over environment qubit |
| `DecoherenceMap.lean` | 105 | Entry lemmas, trace preservation, physical verification |
| `FiniteDecoherence.lean` | 85 | N-step iteration, geometric decay formula |
| `MonotoneDecay.lean` | 54 | Antitone + bounded properties of coherence |
| `CauchyModulus.lean` | 101 | BISH ε-bound (minimum publishable result) |
| `LPO_BMC.lean` | 62 | LPO/BMC definitions + axiomatized equivalence |
| `ExactDecoherence.lean` | 161 | ABC ↔ BMC ↔ LPO equivalence |
| `Main.lean` | 95 | Assembly + `#print axioms` audit |

### Other Files

| File | Description |
|------|-------------|
| `paper14_writeup.tex` | LaTeX source for the paper |
| `paper14_writeup.pdf` | Compiled PDF (13 pages) |
| `README.md` | This file |

## Build

```bash
cd P14_Decoherence
lake exe cache get    # download prebuilt Mathlib oleans
lake build            # ~2 min with cache, ~45 min without
```

Expected output: 0 errors, 0 sorry, 0 warnings (modulo unused simp lemma notes).

## Axiom Certificate

**BISH theorems** (`decoherence_epsilon_bound`, `coherence_eq_geometric`, etc.):
- `[propext, Classical.choice, Quot.sound]` — standard Mathlib infrastructure only
- No custom axioms, no omniscience principles

**LPO theorems** (`exact_decoherence_iff_LPO`, `lpo_iff_bmc`):
- Above + `bmc_of_lpo`, `lpo_of_bmc` (axiomatized, citing Bridges-Vita 2006 and Paper 8)

**Sign-flip lemma** (`abc_iff_bmc`):
- Fully proved, no custom axioms — the antitone/monotone equivalence is elementary

## Architecture

```
Defs.lean
  ├── PartialTrace.lean
  │     └── DecoherenceMap.lean
  │           └── FiniteDecoherence.lean
  │                 └── MonotoneDecay.lean
  │                       └── CauchyModulus.lean       (BISH endpoint)
  ├── LPO_BMC.lean
  │     └── ExactDecoherence.lean                      (LPO endpoint)
  └── Main.lean                                        (assembly + audit)
```

## Mathematical Content

The decoherence map sends a 2×2 density matrix ρ to:
- Diagonal: ρ₀₀ → ρ₀₀, ρ₁₁ → ρ₁₁ (populations preserved)
- Off-diagonal: ρ₀₁ → ρ₀₁ · cos(θ/2) (coherence damped)

After N iterations: c(N) = ‖ρ₀₁‖ · |cos(θ/2)|^N (geometric decay).

The BISH content: for any specific angle with 0 < θ < π, the coherence is
computable to any precision. The LPO content: asserting that the completed
limit exists for ALL bounded antitone sequences — including those with no
explicit decay rate — is the omniscience assertion.

## License

See repository root for license information.
