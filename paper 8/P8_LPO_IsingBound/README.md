# Paper 8: Constructive Finite-Size Bounds for the 1D Ising Free Energy

Lean 4 formalization in two parts:

- **Part A:** The empirical content (finite-size bounds) of the 1D Ising model's thermodynamic limit is provable in BISH without any omniscience principle.
- **Part B:** The idealization (existence of the limit as a completed real) costs exactly LPO — it is equivalent to Bounded Monotone Convergence.

Together: LPO is genuine but dispensable for predictions.

## Main Theorems

### Part A: Dispensability

```lean
theorem ising_1d_dispensability
    (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → (hN : 0 < N) →
      |freeEnergyDensity β N hN - freeEnergyInfVol β| < ε
```

For every inverse temperature β > 0 and tolerance ε > 0, there exists a constructively computable N₀ such that for all N ≥ N₀, the finite-volume free energy density f_N(β) = -(1/N)·log(λ₊^N + λ₋^N) approximates the infinite-volume value f_∞(β) = -log(2·cosh β) within ε.

### Part B: LPO ↔ BMC Equivalence

```lean
theorem lpo_iff_bmc : LPO ↔ BMC
```

Over BISH, the Limited Principle of Omniscience is equivalent to Bounded Monotone Convergence. The backward direction (BMC → LPO) is proved by encoding binary sequences into 1D Ising free energy sequences and extracting decisions from convergence behavior.

## Axiom Profile

```
'Papers.P8.ising_1d_dispensability' depends on axioms: [propext, Classical.choice, Quot.sound]
'Papers.P8.lpo_of_bmc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Papers.P8.lpo_iff_bmc' depends on axioms: [propext, Classical.choice, Quot.sound, Papers.P8.bmc_of_lpo]
```

- Part A and the backward direction of Part B: standard Lean 4 axioms only. No LPO, WLPO, LLPO, or custom axioms.
- The full equivalence depends on one axiomatized result: `bmc_of_lpo` (forward direction, citing Bridges-Vita 2006).

## Build

```bash
lake build
```

Requires Lean 4 v4.28.0-rc1 and Mathlib.

## Verification Status

- **Errors:** 0
- **Warnings:** 0
- **Sorries:** 0
- **Custom axioms:** `bmc_of_lpo` (Part B forward direction, cited)

## File Manifest

### Part A: Finite-Size Bounds (730 lines)

| File | Lines | Purpose |
|------|------:|---------|
| `Basic.lean` | 67 | Core definitions: LPO, eigenvalues λ₊/λ₋, partition function, free energy |
| `EigenvalueProps.lean` | 119 | λ₊ > λ₋ > 0, tanh properties, partition function positivity |
| `LogBounds.lean` | 70 | Elementary inequalities: log(1+x) ≤ x, geometric decay bounds |
| `TransferMatrix.lean` | 117 | 2×2 transfer matrix T, projector decomposition T = λ₊·P₊ + λ₋·P₋ |
| `PartitionTrace.lean` | 64 | Bonus: Tr(T^N) = λ₊^N + λ₋^N via projector induction |
| `FreeEnergyDecomp.lean` | 87 | f_N = -log(λ₊) - (1/N)·log(1 + r^N) decomposition |
| `ErrorBound.lean` | 72 | \|f_N - f_∞\| ≤ (1/N)·r^N with exponential decay form |
| `ComputeN0.lean` | 54 | Constructive N₀ from β and ε |
| `Main.lean` | 72 | Assembly of dispensability theorem + axiom audit |
| `SmokeTest.lean` | 7 | Minimal import validation |

### Part B: LPO ↔ BMC (644 lines)

| File | Lines | Purpose |
|------|------:|---------|
| `PartB_Defs.lean` | 76 | Definitions: BMC, runMax, couplingSeq, freeEnergyAtCoupling, encodedSeq |
| `PartB_RunMax.lean` | 103 | Running maximum properties: monotonicity, characterization lemmas |
| `PartB_FreeEnergyAnti.lean` | 73 | g(J) = -log(2·cosh(β·J)) is strictly anti-monotone for β > 0 |
| `PartB_CouplingSeq.lean` | 76 | Coupling sequence: monotonicity, bounds, eventual constancy |
| `PartB_EncodedSeq.lean` | 83 | Encoded sequence: -F non-decreasing, bounded |
| `PartB_Forward.lean` | 21 | Axiom: LPO → BMC [Bridges-Vita 2006] |
| `PartB_Backward.lean` | 154 | Main theorem: BMC → LPO via free energy encoding |
| `PartB_Main.lean` | 58 | Assembly: LPO ↔ BMC + axiom audit |

**Combined total: 18 files, 1374 lines.**

## Proof Strategy

### Part A

The classical route to the thermodynamic limit uses the monotone convergence theorem (LPO-strength). We bypass this entirely:

1. **Closed-form solution:** The partition function Z_N = λ₊^N + λ₋^N is defined directly via transfer matrix eigenvalues (no configuration sums needed).

2. **Algebraic decomposition:** f_N(β) = -log(λ₊) - (1/N)·log(1 + r^N), where r = tanh(β) = λ₋/λ₊.

3. **Elementary bound:** log(1 + x) ≤ x gives |f_N - f_∞| ≤ (1/N)·r^N.

4. **Geometric decay:** Since 0 < r < 1, the bound (1/N)·r^N < ε for all N ≥ N₀, with N₀ constructively computable.

### Part B

1. **Encoding:** Binary sequence α → running maximum m(n) → coupling J(n) = if m(n) then J₁ else J₀ → free energy F(n) = g(J(n)).

2. **Apply BMC:** -F is non-decreasing and bounded, so BMC gives a limit L.

3. **Gap:** δ = g(J₀) - g(J₁) > 0 separates the two possible limit values.

4. **Decision:** Get N₁ from convergence modulus with ε = δ/2. Case split on runMax α N₁ (Bool, decidable): true gives a witness, false gives a contradiction argument.

## Dependency Graph

```
Part A:
  Basic ───────────┬──→ EigenvalueProps ──→ FreeEnergyDecomp ──→ ErrorBound ──→ ComputeN0 ──→ Main
                   │
  TransferMatrix ──┤──→ PartitionTrace (bonus)
                   │
  LogBounds ───────┘

Part B:
  Basic ──→ EigenvalueProps
                │
        PartB_Defs ──────────────────────────────────────────────────────────┐
           │                                                                 │
  PartB_RunMax    PartB_FreeEnergyAnti                                       │
           │              │                                                  │
  PartB_CouplingSeq       │                                        PartB_Forward (axiom)
           │              │                                                  │
  PartB_EncodedSeq ───────┘                                                  │
           │                                                                 │
  PartB_Backward ────────────────────────────────────────────────────────────┤
                                                                             │
                                                                    PartB_Main
```
