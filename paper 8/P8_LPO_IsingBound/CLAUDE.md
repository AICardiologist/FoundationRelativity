# Claude Agent Instructions (P8_LPO_IsingBound)

## Project
Paper 8: Constructive Finite-Size Bounds for the 1D Ising Free Energy.

Main result: The empirical content of the 1D Ising thermodynamic limit
(finite-system free energy approximates the infinite-volume prediction within
any ε > 0) is provable in BISH — no omniscience principle (LPO, WLPO) needed.

## Build commands (run from P8_LPO_IsingBound/)
```bash
lake exe cache get
lake build
```

## Key files
- `Papers/P8_LPO_IsingBound/Basic.lean` — Core definitions
- `Papers/P8_LPO_IsingBound/Main.lean` — Main theorem assembly
- `paper8_1d_ising_proof_draft.md` — Mathematical proof draft (parent directory)

## Axiom policy
- **0 custom axioms** — `partitionFn` is defined directly as λ₊^N + λ₋^N
- Standard Lean axioms only: propext, Classical.choice, Quot.sound
- Verify with `#print axioms Papers.P8.ising_1d_dispensability`

## Conventions
- Namespace: `Papers.P8`
- All real-valued definitions are `noncomputable`
- Constructive proofs only in the main theorem chain — no LPO, WLPO, or full LEM
