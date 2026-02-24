/-
  Paper 28: Newton vs. Lagrange vs. Hamilton
  Constructive Stratification of Classical Mechanics
  Main.lean — Root module

  Series: Constructive Reverse Mathematics and Physics
  Depends on: Paper 23 (FT ↔ CompactOptimization) — definitions re-stated inline

  Main result: For the discrete harmonic oscillator (N=2 time steps),
  - Solving the EL equation dS/dq = 0 is BISH (constructive, no FT)
  - Solving Hamilton's equations is BISH (constructive, no FT)
  - The Legendre transform bridging them is BISH (invertible, explicit)
  - Asserting a minimizer of S exists is equivalent to the Fan Theorem

  Three-way stratification: all equation-solving is BISH;
  all optimization is FT; the bridge between formulations is BISH.

  Zero `sorry`s. Zero custom axioms.
-/
import Papers.P28_NewtonLagrange.Stratification
