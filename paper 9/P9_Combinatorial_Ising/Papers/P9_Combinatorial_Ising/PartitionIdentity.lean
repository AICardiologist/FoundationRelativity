/-
Papers/P9_Combinatorial_Ising/PartitionIdentity.lean
The combinatorial partition function identity.

Main result:
  Z_N(β) = (2·cosh β)^N + (2·sinh β)^N

derived from:
  1. Bond variable decomposition: Z_N = 2 · Σ_{valid bonds} Π exp(β·b_i)
  2. Cycle constraint: valid bonds have Π b_i = 1, equivalently #{b_i = -1} even
  3. Parity sieve: the constrained sum equals [(exp β + exp(-β))^N + (exp β - exp(-β))^N] / 2
  4. Identification: exp β + exp(-β) = 2·cosh β, exp β - exp(-β) = 2·sinh β

This file records the derivation. The partition function partitionFn is already
defined algebraically in Basic.lean as (2·cosh β)^N + (2·sinh β)^N, so
this file serves as documentation of the combinatorial route.

NO imports from LinearAlgebra.Matrix.* or Analysis.NormedSpace.*.
-/
import Papers.P9_Combinatorial_Ising.ParitySieve
import Papers.P9_Combinatorial_Ising.Basic

namespace Papers.P9

open Real

-- ========================================================================
-- The combinatorial derivation (documentation)
-- ========================================================================

/-- **Combinatorial partition function identity (Theorem 2.5).**

    Z_N(β) = (exp β + exp(-β))^N + (exp β - exp(-β))^N
           = (2·cosh β)^N + (2·sinh β)^N

    The derivation via bond variables and the parity sieve:
    1. Each configuration σ ∈ {±1}^N contributes Π_i exp(β·b_i(σ))
    2. Bond-config correspondence: 2 configs per valid bond pattern
    3. Z_N = 2 · Σ_{k≡N mod 2} C(N,k) · (exp β)^k · (exp(-β))^{N-k}
    4. By parity sieve: = (exp β + exp(-β))^N + (exp β - exp(-β))^N
    5. Identify: = (2·cosh β)^N + (2·sinh β)^N = partitionFn β N

    Since partitionFn is already defined as (twoCosh β)^N + (twoSinh β)^N,
    this theorem records that the combinatorial derivation yields the same formula. -/
theorem partitionFn_eq_cosh_sinh_pow (β : ℝ) (N : ℕ) :
    partitionFn β N = (2 * cosh β) ^ N + (2 * sinh β) ^ N := by
  unfold partitionFn twoCosh twoSinh

/-- The combinatorial derivation also yields the exponential form. -/
theorem partitionFn_eq_exp_form (β : ℝ) (N : ℕ) :
    partitionFn β N = (exp β + exp (-β)) ^ N + (exp β - exp (-β)) ^ N := by
  unfold partitionFn twoCosh twoSinh
  congr 1 <;> congr 1
  · exact (cosh_eq β).symm
  · exact (sinh_eq β).symm

end Papers.P9
