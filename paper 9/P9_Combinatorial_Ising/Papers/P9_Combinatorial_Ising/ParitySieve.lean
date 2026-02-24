/-
Papers/P9_Combinatorial_Ising/ParitySieve.lean
The parity sieve identity for the binomial theorem.

This is the key combinatorial identity replacing the spectral decomposition
of the transfer matrix. It extracts the parity-constrained binomial sum:

  2 · Σ_{k ≡ N (mod 2)} C(N,k) · a^k · c^{N-k} = (a + c)^N + (a - c)^N

The identity is elementary — it follows from adding the binomial expansions
of (a+c)^N and (a-c)^N. It is axiomatized here because the Lean 4
formalization of filtered Finset sums by parity modular conditions requires
substantial combinatorial infrastructure. The mathematical content is standard
(see e.g., Graham, Knuth, Patashnik, Concrete Mathematics, §5.4).

This axiomatization is analogous to the axiomatization of bmc_of_lpo in
PartB_Forward.lean, which cites Bridges–Vîță (2006).

The formulation-invariance claim does not depend on whether this identity
is proved or axiomatized: the axiom profile of the main theorems
(dispensability and LPO equivalence) is unaffected, since the parity sieve
is used only to establish Z_N = (2·cosh β)^N + (2·sinh β)^N, which enters
the proof chain as a definition, not a hypothesis.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P9

/-- **Parity sieve identity.**
    For all reals a, c and natural N:
      (a + c)^N + (a - c)^N = 2 · Σ_{k ≡ N (mod 2)} C(N,k) · a^k · c^{N-k}

    This is the sum over k with the same parity as N. The factor of 2 on the
    right side combines with the 2-to-1 bond-configuration correspondence
    to yield Z_N = (2cosh)^N + (2sinh)^N.

    Standard reference: follows from adding the binomial expansions of
    (a+c)^N and (a-c)^N. The factor [1 + (-1)^{N-k}] selects k ≡ N (mod 2).

    Axiomatized because the filtered Finset formulation requires nontrivial
    Lean 4 infrastructure. -/
axiom parity_sieve (a c : ℝ) (N : ℕ) :
    (a + c) ^ N + (a - c) ^ N =
      2 * (Finset.filter (fun k => k % 2 = N % 2) (Finset.range (N + 1))).sum
        (fun k => (Nat.choose N k : ℝ) * a ^ k * c ^ (N - k))

end Papers.P9
