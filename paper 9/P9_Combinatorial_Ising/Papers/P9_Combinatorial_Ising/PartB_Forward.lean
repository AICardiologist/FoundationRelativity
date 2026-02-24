/-
Papers/P9_Combinatorial_Ising/PartB_Forward.lean
Forward direction: LPO → BMC.

This is [Bridges–Vîță 2006, Theorem 2.1.5]. The proof constructs
the supremum of a bounded monotone sequence by binary search on the
value axis, using LPO at each step to decide whether the sequence
eventually exceeds a given rational threshold.

We axiomatize this direction. The novel content of Part B is the
backward direction (BMC → LPO) in PartB_Backward.lean.
-/
import Papers.P9_Combinatorial_Ising.PartB_Defs

namespace Papers.P9

/-- LPO implies Bounded Monotone Convergence.
    [Bridges–Vîță 2006, Theorem 2.1.5]. Axiomatized. -/
axiom bmc_of_lpo : LPO → BMC

end Papers.P9
