import Gap2.Functor
import APFunctor.Functor
import RNPFunctor.Functor

/-!
# Relativity Index (ρ-degree)

Maps pathologies to their ρ-degree in the hierarchy of classical principles.
-/

namespace Found

/-- The ρ-degree hierarchy classifies pathologies by their logical strength -/
def rho_degree : Lean.Name → Nat
| `Gap₂             => 1    -- Requires WLPO
| `AP_Fail₂         => 1    -- Requires WLPO
| `RNP_Fail₂        => 2    -- Requires DC_ω
| `RNP_Fail₃        => 2    -- Requires DC_{ω+1} (ρ=2+)
| `SpectralGap      => 3    -- Requires AC_ω
| _                 => 0    -- Unknown/unclassified

end Found