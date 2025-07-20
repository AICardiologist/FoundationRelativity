/-!
# Relativity Index (ρ-degree)

Maps pathologies to their ρ-degree in the hierarchy of classical principles.
-/

namespace Found

/-- The ρ-degree hierarchy classifies pathologies by their logical strength -/
def rho_degree : Name → Nat
| ``Gap₂             => 1    -- Requires WLPO
| ``AP_Fail₂         => 1    -- Requires WLPO
| ``RNP_Fail₂        => 2    -- Requires DC_ω
| _                  => 0    -- Unknown/unclassified

end Found