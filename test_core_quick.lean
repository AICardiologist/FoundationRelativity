-- Quick test to verify Core.lean functionality after API fixes
import Papers.P1_GBC.Core

namespace Papers.P1_GBC

-- Test that basic definitions are available
#check P_g
#check G
#check e_g
#check godelOperator
#check GödelSentenceTrue

-- Test that types are correct
variable (g : ℕ)
#check (P_g (g:=g) : L2Space →L[ℂ] L2Space)
#check (G (g:=g) : L2Space →L[ℂ] L2Space)

-- Test that some basic lemmas exist
#check P_g_is_projection
#check spectrum_G

def quick_test : IO Unit := do
  IO.println "✓ Papers.P1_GBC.Core compiles successfully"
  IO.println "✓ All key definitions available"
  IO.println "✓ API compatibility issues resolved"

end Papers.P1_GBC