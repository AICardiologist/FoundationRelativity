import CategoryTheory.PseudoFunctor
import CategoryTheory.PseudoFunctor.Gap
import CategoryTheory.PseudoFunctor.AP
import CategoryTheory.PseudoFunctor.RNP
import CategoryTheory.Bicategory.FoundationAsBicategory

open CategoryTheory

#eval do
  IO.println "✓ PseudoFunctor.id compiles!"

-- Smoke test for pseudo-functors compile
#check @PseudoFunctor.id FoundationBicat _
#check GapFunctor
#check APFunctor
#check RNPFunctor

-- Verify functors have the right types
example : PseudoFunctor FoundationBicat FoundationBicat := PseudoFunctor.id FoundationBicat
example : PseudoFunctor FoundationBicat FoundationBicat := GapFunctor
example : PseudoFunctor FoundationBicat FoundationBicat := APFunctor
example : PseudoFunctor FoundationBicat FoundationBicat := RNPFunctor

#eval do
  IO.println "✓ All pseudo-functors compile successfully"
  IO.println "✓ Ready for Math-AI coherence proof implementation"