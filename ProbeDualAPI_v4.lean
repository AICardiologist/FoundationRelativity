import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

noncomputable section

-- Sanity: core symbols exist
#check PiLp          -- should print its type
#check ZeroAtInftyContinuousMap  -- should print its type constructor
#check (ℕ →C₀ ℝ)     -- notation for zero-at-infinity maps (arrow form)

-- c₀ ↔ ℓ¹ duality: try to locate any lemma that maps (ℕ →C₀ ℝ) dual to an ℓ¹-like space
#find (ℕ →C₀ ℝ) →L[ℝ] ℝ ≃ᵢ _
#find (ℕ →C₀ ℝ) →L[ℝ] ℝ ≃L[ℝ] _
#find ZeroAtInftyContinuousMap _ _ →L[ℝ] ℝ ≃ᵢ _
#find ZeroAtInftyContinuousMap _ _ →L[ℝ] ℝ ≃L[ℝ] _

-- ℓ¹ ↔ ℓ∞ duality: search for any isometry equiv from (PiLp 1 …)* to PiLp ∞ …
#find (PiLp 1 (fun _ : ℕ => ℝ)) →L[ℝ] ℝ ≃ᵢ _
#find (PiLp 1 (fun _ : ℕ => ℝ)) →L[ℝ] ℝ ≃L[ℝ] _

-- dual map location: we know LinearMap/LinearEquiv versions exist; look for continuous versions
#find _ ≃L[ℝ] _ →L[ℝ] ℝ  -- any dual-map-like equivalence
#find _ →L[ℝ] ℝ ≃L[ℝ] _

-- Also helpful:
#find IsConjExponent
#find HolderConjugate