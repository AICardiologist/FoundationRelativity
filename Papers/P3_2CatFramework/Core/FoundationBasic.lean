import Papers.P3_2CatFramework.Core.UniverseLevels

/-- A "foundation" lives in universe that can accommodate its fields. -/
structure Foundation : Type (𝓤₀ + 1) where
  U : Type 𝓤₀          -- the ambient universe / category of small things
  is_CCC   : True      -- stubs; keep proofs `True` until Paper 2
  has_lim  : True
  has_colim: True

/-- Interpretation functor between foundations. Lives in `𝓤₁`. -/
structure Interp (F G : Foundation) : Type 𝓤₁ where
  map_obj : F.U → G.U
  pres_lim : True
  pres_colim : True

attribute [simp] Interp.map_obj

/-- Gap witness structure indexed by foundation. Lives in `𝓤₀`. -/
structure GapWitness (F : Foundation) : Type 𝓤₀ where
  dummy : Unit  -- Paper 3 only needs the *existence*, not the data