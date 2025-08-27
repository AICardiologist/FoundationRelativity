/-
  Sanity tests for D3(c4) layer: chi_matches and symmetric difference bounds
-/
import Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals

open Papers.P4Meta.StoneSupport
open Classical

noncomputable section

-- Pointwise agreement lemma
example {R} [CommRing R] [DecidableEq R] [TwoIdempotents R]
  (f : Linf R) (n : ℕ) (h : f n * f n = f n) :
  chi (R := R) (A_of f) n = f n :=
  chi_matches_of_idem_point (R := R) f h

-- Symmetric difference bound
example {R} [CommRing R] [DecidableEq R] [TwoIdempotents R]
  (f g : Linf R) :
  A_of (R := R) f △ A_of (R := R) g ⊆ supp' (R := R) (f - g) :=
  sdiff_A_of_subset_supp_sub (R := R) f g

-- PhiStoneIdem and PhiStone are definitionally related:
-- PhiStoneIdem returns a subtype {e // e*e = e} while PhiStone returns just the element.
-- The .1 projection of PhiStoneIdem equals PhiStone by construction.

-- Test that supp' of negation equals supp'
-- Note: supp'_neg is defined in section D3c4 which has TwoIdempotents in scope,
-- but the lemma itself doesn't use it (as the linter warns).
-- We need to provide the TwoIdempotents instance even though it's not used.
example {R : Type*} [CommRing R] [DecidableEq R] [TwoIdempotents R] (f : Linf R) :
    supp' (R := R) (-f) = supp' (R := R) f :=
  supp'_neg f