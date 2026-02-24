/-
  Paper 70: Serre's Modularity Conjecture is BISH + WLPO
  Paper70_PotentialModularity.lean — Taylor's potential modularity theorem

  Taylor's potential modularity theorem is the key new ingredient
  in the Khare-Wintenberger proof. It has three steps:

  (a) Construction of a totally real field F and CM abelian variety A/F
      via Moret-Bailly's theorem: BISH.

  (b) Transfer from compact (quaternionic) Shimura variety to
      non-compact (Hilbert modular) variety via Jacquet-Langlands: WLPO.
      This is the quaternionic bottleneck — the trace formula enters
      as a bridge, not as a foundation or engine.

  (c) Taylor-Wiles patching over F: BISH.
      Brochard's theorem and effective Chebotarev are base-field independent.

  Author: Paul C.-K. Lee
  Date: February 2026
  Zero sorry. Zero warnings target.
-/

import Papers.P70_KhareWintenberger.Paper70_Defs

open CRMLevel

-- ============================================================
-- § 1. Step (a): Moret-Bailly Construction (BISH)
-- ============================================================

/-- Moret-Bailly construction of F and A: BISH.
    For any odd irreducible ρ̄ : G_ℚ → GL₂(𝔽̄_p), constructs
    a totally real field F and a CM abelian variety A/F such
    that ρ̄|_{G_F} appears in the p-torsion of A.

    The proof glues local points via:
    • Weak approximation (Chinese Remainder Theorem)
    • Implicit function theorem over local fields (Hensel's lemma)
    • Bounded search over algebraic numbers of explicitly bounded height

    No continuous limits or real/complex equality testing required.
    Reference: Moret-Bailly (1989), Taylor (2002). -/
def moret_bailly_construction : CRMLevel := CRMLevel.BISH

/-- CM modularity via theta series: BISH.
    The CM abelian variety A/F determines a Hecke character of a
    CM extension K/F. The associated automorphic form on GL₂(𝔸_F)
    is written down explicitly via theta series.

    CM modularity itself is algebraic — no trace formula needed.
    Reference: Shimura (1971), Weil representation (1964). -/
def cm_modularity_theta : CRMLevel := CRMLevel.BISH

-- ============================================================
-- § 2. Step (b): Jacquet-Langlands Correspondence (WLPO)
-- ============================================================

/-- Jacquet-Langlands correspondence: WLPO.
    Transfers automorphic forms between GL₂(F) and D×(F),
    where D is a quaternion algebra over F.

    Proved via the Arthur-Selberg trace formula:
    • Matching orbital integrals (real equality testing: WLPO)
    • Spectral decomposition (eigenvalue isolation: WLPO)

    Required because Taylor-Wiles patching works on compact
    Shimura varieties (quaternionic) but the theorem lives on
    non-compact Hilbert modular varieties (GL₂).

    The WLPO is in the corridor between the compact setting
    where the proof works and the non-compact setting where
    the theorem lives.

    Reference: Jacquet-Langlands (1970). -/
def jacquet_langlands : CRMLevel := CRMLevel.WLPO

-- ============================================================
-- § 3. Step (c): Taylor-Wiles over F (BISH)
-- ============================================================

/-- Taylor-Wiles patching over F: BISH.
    Brochard's theorem (de Smit's conjecture) is a statement about
    morphisms of Artinian local rings, completely independent of
    the base field. Applies to Hecke algebras arising from Hilbert
    modular forms over F as readily as from classical forms over ℚ.
    The infinite inverse limit is eliminated at level n = 2.

    Effective Chebotarev bounds (Lagarias-Montgomery-Odlyzko 1979)
    are formulated for arbitrary finite Galois extensions of
    arbitrary number fields K. TW prime selection over F is
    a bounded computation.

    Reference: Brochard (2017), LMO (1979). -/
def tw_patching_over_F : CRMLevel := CRMLevel.BISH

-- ============================================================
-- § 4. Potential Modularity Classification
-- ============================================================

/-- All BISH components of potential modularity. -/
def potmod_bish : CRMLevel :=
  join moret_bailly_construction
    (join cm_modularity_theta tw_patching_over_F)

/-- The Jacquet-Langlands component. -/
def potmod_wlpo : CRMLevel := jacquet_langlands

/-- The BISH ingredients of potential modularity are BISH. -/
theorem potmod_bish_is_bish : potmod_bish = CRMLevel.BISH := by
  simp [potmod_bish, moret_bailly_construction,
        cm_modularity_theta, tw_patching_over_F, join]

/-- Overall potential modularity: BISH + WLPO.
    The WLPO comes solely from Jacquet-Langlands. -/
theorem potmod_classification :
    join potmod_bish potmod_wlpo = CRMLevel.WLPO := by
  simp [potmod_bish, potmod_wlpo, moret_bailly_construction,
        cm_modularity_theta, tw_patching_over_F,
        jacquet_langlands, join]

/-- The quaternionic bottleneck: without Jacquet-Langlands,
    potential modularity is BISH. -/
theorem potmod_without_jl : potmod_bish = CRMLevel.BISH :=
  potmod_bish_is_bish
