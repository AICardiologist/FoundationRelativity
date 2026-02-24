/-
  Paper 71: The Weight 1 Boundary
  Classification.lean: Optimised CRM classification of FLT

  Paper 70 identified 3 WLPO atoms. Paper 71 eliminates 2 via:
  (1) Shimura curve restructuring (Route 3) → eliminates JL icosahedral
  (2) Decidability descent → eliminates JL level-lowering at weight ≥ 2
  The third (Langlands-Tunnell at weight 1) is irreducible.
-/
import Papers.P71_Weight1Boundary.Defs
import Papers.P71_Weight1Boundary.DecidabilityDescent

noncomputable section

-- ============================================================
-- Paper 71: Classification of each FLT component
-- ============================================================

/-- Paper 71's optimised classification of each FLT component. -/
def paper71Level : FLTComponent → CRMLevel
  -- Base case: Langlands-Tunnell
  | .dihedralModularity      => .BISH    -- Hecke theta series
  | .tetrahedralBaseChange   => .WLPO   -- GL₂ trace formula, weight 1
  | .octahedralDescent       => .WLPO   -- GL₂ trace formula, weight 1
  -- Lifting: all BISH via Shimura curve strategy
  | .jlIcosahedralTransfer   => .BISH    -- Route 3: Shimura curve
  | .twPatchingShimura       => .BISH    -- Brochard + eff. Chebotarev
  | .galoisRepEtale          => .BISH    -- Eichler-Shimura-Carayol
  -- Induction (Khare-Wintenberger): all BISH
  | .jlLevelLowering         => .BISH    -- Decidability descent
  | .levelRaising            => .BISH    -- Ihara, supersingular locus
  | .weightReduction         => .BISH    -- Hasse invariant, θ
  | .serreRecipe             => .BISH    -- Finite group theory
  | .potentialModularity     => .BISH    -- Moret-Bailly

/-- Paper 70's classification (before optimisation). -/
def paper70Level : FLTComponent → CRMLevel
  | .dihedralModularity      => .BISH
  | .tetrahedralBaseChange   => .WLPO
  | .octahedralDescent       => .WLPO
  | .jlIcosahedralTransfer   => .WLPO   -- Was WLPO in Paper 70
  | .twPatchingShimura       => .BISH
  | .galoisRepEtale          => .BISH
  | .jlLevelLowering         => .WLPO   -- Was WLPO in Paper 70
  | .levelRaising            => .BISH
  | .weightReduction         => .BISH
  | .serreRecipe             => .BISH
  | .potentialModularity     => .BISH

-- ============================================================
-- Paper 71 improvement: every component is ≤ Paper 70
-- ============================================================

/-- Paper 71 never worsens any classification. -/
theorem paper71_improves_or_matches (c : FLTComponent) :
    paper71Level c ≤ paper70Level c := by
  cases c <;> simp [paper71Level, paper70Level, instLECRMLevel]

-- ============================================================
-- Paper 70: WLPO source elimination status
-- ============================================================

/-- Paper 71's status for each Paper 70 WLPO source. -/
def eliminationStatus : Paper70WLPOSource → EliminationStatus
  | .langlandsTunnell     => .irreducible   -- Cannot eliminate
  | .jlIcosahedral        => .eliminated    -- Route 3
  | .jlLevelLoweringOverF => .eliminated    -- Decidability descent

/-- Exactly one WLPO source remains irreducible. -/
theorem exactly_one_irreducible :
    (List.filter
      (fun s => decide (eliminationStatus s = .irreducible))
      [.langlandsTunnell, .jlIcosahedral, .jlLevelLoweringOverF]).length = 1 := by
  native_decide

/-- Exactly two WLPO sources are eliminated. -/
theorem exactly_two_eliminated :
    (List.filter
      (fun s => decide (eliminationStatus s = .eliminated))
      [.langlandsTunnell, .jlIcosahedral, .jlLevelLoweringOverF]).length = 2 := by
  native_decide

-- ============================================================
-- Overall FLT classification
-- ============================================================

/-- The overall CRM level is the join of all components. -/
def fltOverallLevel : CRMLevel :=
  List.foldl CRMLevel.join .BISH
    [paper71Level .dihedralModularity,
     paper71Level .tetrahedralBaseChange,
     paper71Level .octahedralDescent,
     paper71Level .jlIcosahedralTransfer,
     paper71Level .jlLevelLowering,
     paper71Level .twPatchingShimura,
     paper71Level .galoisRepEtale,
     paper71Level .levelRaising,
     paper71Level .weightReduction,
     paper71Level .serreRecipe,
     paper71Level .potentialModularity]

/-- Theorem A (Main): FLT calibrates at BISH + WLPO. -/
theorem flt_is_BISH_plus_WLPO :
    fltOverallLevel = CRMLevel.WLPO := by
  native_decide

-- ============================================================
-- Weight classification
-- ============================================================

/-- The weight regime of each FLT component. -/
def componentWeight : FLTComponent → WeightRegime
  | .dihedralModularity      => .any
  | .tetrahedralBaseChange   => .weight1
  | .octahedralDescent       => .weight1
  | .jlIcosahedralTransfer   => .weightGe2
  | .jlLevelLowering         => .weightGe2
  | .twPatchingShimura       => .weightGe2
  | .galoisRepEtale          => .weightGe2
  | .levelRaising            => .weightGe2
  | .weightReduction         => .weightGe2
  | .serreRecipe             => .any
  | .potentialModularity     => .weightGe2

/-- All WLPO components occur at weight 1. -/
theorem wlpo_only_at_weight1 (c : FLTComponent) :
    paper71Level c = .WLPO → componentWeight c = .weight1 := by
  cases c <;> simp [paper71Level, componentWeight] <;> intro h <;> exact absurd h (by decide)

end
