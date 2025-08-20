/-
Copyright (c) 2025 Foundation-Relativity Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Foundation-Relativity Team
-/

import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.Logic.WLPOBasic
import Papers.P2_BidualGap.Constructive.Ishihara
import Papers.P2_BidualGap.Constructive.DualStructure
import Papers.P2_BidualGap.HB.DualIsometriesComplete
import Papers.P2_BidualGap.WLPO_Equiv_Gap

/-!
# Paper 2: WLPO ↔ BidualGap∃ Equivalence

This module provides the main formalization from Paper 2, establishing
the equivalence between the Weak Limited Principle of Omniscience (WLPO)
and the existence of a Banach space with a proper bidual embedding.

## Main Results

* `WLPO_Equiv_Gap.wlpo_iff_gap` - The main bidirectional equivalence
* `DualIsometriesComplete` - Dual isometry (c₀ →L[ℝ] ℝ) ≃ₗᵢ ℓ¹
* `Ishihara` - The constructive kernel construction

## Implementation Notes

The formalization uses c₀ (sequences vanishing at infinity) as the witness
space, with only 3 WLPO-conditional sorries remaining in the dual isometry
proofs. The HasWLPO typeclass provides clean separation between constructive
and classical modes.

## Current Status

- Main theorem: Complete (0 sorries)
- Dual isometry: 3 WLPO-conditional sorries
- Build status: Clean compilation
-/

namespace Papers.P2_BidualGap

-- Main theorem is available via the imports

end Papers.P2_BidualGap