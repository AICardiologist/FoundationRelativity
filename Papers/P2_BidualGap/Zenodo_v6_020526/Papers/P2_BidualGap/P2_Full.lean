/-
Copyright (c) 2025 Axiom Calibration Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Calibration Team
-/

-- Papers/P2_BidualGap/P2_Full.lean
-- Local/dev aggregator for the fuller build (mathlib-based).
-- NOTE: This is NOT part of CI. Use locally once toolchain is aligned.

import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.Logic.WLPOBasic
import Papers.P2_BidualGap.HB.DirectDual
-- import Papers.P2_BidualGap.HB.OptionB.ClassicalInstances  -- after you add it
-- import Papers.P2_BidualGap.Constructive.Ishihara           -- when toolchain is OK
-- import Papers.P2_BidualGap.HB.DualIsometriesComplete       -- when toolchain is OK
-- import Papers.P2_BidualGap.WIP.WLPO_Equiv_Gap              -- old approach (moved to WIP)

/-!
# Paper 2: Full Build Target (Development)

This module imports all Paper 2 components including mathlib-dependent files.
Use this for local development once the toolchain is properly aligned.

## Current Status

- Basic definitions and WLPO typeclass: Available
- DirectDual: c₀ bidual construction (0 sorries)
- Option B: See P2_Minimal for the dependency-free core
- Main theorem: Available when toolchain fixed

## Building

```bash
# First fix toolchain:
# Copy mathlib's lean-toolchain to root, then:
lake update
lake clean
lake exe cache get
lake build Papers.P2_BidualGap.P2_Full
```
-/

namespace Papers.P2_BidualGap

-- The full Paper 2 machinery is available via imports

end Papers.P2_BidualGap