/-
Copyright (c) 2025 Foundation-Relativity Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Foundation-Relativity Team
-/

import Papers.P2_BidualGap.HB.OptionB.CorePure
import Papers.P2_BidualGap.HB.OptionB.Instances  -- Dummy instances showing end-to-end usage
-- The following would be imported once toolchain is fixed:
-- import Papers.P2_BidualGap.HB.DirectDual
-- import Papers.P2_BidualGap.Constructive.Ishihara
-- import Papers.P2_BidualGap.Basic
-- import Papers.P2_BidualGap.Logic.WLPOBasic

/-!
# Paper 2: Minimal Build Target

This module imports only the clean, cited files required for Paper 2.
It intentionally excludes:
- Archived/obsolete experiments
- WIP modules with many sorries
- Files being refactored (e.g., DualIsometries.lean)

## Core Components

* `CorePure` - Option B architecture (0 sorries, dependency-free)
* `DirectDual` - Direct c₀ bidual construction (0 sorries)
* `Ishihara` - Gap → WLPO direction (1 sorry for constructive step)
* `Basic` - Foundation definitions
* `WLPOBasic` - WLPO typeclass

## Option B Architecture

Under classical choice (e.g. via a Banach limit on ℓ∞), there exists
a nonzero bounded functional on the quotient ℓ∞/c₀. Our Option B bridge
then yields a bidual gap for ℓ∞. In Lean, we formalize the bridge and
keep the existence of such a functional as an instance/assumption, so
the analytic conclusion is modular and re-usable.

Separately, under WLPO we formalize the c₀ gap (the constructive part
used in Paper 2).
-/

namespace Papers.P2_BidualGap

-- The main theorem components are available via imports

end Papers.P2_BidualGap