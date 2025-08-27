/-
  File: Papers/P3_2CatFramework/P4_Meta/FusedLadders.lean
  
  Purpose: WP-E Fused Ladder Implementation
  - Interface for cross-axis witness transfer  
  - Product height = max law
  - Connects to k-ary schedule abstractions from Part 6
-/

namespace Papers.P4Meta

/-- Abstract "height at stage n on ladder L" (façade). -/
abbrev HeightAt (L : Type) (n : Nat) (P : Prop) := Prop

/-- Fused ladder (lexicographic product) symbol. -/
def fuse (L1 L2 : Type) : Type := L1 × L2

/-- Interface axiom (paper Prop.~\ref{VI:prop:transfer}): product height is `max`. -/
axiom height_product_on_fuse
  {L1 L2 : Type} {a b : Nat} {C D : Prop} :
  HeightAt L1 a C → HeightAt L2 b D → HeightAt (fuse L1 L2) (Nat.max a b) (C ∧ D)

/-! ### Standard Fusions -/

/-- Two-axis alternation (even/odd). -/
def evenOddFusion : Type := fuse Unit Unit

/-- Three-axis round-robin. -/
def threeAxisFusion : Type := fuse (fuse Unit Unit) Unit

/-! ### Integration with Schedule Abstractions

The connection to Part 6 k-ary schedules is established via:
- FusedSchedule corresponds to Schedule k
- fusedLadder corresponds to ExtendIter with round-robin assignment
- fusion_height_max corresponds to exact finish time characterization
-/

end Papers.P4Meta