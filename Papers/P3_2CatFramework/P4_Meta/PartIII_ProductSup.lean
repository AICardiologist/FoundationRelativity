/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_ProductSup.lean

  Product/sup for height certificates:
  If we have certificates for φ and ψ at heights nφ, nψ along the SAME step function,
  we produce a pair certificate at height max nφ nψ (upper bound).
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature

namespace Papers.P4Meta

/-- A "pair-goal": we want both φ and ψ provable at the same stage. -/
structure PairGoal where
  φ : Formula
  ψ : Formula

/-- A product certificate asserting BOTH goals hold at stage `n`. -/
structure HeightCertificatePair
  (T : Theory) (step : Nat → Formula) (g : PairGoal) where
  n          : Nat
  upper_left : (ExtendIter T step n).Provable g.φ
  upper_right: (ExtendIter T step n).Provable g.ψ
  note       : String := ""

/-- Combine two single-goal certificates (same ladder) into a pair at `max`. -/
def combineCertificates
  {T : Theory} {step : Nat → Formula}
  {φ ψ : Formula}
  (cφ : HeightCertificate T step φ)
  (cψ : HeightCertificate T step ψ)
  : HeightCertificatePair T step ⟨φ, ψ⟩ :=
by
  -- lift each proof to stage max cφ.n cψ.n
  let j := Nat.max cφ.n cψ.n
  have hl : (ExtendIter T step j).Provable φ :=
    ExtendIter_le_mono (T := T) (step := step)
      (Nat.le_max_left  _ _) cφ.upper
  have hr : (ExtendIter T step j).Provable ψ :=
    ExtendIter_le_mono (T := T) (step := step)
      (Nat.le_max_right _ _) cψ.upper
  exact
  { n          := j
  , upper_left := hl
  , upper_right:= hr
  , note       :=
      s!"product/sup: lifted to max {cφ.n} {cψ.n} = {j}. " ++
      cφ.note ++ " | " ++ cψ.note
  }

namespace HeightCertificatePair

/-- Lift a pair certificate from stage `p.n` to any `j ≥ p.n`. -/
def lift
  {T : Theory} {step : Nat → Formula} {g : PairGoal}
  (p : HeightCertificatePair T step g) (j : Nat) (h : p.n ≤ j) :
  HeightCertificatePair T step g :=
{ n := j
, upper_left  := ExtendIter_le_mono (T := T) (step := step) h p.upper_left
, upper_right := ExtendIter_le_mono (T := T) (step := step) h p.upper_right
, note := p.note ++ s!" (lifted to stage {j})" }

/-- Transport a pair certificate from `A` to `B` when
    the step functions agree on all indices `< p.n`. Keeps the same height. -/
def transport
  {T : Theory} {A B : Nat → Formula} {g : PairGoal}
  (p : HeightCertificatePair T A g)
  (hagree : ∀ i, i < p.n → A i = B i) :
  HeightCertificatePair T B g :=
{ n := p.n
, upper_left := by
    have hTh := congrArg (fun Th => Th.Provable g.φ)
      (ExtendIter_congr (T := T) (A := A) (B := B) p.n hagree)
    exact Eq.mp hTh p.upper_left
, upper_right := by
    have hTh := congrArg (fun Th => Th.Provable g.ψ)
      (ExtendIter_congr (T := T) (A := A) (B := B) p.n hagree)
    exact Eq.mp hTh p.upper_right
, note := p.note ++ " (transported by pointwise congruence)" }

/-- Definitional stage equality for pair-certificate lift. -/
@[simp] theorem lift_n
  {T : Theory} {step : Nat → Formula} {g : PairGoal}
  (p : HeightCertificatePair T step g) (j : Nat) (h : p.n ≤ j) :
  (p.lift (T := T) (step := step) (g := g) j h).n = j := rfl

/-- Definitional stage equality for pair-certificate transport. -/
@[simp] theorem transport_n
  {T : Theory} {A B : Nat → Formula} {g : PairGoal}
  (p : HeightCertificatePair T A g)
  (hagree : ∀ i, i < p.n → A i = B i) :
  (p.transport (T := T) (A := A) (B := B) (g := g) hagree).n = p.n := rfl

end HeightCertificatePair

end Papers.P4Meta