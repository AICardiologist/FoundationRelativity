/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_PosFam.lean

  A lightweight "positive family" wrapper around height certificates
  that composes neatly with the Part III/IV machinery:
    • stage(fam) := max stage among its certificates
    • toOmega    : push every certificate to the ω-limit theory
    • toBag      : reuse the existing bag aggregator (for bookkeeping)
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.PartIII_MultiSup
import Papers.P3_2CatFramework.P4_Meta.PartIV_Limit

namespace Papers.P4Meta

/-- A positive family is just a list of named height certificates. -/
abbrev PosFam (T : Theory) (step : Nat → Formula) :=
  List (Σ φ, HeightCertificate T step φ)

namespace PosFam
  variable {T : Theory} {step : Nat → Formula}

  /-- The "stage" of a family is the maximum certificate height. -/
  def stage (fam : PosFam T step) : Nat :=
    maxStageOfCerts fam

  @[simp] theorem stage_nil : stage ([] : PosFam T step) = 0 := rfl

  /-- Convert the family to a bag (for consolidated stage bookkeeping). -/
  def toBag (fam : PosFam T step) : HeightCertificateBag T step :=
    HeightCertificateBag.fromList fam

  /-- The bag's consolidated stage is definitionally the family stage. -/
  @[simp] theorem toBag_n (fam : PosFam T step) : (toBag fam).n = stage fam := rfl

  /-- Push every member of the family to the ω‑limit theory. -/
  def toOmega (fam : PosFam T step) :
      List (PSigma fun φ => (Extendω T step).Provable φ) :=
    fam.map (fun ⟨φ, c⟩ => PSigma.mk φ (certToOmega (T := T) (step := step) c))

  /-- Just the goal formulas carried by the family (no proofs). -/
  def goals (fam : PosFam T step) : List Formula :=
    fam.map (fun ⟨φ, _⟩ => φ)

  @[simp] theorem goals_nil : goals ([] : PosFam T step) = [] := rfl

  /-- Disjoint union (just list append). -/
  def union (fam₁ fam₂ : PosFam T step) : PosFam T step := fam₁ ++ fam₂
  infixl:65 " ⊍ " => union

  @[simp] theorem union_def (fam₁ fam₂ : PosFam T step) : fam₁ ⊍ fam₂ = fam₁ ++ fam₂ := rfl

  /-- `stage` unfolds on cons. -/
  theorem stage_cons
      (x : Σ φ, HeightCertificate T step φ) (fam : PosFam T step) :
      stage (x :: fam) = Nat.max x.2.n (stage fam) := by
    simp only [stage, maxStageOfCerts]
    rw [List.foldl_cons]
    -- Need to prove: foldl with initial (max 0 x.2.n) equals max x.2.n (foldl with initial 0)
    suffices ∀ init, List.foldl (fun acc item => Nat.max acc item.2.n) (Nat.max init x.2.n) fam = 
                     Nat.max x.2.n (List.foldl (fun acc item => Nat.max acc item.2.n) init fam) by
      exact this 0
    intro init
    induction fam generalizing init with
    | nil => simp [Nat.max_comm]
    | cons y ys ih =>
        simp only [List.foldl_cons]
        calc List.foldl (fun acc item => Nat.max acc item.2.n) (Nat.max (Nat.max init x.2.n) y.2.n) ys
          = List.foldl (fun acc item => Nat.max acc item.2.n) (Nat.max init (Nat.max x.2.n y.2.n)) ys := by
              congr 1; simp only [Nat.max_assoc]
          _ = Nat.max x.2.n (List.foldl (fun acc item => Nat.max acc item.2.n) (Nat.max init y.2.n) ys) := by
              rw [← ih]
              congr 1
              -- Need: init.max (x.2.n.max y.2.n) = (init.max y.2.n).max x.2.n
              -- This is just commutativity and associativity of max
              simp only [Nat.max_comm, Nat.max_assoc, Nat.max_left_comm]

  /-- Stage of a union is the max of stages. -/
  @[simp] theorem stage_append (fam₁ fam₂ : PosFam T step) :
      stage (fam₁ ++ fam₂) = Nat.max (stage fam₁) (stage fam₂) := by
    induction fam₁ with
    | nil => simp [stage, maxStageOfCerts]
    | cons x xs ih =>
        rw [List.cons_append, stage_cons, stage_cons, ih]
        simp only [Nat.max_assoc]

  /-- Monotonicity in either argument w.r.t. `⊍`. -/
  theorem stage_le_left  (fam₁ fam₂ : PosFam T step) : stage fam₁ ≤ stage (fam₁ ⊍ fam₂) := by
    simpa [union_def] using Nat.le_max_left  (stage fam₁) (stage fam₂)

  theorem stage_le_right (fam₁ fam₂ : PosFam T step) : stage fam₂ ≤ stage (fam₁ ⊍ fam₂) := by
    simpa [union_def] using Nat.le_max_right (stage fam₁) (stage fam₂)

  /-- Goals respect append. -/
  @[simp] theorem goals_append (fam₁ fam₂ : PosFam T step) :
      goals (fam₁ ++ fam₂) = goals fam₁ ++ goals fam₂ := by
    simp [goals, List.map_append]

  /-- ω‑image respects append. -/
  @[simp] theorem toOmega_append (fam₁ fam₂ : PosFam T step) :
      toOmega (fam₁ ++ fam₂) = toOmega fam₁ ++ toOmega fam₂ := by
    simp [toOmega, List.map_append]

  /-- Length is preserved by `toOmega` (it only maps proofs). -/
  @[simp] theorem toOmega_length (fam : PosFam T step) :
      (toOmega fam).length = fam.length := by
    simp [toOmega]

  /-- Push a positive family to `ExtendωPlus T step ε` (ω plus a finite tail). -/
  def toOmegaPlus (ε : Nat) (fam : PosFam T step) :
    List (PSigma fun φ => (ExtendωPlus T step ε).Provable φ) :=
    fam.map (fun ⟨φ, c⟩ =>
      PSigma.mk φ ⟨c.n, ExtendIter_le_mono (T := T) (step := step)
                  (Nat.le_add_right _ _) c.upper⟩)

  @[simp] theorem toOmegaPlus_length (ε : Nat) (fam : PosFam T step) :
    (toOmegaPlus (T := T) (step := step) ε fam).length = fam.length := by
    simp [toOmegaPlus]

  @[simp] theorem toOmegaPlus_append (ε : Nat) (fam₁ fam₂ : PosFam T step) :
    toOmegaPlus (T := T) (step := step) ε (fam₁ ++ fam₂)
      = toOmegaPlus (T := T) (step := step) ε fam₁
      ++ toOmegaPlus (T := T) (step := step) ε fam₂ := by
    simp [toOmegaPlus, List.map_append]

end PosFam

end Papers.P4Meta