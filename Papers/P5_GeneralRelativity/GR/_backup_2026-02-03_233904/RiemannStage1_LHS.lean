/-
  Standalone Stage-1 LHS facts for Riemann.lean.
  This file is NOT imported by Riemann.lean, so it is baseline-neutral by default.
  Build it explicitly to validate Stage-1 lemmas:
    lake build Papers.P5_GeneralRelativity.GR.RiemannStage1_LHS
-/
import Papers.P5_GeneralRelativity.GR.Riemann

open scoped
  -- (add any scopes you normally use)

namespace Papers.P5_GeneralRelativity.GR
namespace Stage1_LHS

section FirstFamily
  /- We parameterize by all indices/coordinates explicitly so this compiles standalone. -/
  variable (M r θ : ℝ) (a b c d : Idx)

  /-- Stage-1 fact: LHS c-branch, first family (expand e = t only). -/
  private def Pt  : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)
  private def Pr  : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)
  private def Pθ  : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)
  private def Pφ  : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)

  lemma Hc_one :
    dCoord c (fun r θ => Pt  M r θ a b c d r θ
                         + Pr  M r θ a b c d r θ
                         + Pθ  M r θ a b c d r θ
                         + Pφ  M r θ a b c d r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ
    + dCoord c (Pr M r θ a b c d) r θ
    + dCoord c (Pθ M r θ a b c d) r θ
    + dCoord c (Pφ M r θ a b c d) r θ := by
    -- 4-term linearity from binary steps
    have hAB :
      dCoord c (fun r θ => Pt M r θ a b c d r θ + Pr M r θ a b c d r θ) r θ
        = dCoord c (Pt M r θ a b c d) r θ + dCoord c (Pr M r θ a b c d) r θ := by
      simpa using dCoord_add c (Pt M r θ a b c d) (Pr M r θ a b c d) r θ
    have hCD :
      dCoord c (fun r θ => Pθ M r θ a b c d r θ + Pφ M r θ a b c d r θ) r θ
        = dCoord c (Pθ M r θ a b c d) r θ + dCoord c (Pφ M r θ a b c d) r θ := by
      simpa using dCoord_add c (Pθ M r θ a b c d) (Pφ M r θ a b c d) r θ

    have hABCD :
      dCoord c
        (fun r θ =>
          (Pt M r θ a b c d r θ + Pr M r θ a b c d r θ) +
          (Pθ M r θ a b c d r θ + Pφ M r θ a b c d r θ)) r θ
      =
      (dCoord c (Pt M r θ a b c d) r θ + dCoord c (Pr M r θ a b c d) r θ)
      + (dCoord c (Pθ M r θ a b c d) r θ + dCoord c (Pφ M r θ a b c d) r θ) := by
      simpa [add_comm, add_left_comm, add_assoc]
        using dCoord_add c
              (fun r θ => Pt  M r θ a b c d r θ + Pr  M r θ a b c d r θ)
              (fun r θ => Pθ M r θ a b c d r θ + Pφ M r θ a b c d r θ) r θ

    have hsum_c :
      dCoord c
        (fun r θ => Pt  M r θ a b c d r θ
                   + Pr  M r θ a b c d r θ
                   + Pθ  M r θ a b c d r θ
                   + Pφ  M r θ a b c d r θ) r θ
      =
      dCoord c (Pt M r θ a b c d) r θ
      + dCoord c (Pr M r θ a b c d) r θ
      + dCoord c (Pθ M r θ a b c d) r θ
      + dCoord c (Pφ M r θ a b c d) r θ := by
      simpa [add_comm, add_left_comm, add_assoc] using hABCD

    -- Product rule on the t-summand
    have hPt_push :
      dCoord c (Pt M r θ a b c d) r θ
      =
      dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * g M Idx.t b r θ
      + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
      simpa using
        dCoord_mul c
          (fun r θ => Γtot M r θ Idx.t d a)
          (fun r θ => g M Idx.t b r θ) r θ

    have H := hsum_c
    rw [hPt_push] at H
    simpa [add_comm, add_left_comm, add_assoc] using H

  /-- Stage-1 fact: LHS d-branch, first family (expand e = t only). -/
  private def Qt  : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.t c a) * (g M Idx.t b r θ)
  private def Qr  : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)
  private def Qθ  : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)
  private def Qφ  : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)

  lemma Hd_one :
    dCoord d (fun r θ => Qt  M r θ a b c d r θ
                         + Qr  M r θ a b c d r θ
                         + Qθ  M r θ a b c d r θ
                         + Qφ  M r θ a b c d r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ
    + dCoord d (Qr M r θ a b c d) r θ
    + dCoord d (Qθ M r θ a b c d) r θ
    + dCoord d (Qφ M r θ a b c d) r θ := by
    have hAB :
      dCoord d (fun r θ => Qt M r θ a b c d r θ + Qr M r θ a b c d r θ) r θ
        = dCoord d (Qt M r θ a b c d) r θ + dCoord d (Qr M r θ a b c d) r θ := by
      simpa using dCoord_add d (Qt M r θ a b c d) (Qr M r θ a b c d) r θ
    have hCD :
      dCoord d (fun r θ => Qθ M r θ a b c d r θ + Qφ M r θ a b c d r θ) r θ
        = dCoord d (Qθ M r θ a b c d) r θ + dCoord d (Qφ M r θ a b c d) r θ := by
      simpa using dCoord_add d (Qθ M r θ a b c d) (Qφ M r θ a b c d) r θ

    have hABCD :
      dCoord d
        (fun r θ =>
          (Qt M r θ a b c d r θ + Qr M r θ a b c d r θ) +
          (Qθ M r θ a b c d r θ + Qφ M r θ a b c d r θ)) r θ
      =
      (dCoord d (Qt M r θ a b c d) r θ + dCoord d (Qr M r θ a b c d) r θ)
      + (dCoord d (Qθ M r θ a b c d) r θ + dCoord d (Qφ M r θ a b c d) r θ) := by
      simpa [add_comm, add_left_comm, add_assoc]
        using dCoord_add d
              (fun r θ => Qt  M r θ a b c d r θ + Qr  M r θ a b c d r θ)
              (fun r θ => Qθ M r θ a b c d r θ + Qφ M r θ a b c d r θ) r θ

    have hsum_d :
      dCoord d
        (fun r θ => Qt  M r θ a b c d r θ
                   + Qr  M r θ a b c d r θ
                   + Qθ  M r θ a b c d r θ
                   + Qφ  M r θ a b c d r θ) r θ
      =
      dCoord d (Qt M r θ a b c d) r θ
      + dCoord d (Qr M r θ a b c d) r θ
      + dCoord d (Qθ M r θ a b c d) r θ
      + dCoord d (Qφ M r θ a b c d) r θ := by
      simpa [add_comm, add_left_comm, add_assoc] using hABCD

    have hQt_push :
      dCoord d (Qt M r θ a b c d) r θ
      =
      dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ * g M Idx.t b r θ
      + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ := by
      simpa using
        dCoord_mul d
          (fun r θ => Γtot M r θ Idx.t c a)
          (fun r θ => g M Idx.t b r θ) r θ

    have H := hsum_d
    rw [hQt_push] at H
    simpa [add_comm, add_left_comm, add_assoc] using H

end FirstFamily

end Stage1_LHS
end Papers.P5_GeneralRelativity.GR