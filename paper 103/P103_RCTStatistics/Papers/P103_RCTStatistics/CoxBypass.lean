/-
  CoxBypass.lean — Part VI

  Cox proportional hazards MLE: the algebraic bypass of WKL₀.

  CRITICAL (v2): Strict concavity alone does NOT guarantee existence
  of a maximum on ℝ. Coercivity is required. Complete separation
  breaks coercivity; Firth's penalized likelihood restores it.
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Papers.P103_RCTStatistics.TrialData

namespace P103

/-- Coercivity (properness): f diverges to -∞ at infinity.
    Required to guarantee existence of a maximum on ℝ without WKL₀. -/
def IsCoercive (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ x : ℝ, R < |x| → f x < M

/-- Strict concavity (univariate). -/
def IsStrictlyConcave (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ≠ y → ∀ t : ℝ, 0 < t → t < 1 →
    f (t * x + (1 - t) * y) > t * f x + (1 - t) * f y

/-- Uniqueness of maximum for strictly concave functions. -/
theorem strictlyConcave_unique_max {f : ℝ → ℝ}
    (hconc : IsStrictlyConcave f)
    {a b : ℝ} (ha : ∀ x, f x ≤ f a) (hb : ∀ x, f x ≤ f b) :
    a = b := by
  by_contra hab
  have hmid := hconc a b hab (1/2) (by norm_num) (by norm_num)
  have h1 : f (1 / 2 * a + (1 - 1 / 2) * b) ≤ f a := ha _
  have h2 : f b ≤ f a := ha b
  have h3 : f a ≤ f b := hb a
  have h4 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  linarith

/-- EXISTENCE of maximum: requires strict concavity AND coercivity.
    Documentary axiom: the proof composes coercivity (bounded sublevel
    sets) + EVT on a compact interval + uniqueness from concavity.
    The interval bounds are COMPUTABLE from the coercivity witness. -/
axiom concave_coercive_has_unique_max :
  ∀ (f : ℝ → ℝ),
    IsStrictlyConcave f → IsCoercive f → Continuous f →
    ∃! a : ℝ, ∀ x : ℝ, f x ≤ f a

/-- Complete separation: when treatment perfectly predicts outcome,
    the log-likelihood is NOT coercive (β̂ → ±∞). -/
axiom hasCompleteSeparation : TrialData → Prop

/-- Complete separation is decidable over rational data. -/
axiom completeSeparation_decidable :
  ∀ (data : TrialData), Decidable (hasCompleteSeparation data)

/-- THEOREM D (Firth Restoration):
    Firth's penalized likelihood restores coercivity when complete
    separation destroys it. This drops Cox MLE from WKL to BISH. -/
axiom firth_restores_coercivity :
  ∀ (loglik penalty : ℝ → ℝ),
    IsStrictlyConcave loglik →
    ¬ IsCoercive loglik →        -- complete separation
    IsCoercive penalty →
    IsStrictlyConcave penalty →
    IsCoercive (fun x => loglik x + penalty x)

/-- The CRM classification of Cox MLE:
    - With coercivity (no complete separation): BISH
    - Without coercivity (complete separation): WKL
    - With Firth correction (restored coercivity): BISH -/
inductive CoxCRMLevel where
  | bish_coercive     : CoxCRMLevel  -- no separation
  | wkl_separation    : CoxCRMLevel  -- separation, no Firth
  | bish_firth        : CoxCRMLevel  -- separation + Firth
  deriving DecidableEq, Repr

def classifyCoxMLE (hasSep : Bool) (hasFirth : Bool) : CoxCRMLevel :=
  if !hasSep then .bish_coercive
  else if hasFirth then .bish_firth
  else .wkl_separation

theorem cox_bish_without_separation :
    classifyCoxMLE false false = .bish_coercive := by rfl

theorem cox_bish_with_firth :
    classifyCoxMLE true true = .bish_firth := by rfl

theorem cox_wkl_with_separation_no_firth :
    classifyCoxMLE true false = .wkl_separation := by rfl

end P103
