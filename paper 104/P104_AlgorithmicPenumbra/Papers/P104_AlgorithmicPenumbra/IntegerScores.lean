/-
  IntegerScores.lean — Part V

  Integer clinical scores (qSOFA, NEWS, HEART) as BISH computations.
  These scores use only integer arithmetic and Boolean comparisons,
  making them strictly ℚ-computable without any omniscience principle.

  Paper 104 of the Constructive Reverse Mathematics Series
-/
import Mathlib.Tactic

namespace P104

/-! ## qSOFA Score (Sepsis)

  Quick Sequential Organ Failure Assessment.
  Three binary criteria, each 0 or 1. Total ∈ {0, 1, 2, 3}.
  Alert threshold: ≥ 2.
  Reference: Singer et al., JAMA (2016). -/

/-- qSOFA input: three binary clinical observations -/
structure QSofaInput where
  systolicBP_le100 : Bool    -- SBP ≤ 100 mmHg
  respRate_ge22    : Bool    -- RR ≥ 22 breaths/min
  alteredMentation : Bool    -- GCS < 15
  deriving DecidableEq, Repr

/-- qSOFA score: sum of binary indicators -/
def qsofaScore (inp : QSofaInput) : ℕ :=
  inp.systolicBP_le100.toNat + inp.respRate_ge22.toNat + inp.alteredMentation.toNat

/-- qSOFA alert: score ≥ 2 -/
def qsofaAlert (inp : QSofaInput) : Bool :=
  decide (qsofaScore inp ≥ 2)

/-- qSOFA score range: 0 to 3 -/
theorem qsofa_range (inp : QSofaInput) : qsofaScore inp ≤ 3 := by
  unfold qsofaScore
  cases inp.systolicBP_le100 <;> cases inp.respRate_ge22 <;>
    cases inp.alteredMentation <;> simp [Bool.toNat]

/-- qSOFA decision is decidable (propositional form) -/
theorem qsofa_dec (inp : QSofaInput) :
    qsofaScore inp ≥ 2 ∨ ¬(qsofaScore inp ≥ 2) :=
  if h : qsofaScore inp ≥ 2 then .inl h else .inr h

/-! ## NEWS Score (Deterioration)

  National Early Warning Score. Seven parameters, each 0-3.
  Total ∈ {0, ..., 21}. Alert threshold: ≥ 5 (medium), ≥ 7 (high).
  Reference: Royal College of Physicians (2012). -/

/-- NEWS component score: 0–3 -/
structure NEWSComponent where
  val : Fin 4
  deriving DecidableEq, Repr

/-- NEWS input: seven component scores -/
structure NEWSInput where
  respRate    : NEWSComponent
  spO2        : NEWSComponent
  airOrO2     : NEWSComponent
  temperature : NEWSComponent
  systolicBP  : NEWSComponent
  heartRate   : NEWSComponent
  consciousness : NEWSComponent
  deriving DecidableEq, Repr

/-- NEWS total score -/
def newsScore (inp : NEWSInput) : ℕ :=
  inp.respRate.val.val + inp.spO2.val.val + inp.airOrO2.val.val +
  inp.temperature.val.val + inp.systolicBP.val.val +
  inp.heartRate.val.val + inp.consciousness.val.val

/-- NEWS score range: 0 to 21 -/
theorem news_range (inp : NEWSInput) : newsScore inp ≤ 21 := by
  unfold newsScore
  have := inp.respRate.val.isLt
  have := inp.spO2.val.isLt
  have := inp.airOrO2.val.isLt
  have := inp.temperature.val.isLt
  have := inp.systolicBP.val.isLt
  have := inp.heartRate.val.isLt
  have := inp.consciousness.val.isLt
  omega

/-- NEWS alert levels -/
inductive NEWSAlert where
  | low    : NEWSAlert  -- 0–4
  | medium : NEWSAlert  -- 5–6
  | high   : NEWSAlert  -- ≥ 7
  deriving DecidableEq, Repr

/-- NEWS alert classification: pure integer comparison -/
def newsAlertLevel (inp : NEWSInput) : NEWSAlert :=
  if newsScore inp ≥ 7 then .high
  else if newsScore inp ≥ 5 then .medium
  else .low

/-- NEWS decision is decidable -/
theorem news_dec (inp : NEWSInput) (k : ℕ) :
    newsScore inp ≥ k ∨ ¬(newsScore inp ≥ k) :=
  if h : newsScore inp ≥ k then .inl h else .inr h

/-! ## HEART Score (Cardiac Risk)

  History, ECG, Age, Risk factors, Troponin.
  Five components, each 0–2. Total ∈ {0, ..., 10}.
  Alert: ≤ 3 low risk, 4–6 moderate, ≥ 7 high.
  Reference: Six et al., Netherlands Heart J (2008). -/

/-- HEART component: 0–2 -/
structure HEARTComponent where
  val : Fin 3
  deriving DecidableEq, Repr

/-- HEART input -/
structure HEARTInput where
  history     : HEARTComponent
  ecg         : HEARTComponent
  age         : HEARTComponent
  riskFactors : HEARTComponent
  troponin    : HEARTComponent
  deriving DecidableEq, Repr

/-- HEART total score -/
def heartScore (inp : HEARTInput) : ℕ :=
  inp.history.val.val + inp.ecg.val.val + inp.age.val.val +
  inp.riskFactors.val.val + inp.troponin.val.val

/-- HEART score range: 0 to 10 -/
theorem heart_range (inp : HEARTInput) : heartScore inp ≤ 10 := by
  unfold heartScore
  have := inp.history.val.isLt
  have := inp.ecg.val.isLt
  have := inp.age.val.isLt
  have := inp.riskFactors.val.isLt
  have := inp.troponin.val.isLt
  omega

/-- HEART risk classification -/
inductive HEARTRisk where
  | low      : HEARTRisk  -- 0–3
  | moderate : HEARTRisk  -- 4–6
  | high     : HEARTRisk  -- 7–10
  deriving DecidableEq, Repr

/-- HEART risk level: pure integer comparison -/
def heartRiskLevel (inp : HEARTInput) : HEARTRisk :=
  if heartScore inp ≥ 7 then .high
  else if heartScore inp ≥ 4 then .moderate
  else .low

/-- HEART decision is decidable -/
theorem heart_dec (inp : HEARTInput) (k : ℕ) :
    heartScore inp ≥ k ∨ ¬(heartScore inp ≥ k) :=
  if h : heartScore inp ≥ k then .inl h else .inr h

/-! ## Theorem A: Integer Scores Are BISH -/

/-- Theorem A: All integer clinical scores produce ℕ-valued output
    and their alert decisions are decidable without any omniscience principle.
    This is the formal content of the claim that integer scores are BISH. -/
theorem integer_scores_bish :
    -- qSOFA: ℕ-valued, bounded
    (∀ inp : QSofaInput, qsofaScore inp ≤ 3)
    -- NEWS: ℕ-valued, bounded
    ∧ (∀ inp : NEWSInput, newsScore inp ≤ 21)
    -- HEART: ℕ-valued, bounded
    ∧ (∀ inp : HEARTInput, heartScore inp ≤ 10)
    -- All threshold comparisons natively decidable over ℕ
    ∧ (∀ (n k : ℕ), n ≥ k ∨ ¬(n ≥ k)) :=
  ⟨qsofa_range, news_range, heart_range,
   fun n k => if h : n ≥ k then .inl h else .inr h⟩

end P104
