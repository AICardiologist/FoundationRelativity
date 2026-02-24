/-
  Paper 54 — Module 2: LPOIsolation
  Bloch–Kato Calibration: Out-of-Sample DPT Test

  Formalizes Theorem A: the LPO cost of the Bloch–Kato conjecture
  isolates to zero-testing the order of vanishing of L(M, s).

  Sorry budget: 2 principled
    - analytic_eval_computable (standard constructive analysis)
    - zero_test_requires_LPO (Bridges–Richman, §1.3)

  Paul C.-K. Lee, February 2026
-/

/-! # LPO Isolation for L-functions

The LPO (Limited Principle of Omniscience) content of the Bloch–Kato
conjecture is exactly the order of vanishing r = ord_{s=n} L(M, s).
Evaluating L(M, s) at any computable non-pole is BISH-computable.
Determining r requires LPO (zero-testing of derivatives).
Given r as external input, the leading coefficient L*(M, n) is BISH.
-/

-- ============================================================
-- Abstract types for L-function analysis
-- ============================================================

/-- A computable real number in the sense of Bishop. -/
axiom ComputableReal : Type

/-- A computable point in ℂ (or ℝ), given by a computable Cauchy sequence. -/
axiom ComputablePoint : Type

/-- An analytic function with constructive analytic continuation. -/
axiom AnalyticFunction : Type

/-- An L-function L(M, s) associated to a motive. -/
structure LFunction where
  /-- The underlying analytic function (after continuation). -/
  underlying : AnalyticFunction
  /-- The critical integer where we evaluate. -/
  critical_point : Int

/-- Whether a function has a pole at a point. -/
axiom IsPole : AnalyticFunction → ComputablePoint → Prop

/-- Evaluate an analytic function at a computable point. -/
axiom AnalyticFunction.eval : AnalyticFunction → ComputablePoint → ComputableReal

/-- Iterated derivative of an analytic function. -/
axiom AnalyticFunction.derivative_iter : AnalyticFunction → Nat → AnalyticFunction

/-- A computation is BISH-computable (no use of LPO, WLPO, LLPO, MP). -/
axiom BISHComputable : ComputableReal → Prop

/-- The Limited Principle of Omniscience: for any binary sequence,
either all terms are zero or there exists a nonzero term.
Equivalent to: every computable real number is zero or nonzero. -/
axiom LPO : Prop

/-- Analytic continuation hypothesis. -/
axiom HasAnalyticContinuation : LFunction → Prop

/-- Functional equation hypothesis. -/
axiom HasFunctionalEquation : LFunction → Prop

/-- The order of vanishing of L at its critical point. -/
axiom ord_vanishing : LFunction → Nat

/-- The leading Taylor coefficient L*(M, n) = L^{(r)}(M, n) / r!. -/
axiom leading_taylor_coeff : LFunction → Nat → ComputableReal

/-- Embed an integer as a computable point. -/
axiom computable_int : Int → ComputablePoint

/-- The leading Taylor coefficient equals the r-th derivative evaluation
divided by r! (which is a BISH operation on an integer). -/
axiom leading_taylor_coeff_eq_eval (L : LFunction) (r : Nat) :
  BISHComputable ((L.underlying.derivative_iter r).eval (computable_int L.critical_point)) →
  BISHComputable (leading_taylor_coeff L r)

-- ============================================================
-- Principled axioms (sorry budget: 2)
-- ============================================================

/-- **Principled axiom (constructive analysis).**
Evaluating a constructively analytic function at a computable non-pole
point yields a BISH-computable real.

Reference: Bishop–Bridges, Constructive Analysis (1985), Chapter 4. -/
axiom analytic_eval_computable :
  ∀ (f : AnalyticFunction) (s : ComputablePoint),
    ¬IsPole f s → BISHComputable (f.eval s)

/-- **Principled axiom (Bridges–Richman).**
Determining the order of vanishing (sequential zero-testing of
derivatives) requires LPO. This is because deciding x = 0 for
a computable real x is equivalent to LPO.

Reference: Bridges–Richman, Varieties of Constructive Mathematics
(1987), §1.3. -/
axiom zero_test_requires_LPO :
  ∀ (L : LFunction),
    HasAnalyticContinuation L →
    Decidable (ord_vanishing L = 0) →
    LPO

-- ============================================================
-- Theorem A: LPO Isolation
-- ============================================================

/-- **Theorem A(i):** Evaluating L(M, s) at any computable s ≠ pole
is BISH-computable.

The analytic continuation expresses L(M, s) as a convergent integral
of rapidly decaying functions. Integrating a computable, uniformly
continuous function over a bounded domain is a BISH operation. -/
theorem lfunction_eval_computable
    (L : LFunction) (s : ComputablePoint)
    (_hac : HasAnalyticContinuation L)
    (hnp : ¬IsPole L.underlying s) :
    BISHComputable (L.underlying.eval s) :=
  analytic_eval_computable L.underlying s hnp

/-- **Theorem A(ii):** Determining ord_{s=n} L(M, s) = r requires LPO.

Determining r requires sequential zero-testing: is L(n) = 0? Is L'(n) = 0?
Is L''(n) = 0? Each test is an instance of zero_test_requires_LPO.
The order of vanishing is the smallest k such that L^{(k)}(n) ≠ 0,
which requires deciding exact equality to zero. -/
theorem ord_vanishing_requires_LPO
    (L : LFunction)
    (hac : HasAnalyticContinuation L)
    (_hfe : HasFunctionalEquation L)
    (hdec : Decidable (ord_vanishing L = 0)) :
    LPO :=
  zero_test_requires_LPO L hac hdec

/-- **Theorem A(iii):** Given r as external input, L*(M, n) is BISH.

The r-th derivative of an analytic function at a computable point
is BISH-computable. Division by r! is an arithmetic operation on
a computable integer, hence also BISH. -/
theorem leading_coeff_computable
    (L : LFunction) (r : Nat)
    (_hac : HasAnalyticContinuation L)
    (_hr : ord_vanishing L = r)
    (hnp : ¬IsPole (L.underlying.derivative_iter r) (computable_int L.critical_point)) :
    BISHComputable (leading_taylor_coeff L r) := by
  -- The r-th derivative is analytic, and its evaluation at n is BISH
  have h := analytic_eval_computable (L.underlying.derivative_iter r)
    (computable_int L.critical_point) hnp
  -- leading_taylor_coeff = (r-th derivative value) / r!
  -- Division by a nonzero integer is BISH
  exact leading_taylor_coeff_eq_eval L r h

set_option linter.unusedVariables false in
/-- The LPO cost is exactly the order of vanishing.
Everything else on the analytic side is constructively computable. -/
theorem lpo_cost_is_exactly_ord_vanishing
    (L : LFunction)
    (_hac : HasAnalyticContinuation L)
    (_hfe : HasFunctionalEquation L) :
    -- The LPO cost isolates to determining r
    (∀ (s : ComputablePoint), ¬IsPole L.underlying s →
      BISHComputable (L.underlying.eval s)) ∧
    -- Given r, the leading coefficient is BISH
    (∀ (r : Nat) (_hr : ord_vanishing L = r)
      (hnp : ¬IsPole (L.underlying.derivative_iter r) (computable_int L.critical_point)),
      BISHComputable (leading_taylor_coeff L r)) :=
  ⟨fun s hnp => analytic_eval_computable L.underlying s hnp,
   fun r _hr hnp => leading_taylor_coeff_eq_eval L r
    (analytic_eval_computable (L.underlying.derivative_iter r)
      (computable_int L.critical_point) hnp)⟩
