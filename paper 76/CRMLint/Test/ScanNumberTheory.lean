/-
  CRMLint — NumberTheory Namespace Scan
  Paper 76 of the Constructive Reverse Mathematics Series

  Scans actual Mathlib declaration namespaces related to number theory.
-/
import CRMLint
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic

-- Number theory namespaces
#crm_scan Nat.Prime
#crm_scan ZMod
#crm_scan Int.ModEq

-- Real analysis namespace
#crm_scan Real
