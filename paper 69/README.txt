Paper 69: The Logical Cost of the Archimedean Place
Function Field Langlands is BISH
Paul Chun-Kit Lee, New York University
February 2026

Paper 69, Constructive Reverse Mathematics Series
Zenodo DOI: 10.5281/zenodo.18749757


SUMMARY

This paper applies Constructive Reverse Mathematics (CRM) to the function
field Langlands correspondence. Both Laurent Lafforgue's proof for GL_n
(Inventiones, 2002) and Vincent Lafforgue's proof for general reductive G
(JAMS, 2018) are classified at BISH: every component operates within
Bishop's constructive mathematics, with no omniscience principle required.

Paper 68 showed that the number field Langlands program costs BISH + WLPO,
with the WLPO entering solely through the Archimedean place. This paper
shows that every WLPO component over number fields has a BISH counterpart
over function fields. The comparison yields: the logical cost of the
Langlands program is the logical cost of R.

This is the final audit paper of the CRM series. Paper 70 provides the
synthesis.


MAIN RESULTS

Theorem A. Laurent Lafforgue's proof (GL_n over F_q(C)) is BISH.
           Five components audited, all BISH.

Theorem B. Vincent Lafforgue's proof (general G over F_q(C)) is BISH.
           Five components audited, all BISH.

Theorem C. Every WLPO component over number fields has a BISH counterpart
           over function fields. The structural source of the WLPO is the
           Archimedean place. (Structural identification, not a proved
           lower bound.)


PACKAGE CONTENTS

paper69_funcfield.pdf       Paper (13 pages)
paper69_funcfield.tex       LaTeX source
P69_FuncField/              Lean 4 Lake project
  Papers/P69_FuncField/
    Main.lean               Main formalization (236 lines)
  lakefile.lean             Build configuration (no Mathlib dependency)
  lean-toolchain            leanprover/lean4:v4.28.0-rc1
  Papers.lean               Root module
README.txt                  This file


LEAN 4 FORMALIZATION

Build status:   0 errors, 0 warnings, 0 sorry
Lean version:   v4.28.0-rc1
Mathlib:        Not used (pure Lean 4 kernel)
Axioms:         28 custom axioms (14 component/classification pairs)
Classical.choice: Not present in #print axioms for any theorem

To build:
  cd P69_FuncField
  lake build

The formalization encodes the CRM hierarchy as an inductive type with
decidable ordering. Each proof component is axiomatized with a CRM
classification, and the assembly theorems verify that the join of all
component levels equals BISH. The main theorems (funcfield_langlands_is_BISH,
logical_cost_of_R) are verified by the Lean kernel using decide.


AXIOM INVENTORY

Function field (Laurent Lafforgue, GL_n):
  1. laurent_compactification      = BISH   [Lafforgue 2002, Ch. I-IV]
  2. laurent_etale_cohomology       = BISH   [Deligne 1980]
  3. grothendieck_lefschetz         = BISH   [SGA 4.5]
  4. funcfield_arthur_selberg       = BISH   [Lafforgue 2002, S.V]
  5. laurent_cuspidal_isolation     = BISH   [Harder 1974]

Function field (Vincent Lafforgue, general G):
  6. vincent_shtuka_cohomology      = BISH   [V. Lafforgue 2018, SS.3-5]
  7. geometric_satake               = BISH   [Mirkovic-Vilonen 2007]
  8. excursion_algebra              = BISH   [V. Lafforgue 2018, SS.10-11]
  9. chars_to_parameters            = BISH   [V. Lafforgue 2018, S.12]
 10. funcfield_chebotarev           = BISH   [Weil 1948]

Number field comparison (from Paper 68):
 11. numfield_arthur_selberg        = WLPO   [Paper 68, SS.6-7]
 12. langlands_tunnell              = WLPO   [Paper 68, S.6]
 13. numfield_weight1_space         = WLPO   [Paper 68, S.11.4]
 14. taylor_wiles                   = BISH   [Paper 68, SS.8-9] (documentary)


SERIES CONTEXT

This is Paper 69 of the Constructive Reverse Mathematics series.
Predecessor: Paper 68 (Fermat's Last Theorem is BISH)
Successor:   Paper 70 (Synthesis: the logical cost of R)

The series began with Paper 2 (bidual gap, WLPO) and progresses through
69 audit papers covering quantum mechanics, statistical mechanics, algebraic
geometry, and the Langlands program. Paper 70 provides the synthesis.


REPRODUCIBILITY

Zenodo:   https://doi.org/10.5281/zenodo.18749757
Lean:     leanprover/lean4:v4.28.0-rc1
Build:    lake build (completes in under one second)


CONTACT

Paul Chun-Kit Lee
dr.paul.c.lee@gmail.com
New York University
