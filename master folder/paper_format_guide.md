Use Paper 45 as your guide for format.
use paper 50 as the foundation paper, paper 51/52/53 as the key support (tetralogy set of paper)
 Structure:
(0) Title: use title this is informative. Include (Paper number, of constructive reverse mathematics series) after title
(0a) abstract: should summize key finding so reader can known the main finding of the ppaer witjout reading
(1) INTRODUCTION (2-3 pages)
- State main theorems numbered (Theorem A, B, C...)
- Essential context for non-expert: brief CRM primer
(cite Papers 1-45 for full background, don't re-derive)
- Current state of the art for THIS conjecture (terse,
cite primary sources only)
- Relationship to atlas: where this paper fits in the
paper 50-53 framework
- Point back to relevant earlier papers in our series (especially trace progression why this paper exists)
(2) PRELIMINARIES (1 page)
- Definitions and axiomatized objects
- Logical principles used (LPO, MP, BISH — state precisely,
cite Bridges-Richman for details)
- No proofs in this section
(3) MAIN RESULTS with proofs (5-10 pages)
- Theorem-Proof-Theorem-Proof format
- Proofs must be complete and human-readable
- Terse but not cryptic: every step justified, minimal
connecting prose
- Flag where axioms are used explicitly
- For equivalence results (X ↔ LPO), prove both directions
(4) CRM AUDIT (1 page)
- Constructive strength classification of each result
- Which principles are necessary, which sufficient
- Comparison with Paper 45 calibration pattern
- Explicit statement of what descends, from where, to where
(5) FORMAL VERIFICATION (2-3 pages)
- Lean 4 file structure and build status
- Axiom inventory table (used/unused, load-bearing/documentary)
- Code snippets for KEY theorems only (not full listings)
- #print axioms output for main results
- Classical.choice audit: which theorems are constructively clean
(5a) include reproducibility details (Zenodo doi, mathlib build, etc_
(6) DISCUSSION (1 page)
- Connection to de-omniscientizing descent pattern
- What this calibration reveals about the motive
- Relationship to existing literature (Deligne, Grothendieck,
Scholze etc. as appropriate)
- Open questions specific to this conjecture
(7) CONCLUSION (half page)
- Significance: honest, precise. Do not undersell or overreach.
- State clearly: what is proved (Lean-verified), what is
rigorous analysis, what is conjecture.
(8) ACKNOWLEDGMENTS
- Standard AI disclosure and non-domain-expert disclaimer
- Reference to CRM community / Bishop dedication
(brief per paper, full dedication in Paper 50 atlas)
- Cite Mathlib contributors
References: 15-30 items. Cite what you use. Primary sources
preferred over surveys.
Target length: 15-20 pages per paper. Paper 50 (atlas survey):
25-35 pages.
Tone: mathematical — substance over narrative. But retain
enough exposition that a reader from constructive mathematics
OR arithmetic geometry can follow without the other background. 
(also: spell "program" US spelling; do not include Githib, only Zenodo site for Lean files download)
