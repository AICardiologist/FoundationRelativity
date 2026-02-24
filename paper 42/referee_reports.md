# Referee Reports — Paper 42

**"The Worst Prediction in Physics Is Not a Prediction: Axiom Calibration of the Cosmological Constant Problem"**
*Paul Chun-Kit Lee (NYU), February 2026, Paper 42 of the CRM Programme*

---

## Report 1: Constructive Reverse Mathematics Expert

**Reviewer expertise:** Constructive mathematics, Weihrauch degrees, omniscience principles, reverse mathematics.

### Summary

This paper applies a "constructive reverse mathematics" (CRM) framework to the cosmological constant problem in physics, decomposing the infamous 10^120 discrepancy into three logically distinct components classified by their position in the omniscience hierarchy (BISH, LPO). Seven theorems are formalized in Lean 4 with Mathlib. The paper claims: (I) the divergence is regulator-dependent scaffolding, (II) naturalness is a Bayesian prior outside the constructive hierarchy, and (III) the genuine fine-tuning equation is an LPO equality via Fekete's subadditive lemma.

### Evaluation

**Strengths:**

1. **Well-structured CRM introduction.** The introduction provides a competent, self-contained overview of the omniscience spine (BISH < LLPO < WLPO < LPO < LEM) with correct physical interpretations at each level. The citations to Bishop [6], Bridges & Richman [21], Bridges & Vita [7], Ishihara [22], and Brattka et al. [8] are appropriate and correctly attributed. The Fan Theorem is correctly identified as independent of the omniscience spine.

2. **Correct identification of the core mechanism.** The claim that the LPO cost enters via Fekete's subadditive lemma (and the equivalence Fekete ≡ LPO established in Paper 29) is the strongest part of the paper from a CRM standpoint. Bounded monotone convergence (BMC) is indeed equivalent to LPO in the constructive reverse mathematics sense, and subadditive sequences converge via BMC. The logical flow Theorem 5 → Theorem 7 correctly identifies where the non-constructive content enters.

3. **Clean separation of concerns.** The three-claim decomposition is logically clean: Claims I and II involve no omniscience principles at all, while Claim III pins the cost precisely at LPO. This is a genuine contribution to understanding the logical structure.

**Weaknesses and Required Revisions:**

4. **The "axiom calibration" methodology is non-standard CRM.** Classical CRM (Ishihara, Bridges, Richman, Diener, et al.) establishes equivalences: "Theorem T is equivalent to Principle P over BISH." This paper establishes at most one direction: "Principle P suffices for Theorem T." The paper does not prove that the fine-tuning equation *requires* LPO — only that LPO suffices. To make a genuine CRM contribution, the authors would need to show that the existence of the thermodynamic limit for interacting QFT vacuum energy *implies* LPO (or some omniscience principle). Without the reverse direction, the calibration is an upper bound on logical cost, not a tight equivalence. The paper acknowledges this implicitly by appealing to Paper 29 (Fekete ≡ LPO), but the bridge axioms (subadditivity, bounded below) mean the connection is *via* Fekete, not a direct equivalence for the physical quantity.

   **Recommendation:** State explicitly whether the calibration is a tight equivalence or an upper bound. If only an upper bound, discuss what additional work would be needed for the reverse direction. The current phrasing ("placing the fine-tuning equation at exactly LPO") suggests tightness that has not been established.

5. **Bridge axioms sidestep the hard CRM questions.** The entire constructive content of the formalization rests on the bridge axioms (11 physics axioms declared in Defs.lean). These axioms assert properties like "the mode sum is unbounded" and "the lattice energy is subadditive" without proof. From a CRM perspective, the interesting question is *whether* these properties hold constructively — i.e., whether subadditivity of lattice ground-state energy is provable in BISH, or whether it requires additional principles. The paper treats these as given, which is appropriate for the physics application but means the CRM analysis is conditional on unverified constructive premises.

   **Recommendation:** Add a remark or subsection discussing the constructive status of the bridge axioms themselves. Are they BISH-provable facts about lattice Hamiltonians? Or do some require additional principles? This is where a CRM expert would want more precision.

6. **The role of `Classical.choice` deserves more nuance.** The paper correctly notes that `Classical.choice` appears due to Mathlib's construction of ℝ and argues that constructive stratification is established by proof content, not by axiom-checker output (citing Paper 10). This is a reasonable position but requires care: in a Lean formalization that imports Mathlib, *every* theorem about ℝ inherits `Classical.choice`, making the axiom checker uninformative for distinguishing BISH from LPO. The entire stratification then rests on the author's assertion about "proof content," which is not machine-checkable.

   **Recommendation:** The paper should be more forthright about this limitation. The machine-checked guarantee is that the proofs are correct in classical logic; the constructive stratification is a *mathematical claim about the proofs*, verified by human inspection, not by the Lean type checker. This is still valuable but should be stated clearly.

7. **Missing connection to Weihrauch degrees.** The introduction cites Brattka et al. [8] for the omniscience spine but does not use Weihrauch degrees at all. The modern CRM community increasingly uses Weihrauch reducibility to calibrate mathematical theorems. The Fekete ≡ LPO equivalence, if established as a Weihrauch equivalence, would be significantly stronger than a mere provability equivalence. Does Paper 29 establish this? If so, it should be mentioned.

   **Recommendation:** Clarify whether the Fekete ≡ LPO equivalence is in the sense of Weihrauch degrees, provability over BISH, or some other notion. This matters for the CRM community.

8. **Minor: LLPO and WLPO appear in the introduction but never in the paper's theorems.** All seven theorems are classified as BISH or LPO. The intermediate levels (LLPO, WLPO) are mentioned only for context. This is not an error — the CC problem may genuinely not engage these levels — but it slightly undermines the motivation for introducing them so carefully.

### Verdict

The paper makes a legitimate contribution by applying CRM methodology to a high-profile physics problem and correctly identifying the logical cost as LPO (via Fekete). However, the analysis is weaker than standard CRM in several respects: the calibration is an upper bound rather than a tight equivalence, the bridge axioms are unverified constructive premises, and the machine-checking guarantees classical correctness rather than constructive stratification. With the recommended revisions (particularly items 4, 5, and 6), the paper would be a solid contribution to the CRM-physics interface.

**Recommendation: Major revision** (address items 4–7; items 5 and 6 require new discussion, not new proofs).

---

## Report 2: Theoretical Physics Expert

**Reviewer expertise:** Quantum field theory in curved spacetime, cosmological constant problem, vacuum energy, naturalness.

### Summary

The paper applies a formal logical framework ("constructive reverse mathematics") to the cosmological constant problem, decomposing it into three claims: (I) the 10^120 is a regulator-dependent artifact, (II) naturalness is a Bayesian prior, (III) the fine-tuning is an "LPO equality." Seven theorems are stated and formalized in a proof assistant.

### Evaluation

**Strengths:**

1. **The three-claim decomposition is physically reasonable.** The distinction between the regulator-dependent divergence, the naturalness argument, and the genuine fine-tuning equation is well-motivated and largely correct. The paper correctly identifies that different regularization schemes yield different values (Martin [25] is the right reference), that the Hollands-Wald framework [2,3] establishes c₁ as a free parameter, and that the Casimir effect demonstrates the physical significance of energy *differences* rather than absolutes. The literature engagement in the introduction and discussion is now substantial and mostly accurate.

2. **Correct treatment of Hollands-Wald.** The paper correctly represents the Hollands-Wald result: in algebraic QFT on curved spacetime, the renormalized stress-energy tensor contains undetermined local curvature terms, and the cosmological constant coefficient c₁ is genuinely free. This is one of the strongest arguments in the paper and is properly supported by the formalization (Theorem 3, `lambda_free_parameter`), even though the formal proof is just subtraction.

3. **Good engagement with the naturalness debate.** The citations to 't Hooft [26], Burgess [27], Hossenfelder [29], Giudice [30], and Bianchi-Rovelli [28] correctly represent the current state of the naturalness debate. The characterization of naturalness as a "Bayesian prior" rather than a theorem is defensible, though see criticism below.

**Weaknesses and Required Revisions:**

4. **The 10^120 number and the "worst prediction" framing need more care.** The paper's title claims "the worst prediction in physics is not a prediction." This is too strong. While it is true that the *exact* value of the vacuum energy depends on the regularization scheme, the *existence* of a large vacuum energy contribution is a prediction of QFT (any massive field contributes to the cosmological constant at at least the scale m^4/(16π²)). Martin [25] carefully argues that the properly renormalized value is much smaller than the naively quoted 10^120 but is still non-zero and still requires explanation. The paper should distinguish between the naively large cutoff-regularized value (which is indeed scheme-dependent) and the properly renormalized but still non-zero contribution (which is scheme-independent, though of order m^4, not M_Pl^4).

   **Recommendation:** Modify the dissolution claim to acknowledge that while the 10^120 is scheme-dependent, the existence of vacuum energy contributions at the scale of known particle masses (Higgs, top quark) is scheme-independent. The "dissolution" applies to the *magnitude* of the discrepancy, not to the *existence* of a vacuum energy contribution.

5. **Subadditivity of lattice ground-state energy is stated without justification.** The bridge axiom `lattice_energy_subadditive` (∀ m n, E(m+n) ≤ E(m) + E(n)) is central to the LPO classification. The paper attributes this to "translation invariance of the Hamiltonian; the boundary interaction between two subsystems is bounded." But this is far from obvious for interacting QFT. In lattice gauge theory, the ground-state energy is subadditive *only* for systems with short-range interactions and with careful treatment of boundary conditions. For QED (long-range), subadditivity is not straightforward. For non-Abelian gauge theories with confinement, it holds but requires non-trivial arguments about cluster decomposition.

   **Recommendation:** Provide a more careful justification of the subadditivity bridge axiom, or at minimum acknowledge the physical conditions under which it holds and fails. This is the weakest physical link in the chain.

6. **The "55-digit fine-tuning" is misleadingly stated.** The paper repeatedly refers to a "55-decimal-place cancellation" between Λ_bare and vacuum condensate contributions. This number appears to come from comparing tree-level electroweak condensate contributions ((100 GeV)^4 ≈ 10^8 GeV^4) with the observed Λ ≈ 10^-47 GeV^4, a ratio of ~10^55. But this comparison is not the standard statement of the fine-tuning problem. The standard version compares the Planck scale contribution (10^71 GeV^4) with the observed value (10^-47 GeV^4), yielding 10^118 — which the paper correctly identifies as regulator-dependent. If the paper's claim is that after dissolving Claim I, the remaining fine-tuning is "only" 55 digits (between tree-level condensates and Λ_obs), this should be stated more clearly, with an explicit calculation.

   **Recommendation:** Provide an explicit numerical derivation of the "55-digit" figure. Is it 10^55 = (100 GeV)^4 / (2.8 × 10^-47 GeV^4)? If so, say so explicitly. The current paper uses the number without deriving it.

7. **The RG running theorem (Theorem 6) is physically vacuous.** The theorem states that the perturbative RG running of Λ is "BISH-computable." But the actual Lean proof (`rg_running_bish`) merely applies the Picard-Lindelöf bridge axiom and constructs a witness `⟨sol μ_target, trivial⟩`. The theorem proves `∃ _L_val : ℝ, True` — the *existence* of a real number satisfying `True`. This is trivially true for any type. The theorem says nothing about the RG running being correct, bounded, or related to physics. The claim that "perturbative RG running is BISH" may well be true, but this formalization does not establish it.

   **Recommendation:** Either strengthen the theorem to assert a non-trivial property of the RG running (e.g., that the solution stays within a bounded interval, or that it agrees with the initial condition), or acknowledge that the formalization captures only the existence of a solution to a Lipschitz ODE, not the physical content of RG running. The current discrepancy between the narrative ("perturbative RG running is BISH-computable") and the formal statement (∃ x : ℝ, True) is significant.

8. **The coincidence problem is mentioned but not analyzed.** The introduction correctly identifies three sub-problems, including the coincidence problem (why is ρ_Λ comparable to matter density now?). But none of the seven theorems address this. The paper should explicitly state that the coincidence problem is outside the scope of the current analysis.

9. **DESI discussion is speculative.** The discussion of DESI hints at evolving dark energy (§14.4) is appropriate as future outlook but should note that the DESI evidence for w₀ > -1 is still preliminary and has been disputed. The 2.5-3.9σ range cited mixes different data combinations and should be stated more carefully.

### Verdict

The paper's three-claim decomposition is a genuine conceptual contribution to understanding the logical structure of the cosmological constant problem. The Hollands-Wald analysis (Claim II) and the Casimir distinction (energy differences vs. absolutes) are physically well-grounded. However, the "dissolution" of Claim I is overstated (vacuum energy contributions at the scale of known particle masses are scheme-independent), the "55-digit" figure needs derivation, and several of the formalizations (especially Theorem 6) are weaker than the narrative claims suggest.

**Recommendation: Major revision** (address items 4, 5, 6, 7; item 4 requires rewriting the dissolution claim, item 7 requires either strengthening the theorem or softening the narrative).

---

## Report 3: Lean 4 / Formal Verification Expert

**Reviewer expertise:** Lean 4, Mathlib, interactive theorem proving, formal verification of mathematics.

### Summary

The paper presents a Lean 4 + Mathlib formalization of seven theorems about the cosmological constant problem, organized into 10 modules totalling ~800 lines (the paper says ~600). The code compiles with 0 errors, 0 warnings, 0 `sorry`. The axiom audit (`#print axioms cc_master`) shows 15 dependencies: 11 physics axioms, 1 CRM axiom, and 3 Lean infrastructure axioms.

### Evaluation

**Strengths:**

1. **Clean build and reproducibility.** The formalization compiles cleanly (verified: `lake build` with 0 errors, 0 warnings). The reproducibility box provides clear instructions. The `lean-toolchain` specifies `leanprover/lean4:v4.28.0-rc1`, and the project structure follows standard lakefile conventions. The axiom audit output is provided verbatim. This is a model of reproducibility for formalization papers.

2. **Good Lean 4 style.** The code uses appropriate Lean 4 idioms: anonymous constructor syntax `⟨...⟩`, `by` blocks for tactic proofs, structured `obtain`/`have`/`exact` chains, and `positivity`/`linarith` automation. The `neg_div` normalization for the Casimir negativity proof is a nice example of dealing with Lean's precedence conventions. Variable naming follows Lean conventions (underscore prefix for unused binders).

3. **Well-structured module dependency.** The 10-module architecture (Defs → 6 theorem files → FineTuningLPO → CalibrationTable → Main) is clean and mirrors the mathematical dependency structure. Each module has a single responsibility. The assembly theorem correctly combines all seven parts.

4. **Transparent axiom management.** The paper clearly lists all 15 axiom dependencies, classifies them into three categories (physics, CRM, infrastructure), and documents which declared axioms are *not* used in the master theorem. The `#print axioms` output is the correct tool for this audit in Lean 4.

**Weaknesses and Required Revisions:**

5. **Heavy reliance on unverified axioms undermines the "formalization" claim.** The Defs.lean file declares 17 axioms (by my count from the source: `regularized_vacuum_energy`, `mode_sum_partial`, `mode_sum_nonneg`, `mode_sum_mono`, `mode_sum_unbounded`, `cutoff_gives_quartic`, `dimreg_value_different`, `lattice_vacuum_energy`, `lattice_energy_subadditive`, `lattice_energy_bdd_below`, `bmc_from_subadditive`, `bmc_of_lpo`, `casimir_cauchy_modulus`, `picard_lindelof_lambda`, `eight_pi_G`, `eight_pi_G_pos`, `Lambda_obs`, `Lambda_obs_pos`, plus tree-level axioms). Of these, only `propext`, `Classical.choice`, and `Quot.sound` are standard Lean axioms; the other 17+ are user-declared.

   In a typical Lean formalization, theorems are proved from definitions and Mathlib lemmas. Here, most of the mathematical content is *asserted* via `axiom` rather than *proved*. The proofs that do exist (vacuum divergence, regulator dependence, Wald ambiguity, Casimir, fine-tuning) are relatively short (5-20 lines each) and are essentially bookkeeping: they combine the axioms using `linarith`, `ring`, and direct construction. The heaviest proof is `vacuum_energy_divergent` (11 lines), which is a standard "assume convergence, derive contradiction via unboundedness" argument.

   This is not inherently wrong — the paper explicitly calls these "bridge axioms" and treats them as the physics-to-mathematics interface. But it means the Lean formalization verifies the *logical structure* of the argument, not the *mathematical content*. A reader should understand that "machine-checked" here means "the logical inferences between the axioms and the theorems are correct," not "the underlying mathematics has been verified from first principles."

   **Recommendation:** Add a clear statement (e.g., in the reproducibility box or CRM audit) quantifying the ratio: "Of the 15 axiom dependencies of `cc_master`, 12 are unverified premises (physics + CRM) and 3 are standard Lean axioms. The formalization verifies that the seven theorems follow from these premises, not that the premises themselves are true."

6. **Theorem 6 (`rg_running_bish`) proves a trivially true statement.** As noted in the Lean source:
   ```lean
   theorem rg_running_bish ... :
       exists _L_val : R, True := by
     obtain ⟨sol, _hsol, _⟩ := picard_lindelof_lambda ...
     exact ⟨sol mu_target, trivial⟩
   ```
   The goal `∃ _L_val : ℝ, True` is provable without any axioms at all — `⟨0, trivial⟩` suffices. The `picard_lindelof_lambda` axiom is invoked but its output is destructured with `_hsol` (unused) and `_` (discarded). The theorem's type does not constrain the witness in any way. This is a significant formalization weakness: the theorem claims to establish that "perturbative RG running is BISH-computable," but the formal statement says only "there exists a real number." The `rg_lpo_boundary` theorem has the same issue: both conjuncts assert `∃ _x : ℝ, True`.

   **Recommendation:** Strengthen the type signature of `rg_running_bish` to assert a meaningful property. For example:
   ```lean
   theorem rg_running_bish ... :
       ∃ L_sol : ℝ → ℝ, L_sol mu0 = L_init ∧
         ∀ μ, mu0 ≤ μ → μ ≤ mu_target → ∃ ε, 0 < ε
   ```
   This would at least capture the initial condition and existence on the interval, rather than asserting `True`. The current version makes the axiom audit misleading: `picard_lindelof_lambda` appears in `#print axioms` but its content is never actually used.

7. **The `bmc_from_subadditive` axiom duplicates content that should be a theorem.** If Paper 29 already formalizes the Fekete ≡ LPO equivalence, this result should be imported as a theorem (via cross-project import or by reproducing the proof), not re-declared as an axiom. As an axiom, it is indistinguishable from the physics bridge axioms in the `#print axioms` output, but conceptually it is a mathematical theorem, not a physical fact. This conflation muddies the axiom classification.

   **Recommendation:** Either (a) import the Paper 29 result directly, or (b) add a clear comment in Defs.lean and in the paper explaining that `bmc_from_subadditive` is a *mathematical theorem proved in Paper 29* that is declared as an axiom here only for modularity, not because its proof is unknown.

8. **Line count discrepancy.** The paper states "~600 lines" but `wc -l` gives 817 lines. This discrepancy should be corrected. If the authors are counting non-blank, non-comment lines, they should say so.

9. **The `picard_lindelof_lambda` axiom is weaker than claimed.** The axiom asserts:
   ```lean
   ∃ Λ_sol : ℝ → ℝ,
     Λ_sol μ_min = Λ_init ∧
     ∀ μ, μ_min ≤ μ → μ ≤ μ_max → ∃ ε, 0 < ε
   ```
   The inner `∃ ε, 0 < ε` says only "there exists a positive real number" — it doesn't relate ε to the solution or impose any continuity/differentiability condition. A true Picard-Lindelöf axiom should assert the solution satisfies the ODE (or at least stays in a bounded region). As stated, this axiom is equivalent to: "there exists a function mapping μ_min to L_init, and for every μ in the interval, a positive real number exists." The second conjunct is trivially true.

   **Recommendation:** Either strengthen the axiom to assert a meaningful property of the ODE solution (e.g., uniqueness, continuity, or satisfaction of the equation), or rename it to something more modest (e.g., `ode_solution_exists`).

10. **Minor: `CalibrationTable.lean` uses `deriving Repr` correctly.** The `CalibrationEntry` structure with `deriving Repr` is a clean way to define the calibration data. The 12-row table is well-organized. This is good practice.

11. **Minor: The `casimir_cauchy_modulus` axiom has an unusual form.** It asserts `∃ (_N : ℕ) (approx : ℝ), |approx - target| < ε` where the `_N` is unused. This means the axiom says "for any ε > 0, there exists an approximation within ε of the target" — which is true for *any* real number (just take `approx = target`). The `_N` parameter, which would normally give the computational content (truncation index), is discarded. To be meaningful, the axiom should relate `N` to the approximation, e.g., by requiring `approx` to be defined in terms of `N` partial sums.

   **Recommendation:** Either (a) strengthen the axiom to connect `N` with the approximation scheme, or (b) simplify by dropping the unused `_N` parameter.

### Verdict

The formalization is well-organized, compiles cleanly, and uses appropriate Lean 4 conventions. The module structure is clean, the axiom audit is transparent, and the reproducibility is excellent. However, the mathematical depth of the formalization is limited: most content is asserted via axioms, and several theorems (especially Theorem 6 and the Casimir result) have formal statements that are significantly weaker than the narrative claims. The axiom `picard_lindelof_lambda` and `casimir_cauchy_modulus` are both weaker than their names suggest. These issues do not affect the correctness of the formalization (the proofs are valid) but do affect its informativeness.

**Recommendation: Minor revision** (address items 5-9; these are clarifications and strengthening of formal statements, not fundamental restructuring). The build quality and reproducibility are commendable.

---

## Summary of All Three Reports

| Reviewer | Recommendation | Key Issues |
|----------|---------------|------------|
| CRM Expert | Major revision | Calibration is upper bound not tight equivalence; bridge axioms unverified; `Classical.choice` limitation |
| Physics Expert | Major revision | Dissolution overstated; 55-digit not derived; Theorem 6 vacuous; subadditivity unjustified |
| Lean Expert | Minor revision | Theorem 6 proves `∃ x, True`; axioms weaker than names suggest; line count wrong; good build quality |

**Common theme across all three reports:** The gap between the narrative claims and the formal content. The paper tells a compelling story about the logical structure of the cosmological constant problem, but the formalization is thinner than the story suggests. Strengthening the formal statements (particularly Theorems 5-7) and being more explicit about what the machine-checking guarantees (logical structure, not mathematical content) would address most concerns from all three reviewers.
