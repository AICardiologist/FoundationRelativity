# Referee Reports for Paper 44: "The Measurement Problem Dissolved"

Three expert referees were solicited. Reports are presented in full below.

---

# REPORT 1: Constructive Reverse Mathematics (CRM) Expert

**Recommendation: Major Revision**

## 1. Summary

The manuscript proposes that the quantum measurement problem decomposes into three logically distinct commitments by calibrating the Copenhagen, Many-Worlds, and Bohmian interpretations against the constructive hierarchy: Copenhagen at WLPO, Many-Worlds at DC, and Bohmian mechanics at LPO. A Lean 4/Mathlib formalization accompanies the paper, with one fully machine-checked direction (Copenhagen implies WLPO) and one BISH-level bonus (uniform branching requires no choice). The remaining eight proof obligations are sorry'd. The author argues that the incomparability and strict separation of these principles "dissolves" the measurement problem by revealing it as a category error.

## 2. Main Assessment

**Correctness.** The one fully proved direction (Theorem 2.1, `copenhagen_implies_WLPO`) is correct and is a genuine, if modest, result. The encoding argument is clean: binary encoding of a sequence into a real, lifting to a qubit amplitude, and reading off the WLPO disjunction from the Copenhagen postulate. The axiom audit showing only `propext`, `Classical.choice`, and `Quot.sound` (all Mathlib infrastructure for the Cauchy reals) is appropriately transparent. However, with only 1 of 6 equivalence directions fully proved and 0 of 3 full equivalences machine-checked, the central theorem (`measurement_problem_dissolved`) is a conjecture, not a result. The paper does not always make this status sufficiently clear.

**Significance.** The idea of applying CRM calibration to the measurement problem is genuinely novel and potentially valuable. If the calibrations are correct, the observation that three interpretations sit at provably distinct and (in one case) incomparable positions in the constructive hierarchy is a meaningful philosophical contribution. However, the significance is substantially undermined by the number of sorry'd obligations and by several technical concerns detailed below.

**Novelty.** I am not aware of prior work applying CRM calibration specifically to quantum interpretations. Döring–Isham [13] uses topos theory, which is a different programme entirely. The novelty claim in Section 1.3 appears justified.

## 3. Specific Technical Concerns

### Issue 1 (Major): The Copenhagen postulate formalization may not calibrate at WLPO.

The formalization is: `∀ (ψ : QubitState), ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0)`

This is precisely WLPO lifted to the reals/complex numbers, which is equivalent to WLPO by standard results (Bridges–Vîță [5], Proposition 1.2.3).

However, one must ask: **is this really the Copenhagen postulate?** The Copenhagen postulate as physicists understand it is closer to: measurement yields outcome 0 or outcome 1, with the state collapsing to the corresponding eigenstate. The constructive content of this is arguably `α = 0 ∨ α ≠ 0` (a *decidability* statement, i.e., LPO-strength for reals), not `α = 0 ∨ ¬¬(α ≠ 0)`. The double negation in the second disjunct weakens the postulate from "we can decide which outcome occurs" to "we can decide whether the state is definitely in an eigenstate, or we cannot rule out that it is not."

If one formalizes Copenhagen as `α = 0 ∨ α ≠ 0`, the calibration would be at LPO, not WLPO, and the stratification partially collapses.

### Issue 2 (Major): The DC calibration for Many-Worlds is not convincingly argued.

Both directions are sorry'd, so there is no machine-checked evidence. More importantly:

(a) The paper claims CC does not suffice because the measurement at step n depends on history. This motivates DC's *relevance* but does not establish DC is *necessary*.

(b) The `Nonempty` type in Lean is proof-irrelevant — it lives in `Prop`. Does mere propositional existence of an infinite path through a finitely-branching tree really require DC? This is related to König's lemma, which in CRM calibrates at different levels depending on the exact formulation (see Diener [4] and Berger–Bridges on the fan theorem).

(c) The statement that "DC strictly extends CC" is standard but the claim that CC does not suffice needs more care. The paper should clarify which form of countable choice is included in its version of BISH.

### Issue 3 (Major): The claim "DC is incomparable with every principle on the vertical tower" needs qualification.

The independence of DC from LPO in BISH depends on the precise ambient framework. The paper should cite specific models or independence results. Beeson's work and Rathjen's realizability models are relevant here.

### Issue 4 (Major): The sorry ratio undermines the central theorem.

1 of 6 directions proved. The theorem `measurement_problem_dissolved` compiles only because sorry-dependent lemmas are accepted by the kernel. The paper's title ("Dissolved") and abstract language ("calibrates at") present these as established facts. This overstates what has been demonstrated.

### Issue 5 (Minor): BMC ↔ LPO application.

The application to the Bohmian velocity sequence requires checking that the sequence is indeed bounded and monotone *constructively*, which is claimed but sorry'd. For a free Gaussian packet, this should be provable.

### Issue 6 (Minor): CC vs DC in §3.2.

The paper should clarify which form of countable choice is included in its version of BISH and whether the CC being discussed is AC_ω, AC_ω,ω, or broader CC.

### Issue 7 (Minor): The "dissolution" claim is philosophically over-strong.

Even granting all three calibrations, what is established is that three *formalizations* sit at different levels. The "dissolution" requires accepting that these formalizations capture the essential content of the interpretations.

### Issue 8 (Minor): Scope limitations may be more severe than presented.

Whether the calibrations remain stable under physically realistic generalizations (e.g., interacting multi-particle Bohmian systems) deserves discussion.

### Issue 9 (Remark): Lean infrastructure axioms handled well.

The paper could briefly note that an alternative development over Bishop reals (as in Krebbers–Spitters) would avoid this artifact entirely.

### Issue 10 (Remark): Weihrauch degree refinement.

Could be promoted from future work to a brief discussion, especially for DC.

## 4. Questions for the Authors

1. Why is `α = 0 ∨ ¬¬(α ≠ 0)` the correct formalization rather than `α = 0 ∨ α ≠ 0`?
2. Can you provide a concrete model witnessing ManyWorldsPostulate's independence from LPO?
3. What is the status of countable choice in your version of BISH?
4. Have you verified velocity sequence monotonicity constructively?
5. How sensitive are calibrations to formalization choices?
6. Can you cite precise models for DC's incomparability with each of LLPO, WLPO, LPO?

---

# REPORT 2: Physics / Quantum Foundations Expert

**Recommendation: Major Revision**

## 1. Summary

This manuscript applies the framework of constructive reverse mathematics (CRM) to the quantum measurement problem, arguing that Copenhagen, Many-Worlds, and Bohmian mechanics each require a distinct constructive principle (WLPO, DC, LPO). The author claims this constitutes a "dissolution" of the measurement problem. A partial Lean 4 formalization accompanies the paper, with one direction fully machine-checked.

## 2. Main Assessment

The paper attempts something genuinely original. The technical machinery of CRM is real, and the idea that different physical postulates might calibrate to different constructive principles is intellectually interesting.

However, the paper's central claim depends critically on whether the formal postulates faithfully capture the physical and philosophical content of the three interpretations. On close examination, each formalization is significantly narrower than what the interpretations actually assert, and this gap is not adequately acknowledged.

## 3. Specific Technical Concerns

### Concern 1 (Major): The Copenhagen formalization does not capture the measurement postulate.

The formalization captures at most a narrow logical precondition (can we decide whether the state is already an eigenstate?) rather than the dynamical collapse process itself. The choice to privilege α = 0 rather than the general question "is the state an eigenstate of the measured observable?" introduces an asymmetry that is not physically motivated. A more faithful formalization would involve decidability of whether a state lies in a given closed subspace. Furthermore, the double-negation weakening is the author's interpretive move — Copenhagen asserts a positive fact: the outcome *is* 0 or *is* 1, with definite probabilities.

### Concern 2 (Major): The Many-Worlds formalization conflates the interpretive claim with a mathematical artifact.

The Everettian interpretation does not postulate the *existence* of complete branches as an additional axiom. It postulates unitary evolution with all branches co-existing. An Everettian would likely object that the formalization smuggles in a requirement (selecting a single infinite path) that is foreign to the interpretation. The DC requirement enters only because the author has modeled history-dependent adaptive measurements; whether such adaptive branching is essential to Many-Worlds is debatable.

### Concern 3 (Major): The Bohmian formalization is restricted to a single pedagogical example.

The free Gaussian is the simplest possible case and does not involve any of the features that make Bohmian mechanics physically nontrivial (nonlocality, contextuality, quantum equilibrium). Moreover, Bohmian mechanics does not *require* taking the t → ∞ limit to make predictions. All empirical content is extracted at finite times, where the author acknowledges BISH suffices. The LPO content therefore arises from a mathematical idealization that is not essential to the interpretation's empirical content.

### Concern 4 (Major): The "dissolution" claim is not supported by the technical results.

Even granting the formalizations, the conclusion that the measurement problem is a "category error" does not follow. The measurement problem concerns the tension between unitary evolution and definite outcomes. The fact that different proposed resolutions have different logical costs does not show the original problem was misconceived. It shows, at most, that different solutions have different constructive overhead.

### Concern 5 (Minor): Spreading coefficient and trajectory formulas are correct.

c = ℏ²/(4m²σ₀²) and x(t) = x₀ + v₀t + (x_init − x₀)σ(t)/σ₀ are stated correctly for the free Gaussian case. The erratum note is appropriate. The asymptotic velocity formula checks out.

### Concern 6 (Minor): Formalization incompleteness.

Honest about the 1-of-6 completion, but limits the contribution.

### Concern 7 (Minor): Engagement with decoherence is insufficient.

Decoherence is central to how all three interpretations function in practice. Copenhagen relies on it for emergence of classical outcomes; Many-Worlds relies on it for the preferred basis; Bohmian mechanics relies on it for effective collapse. The omission is more consequential than §9 suggests.

### Concern 9 (Remark): Döring–Isham comparison deserves more detail.

### Concern 10 (Remark): Cubitt et al. connection is thematic, not technical.

## 4. Questions for the Authors

1. Why is "α = 0 ∨ ¬¬(α ≠ 0)" the right formalization of "measurement yields a definite outcome"?
2. How do you respond to the Everettian objection that requiring "existence of a complete path" imports a single-world perspective into a many-worlds framework?
3. Given that all empirical content of Bohmian mechanics is extracted at finite times (where BISH suffices), what is the physical significance of the asymptotic velocity limit?
4. If the formalizations were modified to be more faithful, would calibration results change?
5. Is this establishing that the measurement problem *is* dissolved, or proposing a methodology that *could* lead to dissolution if formalizations were completed and validated?

---

# REPORT 3: Lean 4 / Formalization Expert

**Recommendation: Major Revision**

## 1. Summary

This manuscript presents a Lean 4 formalization (~1,100 LOC across 10 files) that encodes three quantum-mechanical interpretations as propositions in type theory and attempts to establish logical equivalences between each and a constructive principle. Of the six main implication directions, only two are fully proved (`copenhagen_implies_WLPO` and `uniform_world_exists`); the remaining four are sorry'd, and the paper relies on transparent sorry-tracking and axiom auditing.

## 2. Main Assessment

**Architecture and organization.** The 10-file structure is clean. The dependency graph is acyclic and legible. File sizes are reasonable. For a ~1,100 LOC project this level of modularity is appropriate.

**Fully proved content.** `copenhagen_implies_WLPO` is a legitimate, non-trivial formalization achievement. The proof chain (binary encoding via tsum → qubit construction → logical extraction) is well-executed. The `qubitFromReal` construction with its `norm_eq` proof demonstrates competent Mathlib usage. `uniform_world_exists` is essentially trivial (four lines, constant function). `lpo_implies_wlpo` is elementary.

**Sorry transparency.** The axiom audit table showing `sorryAx` is the right approach. However, the ratio of sorry'd to proved content is concerning for a formalization paper: 4 of 6 main implications are sorry'd.

**Axiom audit methodology.** Correctly applied. `Classical.choice` identification as Mathlib artifact is correct.

## 3. Specific Technical Concerns

### Issue 1 (Major): Sorry load too high for central claims.

Four of six main implications are sorry'd. The headline "three biconditionals" result is entirely sorry-dependent. For ITP/CPP, the expectation is that main claimed results are fully machine-checked. This is better described as a *formalization specification* or *proof plan* than a *formalization result*.

### Issue 2 (Major): `bmc_of_lpo` and `lpo_of_bmc` are declared as axioms, not sorry'd theorems.

Declaring as `axiom` rather than `theorem ... := sorry` means the axiom audit may undercount sorry-equivalent obligations. The `axiom` does not produce `sorryAx` dependency. The convention for formalization papers is that `sorry` is for obligations to be filled, `axiom` for genuinely external assumptions. If `bmc_of_lpo` is a known fact, it should be sorry'd with a comment, not axiomatized.

### Issue 3 (Major): `Classical.choice` / constructivity tension insufficiently resolved.

The `binaryEncoding` function uses `tsum`, which in Mathlib is defined using `Classical.choice` for decidability of summability. The encoding itself relies on classical infrastructure. The paper should discuss whether an alternative encoding avoiding `tsum` and `ℝ` would yield a proof with fewer axiom dependencies.

### Issue 4 (Minor): `Nonempty` vs constructive witness.

`uniform_world_exists` returns `Nonempty (World U.toBranching)`, which lives in `Prop` and doesn't provide a computable witness. The proof uses `Nonempty.choose`, which itself relies on `Classical.choice`. For a paper about constructive principles, a stronger `Type`-valued existence (Σ-types) would make constructive content explicit.

### Issue 5 (Minor): `CopenhagenPostulate` is a weak formalization.

The double negation `¬¬(ψ.α ≠ 0)` is weaker than `ψ.α ≠ 0`. The connection to physical Copenhagen deserves explicit philosophical argument.

### Issue 6 (Minor): `ManyWorldsPostulate` quantifies over all branching structures.

Asserting that *every conceivable* branching structure admits a world is extremely strong. A physicist would object that Many-Worlds applies to a *specific* branching structure, not all possible ones.

### Issue 7 (Minor): Gap between `BohmianAsymptoticVelocity` and actual Bohmian mechanics.

`BohmianParams` models a single free Gaussian. The connection to LPO through BMC is sorry'd, so the paper does not actually establish this connection.

### Issue 8 (Minor): `finite_time_bish` proves `True`.

A placeholder that proves nothing. Should either be formalized or removed.

### Issue 9 (Remark): `noncomputable section` usage appropriate.

Standard practice, correctly applied.

### Issue 10 (Remark): Binary encoding via `tsum` defensible.

Alternative using `Finset.sum` would avoid classical infrastructure but complicate bijectivity.

### Issue 11 (Remark): Code snippets in manuscript consistent with source.

## 4. Questions for the Authors

1. Which sorry obligations are closest to completion? What is the realistic difficulty of each?
2. Why are `bmc_of_lpo` / `lpo_of_bmc` axioms rather than sorry'd theorems?
3. Could `copenhagen_implies_WLPO` be proved without routing through ℝ?
4. Would restricting `ManyWorldsPostulate` to physically realizable branching structures change the DC equivalence?
5. What is the status of `finite_time_bish`?
6. Have you considered `Type`-valued existence (Σ-types) to make constructive content explicit?

---

# SUMMARY OF RECOMMENDATIONS

| Referee | Expertise | Verdict |
|---------|-----------|---------|
| 1 | CRM Expert | **Major Revision** |
| 2 | Physics Expert | **Major Revision** |
| 3 | Lean Expert | **Major Revision** |

## Convergent Themes Across All Three Reports

1. **Faithfulness of the Copenhagen formalization** — All three referees question whether `α = 0 ∨ ¬¬(α ≠ 0)` correctly captures the Copenhagen postulate. The double-negation weakening is the single most contested modeling decision.

2. **Sorry load** — All three note that 1 of 6 directions proved (4 of 6 sorry'd) is insufficient for the strength of the claims. The title "Dissolved" and abstract language overstate what has been demonstrated.

3. **Faithfulness of the Many-Worlds formalization** — Both the CRM and physics referees question whether requiring existence of a complete path captures the Everettian picture (which posits co-existence of all branches, not selection of one).

4. **Scope of the Bohmian model** — The physics referee notes that the free Gaussian is pedagogical, not physically representative, and that the LPO cost arises from an idealization (asymptotic velocity) not required for empirical predictions.

5. **The "dissolution" claim** — All three consider the philosophical conclusion stronger than the technical results warrant.

## Unique Concerns by Referee

- **CRM referee**: DC incomparability citations needed; CC vs DC distinction needs precision; König's lemma / fan theorem relationship for MWI
- **Physics referee**: Decoherence omission is consequential; dynamical collapse not modeled; Bell nonlocality not addressed in Bohmian
- **Lean referee**: axiom vs sorry convention; `Nonempty` vs Σ-type; `Classical.choice` in tsum; `finite_time_bish` proves True
