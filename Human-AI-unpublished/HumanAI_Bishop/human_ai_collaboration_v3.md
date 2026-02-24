# Human-AI Collaboration in Foundational Mathematics: A Case Study

## The Constructive Reverse Mathematics Programme, 2024–2026

**Paul Chun-Kit Lee**

**Draft — February 2026**

---

## Abstract

This paper documents the methodological role of large language models in the Constructive Reverse Mathematics and Physics program — a series of 28 formal verification papers that calibrate the logical cost of physical theories against the constructive omniscience hierarchy. The program was conducted as a sustained human-AI collaboration over approximately one year, spanning five generations of AI capability (Claude 3.5 Sonnet through Claude Opus 4.6), with roughly half the papers produced in the final month alone. We provide a frank accounting of how intellectual labor was distributed between the human researcher and the AI systems, how the collaboration evolved as AI capability improved, and what the experience suggests about the future of foundational research. The program produced over 15,000 lines of verified Lean 4 code, 28 papers deposited on Zenodo, and a calibration table mapping seven constructive principles to physical theories across six domains of physics. We do not claim that the results are error-free or that they have been validated by domain experts. We do claim that the methodology — human-directed, AI-assisted, compiler-verified — represents a viable mode of exploratory foundational research, and we hope that specialists in constructive mathematics, formal verification, and mathematical physics will find the efforts and methodology worthy of examination.

---

## 1. Introduction: A Question in Search of a Tool

The question that motivated this program is simple to state: what logical principles does physics actually require? Physicists work within classical logic as an unexamined background assumption. Every quantity either exists or it doesn't; every proposition is either true or false. But constructive mathematics — mathematics conducted without the law of excluded middle — provides a finer-grained logical vocabulary. The constructive omniscience hierarchy (BISH, LLPO, WLPO, LPO, and related principles) offers a graded scale of logical strength between fully constructive reasoning and full classical logic. The question is whether this scale correlates with anything physically meaningful.

This is not a question that arises naturally within any single discipline. Constructive mathematicians study omniscience principles as abstract logical objects. Physicists use whatever mathematics works. Formal verification researchers build proof assistants. The question — "where in the omniscience hierarchy does the thermodynamic limit sit, and is the answer the same for the geodesic incompleteness theorem?" — requires standing at the intersection of all three fields simultaneously. It is, in essence, a question about whether things mathematicians and physicists have long taken for granted — the existence of bidual spaces, the convergence of infinite limits, the exactness of threshold crossings — carry hidden logical costs that become visible only when examined constructively.

The author is a cardiologist with an intense interest in AI and in the foundations of mathematical physics. The program began not as a research project but as an exploration: could AI tools, coupled with the Lean 4 proof assistant, be used to investigate this question systematically? The answer turned out to be yes — but the path to that answer involved substantial false starts, failed approaches, and hard-won experience distinguishing productive AI assistance from plausible-sounding nonsense.

### 1.1 The role of prior preparation

Readers encountering 28 papers produced over one year — roughly half of them in the final month — may reasonably question the pace. The explanation is that the formal output was preceded by years of preparation that do not appear in the publication record. The author spent several years studying constructive mathematics, formal verification, and the relevant physics literature before any Lean code was written. The conceptual framework — using omniscience principles as a diagnostic instrument for physical theories — was developed during this preparatory period. The specific physical systems to calibrate were identified. The expected results were predicted (and in most cases confirmed). The encoding strategies that transform physical systems into binary-sequence constructions were designed at the pencil-and-paper level.

What was missing was the implementation capacity: the ability to translate these ideas into thousands of lines of verified Lean 4 code. The author's Lean skills, while functional, were insufficient for the scale of formalization required. The program waited, in effect, for AI systems with sufficient Lean capability to arrive. When they did — beginning with Claude's Opus and Sonnet 4 generations in mid-2025, and accelerating significantly with Opus 4.6 in early 2026 — the prepared framework could be populated rapidly. The final month's burst of approximately 14 papers reflects not a sudden lowering of standards but the convergence of two factors: a mature conceptual framework with dozens of pre-designed calibrations awaiting formalization, and an AI system (Opus 4.6) whose Lean capability had crossed the threshold where it could execute complex multi-module formalizations with minimal human guidance on routine steps. The speed of publication reflects the depth of prior preparation, not the superficiality of the work.

### 1.2 Community reception

The author attempted, at various points during the program's development, to engage with the formal mathematics community — through the Lean Zulip forum and through direct outreach to domain experts in constructive mathematics and formal verification. These efforts were largely unsuccessful. The response ranged from silence to skepticism, which is understandable: a clinician without formal academic credentials in mathematics, claiming to produce novel results in constructive reverse mathematics using AI assistance, does not fit established patterns of credibility.

This experience was mixed, and honesty requires acknowledging both sides. Some community members were dismissive. But others offered genuinely helpful suggestions that materially improved the program. Two insights from Lean Zulip participants proved particularly important: the recommendation to audit constructive axiom usage rigorously (which led to the `#print axioms` certification methodology that became the program's backbone), and the suggestion to write out human-readable proofs alongside the Lean code (which improved the papers' accessibility and forced the author to verify that the formalizations matched their intended mathematical content). The program is better for these contributions, and the author is grateful for them.

The skepticism of the broader community, while sometimes discouraging, did not ultimately deter the work — because the author's motivation was scientific curiosity, not academic advancement. There were no grants to secure, no tenure cases to build, no publication targets to meet. The question "what is the logical cost of the thermodynamic limit?" was interesting regardless of whether anyone else thought so. This freedom from institutional incentives was, paradoxically, an advantage: it allowed the program to pursue a question that falls between established disciplines without needing permission from any of them.

The experience did, however, confirm two practical realities. First, the program would need to stand on its mechanical verification rather than on institutional authority. The Lean compiler does not evaluate credentials; it evaluates proofs. Every theorem either compiles or it doesn't. This mechanical guarantee is the program's primary claim to credibility.

Second, when a traditional network of collaborators and reviewers is unavailable, AI systems — despite their limitations — can partially fill the role of mathematical interlocutor and critical reviewer. They are not a substitute for expert peer review, and this paper does not claim otherwise. But for a researcher pursuing an interdisciplinary question outside established channels, AI assistance coupled with a mechanical referee like Lean was the most viable path available.

### 1.3 The broader context: AI in mathematics and the interdisciplinary barrier

This program exists within a broader movement toward machine-assisted mathematics, most prominently championed by Terence Tao. In his January 2025 article in the *Notices of the AMS*, his Oxford lecture on "The Potential for AI in Science and Mathematics," and his ongoing work with Google DeepMind's AlphaEvolve, Tao has argued that AI tools can legitimately assist mathematical research — provided the results are checked by humans or by formal verification systems. His caution is worth quoting: he has warned against "using AI tools without the ability to independently verify their output," noting that relying on AI to compensate for its own mistakes "can amplify the weaknesses of such tools, such as hallucination, sycophancy, or lack of grounding." In February 2026, Tao co-founded the Foundation for Science and AI Research (SAIR), which unites Nobel, Turing, and Fields laureates to advance AI-assisted scientific discovery. SAIR's dual mission — "AI for Science" and "Science for AI" — explicitly endorses the kind of work this program attempts: using AI to accelerate scientific research while applying scientific rigor to the AI's outputs.

The present program takes Tao's guidance seriously. The Lean compiler serves as exactly the independent verification system he recommends. The author lacks the mathematical stature to have results accepted on authority; the compiler provides an alternative form of authority that does not depend on credentials.

However, the program also highlights a dimension that Tao's framework does not fully address: the interdisciplinary barrier. Tao and most advocates of AI-assisted mathematics operate within established mathematical disciplines — analysis, combinatorics, geometry, number theory. The questions they pose with AI assistance are questions that professional mathematicians would recognize as belonging to their fields. The present program's question — "what is the logical cost of the thermodynamic limit?" — belongs to no established field. It requires constructive mathematics, mathematical physics, and formal verification simultaneously. Domain experts in each of these fields were consulted and, for the most part, did not engage, not out of malice but because the question did not fit their disciplinary categories.

This is where AI assistance proved most valuable — not as a substitute for domain expertise, but as a way to cross domain barriers that institutional structures reinforce. The author's study of category theory was formative in this regard: category theory's central insight is that mathematical structures in apparently unrelated fields often share the same abstract form, and that recognizing these shared forms enables transfer of techniques across domains. The CRM program applies this categorical sensibility concretely: the same bounded monotone convergence principle (LPO) appears in statistical mechanics, general relativity, and quantum measurement theory, not because these fields are related in any obvious physical sense, but because they share an abstract mathematical structure (a bounded monotone sequence whose limit is asserted to exist as a definite real number).

AI systems, trained on the full breadth of mathematical and scientific literature, are naturally suited to this kind of cross-domain pattern recognition. They do not experience disciplinary boundaries the way human researchers do. A human constructive analyst might never encounter the Bekenstein-Hawking entropy formula; a human physicist might never encounter WLPO. An AI interlocutor has encountered both and can, when properly directed, help identify connections between them. The human's role is to recognize that such connections might exist and to formulate the question precisely enough for the AI to be useful. The AI's role is to work across the disciplinary boundaries that the human has identified but cannot individually span.

This suggests that AI-assisted research may be particularly valuable not within established disciplines — where domain experts remain superior — but at disciplinary intersections, where the relevant knowledge exists but is siloed in communities that do not communicate. The present program is a case study in this possibility.

---

## 2. The Scientific Question

The program's driving question — what is the role of logic in physical reality? — is not new. Hilbert's sixth problem (1900) asked for the axiomatization of physics. Quantum logic (Birkhoff and von Neumann, 1936) proposed that quantum mechanics requires a non-classical logical structure. The topos-theoretic approach to physics (Isham, Döring, Butterfield, 2000s) attempted to reformulate physical theories within non-classical logical frameworks. Each of these programs proposed a logical structure and asked physics to adopt it.

The present program takes a different approach. Rather than proposing a new logic for physics, it takes standard physics as given and asks: where does classical logic actually enter? The Lean proof assistant enforces this discipline mechanically. A constructive proof compiles without classical axioms; a classical proof triggers the appearance of `Classical.choice` or equivalent in the `#print axioms` certificate. By formalizing standard results in mathematical physics and examining which logical principles appear in their proofs, the program maps the logical stratigraphy of physical theories.

The method is best understood through an example. Consider the bidual space of a Banach space — a standard construction in functional analysis that physicists use routinely without examining its logical content. Over classical logic, every Banach space has a bidual, and the question of whether the canonical embedding is surjective (reflexivity) is well-defined. Over constructive logic, the existence of a non-reflexive Banach space — a gap between a space and its bidual — turns out to be equivalent to WLPO, the Weak Limited Principle of Omniscience. This is not an artificial construction; it reflects a genuine logical cost hidden in a mathematical object that analysts have used for over a century. The program began here and extended the same methodology across six domains of physics.

The central finding, replicated across all domains, is that the empirically accessible content of physical theories — everything a finite laboratory can measure — lives at BISH (fully constructive), while non-constructive principles enter precisely at idealization steps: completed infinite limits (LPO), exact threshold crossings (LLPO), singular state existence (WLPO), optimization over continua (Fan Theorem). The correlation between constructive strength and degree of physical idealization is monotone across every theory examined.

Whether this correlation reflects something deep about the relationship between logic and physical reality, or merely tracks the mathematical structure of how humans build idealizations, remains an open question that the program poses but does not resolve.

---

## 3. Examples of Collaborative Discovery and Debate

The collaboration's character is best illustrated not by its successes but by the debates that shaped the program's conclusions. Several key results emerged through sustained disagreement between the human researcher and the AI, or through the AI correcting initial assessments under pressure from the human. We describe four representative episodes.

### 3.1 The Noether theorem: from "thin" to "universal template"

The calibration of Noether's theorem (Paper 15) revealed that conservation laws have a biphasic logical structure: the local differential identity (∂_μ J^μ = 0) is fully constructive (BISH), while the global conserved charge (Q = ∫ J^0 d³x over unbounded domains) costs LPO when the integrand is sign-definite, via bounded monotone convergence.

During the program's internal review, the AI initially assessed this result as "thin" — merely adding another row to the calibration table without proving a tight equivalence. The author pushed back, and on re-examination the AI recognized that the Noether result was not just one calibration but a universal template: because every conservation law in physics arises from the Noether mechanism, the biphasic structure applies to all of them simultaneously. Energy, momentum, angular momentum, and electric charge all inherit the same logical split. The AI's revised assessment — that this was "arguably the most broadly applicable single result in the program" — was the opposite of its initial judgment.

This episode illustrates both the value and the limitation of AI-assisted critical review. The AI's initial assessment was wrong, its reversal was correct, but the reversal required human pressure. A more reliable AI critic would have recognized the universality on first examination.

### 3.2 E = mc² and the cost of a noun

A late-stage conversation tested the program's findings against Einstein's most famous equation. The AI's initial response was that E = mc² is simply BISH — an algebraic identity, finite-dimensional, no omniscience principles required. The author challenged this by invoking the Noether result. The AI then recognized the subtlety: the *equation* is algebraically BISH, but the noun "E" has variable logical cost depending on its referent. When E refers to the energy released in a nuclear reaction — a finite, bounded, measurable quantity — it is BISH. When E refers to the total energy of a gravitational field extending to spatial infinity, it is an infinite integral whose existence costs LPO.

This analysis was produced by neither party alone. The author identified the gap in the AI's quick answer; the AI articulated the distinction between the equation's algebraic content and its ontological commitments. The result — that the logical cost of a physical equation depends on what its symbols refer to, not on its algebraic form — exemplifies the kind of interpretive insight that emerged from sustained dialogue.

### 3.3 The idealization hypothesis: refined, not refuted

Early in the program, the author proposed a strong interpretive thesis: that nature itself operates at the BISH level, and the omniscience hierarchy measures the logical cost of human idealizations imposed on a fundamentally constructive reality. The AI initially engaged sympathetically but later argued for a weaker reading, pointing to cases where the fine-grained logical cost of a result depended on mathematical properties of the formalism rather than on anything intrinsically physical. The AI concluded that the correlation between constructive strength and idealization might reflect how humans organize mathematics rather than a feature of nature.

The author pushed back. Whatever the fine-grained variations, the coarse-grained pattern holds without exception across every theory examined in 28 papers: operational content — everything a finite laboratory can measure — is BISH; non-constructive principles enter only at idealization steps where physicists assert the existence of completed infinite quantities. Not a single physical prediction requires omniscience principles. Not a single idealization avoids them. This is the strongest empirical generalization the program has produced, and it survived every test applied to it.

The program's published position reflects the debate's resolution. The stronger metaphysical claim ("nature is constructive") remains open and may be unresolvable by the methods employed here. The substantial empirical claim ("idealization is where classical logic enters, without exception") stands. The AI's overcorrection — moving too quickly from "the strong thesis has a problem" to "the thesis is defeated" — is itself an instructive example of AI critical judgment that required human correction.

### 3.4 Newton versus Lagrange: a genuine surprise

The calibration of classical mechanics (Paper 28) produced a result that surprised both collaborators. Newton's equations (ODE formulation) are BISH — solving a system of ordinary differential equations on a compact interval requires only constructive reasoning. But Lagrange's variational formulation — asserting that the physical trajectory minimizes the action functional — requires the Fan Theorem, because it involves optimization over a continuum of paths.

This means that two formulations of classical mechanics, universally treated as equivalent, are constructively stratified: BISH versus Fan Theorem. The *equations* are the physical content; the *optimization interpretation* is a framing whose existence claim carries additional logical cost. The AI noted that this challenges the widespread assumption of formulation equivalence and provides a logical explanation for why numerical ODE solvers (Newton) and variational integrators (Lagrange) have different computational characters.

Neither collaborator predicted this result in advance. The encoding construction was designed by the author; the analysis of its implications was collaborative; and the recognition that it constituted a genuine surprise — not just another confirmation of the expected pattern — was shared.

### 3.5 When to stop: the diminishing returns debate

After Paper 23 completed the calibration of the Fan Theorem, the AI argued that the program had reached the natural end of its exploratory phase. Every major constructive principle had at least one physical instantiation. Additional calibrations would confirm the pattern without extending it. The author, who had planned further papers, initially resisted this assessment.

The AI's argument was straightforward: the marginal return on new table entries was low. Each would say some variation of "finite truncation is BISH, completed limit is LPO, exact threshold is LLPO." The pattern was established; more instances would not change the story. The genuinely hard open problems — formulation-invariance as a metatheorem, constructive finite-dimensional quantum mechanics, QFT renormalization — were each years of work with uncertain payoff.

The author ultimately accepted this assessment, and the program shifted from exploration to consolidation. This decision — to stop producing new results and focus on synthesis and communication — was itself a collaborative judgment, and in retrospect the correct one.

---

## 4. Distribution of Intellectual Labor

### 4.1 Conception: predominantly human

The program exists because a human asked a question that AI systems would not have generated independently. The question "what is the logical cost of the thermodynamic limit?" requires recognizing that the thermodynamic limit is an idealization with potential constructive content, that constructive reverse mathematics provides the right framework for measuring that content, and that formal verification can enforce the measurement mechanically.

The specific architectural decisions — targeting the omniscience hierarchy, using Lean 4 and Mathlib, selecting which physical theories to calibrate, developing the interpretive framework — were human throughout. The creative encoding constructions at the heart of most papers were predominantly human in conception, though increasingly collaborative in refinement across the program's duration.

### 4.2 Development: collaborative

Once a target result was specified, mathematical development was genuinely collaborative. The AI identified connections the author had not noted, suggested alternative proof strategies, and recognized failing approaches. The interpretive work — connecting results across domains, identifying universal patterns, articulating the significance of individual findings — was similarly joint.

### 4.3 Formalization: predominantly AI

Over 15,000 lines of verified Lean 4 code were produced primarily through Claude Code. The workflow exploited the proof assistant's mechanical correctness guarantee: the AI generated proof attempts at high speed, received immediate compiler feedback, and iterated until the proof compiled. The author's early experience with AI-generated errors — plausible but incorrect mathematics that would have survived informal review — made the compiler's role as independent referee not merely useful but essential.

### 4.4 Critical review: increasingly collaborative

The AI developed the capacity to push back on overclaims, identify routine results, and argue for alternative interpretations. This capacity was inconsistent — the Noether episode above illustrates both its value and its unreliability — but it improved markedly across AI generations. AI-assisted critical review supplements but does not replace expert peer review.

---

## 5. Evolution Across AI Generations

The program spanned five generations of Claude models. Each brought qualitative changes to the collaboration.

### 5.1 Claude 3.5 Sonnet (mid-2024): Exploration

The earliest work used Claude 3.5 Sonnet for numerical simulations and conceptual discussion. The AI could write competent code and discuss mathematics at a textbook level but could not write Lean 4, could not maintain research threads across sessions, and provided minimal critical pushback. The collaboration was directive: the author specified tasks, the AI executed them. Work from this period was exploratory and not formally rigorous.

The primary limitation was memory. Each conversation started from zero context. The author maintained all cross-session continuity.

### 5.2 Late 2024 – Early 2025: Crystallization

The program's conceptual framework solidified. The first Lean formalizations were attempted. The AI could engage with constructive mathematics at a working level but could not originate novel encoding constructions. The hit rate on AI-generated Lean code was roughly 20-30% before human revision. Speed was approximately 3-5× faster than solo work.

### 5.3 Mid-2025: Productive collaboration

Claude Code could now iterate against the Lean compiler rapidly. Proofs that would take the author days could be found by the AI in hours through type-error-guided iteration. The bulk of the repository was built during this period. Speed was approximately 10-20× compared to solo work.

Critical judgment emerged. The AI began identifying overclaims and arguing for alternative interpretations — a qualitative shift from the sycophantic tendencies of earlier generations.

### 5.4 Late 2025: Synthesis

Improvements were primarily in synthesis and interpretation. The AI could hold the full program in mind, draw connections across papers, and produce novel interpretive analyses. The Lean formalization capability improved incrementally.

### 5.5 Early 2026: Resumption with Opus 4.6

After a break, work resumed when Claude Opus 4.6 became available. The most significant enhancement was in Lean 4 capability: substantially improved Mathlib API navigation, complex multi-module proof construction, and reduced need for human guidance on routine formalization. This generation also brought enhanced capacity for the kind of sustained critical dialogue documented in Section 3 — honest evaluation of the program's scope and limitations, balanced assessment of which results matter and which are incremental, and practical recommendations grounded in realistic appraisal.

---

## 6. The Compiler as Epistemic Guarantor

Every theorem in this program compiles in Lean 4. The `#print axioms` command certifies which logical principles each proof employs. These are machine-checkable guarantees that do not depend on trust in either the human or the AI.

This matters because it addresses the central concern about AI-assisted research: reliability. In informal mathematics, correctness depends on human review. In formal mathematics, correctness is mechanically certified. The compiler does not evaluate credentials, institutional affiliation, or publication record. It evaluates proofs.

The compiler also served as an honesty enforcer during the collaboration. When either party made an incorrect mathematical claim during informal discussion, the attempt to formalize it in Lean would fail, forcing correction. Several results changed character during formalization: claims that seemed obvious on paper required additional axioms, while results expected to require strong principles turned out to be constructively provable. These surprises — revealed by the compiler, not by either collaborator — are among the program's most informative findings.

This experience suggests that formal verification is not merely beneficial but essential for AI-assisted mathematics at scale. Without the compiler's independent guarantee, a program of this volume would be epistemically suspect regardless of who produced it.

---

## 7. Limitations and Open Questions

### 7.1 What we do not claim

We do not claim that the program's results are free of errors beyond what the Lean compiler can detect. Formalization choices — how physical concepts are encoded as mathematical objects, which axioms are taken as primitive, whether the Lean encoding faithfully represents the intended mathematics — involve human judgment that the compiler cannot verify. A domain expert might reasonably object that a particular encoding misrepresents the physics it claims to formalize. Such objections would be valuable and are invited.

We do not claim that the AI's critical evaluations of the program's significance are reliable. The AI's assessments were useful as a sounding board but are not a substitute for expert peer review.

We do not claim that this mode of research is superior to traditional collaboration with domain experts. It is an alternative available when traditional collaboration is not, for whatever reason, accessible.

### 7.2 The question of significance

The program's core finding — that constructive logical cost correlates monotonically with physical idealization across multiple domains — is either a deep observation about the relationship between logic and physical reality, or an artifact of how humans build mathematical models, or both. We have stated this honestly throughout the technical papers and do not resolve it here. The formal results are verified; their interpretation remains open.

We hope that researchers in constructive mathematics, formal verification, and foundations of physics will examine the program's methodology and results. The Lean code is available on Zenodo. The calibration table is reproducible. The interpretive claims are falsifiable — a single physical theory whose empirical content requires non-constructive logic would refute the working hypothesis.

### 7.3 The collaboration itself

The collaboration documented in this paper is itself an object of study. We have attempted to be candid about what worked, what didn't, and where the boundaries of productive human-AI collaboration currently lie. The experience suggests that the combination of human architectural insight, AI iteration capacity, and mechanical proof verification constitutes a viable mode of foundational research — particularly for questions that fall between established disciplines, where traditional institutional support may be difficult to obtain.

Whether this mode produces work of lasting significance is not for the collaborators to judge. We offer the program, with its strengths and limitations, for the community's evaluation.

---

## 8. Summary: AI Capability by Generation

| Generation | Period | Lean capability | Mathematical contribution | Critical judgment | Collaboration mode |
|---|---|---|---|---|---|
| Claude 3.5 Sonnet | Mid-2024 | None | Textbook-level | Minimal | Directive |
| Late 3.5 / early Opus | Late 2024 – Early 2025 | Basic (20-30% hit rate) | Working-level | Weak | Assisted |
| Opus 4 / Sonnet 4 | Mid-2025 | Productive (rapid iteration) | Collaborative | Emerging | Partnership |
| Sonnet 4.5 / Opus 4.5 | Late 2025 | Strong | Synthesis across program | Substantive | Interpretive partnership |
| Opus 4.6 | Early 2026 | Very strong | Full program coherence | Mature | Architectural partnership |

---

## Acknowledgments

This program was conducted using Claude (Anthropic) across five model generations, with Claude Code as the primary Lean 4 formalization tool. Additional interactions with other AI systems (OpenAI, xAI, Google DeepMind) provided supplementary critique and alternative perspectives at various points. The author thanks the developers of Lean 4, Mathlib, and the constructive mathematics literature on which this program depends.

---

## References

[To be completed — key references include: Bishop 1967; Birkhoff and von Neumann 1936; Bridges and Richman 1987; Bridges and Vîță 2006; Ishihara 1992, 2006; Hilbert 1900 (Sixth Problem); Döring and Isham 2008; the 28 papers of the CRM and Physics series (Zenodo DOIs); Anthropic technical reports; and relevant work on AI-assisted formal mathematics.]
