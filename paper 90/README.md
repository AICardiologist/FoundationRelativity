# Paper 90: The Squeeze Is a Microscope

**Full title:** The Squeeze Is a Microscope: Automated Constructivization from CRMLint to the Hodge Horizon (Paper 90, Constructive Reverse Mathematics Series)

**Author:** Paul Chun-Kit Lee, New York University, Brooklyn, NY

## Summary

This synthesis monograph covers the generative phase (Papers 76-89) of the Constructive Reverse Mathematics program. It documents the CRMLint Squeeze protocol — a four-step procedure (Scaffold, X-Ray, Excise, Squeeze) that isolates the constructive core of a classical theorem from its irreducible classical boundary — and its application across eleven domains.

## Main Results

- **Theorem A (Squeeze Protocol):** The CRMLint Squeeze decomposes classical theorems into BISH-verified components and CLASS axiom stubs. Across 11 applications, >80% of formal content is BISH.

- **Theorem B (Bifurcation):** For the universal genus-4 Weil family, the palindromic locus {a=c} gives unconditional algebraicity via Kani-Rosen splitting; the generic complement requires the Variational Hodge Conjecture.

- **Theorem C (Hodge Horizon):** The uniform Hodge test is equivalent to WLPO (Paper 87). VHC is the irreducible CLASS boundary for generic exotic Weil classes.

- **Theorem D (Asymmetric Offloading):** CAS-generated polynomial identities verified by Lean's `ring` tactic constitute >80% of formal content across 11 Squeeze applications.

## Paper Type

Synthesis monograph (no new Lean bundle). Reports aggregate formal verification statistics from Papers 77-89 (~5,300 lines Lean 4, zero sorry).

## Structure

- Part I: The Method (Squeeze protocol, asymmetric offloading, infrastructure arc)
- Part II: The Campaign (Hodge campaign, bifurcation theorem, Hodge horizon)
- Part III: The Architecture (CRM audit, formal verification, discussion)

## Dependencies

This paper synthesizes results from Papers 77-89. No new Lean code is introduced.

## Citation

Lee, P. C.-K. (2026). The Squeeze Is a Microscope: Automated Constructivisation from CRMLint to the Hodge Horizon (Paper 90, CRM Series). Zenodo.
