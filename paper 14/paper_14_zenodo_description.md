# Zenodo Upload Metadata for Paper 14

## Title

The Measurement Problem as a Logical Artefact: Constructive Calibration of Quantum Decoherence (Paper 14 — Lean 4 Formalization)

## Authors

Paul Chun-Kit Lee (New York University)

## Description (paste into Zenodo HTML description field)

---

<p><strong>Paper 14</strong> in the Constructive Reverse Mathematics of Physics series.</p>

<p>This deposit contains the complete Lean 4 + Mathlib formalization of quantum decoherence calibrated against constructive omniscience principles, together with the accompanying paper (LaTeX source and compiled PDF).</p>

<h3>Main Results</h3>

<p><strong>Part A — BISH content (constructive, no omniscience):</strong></p>
<ul>
  <li><code>decoherence_epsilon_bound</code>: For any ε &gt; 0 and interaction angle 0 &lt; θ &lt; π, there exists an explicitly computable N₀ such that the quantum coherence c(N) &lt; ε for all N ≥ N₀.</li>
  <li><code>coherence_eq_geometric</code>: The coherence decays geometrically: c(N) = ‖ρ₀₁‖ · |cos(θ/2)|<sup>N</sup>.</li>
  <li><code>decoherenceMap_eq_physical</code>: The explicit decoherence formula equals the physical definition Φ(ρ) = Tr<sub>E</sub>[U(θ)·(ρ⊗|0⟩⟨0|)·U†(θ)], verified by brute-force 4×4 matrix computation.</li>
</ul>

<p><strong>Part B — LPO equivalence:</strong></p>
<ul>
  <li><code>exact_decoherence_iff_LPO</code>: The assertion "every bounded antitone sequence converges exactly" is equivalent to the Limited Principle of Omniscience (LPO).</li>
  <li><code>abc_iff_bmc</code>: Antitone Bounded Convergence ↔ (monotone) Bounded Monotone Convergence, via sign-flip (fully proved, no axioms).</li>
</ul>

<h3>Three Domains, One Logical Structure</h3>

<p>This is the third physical domain producing the BMC ↔ LPO pattern:</p>
<table>
  <tr><th>Domain</th><th>Bounded Monotone Sequence</th><th>LPO Content</th></tr>
  <tr><td>Statistical Mechanics (Paper 8)</td><td>Free energy f<sub>N</sub></td><td>f<sub>∞</sub> exists exactly</td></tr>
  <tr><td>General Relativity (Paper 13)</td><td>Radial coordinate r(τ)</td><td>r → 0 exactly</td></tr>
  <tr><td>Quantum Measurement (Paper 14)</td><td>Coherence c(N)</td><td>c → 0 exactly (collapse)</td></tr>
</table>

<h3>Axiom Certificate</h3>
<ul>
  <li><strong>BISH theorems:</strong> <code>[propext, Classical.choice, Quot.sound]</code> — standard Mathlib infrastructure only. No omniscience principles.</li>
  <li><strong>LPO theorems:</strong> Above plus <code>bmc_of_lpo</code>, <code>lpo_of_bmc</code> (axiomatized, citing Bridges–Vîță 2006 and Paper 8).</li>
  <li><strong>Sign-flip lemma</strong> (<code>abc_iff_bmc</code>): Fully proved, no custom axioms.</li>
</ul>

<h3>Technical Details</h3>
<ul>
  <li><strong>Lean 4:</strong> leanprover/lean4:v4.28.0-rc1</li>
  <li><strong>Mathlib4:</strong> commit <code>7091f0f601d5aaea565d2304c1a290cc8af03e18</code></li>
  <li><strong>Build:</strong> <code>cd P14_Decoherence && lake exe cache get && lake build</code></li>
  <li><strong>Status:</strong> 0 errors, 0 sorry</li>
</ul>

<h3>Package Contents</h3>
<ul>
  <li><code>P14_Decoherence/</code> — Self-contained Lean 4 package (9 source files, 805 lines)</li>
  <li><code>paper14_writeup.tex</code> — LaTeX source</li>
  <li><code>paper14_writeup.pdf</code> — Compiled paper (13 pages)</li>
  <li><code>README.md</code> — Build instructions and file manifest</li>
</ul>

---

## Keywords

constructive mathematics, reverse mathematics, quantum decoherence, measurement problem, Lean 4, Mathlib, formal verification, LPO, bounded monotone convergence, density matrix

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)

## Related Identifiers

- Paper 8 (1D Ising / LPO): https://doi.org/10.5281/zenodo.15043592
- Paper 13 (Schwarzschild / LPO): [insert DOI when available]

## Resource Type

Software / Dataset

## Version

v1.0
