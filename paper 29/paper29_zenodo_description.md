# Zenodo Upload Metadata for Paper 29

## Title

Fekete's Subadditive Lemma is Equivalent to LPO: A Lean 4 Formalization (Paper 29, CRM Series)

## Authors

Paul Chun-Kit Lee (New York University)

## Description (paste into Zenodo HTML description field)

---

<p><strong>Paper 29</strong> in the Constructive Reverse Mathematics (CRM) of Physics series.</p>

<p>This deposit contains the complete Lean 4 + Mathlib formalization proving that <strong>Fekete's Subadditive Lemma</strong> &mdash; the assertion that every subadditive sequence with u(n)/n bounded below converges &mdash; is <strong>equivalent to the Limited Principle of Omniscience (LPO)</strong> over Bishop-style constructive mathematics (BISH). Includes the accompanying paper (LaTeX source and compiled PDF).</p>

<h3>Main Results</h3>

<p><strong>Backward direction (fully proved, zero sorry):</strong></p>
<ul>
  <li><code>lpo_of_fekete</code>: Given any binary sequence &alpha;, encode it into a mock free energy F<sub>n</sub> = &minus;n &middot; x<sub>n</sub> where x<sub>n</sub> = 1 iff &exist; k &lt; n, &alpha;(k) = true. F is subadditive with F<sub>n</sub>/n &ge; &minus;1. Applying Fekete's lemma and evaluating at a sufficiently large truncation decides LPO.</li>
</ul>

<p><strong>Forward direction (axiomatized from literature):</strong></p>
<ul>
  <li><code>fekete_of_lpo</code>: Composes LPO &rarr; BMC (Bridges&ndash;V&icirc;&#x163;&abreve; 2006, Theorem 2.1.5) with the classical Fekete proof via bounded monotone convergence (available in Mathlib as <code>Subadditive.tendsto_lim</code>).</li>
</ul>

<p><strong>Main equivalence:</strong></p>
<ul>
  <li><code>fekete_iff_lpo</code>: FeketeConvergence &harr; LPO (over BISH).</li>
</ul>

<h3>Three-Tier Hierarchy for Thermodynamic-Limit Convergence</h3>

<p>This result establishes a sharp constructive stratification:</p>

<table>
  <tr><th>Route</th><th>Logical Cost</th><th>Example</th></tr>
  <tr><td>Exact solution (closed-form modulus)</td><td>BISH</td><td>1D Ising model (Papers 8, 9)</td></tr>
  <tr><td>Cluster expansion (exponential decay)</td><td>BISH</td><td>High-temperature lattice gases</td></tr>
  <tr><td>Generic subadditivity (Fekete)</td><td>LPO</td><td>This paper</td></tr>
</table>

<p>The LPO cost becomes <strong>ineliminable</strong> when explicit finite-size bounds are unavailable &mdash; typically near phase transitions where correlation lengths diverge. This resolves <strong>Problem 1</strong> from Paper 10 (the synthesis paper): the LPO cost of the thermodynamic limit is ineliminable at the generic level of Fekete's lemma.</p>

<h3>Axiom Certificate</h3>

<ul>
  <li><strong>Backward direction:</strong> <code>[propext, Classical.choice, Quot.sound]</code> &mdash; standard Mathlib infrastructure only. No LPO, WLPO, LLPO, or custom axioms.</li>
  <li><strong>Full equivalence:</strong> Above plus <code>bmc_of_lpo</code> and <code>fekete_of_bmc</code> (axiomatized, citing Bridges&ndash;V&icirc;&#x163;&abreve; 2006 and Mathlib's <code>Subadditive.tendsto_lim</code>).</li>
  <li><strong>Zero sorry. Zero custom axioms in backward direction.</strong></li>
</ul>

<h3>Technical Details</h3>

<ul>
  <li><strong>Lean 4:</strong> leanprover/lean4:v4.28.0-rc1</li>
  <li><strong>Mathlib4:</strong> commit <code>2598404fe9e0a5aee87ffca4ff83e2d01b23b024</code></li>
  <li><strong>Build:</strong> <code>cd P29_FeketeLPO && lake exe cache get && lake build</code></li>
  <li><strong>Status:</strong> 0 errors, 0 warnings, 0 sorry</li>
</ul>

<h3>Package Contents</h3>

<ul>
  <li><code>P29_FeketeLPO/</code> &mdash; Self-contained Lean 4 package (6 source files, 549 lines)</li>
  <li><code>paper29_fekete_lpo.tex</code> &mdash; LaTeX source</li>
  <li><code>paper29_fekete_lpo.pdf</code> &mdash; Compiled paper</li>
  <li><code>README.md</code> &mdash; Build instructions and file manifest</li>
</ul>

---

## Keywords

constructive reverse mathematics, Fekete's lemma, subadditive sequences, Limited Principle of Omniscience, LPO, thermodynamic limit, BISH, Lean 4, Mathlib, formal verification, constructive mathematics, statistical mechanics, phase transitions

## License

Apache 2.0 (code) / Creative Commons Attribution 4.0 International (CC BY 4.0) (paper)

## Related Identifiers

- Paper 8 (1D Ising / LPO): https://doi.org/10.5281/zenodo.18516813
- Paper 9 (Ising formulation-invariance): https://doi.org/10.5281/zenodo.18517570
- Paper 10 (Logical geography / synthesis): https://doi.org/10.5281/zenodo.18580342

## Resource Type

Software / Dataset

## Version

v1.0

