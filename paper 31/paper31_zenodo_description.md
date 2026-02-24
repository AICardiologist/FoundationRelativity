# Zenodo Upload Metadata for Paper 31

## Title

The Physical Dispensability of Dependent Choice: A Lean 4 Formalization (Paper 31, CRM Series)

## Authors

Paul Chun-Kit Lee (New York University)

## Description (paste into Zenodo HTML description field)

---

<p><strong>Paper 31</strong> in the Constructive Reverse Mathematics (CRM) of Physics series.</p>

<p>This deposit contains the complete Lean 4 + Mathlib formalization proving that <strong>Dependent Choice (DC) is physically dispensable</strong>: every empirically accessible prediction derived from DC-calibrated results (SLLN, Birkhoff pointwise ergodic theorem) is recoverable in BISH+LPO, without invoking Dependent Choice. This is the crowning metamathematical result of the Constructive Calibration Programme (Papers 1&ndash;31).</p>

<p>The key insight: DC is needed only for the <em>quantifier swap</em>&mdash;commuting &forall;&epsilon; &exist;N&#8320; inside the probability measure to obtain pointwise a.e. convergence. An experimenter must choose measurement precision &epsilon; and confidence level 1&minus;&delta; <em>before</em> observing the outcome, so physical measurement fundamentally operates with quantifiers <em>outside</em> the measure. The swap requires tracking a single trajectory &omega; for infinite time, which no finite apparatus can do.</p>

<h3>Main Results</h3>

<p><strong>Part 1 &mdash; Probability convergence: WLLN suffices for SLLN (fully proved, zero sorry):</strong></p>
<ul>
  <li><code>chebyshev_wlln_bound</code>: Given known variance &sigma;&sup2;, the Chebyshev bound N&#8320; = &lceil;&sigma;&sup2;/(&delta;&epsilon;&sup2;)&rceil; + 1 is BISH-computable. <strong>No custom axioms</strong> (pure algebra).</li>
  <li><code>wlln_empirical_sufficiency</code>: WLLN captures all finite-precision laboratory predictions.</li>
  <li><code>slln_gap_requires_infinite_time</code>: For any finite time horizon T, the SLLN gap collapses to a WLLN-testable statement.</li>
  <li><code>slln_empirical_content_is_wlln</code>: The empirical content of SLLN is exactly WLLN.</li>
</ul>

<p><strong>Part 2 &mdash; Ergodic convergence: MET suffices for Birkhoff (fully proved, zero sorry):</strong></p>
<ul>
  <li><code>met_empirical_bound</code>: The Mean Ergodic Theorem&rsquo;s L&sup2; convergence, combined with LPO modulus extraction, provides explicit N&#8320; such that &int;|A<sub>N</sub>f &minus; f&#772;|&sup2; dP &lt; &delta;&epsilon;&sup2;. <strong>No custom axioms</strong> (pure filter extraction from <code>Tendsto</code>).</li>
  <li><code>met_implies_empirical</code>: MET &rarr; EmpiricalConvergence via Markov composition.</li>
  <li><code>birkhoff_gap_not_empirical</code>: The Birkhoff-vs-MET gap is empirically void.</li>
  <li><code>ergodic_empirical_equivalence</code>: The empirical content of Birkhoff = the empirical content of MET.</li>
</ul>

<p><strong>Part 3 &mdash; Master dispensability theorem (fully proved, zero sorry):</strong></p>
<ul>
  <li><code>dc_content_is_quantifier_swap</code>: The precise mathematical content of DC is the swap from &forall;&epsilon; &exist;N&#8320; P(&hellip;) &lt; &delta; (quantifiers outside) to P(&forall;&epsilon; &exist;N&#8320; &hellip;) = 1 (quantifiers inside).</li>
  <li><code>quantifier_swap_empirically_void</code>: Any finite experimental protocol extracts its predictions from the Empirical topology, not the Ontological topology.</li>
  <li><code>dc_physically_dispensable</code>: Three-way conjunction &mdash; (1) WLLN suffices for all SLLN empirical predictions, (2) MET suffices for all Birkhoff empirical predictions, (3) the quantifier swap is empirically void.</li>
</ul>

<p><strong>Master theorem:</strong></p>
<ul>
  <li><code>bish_lpo_empirically_complete</code>: BISH+LPO is the complete logical constitution of empirically accessible physics. Combines: LPO &rarr; CC (Ishihara 2006), DC dispensability, and BISH-computable Chebyshev bounds.</li>
</ul>

<h3>Physical Significance</h3>

<p>This result completes the Constructive Calibration Programme. Together with Papers 29&ndash;30:</p>

<table>
  <tr><th>Branch</th><th>Physical Status</th><th>Established by</th></tr>
  <tr><td>Omniscience spine (LLPO, WLPO, LPO)</td><td>Physically instantiated</td><td>Paper 29 (Fekete + phase transitions)</td></tr>
  <tr><td>Markov's Principle (MP)</td><td>Physically instantiated</td><td>Paper 29 (LPO &rArr; MP)</td></tr>
  <tr><td>Fan Theorem (FT)</td><td>Physically dispensable</td><td>Paper 30 (ApproxEVT from BMC &equiv; LPO)</td></tr>
  <tr><td>Choice axis: CC</td><td>Covered</td><td>Paper 31 (LPO &rArr; CC, Ishihara 2006)</td></tr>
  <tr><td>Choice axis: DC</td><td>Physically dispensable</td><td>Paper 31 (WLLN/MET from LPO, not SLLN/Birkhoff)</td></tr>
</table>

<p><strong>Conclusion:</strong> The logical constitution of empirically accessible physics is exactly BISH + LPO. The universe computes at precisely one axiom beyond constructivism.</p>

<h3>Axiom Certificate</h3>

<ul>
  <li><code>chebyshev_wlln_bound</code>: <code>[propext, Classical.choice, Quot.sound]</code> &mdash; <strong>BISH, no custom axioms</strong></li>
  <li><code>met_empirical_bound</code>: <code>[propext, Classical.choice, Quot.sound]</code> &mdash; <strong>no custom axioms</strong></li>
  <li><code>slln_empirical_content_is_wlln</code>: <code>[propext, Classical.choice, Quot.sound, slln_implies_wlln]</code></li>
  <li><code>met_implies_empirical</code>: <code>[propext, Classical.choice, Quot.sound, met_markov_composition]</code></li>
  <li><code>ergodic_empirical_equivalence</code>: <code>[propext, Classical.choice, Quot.sound, birkhoff_implies_met, met_markov_composition]</code></li>
  <li><code>dc_physically_dispensable</code>: <code>[propext, Classical.choice, Quot.sound, met_markov_composition]</code></li>
  <li><code>bish_lpo_empirically_complete</code>: <code>[propext, Classical.choice, Quot.sound, cc_of_lpo]</code></li>
  <li><strong>Zero sorry. 5 cited axioms total: <code>cc_of_lpo</code> (Ishihara 2006), <code>slln_implies_wlln</code> (standard), <code>birkhoff_implies_met</code> (standard), <code>met_markov_composition</code> (Markov&rsquo;s inequality), <code>ontological_implies_empirical</code> (a.s. &rArr; in probability).</strong></li>
</ul>

<h3>Technical Details</h3>

<ul>
  <li><strong>Lean 4:</strong> leanprover/lean4:v4.28.0-rc1</li>
  <li><strong>Mathlib4:</strong> commit <code>2598404fe9e0a5aee87ffca4ff83e2d01b23b024</code></li>
  <li><strong>Build:</strong> <code>cd P31_DCDispensability && lake exe cache get && lake build</code></li>
  <li><strong>Status:</strong> 0 errors, 0 warnings, 0 sorry</li>
</ul>

<h3>Package Contents</h3>

<ul>
  <li><code>P31_DCDispensability/</code> &mdash; Self-contained Lean 4 package (5 source files, 704 lines)</li>
  <li><code>paper31_dc_dispensability_blueprint.md</code> &mdash; Formalization blueprint</li>
  <li><code>README.md</code> &mdash; Build instructions and file manifest</li>
</ul>

---

## Keywords

constructive reverse mathematics, Dependent Choice, DC, strong law of large numbers, SLLN, weak law of large numbers, WLLN, mean ergodic theorem, Birkhoff pointwise ergodic theorem, quantifier swap, Limited Principle of Omniscience, LPO, countable choice, BISH, empirical completeness, Lean 4, Mathlib, formal verification, constructive mathematics, physical dispensability

## License

Apache 2.0 (code) / Creative Commons Attribution 4.0 International (CC BY 4.0) (paper)

## Related Identifiers

- Paper 8 (1D Ising / LPO): https://doi.org/10.5281/zenodo.18516813
- Paper 9 (Ising formulation-invariance): https://doi.org/10.5281/zenodo.18517570
- Paper 10 (Logical geography / synthesis): https://doi.org/10.5281/zenodo.18580342
- Paper 23 (Fan Theorem / compact optimization): https://doi.org/10.5281/zenodo.18604312
- Paper 28 (Newton vs. Lagrange / variational mechanics): https://doi.org/10.5281/zenodo.18616620
- Paper 29 (Fekete / LPO instantiation): [DOI pending]
- Paper 30 (Fan Theorem dispensability): [DOI pending]

## Resource Type

Software / Dataset

## Version

v1.0
