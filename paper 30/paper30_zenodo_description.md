# Zenodo Upload Metadata for Paper 30

## Title

The Physical Dispensability of the Fan Theorem: A Lean 4 Formalization (Paper 30, CRM Series)

## Authors

Paul Chun-Kit Lee (New York University)

## Description (paste into Zenodo HTML description field)

---

<p><strong>Paper 30</strong> in the Constructive Reverse Mathematics (CRM) of Physics series.</p>

<p>This deposit contains the complete Lean 4 + Mathlib formalization proving that the <strong>Fan Theorem (FT) is physically dispensable</strong>: every empirically accessible prediction derived from the FT-calibrated results in Papers 23 and 28 is recoverable in BISH+LPO, without invoking the Fan Theorem. Includes the accompanying paper (LaTeX source and compiled PDF).</p>

<p>The key insight is twofold: (1) approximate optimization to any finite precision &varepsilon; &gt; 0 requires only BMC (&equiv; LPO), not FT; and (2) the physical content of variational mechanics is the Euler&ndash;Lagrange equation (BISH), not the existence of an action minimizer (FT). Since no finite experiment can distinguish exact attainment from &varepsilon;-approximate attainment, FT is dispensable for all empirical predictions.</p>

<h3>Main Results</h3>

<p><strong>Pillar 1 &mdash; Approximate optimization from LPO (fully proved, zero sorry):</strong></p>
<ul>
  <li><code>sup_exists_of_bmc</code>: Given a continuous f on [a,b], construct a monotone bounded sequence of running grid maxima. Apply BMC to obtain the supremum S. Prove S is an upper bound (via uniform continuity + grid density) and &varepsilon;-attainable (via grid witnesses converging to S).</li>
  <li><code>approxEVT_of_lpo</code>: Composes LPO &rarr; BMC (Bridges&ndash;V&icirc;&#x163;&abreve; 2006) with <code>sup_exists_of_bmc</code> to obtain ApproxEVT.</li>
  <li><code>empirical_completeness</code>: LPO &rarr; for any &varepsilon; &gt; 0, there exists x<sub>&varepsilon;</sub> &isin; [a,b] with f(y) &lt; f(x<sub>&varepsilon;</sub>) + &varepsilon; for all y &isin; [a,b].</li>
</ul>

<p><strong>Pillar 2 &mdash; Separation (fully proved, zero sorry, no custom axioms):</strong></p>
<ul>
  <li><code>exactEVT_iff_ft</code>: ExactEVT &harr; FanTheorem. The forward direction uses rescaling from [0,1] to [a,b]; the backward direction is immediate (ExactEVT on [0,1] gives EVT_max).</li>
</ul>

<p><strong>Pillar 3 &mdash; Variational stratification:</strong></p>
<ul>
  <li><code>variational_stratification</code>: Three-way decomposition &mdash; (1) Euler&ndash;Lagrange solution exists (BISH), (2) approximate minimizer exists (LPO), (3) exact minimizer existence &harr; FT (cited from Paper 28).</li>
</ul>

<p><strong>Master theorem:</strong></p>
<ul>
  <li><code>ft_physically_dispensable</code>: (LPO &rarr; ApproxEVT) &and; (ExactEVT &harr; FanTheorem) &and; (LPO &rarr; empirical completeness).</li>
</ul>

<h3>Physical Significance</h3>

<p>This result narrows the question &ldquo;what is the logical constitution of empirically accessible physics?&rdquo; from &ldquo;BISH + some subset of {LPO, FT, DC, &hellip;}&rdquo; to &ldquo;BISH + LPO + possibly DC.&rdquo; Together with Paper 29 (LPO is physically instantiated via Fekete's lemma and the reality of phase transitions), this establishes:</p>

<table>
  <tr><th>Branch</th><th>Physical Status</th><th>Covered by LPO?</th></tr>
  <tr><td>Omniscience spine (LLPO, WLPO, LPO)</td><td>Physically instantiated</td><td>Yes</td></tr>
  <tr><td>Markov's Principle (MP)</td><td>Physically instantiated</td><td>Yes</td></tr>
  <tr><td>Fan Theorem (FT)</td><td>Physically dispensable</td><td>N/A (dispensable)</td></tr>
  <tr><td>Choice axis (CC, DC)</td><td>Open (Paper 31)</td><td>CC yes; DC open</td></tr>
</table>

<h3>Axiom Certificate</h3>

<ul>
  <li><code>approxEVT_of_lpo</code>: <code>[propext, Classical.choice, Quot.sound, bmc_of_lpo]</code></li>
  <li><code>exactEVT_iff_ft</code>: <code>[propext, Classical.choice, Quot.sound]</code> &mdash; no custom axioms (pure rescaling argument)</li>
  <li><code>empirical_completeness</code>: <code>[propext, Classical.choice, Quot.sound, bmc_of_lpo]</code></li>
  <li><code>variational_stratification</code>: <code>[propext, Classical.choice, Quot.sound, bmc_of_lpo, minimizer_iff_ft_cited]</code></li>
  <li><code>ft_physically_dispensable</code>: <code>[propext, Classical.choice, Quot.sound, bmc_of_lpo]</code></li>
  <li><strong>Zero sorry. 3 cited axioms total: <code>bmc_of_lpo</code> (Bridges&ndash;V&icirc;&#x163;&abreve; 2006), <code>el_unique_bish</code> (Paper 28), <code>minimizer_iff_ft_cited</code> (Paper 28).</strong></li>
</ul>

<h3>Technical Details</h3>

<ul>
  <li><strong>Lean 4:</strong> leanprover/lean4:v4.28.0-rc1</li>
  <li><strong>Mathlib4:</strong> commit <code>2598404fe9e0a5aee87ffca4ff83e2d01b23b024</code></li>
  <li><strong>Build:</strong> <code>cd P30_FTDispensability && lake exe cache get && lake build</code></li>
  <li><strong>Status:</strong> 0 errors, 0 warnings, 0 sorry</li>
</ul>

<h3>Package Contents</h3>

<ul>
  <li><code>P30_FTDispensability/</code> &mdash; Self-contained Lean 4 package (7 source files, 918 lines)</li>
  <li><code>paper30_ft_dispensability.tex</code> &mdash; LaTeX source</li>
  <li><code>paper30_ft_dispensability.pdf</code> &mdash; Compiled paper</li>
  <li><code>README.md</code> &mdash; Build instructions and file manifest</li>
</ul>

---

## Keywords

constructive reverse mathematics, Fan Theorem, extreme value theorem, approximate optimization, Limited Principle of Omniscience, LPO, bounded monotone convergence, BMC, variational mechanics, Euler-Lagrange equations, BISH, Lean 4, Mathlib, formal verification, constructive mathematics, physical dispensability

## License

Apache 2.0 (code) / Creative Commons Attribution 4.0 International (CC BY 4.0) (paper)

## Related Identifiers

- Paper 8 (1D Ising / LPO): https://doi.org/10.5281/zenodo.18516813
- Paper 9 (Ising formulation-invariance): https://doi.org/10.5281/zenodo.18517570
- Paper 10 (Logical geography / synthesis): https://doi.org/10.5281/zenodo.18580342
- Paper 23 (Fan Theorem / compact optimization): https://doi.org/10.5281/zenodo.18604312
- Paper 28 (Newton vs. Lagrange / variational mechanics): https://doi.org/10.5281/zenodo.18616620

## Resource Type

Software / Dataset

## Version

v1.0
