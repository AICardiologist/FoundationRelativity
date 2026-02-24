# Response to Referee Reports: Paper 44 — "The Measurement Problem Dissolved"

We thank all three referees for their careful, constructive, and technically precise feedback. The convergent themes identified by the referees have led to substantial improvements in both the formalization and the manuscript. Below we address each major concern.

---

## Summary of Changes

### New Genuine Proofs (Lean, no sorry)

| Theorem | Description | Addresses |
|---------|-------------|-----------|
| `strong_copenhagen_implies_LPO` | Strong Copenhagen → LPO | All 3 referees: Copenhagen formalization |
| `strong_implies_weak` | CopenhagenStrong → CopenhagenPostulate | All 3 referees: justifies WLPO choice |
| `DC_implies_manyworlds` | DC → ManyWorldsPostulate | Referee 1 Issue 2b, Referee 3 Issue 1 |
| `velocity_seq_bounded` | Velocity sequence bounded above | Referee 1 Issue 5, Referee 3 Issue 7 |
| `uniform_world_witness` | Σ-type constructive witness | Referee 3 Issue 4 |
| `finite_time_bish` | Meaningful initial-condition proof | Referee 3 Issue 8 |
| `copenhagen_spectrum` | Synthesis of weak+strong calibrations | All 3 referees |

### Code Convention Changes

- `axiom bmc_of_lpo` and `axiom lpo_of_bmc` converted to `theorem ... := by sorry` per ITP convention (Referee 3 Issue 2)

### Sorry Count

- **Before revision:** 8 sorry'd theorems + 2 axiom declarations = 10 sorry-equivalent obligations
- **After revision:** 8 sorry'd theorems (2 previously axiom, now transparently sorry'd) + 7 new genuine proofs

### Manuscript Revisions

- New §2.5: Defense of Copenhagen formalization with weak/strong comparison
- New §3.5: Everettian objection discussion, CC vs DC precision, DC independence citations
- New §4.6: Bohmian scope acknowledgment, asymptotic limit discussion
- Expanded §9.2: Decoherence discussion
- Softened "dissolution" language throughout (title retained, claims qualified)
- Updated CRM audit table, axiom audit table, results summary

---

## Responses to Convergent Themes

### 1. Faithfulness of the Copenhagen Formalization (All Three Referees)

**Concern:** All three referees questioned whether `α = 0 ∨ ¬¬(α ≠ 0)` correctly captures the Copenhagen postulate, noting that the full dichotomy `α = 0 ∨ α ≠ 0` would be more natural.

**Response:** We added `CopenhagenStrong` (the full dichotomy) and proved `strong_copenhagen_implies_LPO` with no sorry. The comparison is now a feature, not a bug:

| Formalization | Calibrates at | Forward proof status |
|--------------|---------------|---------------------|
| α = 0 ∨ ¬¬(α ≠ 0) (weak) | WLPO | **proved** |
| α = 0 ∨ α ≠ 0 (strong) | LPO | **proved** |

The gap between WLPO and LPO *measures the constructive cost* of the double-negation weakening. We present the weak formalization as primary because it yields the finest stratification, but §2.5 makes both options explicit and transparent. (Referee 1 Q1, Referee 2 Q1, Referee 3 Issue 5)

### 2. Sorry Load (All Three Referees)

**Concern:** 1 of 6 equivalence directions fully proved was insufficient for the strength of the claims.

**Response:** We have now proved three additional theorems:
- `strong_copenhagen_implies_LPO` (new calibration direction, fully proved)
- `DC_implies_manyworlds` (reverse direction of MWI ↔ DC, fully proved — notable for requiring only `propext` and `Quot.sound`, avoiding `Classical.choice`)
- `velocity_seq_bounded` (key lemma for Bohmian calibration, fully proved)

The formalization now has 4 fully proved calibration-relevant theorems (up from 1), plus the BISH bonus results. The manuscript language has been softened throughout: "dissolution thesis" rather than "established fact"; "calibrations suggest" rather than "calibrates at" for sorry-dependent directions. (Referee 1 Issue 4, Referee 2 Concern 6, Referee 3 Issue 1)

### 3. Many-Worlds Formalization (Referees 1 and 2)

**Concern:** Requiring existence of a complete path imports a single-world perspective foreign to Many-Worlds. DC requirement may be an artifact.

**Response:** New §3.5 addresses this directly. We argue that the formalization captures the *mathematical precondition* for Everett's claim — if one cannot constructively produce even a single complete branch, the assertion "all branches co-exist" is constructively vacuous. We acknowledge this as a formalization choice and discuss alternatives.

The proof of `DC_implies_manyworlds` demonstrates that DC is *sufficient* for constructing worlds. The sorry'd forward direction (`manyworlds_implies_DC`) would establish necessity.

**CC vs DC precision:** We now specify that BISH includes AC_ω,ω and explain that DC extends this by allowing history-dependent choices. Independence citations added: Beeson [21], Rathjen [22]. (Referee 1 Issues 2, 3, 6; Referee 2 Concern 2)

### 4. Bohmian Scope (Referees 1 and 2)

**Concern:** Free Gaussian is pedagogical; asymptotic velocity is an idealization not required for empirical predictions.

**Response:** New §4.6 acknowledges both points explicitly:
- The free Gaussian is a pedagogical example chosen for its explicit trajectory formula
- All empirical content is at finite time (where BISH suffices)
- The LPO cost measures the logical overhead of the *ontological* claim that trajectories extend to [0,∞) with well-defined limits
- We note that in scattering theory, the asymptotic velocity determines scattering cross-sections — so the limit is not empirically vacuous in all contexts

`velocity_seq_bounded` is now fully proved, reducing the Bohmian sorry count from 5 to 4. (Referee 1 Issues 5, 8; Referee 2 Concerns 3, 5)

### 5. "Dissolution" Language (All Three Referees)

**Concern:** The philosophical conclusion is stronger than the technical results warrant.

**Response:** Systematic revision throughout:
- Abstract: "We propose that arguing..." (was "Arguing...")
- §1.3: "dissolution thesis" (was "dissolves")
- §5.3: "may have been a category error" (was "was a category error"), qualified with "if the calibrations are correct"
- §9.3: "dissolution thesis" with explicit acknowledgment that "whether these formalizations capture the essential content of the interpretations is a philosophical judgment that the formal machinery cannot settle"
- §10: "dissolution thesis" with "supported by the fully proved directions and corroborated by proof sketches"

Title retained ("Dissolved") as it captures the aspiration; the body now consistently presents dissolution as a thesis to be established, not an established fact. (Referee 1 Issue 7; Referee 2 Concern 4; Referee 3 Issue 5)

---

## Responses to Unique Concerns

### Referee 1 (CRM Expert)

**Issue 3 (DC incomparability):** Added citations to Beeson [21] and Rathjen [22] with specific model descriptions in §3.5.

**Issue 9 (Lean infrastructure):** The suggestion to note that Bishop reals (Krebbers–Spitters) would avoid `Classical.choice` is well-taken. We note that `DC_implies_manyworlds` already achieves this — it requires only `propext` and `Quot.sound`, demonstrating that the cleanest proofs can avoid `Classical.choice` entirely.

**Issue 10 (Weihrauch degrees):** Retained as future work in §9.2 with expanded discussion.

### Referee 2 (Physics Expert)

**Concern 7 (Decoherence):** Added discussion in §9.2 acknowledging decoherence as a scope limitation and discussing potential effects on calibrations.

**Concern 9 (Döring–Isham comparison):** The existing §9.1 comparison is retained; the complementary relationship (they restructure the framework; we calibrate within it) is the key distinction.

**Q5 (Methodology vs. result):** The manuscript now consistently presents this as proposing a *methodology* with concrete results (the fully proved directions) rather than claiming the dissolution is fully established.

### Referee 3 (Lean Expert)

**Issue 2 (`axiom` vs `sorry`):** Converted both to `theorem ... := by sorry`. The `#print axioms` output now correctly shows `sorryAx` for all sorry-dependent theorems. No hidden obligations.

**Issue 3 (`Classical.choice` in tsum):** Noted in §6 that `Classical.choice` is infrastructure. The DC proof (`DC_implies_manyworlds`) demonstrates that calibration proofs need not inherently depend on `Classical.choice`.

**Issue 4 (`Nonempty` vs Σ-type):** Added `uniform_world_witness : World U.toBranching` as a Type-valued constructive witness.

**Issue 8 (`finite_time_bish` proves True):** Replaced with `bohmian_trajectory p x_init 0 = x_init`, delegating to the existing `bohmian_trajectory_zero`.

**Q1 (Which sorry obligations are closest?):** `velocity_seq_monotone_of_ge` (pure calculus sign analysis) is closest; `trajectory_satisfies_ODE` requires `HasDerivAt` composition which is verbose but standard; `manyworlds_implies_DC` (type encoding for arbitrary types) and `bohmian_implies_LPO` (encoding+decision) are hardest.

---

## Verification

- `lake build`: zero errors, zero non-sorry warnings
- Sorry count: 8 (transparently tracked via `#print axioms`)
- All code snippets in the manuscript match the actual Lean source files
- Zenodo bundle will be updated with revision

---

*We believe these changes address all major and minor concerns raised by the referees. We are grateful for the thoroughness and precision of the reviews, which have substantially strengthened both the formalization and the manuscript.*
