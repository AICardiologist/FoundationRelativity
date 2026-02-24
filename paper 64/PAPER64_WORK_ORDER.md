# Paper 64: Effective Colmez-Fontaine — Computational Work Order

**For:** Computational AI agent (Claude Code, or equivalent)
**From:** Paul Lee / editorial team
**Date:** February 2026
**Priority:** Execute now (parallel with Papers 61–62 writing/Lean work)

---

## Context

Paper 59 in the Constructive Reverse Mathematics series proved that for an elliptic curve E over ℚ, the p-adic precision needed to decide crystalline equivalence is:

```
N_M = v_p(#E(𝔽_p))
```

where:
- p is a prime of good reduction for E
- #E(𝔽_p) = p + 1 - a_p is the number of points on E mod p
- a_p is the Frobenius trace (available from Cremona/LMFDB databases)
- v_p(n) is the p-adic valuation of n (how many times p divides n)

Paper 59 proved N_M is BISH-computable for individual curves. Paper 64 asks: **what happens across families?** Is N_M bounded? Does it correlate with known invariants? Are there patterns?

This is a data-generation and pattern-search task. No new theorems to prove. The mathematics is grade-school arithmetic (subtract two integers, count prime factors). The value is in systematic computation at scale and in recognizing patterns in the output.

---

## Phase 1: Data Extraction

### 1A. Elliptic curves from LMFDB

**Source:** LMFDB API (https://www.lmfdb.org/api/) or Cremona database

**Query:** All elliptic curves over ℚ with conductor N ≤ 1000.

**For each curve, extract:**
- LMFDB label (e.g., "11.a1")
- Conductor N
- Rank (analytic rank)
- Torsion group (e.g., ℤ/2ℤ, ℤ/5ℤ, trivial)
- CM discriminant (0 if non-CM, otherwise the CM discriminant)
- a_p for all primes p ≤ 200 (or as many as available)
- Cremona label (for cross-reference)

**Expected scale:** ~5,000–6,000 curves. The LMFDB has complete data for conductor ≤ 500,000.

**Storage format:** JSON or CSV. One row per curve. a_p stored as a list indexed by prime index.

**Access method (preferred):**
```python
import requests

# LMFDB API example
url = "https://www.lmfdb.org/api/ec_curvedata/"
params = {
    "conductor": {"$lte": 1000},
    "_fields": "label,conductor,rank,torsion_structure,cm_discriminant,aplist",
    "_limit": 100,
    "_offset": 0
}
response = requests.get(url, params=params)
```

**Alternative:** If the API is slow or rate-limited, download the Cremona database directly:
```python
# SageMath approach (if available)
from sage.databases.cremona import CremonaDatabase
db = CremonaDatabase()
```

**Alternative 2:** Use the LMFDB bulk download files if available at https://www.lmfdb.org/data/

**Fallback:** If neither API nor download works, use web scraping on individual curve pages. This is slow but works.

### 1B. Weight-2 newforms from LMFDB

**Source:** LMFDB API, classical modular forms section

**Query:** All weight-2 newforms of level N ≤ 100 with trivial character.

**For each newform, extract:**
- LMFDB label
- Level N
- Dimension (should be 1 for rational newforms corresponding to elliptic curves)
- a_p coefficients for primes p ≤ 200
- Associated elliptic curve label (if known)

**Expected scale:** ~100–200 newforms. Much smaller dataset.

**Purpose:** Cross-check against elliptic curve data (by modularity, every weight-2 rational newform corresponds to an elliptic curve). Confirm N_M values match between the two data sources.

---

## Phase 2: Compute N_M Tables

### 2A. Core computation

For each (curve E, prime p) pair where p does not divide the conductor of E (good reduction):

```python
def compute_N_M(a_p, p):
    """
    Compute N_M = v_p(#E(F_p)) = v_p(p + 1 - a_p).
    
    Args:
        a_p: Frobenius trace at p
        p: prime
    Returns:
        v_p(p + 1 - a_p), the p-adic valuation
    """
    point_count = p + 1 - a_p
    if point_count == 0:
        return float('inf')  # supersingular at p, flag this
    
    v = 0
    n = abs(point_count)
    while n % p == 0:
        v += 1
        n //= p
    return v
```

### 2B. Output table structure

Produce a table with columns:

| Column | Type | Description |
|--------|------|-------------|
| label | string | LMFDB label |
| conductor | int | Conductor of E |
| rank | int | Analytic rank |
| torsion | string | Torsion group |
| cm | int | CM discriminant (0 if non-CM) |
| p | int | Prime |
| a_p | int | Frobenius trace |
| point_count | int | p + 1 - a_p |
| N_M | int | v_p(point_count) |

**Scale:** ~5,000 curves × ~50 primes (primes p ≤ 200 not dividing N) ≈ 250,000 rows.

### 2C. Summary statistics per curve

For each curve, also compute:

| Column | Description |
|--------|-------------|
| max_N_M | Maximum N_M across all primes computed |
| max_N_M_prime | The prime where max_N_M is achieved |
| num_anomalous | Count of primes where a_p = 1 (anomalous primes) |
| num_supersingular | Count of primes where a_p = 0 |
| num_N_M_positive | Count of primes where N_M > 0 |
| num_N_M_geq_2 | Count of primes where N_M ≥ 2 |

### 2D. Summary statistics per prime

For each prime p ≤ 200:

| Column | Description |
|--------|-------------|
| p | The prime |
| total_curves | Number of curves with good reduction at p |
| num_N_M_0 | Count where N_M = 0 |
| num_N_M_1 | Count where N_M = 1 |
| num_N_M_2 | Count where N_M = 2 |
| num_N_M_geq_3 | Count where N_M ≥ 3 |
| max_N_M | Maximum N_M across all curves |
| max_N_M_curve | Curve label achieving max_N_M |

---

## Phase 3: Pattern Search

This is the scientifically interesting phase. Run the following analyses on the computed data.

### 3A. Global boundedness

**Question:** Is max_N_M bounded across all curves of conductor ≤ 1000?

**Analysis:**
- Plot histogram of max_N_M values across all curves.
- What is the global maximum of max_N_M? At which (curve, prime) pair is it achieved?
- Does max_N_M grow with conductor? Plot max_N_M vs. conductor (scatter plot).
- Compute: for each prime p, what is the maximum N_M = v_p(p + 1 - a_p) possible given the Hasse bound |a_p| ≤ 2√p? This gives a theoretical upper bound. Is it achieved?

**Theoretical bound check:**
```python
import math

def hasse_max_N_M(p):
    """
    Maximum possible N_M at prime p, given Hasse bound.
    a_p ranges from -floor(2*sqrt(p)) to +floor(2*sqrt(p)).
    point_count = p + 1 - a_p ranges from 
      p + 1 - floor(2*sqrt(p)) to p + 1 + floor(2*sqrt(p)).
    We need the value in this range with highest p-adic valuation.
    """
    a_max = int(2 * math.sqrt(p))
    max_v = 0
    for a in range(-a_max, a_max + 1):
        pc = p + 1 - a
        if pc == 0:
            continue
        v = 0
        n = abs(pc)
        while n % p == 0:
            v += 1
            n //= p
        max_v = max(max_v, v)
    return max_v
```

Compute this for all primes p ≤ 200. Compare with the empirical maximum.

### 3B. Correlation with rank

**Question:** Does N_M behave differently for rank 0 vs rank 1 vs rank ≥ 2 curves?

**Analysis:**
- Stratify curves by rank (0, 1, 2, ≥3).
- For each stratum, compute the distribution of max_N_M.
- T-test or KS test: is the max_N_M distribution different across ranks?
- Specific check: do rank ≥ 2 curves have systematically higher N_M? (This would be a p-adic analogue of the rank obstruction identified in Paper 59.)

### 3C. Correlation with torsion

**Question:** Does the torsion group affect N_M?

**Analysis:**
- Stratify by torsion group.
- For primes p dividing the torsion order, does N_M behave specially? (If E has a point of order p over ℚ, then p | #E(𝔽_p) for all primes of good reduction, so N_M ≥ 1 always. This is known but worth verifying in the data.)
- For primes not dividing the torsion order, is there still a torsion effect?

### 3D. CM vs non-CM

**Question:** Do CM curves behave differently?

**Analysis:**
- Separate CM curves (there are very few with conductor ≤ 1000: the 13 CM j-invariants give twists, but most have small conductor).
- For CM curves, the distribution of a_p is known (equidistributed on a circle, not Sato-Tate). Does this produce different N_M distributions?

### 3E. Anomalous primes

**Question:** How are anomalous primes (a_p = 1, so #E(𝔽_p) = p) distributed?

**Analysis:**
- For anomalous primes, N_M = v_p(p) = 1 always (since p | p but p² ∤ p). So anomalous primes always give N_M = 1.
- Count anomalous primes per curve. Is this count correlated with any invariant?
- List all (curve, prime) pairs where the prime is anomalous.

### 3F. Large N_M events

**Question:** When does N_M ≥ 2? When does N_M ≥ 3?

**Analysis:**
- List all (curve, prime) pairs with N_M ≥ 2. How rare are these?
- List all with N_M ≥ 3. Even rarer?
- For N_M = k, we need p^k | (p + 1 - a_p). For k = 2, this means p² | (p + 1 - a_p), so a_p ≡ p + 1 (mod p²), i.e., a_p ≡ 1 (mod p). Since |a_p| ≤ 2√p, this forces a_p = 1 for large p (when p > 4). So for p > 4, N_M ≥ 2 implies a_p = 1 AND p² | p, which is impossible unless p + 1 - 1 = p and p² | p, meaning p = 1. Contradiction.
- **WAIT: This means for p > 4, N_M ≤ 1 always.** Verify this in the data.
- For small primes (p = 2, 3), N_M can be larger. Compute the exact possible values.

**This is potentially the main result of Paper 64: N_M ≤ 1 for all p > 4, giving uniform p-adic decidability with at most 1 digit of p-adic precision.**

### 3G. Small prime analysis

For p = 2 and p = 3 specifically:

**p = 2:**
- a_2 ∈ {-2, -1, 0, 1, 2} (Hasse bound)
- #E(𝔽_2) = 3 - a_2 ∈ {1, 2, 3, 4, 5}
- N_M = v_2(#E(𝔽_2)):
  - a_2 = -2 → #E = 5, N_M = 0
  - a_2 = -1 → #E = 4, N_M = 2
  - a_2 = 0 → #E = 3, N_M = 0
  - a_2 = 1 → #E = 2, N_M = 1
  - a_2 = 2 → #E = 1, N_M = 0
- **Max N_M at p = 2 is 2** (when a_2 = -1, i.e., #E(𝔽_2) = 4).

**p = 3:**
- a_3 ∈ {-3, -2, -1, 0, 1, 2, 3}
- #E(𝔽_3) = 4 - a_3 ∈ {1, 2, 3, 4, 5, 6, 7}
- N_M = v_3(#E(𝔽_3)):
  - #E = 3, N_M = 1 (a_3 = 1)
  - #E = 6, N_M = 1 (a_3 = -2)
  - All others: N_M = 0
  - **Wait:** #E = 9 would give N_M = 2, but max #E(𝔽_3) = 7. So N_M ≤ 1 at p = 3 too.
- **Max N_M at p = 3 is 1.**

**p = 2 is the only prime where N_M can exceed 1, and there N_M ≤ 2.**

Verify this analysis empirically in the data.

### 3H. Newform cross-check

**Question:** Do the N_M values from the newform data match the elliptic curve data?

**Analysis:**
- For each newform of level ≤ 100 with a known associated elliptic curve, compare N_M values.
- They should match exactly (by modularity). Any discrepancy indicates a data error.

---

## Phase 4: Deliverables

### 4A. Data files

Save all outputs to the working directory:

1. `p64_curves_raw.json` — Raw extracted curve data from LMFDB
2. `p64_N_M_table.csv` — Full (curve, prime, N_M) table
3. `p64_curve_summary.csv` — Per-curve summary statistics
4. `p64_prime_summary.csv` — Per-prime summary statistics
5. `p64_newform_data.json` — Newform extraction and cross-check

### 4B. Plots

Generate and save as PNG:

1. `p64_histogram_max_NM.png` — Histogram of max_N_M across all curves
2. `p64_scatter_NM_vs_conductor.png` — max_N_M vs conductor scatter
3. `p64_NM_by_rank.png` — max_N_M distribution stratified by rank
4. `p64_NM_by_torsion.png` — max_N_M distribution stratified by torsion group
5. `p64_small_primes.png` — N_M distribution at p = 2, 3, 5 specifically
6. `p64_hasse_bound_comparison.png` — Theoretical max N_M vs empirical max, by prime

### 4C. Summary report

Write `p64_computation_report.md` containing:

1. **Data summary:** How many curves, how many (curve, prime) pairs computed
2. **Main finding:** Is N_M bounded? What is the global maximum? At which (curve, prime)?
3. **The N_M ≤ 1 conjecture:** Verify or refute: for p > 4, N_M ≤ 1 always. If verified, prove it (the proof is the mod-p² argument in §3F above).
4. **Rank correlation:** Any signal? Statistical significance?
5. **Torsion effect:** Confirmed that p | #torsion implies N_M ≥ 1?
6. **CM vs non-CM:** Different distributions?
7. **Anomalous prime count:** Statistics
8. **Cross-check:** Newform data matches?
9. **Surprises:** Anything unexpected in the data

---

## Phase 5: Implications for Paper 64

Based on the computational results, draft a one-page assessment:

1. **Is uniform p-adic decidability proved?** If N_M ≤ 2 for all (E, p) with conductor ≤ 1000, this strongly suggests N_M is uniformly bounded for all elliptic curves. State the bound.

2. **What's the Lean formalization scope?** If the bound is N_M ≤ 2 (with N_M = 2 only at p = 2), the Lean verification needs:
   - The Hasse bound |a_p| ≤ 2√p
   - Case analysis showing p² cannot divide (p + 1 - a_p) for p > 4 within the Hasse range
   - Exhaustive check for p = 2, 3 (small number of cases)
   - This is ~200 lines of Lean, mostly case-splitting with norm_num

3. **Does anything suggest a p-adic analogue of the rank obstruction?** If rank doesn't correlate with N_M, the answer is no — the p-adic side is uniformly tame, unlike the Archimedean side where rank creates genuine stratification. This asymmetry (p-adic uniform, Archimedean stratified) would be a clean result.

4. **Should we extend to higher-dimensional motives?** If elliptic curves are uniformly bounded, the next question is abelian surfaces, threefolds, etc. Does N_M grow with dimension? This would require a different data source (not Cremona) and is a separate project.

---

## Technical Notes

### Network access
- LMFDB API: https://www.lmfdb.org/api/
- May need pagination (limit/offset) for large queries
- Respect rate limits; add delays between requests if needed
- If LMFDB API is unavailable, fall back to direct web fetch of individual curve pages

### Dependencies
- Python 3 with requests, json, csv, math
- matplotlib for plots
- numpy/scipy for statistical tests (optional but helpful)
- No SageMath required — all computations are elementary integer arithmetic

### Verification
- Spot-check 10 curves by hand: compute a_p, point count, and N_M manually
- Cross-check against LMFDB's own "local data" pages for those curves
- Verify the Hasse bound |a_p| ≤ 2√p holds for all extracted data (data quality check)

---

## Key Insight to Watch For

The analysis in §3F suggests that **N_M ≤ 1 for all primes p ≥ 5**, with equality iff the prime is anomalous (a_p = 1). At p = 2, N_M can reach 2 (when #E(𝔽_2) = 4). At p = 3, N_M ≤ 1.

If this is confirmed empirically, it means: **p-adic decidability for elliptic curves requires at most 2 digits of precision at p = 2, and at most 1 digit everywhere else.** This is an extremely strong uniform bound — much stronger than what Paper 59 suggested. The p-adic side is essentially trivial.

This would make the paper's main theorem:

> **Theorem.** For any elliptic curve E/ℚ and any prime p of good reduction, the crystalline precision bound satisfies N_M ≤ 2, with N_M = 2 only possible at p = 2. For p ≥ 5, N_M ≤ 1 with equality iff E is anomalous at p.

The proof is a one-paragraph argument from the Hasse bound. The computation is the evidence that makes the theorem worth stating.

**This is the h = f methodology: force exact computation, find a clean pattern, then prove it.**
