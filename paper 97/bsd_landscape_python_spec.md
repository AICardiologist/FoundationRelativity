# BSD Landscape Survey: Systematic Computation Across Elliptic Curve Data
## Specification for Python Agent (No Sage Required)

---

## Purpose

We are looking for unexpected patterns in arithmetic data across families of elliptic curves. We don't know what we're looking for. The methodology is: collect everything computable, dump it into a table, and surface anomalies.

This is how our previous discovery (τ₊ = 0 in the Hodge campaign) was made — by computing an invariant across a family and noticing it was unexpectedly zero.

---

## Data Source: LMFDB API

The LMFDB (L-functions and Modular Forms Database) provides a free JSON API.

**Base URL:** `https://www.lmfdb.org/api/ec_curvedata/`

**Query format:**
```
https://www.lmfdb.org/api/ec_curvedata/?conductor=11&_fields=label,conductor,rank,ainvs,torsion_structure,torsion_order,tamagawa_product,sha_an,modular_degree,root_number,special_value,real_period,regulator,selmer_rank_2,cm_discriminant,isogeny_class_size,gens,heights
```

**Pagination:** Use `_offset=0&_limit=100` and increment offset.

**To get all curves with conductor ≤ 500:**
```
https://www.lmfdb.org/api/ec_curvedata/?conductor=1-500&_limit=100&_offset=0&_fields=...
```

Alternatively, download the full dataset:
```
https://www.lmfdb.org/api/ec_curvedata/?conductor=1-500&_limit=5000&_fields=label,lmfdb_label,conductor,rank,ainvs,torsion_structure,torsion_order,tamagawa_product,sha_an,root_number,special_value,real_period,regulator,cm_discriminant,isogeny_class_size,gens,heights,kodaira_symbol,modular_degree,class_size
```

**IMPORTANT:** The LMFDB API may rate-limit. Be polite: add 0.5s delay between requests. Batch with `_limit=100` or more.

**FALLBACK if LMFDB API is unavailable or rate-limited:**
Download Cremona's tables directly. They are available as plain text at:
```
https://github.com/JohnCremona/ecdata
```
The file `allcurves/allcurves.00000-09999` contains all curves with conductor ≤ 9999. Format is documented in the repo README. Parse it as a text file.

---

## Phase 1: Data Collection

### Step 1: Fetch data from LMFDB

```python
import requests
import json
import time
from fractions import Fraction

def fetch_lmfdb_curves(max_conductor=500, batch_size=100):
    """Fetch all elliptic curves with conductor ≤ max_conductor from LMFDB."""
    
    fields = [
        'label', 'lmfdb_label', 'conductor', 'rank', 'ainvs',
        'torsion_structure', 'torsion_order', 'tamagawa_product',
        'sha_an', 'root_number', 'special_value', 'real_period',
        'regulator', 'cm_discriminant', 'isogeny_class_size',
        'gens', 'heights', 'modular_degree', 'class_size',
        'num_bad_primes', 'bad_primes'
    ]
    
    all_curves = []
    offset = 0
    
    while True:
        url = (
            f"https://www.lmfdb.org/api/ec_curvedata/"
            f"?conductor=1-{max_conductor}"
            f"&_fields={','.join(fields)}"
            f"&_limit={batch_size}"
            f"&_offset={offset}"
        )
        
        response = requests.get(url)
        if response.status_code != 200:
            print(f"Error at offset {offset}: {response.status_code}")
            break
        
        data = response.json()
        records = data.get('data', [])
        
        if not records:
            break
        
        all_curves.extend(records)
        offset += batch_size
        print(f"Fetched {len(all_curves)} curves so far...")
        time.sleep(0.5)  # rate limiting
    
    return all_curves
```

### Step 2: Compute derived quantities

For each curve, compute:

```python
def process_curve(record):
    """Compute derived BSD quantities from LMFDB record."""
    
    result = dict(record)  # copy all LMFDB fields
    
    # Root number as integer
    result['w'] = int(record.get('root_number', 0))
    
    # Modular symbol ratio: L(E,1)/Omega^+ for rank 0
    # LMFDB gives 'special_value' = L(E,1) (floating point)
    # and 'real_period' = Omega^+ (floating point)
    # But we want the EXACT rational value.
    #
    # The exact rational value is:
    #   L(E,1)/Omega^+ = sha_an * tamagawa_product / torsion_order^2
    # by BSD. So for rank 0, we can COMPUTE the modular symbol
    # from the algebraic side if we trust BSD.
    #
    # BUT: we want to CHECK BSD, not assume it.
    # 
    # LMFDB stores 'special_value' as a float. For rank 0, this is L(E,1).
    # We can compute L(E,1)/Omega^+ as a float and compare to the
    # rational prediction.
    
    rank = record.get('rank', -1)
    tors = record.get('torsion_order', 1)
    tam = record.get('tamagawa_product', 1)
    sha = record.get('sha_an', 1)
    
    # BSD algebraic side (exact rational)
    if rank == 0:
        # bsd_rhs = |Sha| * prod(c_p) / |tors|^2
        result['bsd_rhs'] = Fraction(int(sha) * int(tam), int(tors)**2)
        
        # L(E,1)/Omega^+ from LMFDB special_value / real_period
        sv = record.get('special_value', None)
        rp = record.get('real_period', None)
        if sv is not None and rp is not None and rp != 0:
            result['lvalue_ratio_float'] = float(sv) / float(rp)
            # Try to recognize as rational
            result['lvalue_ratio_rational'] = rationalize(
                result['lvalue_ratio_float'], int(tors)**2 * 1000
            )
        else:
            result['lvalue_ratio_float'] = None
            result['lvalue_ratio_rational'] = None
        
        # BSD residual (float): should be ~0
        if result['lvalue_ratio_float'] is not None:
            result['bsd_residual_float'] = (
                result['lvalue_ratio_float'] - float(result['bsd_rhs'])
            )
        else:
            result['bsd_residual_float'] = None
    else:
        result['bsd_rhs'] = None
        result['lvalue_ratio_float'] = None
        result['lvalue_ratio_rational'] = None
        result['bsd_residual_float'] = None
    
    # Selmer excess: measures dim Sha[2]
    sel2 = record.get('selmer_rank_2', None)  # LMFDB field name may vary
    if sel2 is not None:
        # Need dim E(Q)[2] — compute from torsion structure
        tors_struct = record.get('torsion_structure', [])
        two_tors_rank = sum(1 for d in tors_struct if int(d) % 2 == 0)
        result['two_tors_rank'] = two_tors_rank
        result['selmer_excess'] = int(sel2) - int(rank) - two_tors_rank
    else:
        result['two_tors_rank'] = None
        result['selmer_excess'] = None
    
    # Generator height (rank 1)
    heights = record.get('heights', [])
    if rank == 1 and heights:
        result['gen_height'] = float(heights[0])
    else:
        result['gen_height'] = None
    
    # CM status
    result['has_cm'] = record.get('cm_discriminant', 0) != 0
    
    # BSD formula denominator (rank 0)
    if rank == 0 and result['bsd_rhs'] is not None:
        result['bsd_rhs_num'] = result['bsd_rhs'].numerator
        result['bsd_rhs_den'] = result['bsd_rhs'].denominator
    else:
        result['bsd_rhs_num'] = None
        result['bsd_rhs_den'] = None
    
    return result


def rationalize(x, max_denom=10000):
    """Try to recognize a float as a rational number."""
    f = Fraction(x).limit_denominator(max_denom)
    # Check if close enough
    if abs(float(f) - x) < 1e-8:
        return f
    return None
```

### Step 3: Heegner discriminant computation (pure Python)

```python
def kronecker_symbol(a, p):
    """Compute the Kronecker symbol (a/p) for odd prime p."""
    if p == 2:
        if a % 2 == 0:
            return 0
        a_mod_8 = a % 8
        if a_mod_8 in (1, 7):
            return 1
        else:
            return -1
    # Legendre symbol for odd prime
    a = a % p
    if a == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    if result == p - 1:
        return -1
    return result

def is_fundamental_discriminant(D):
    """Check if -D is a fundamental discriminant (D > 0)."""
    if D <= 0:
        return False
    if D % 4 == 3:
        # -D ≡ 1 mod 4, fundamental if D is squarefree
        return is_squarefree(D)
    if D % 4 == 0:
        d = D // 4
        if d % 4 in (1, 2):
            return is_squarefree(d)
    return False

def is_squarefree(n):
    """Check if n is squarefree."""
    if n <= 1:
        return n == 1
    for p in range(2, int(n**0.5) + 1):
        if n % (p * p) == 0:
            return False
    return True

def find_heegner_disc(N):
    """Find smallest D > 0 such that Q(sqrt(-D)) satisfies Heegner hypothesis for N.
    
    Heegner hypothesis: every prime p dividing N splits in Q(sqrt(-D)).
    A prime p splits in Q(sqrt(-D)) iff kronecker(-D, p) = 1.
    """
    if N <= 0:
        return None
    
    bad_primes = prime_factors(N)
    
    for D in range(3, 100000):
        if not is_fundamental_discriminant(D):
            continue
        
        all_split = True
        for p in bad_primes:
            if kronecker_symbol(-D, p) != 1:
                all_split = False
                break
        
        if all_split:
            return D
    
    return None

def prime_factors(n):
    """Return list of prime factors of n."""
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            if d not in factors:
                factors.append(d)
            n //= d
        d += 1
    if n > 1 and n not in factors:
        factors.append(n)
    return factors
```

### IMPORTANT: LMFDB Field Names

The LMFDB API field names may differ from what I've written above. Before running the main collection, do a test query:

```python
# Test: fetch one curve and print all available fields
test = requests.get(
    "https://www.lmfdb.org/api/ec_curvedata/?label=11.a1&_limit=1"
)
print(json.dumps(test.json()['data'][0], indent=2))
```

Use the actual field names from this output. Common gotchas:
- Label format might be `'11.a1'` (LMFDB style) not `'11a1'` (Cremona style)
- `selmer_rank_2` might be called `two_selmer_rank` or similar
- `sha_an` might be called `analytic_sha_order` or `sha`
- `special_value` might be the L-value at s=1 or might not exist
- `heights` might be called `heegner_height` or stored differently

**ADAPT THE CODE TO MATCH ACTUAL LMFDB FIELD NAMES.**

---

## Phase 2: Export

Save three files:

1. **bsd_landscape.csv** — One row per curve. All fields.
2. **bsd_landscape.json** — Full data with rational numbers as strings "p/q".
3. **bsd_summary.txt** — Summary statistics:
   - Total curves
   - Count by rank (0, 1, 2, 3+)
   - Count by root number (+1, -1)
   - Count CM vs non-CM
   - Distribution of torsion structures (table of torsion_structure → count)
   - Distribution of Tamagawa products (table of value → count)
   - Distribution of Sha analytic orders (table of value → count)
   - For rank 0: distribution of BSD rational value denominators
   - For rank 1: histogram of generator heights (buckets of 0.5)
   - Count of curves with selmer_excess = 0, 1, 2, etc.

---

## Phase 3: Analysis

Run these ten analyses. For each, produce a section in the anomaly report.

### Analysis 1: BSD Consistency Check
For every rank-0 curve, check: `|lvalue_ratio_float - float(bsd_rhs)| < 1e-6`.
Flag any failures. (There should be zero failures. If there are, it's a data or computation error.)

Report: count of checks passed, count of failures, list any failures with full data.

### Analysis 2: BSD Rational Value Structure (Rank 0)
For every rank-0 curve, the BSD formula gives `L(E,1)/Ω⁺ = |Sha| · ∏c_p / |tors|²`.

Tabulate: for each torsion structure, what BSD values appear?

```python
# Group by torsion structure, list all bsd_rhs values
from collections import defaultdict
tors_to_bsd = defaultdict(list)
for curve in rank0_curves:
    key = str(curve['torsion_structure'])
    tors_to_bsd[key].append(curve['bsd_rhs'])
```

Questions:
- For torsion Z/nZ, is the denominator always n²? Or can Tamagawa and Sha change it?
- Which torsion structures produce the most diverse BSD values?
- Are there BSD values that appear surprisingly often?

### Analysis 3: Selmer Excess Distribution
Compute `selmer_excess = selmer2_rank - rank - two_tors_rank` for all curves where data is available.

Tabulate:
- Fraction with selmer_excess = 0 (descent determines rank exactly)
- Fraction with selmer_excess = 1, 2, etc.
- Broken down by: rank, torsion structure, CM status, conductor range

Key question: **Is there a simple criterion predicting selmer_excess = 0?**
- Does CM ⟹ selmer_excess = 0?
- Does having rational 2-torsion affect selmer_excess?
- Does conductor being prime affect selmer_excess?

### Analysis 4: Heegner Discriminants (Rank 1)
For each rank-1 curve, compute the smallest Heegner discriminant D.

Tabulate:
- Distribution of D values
- D vs conductor (scatter plot data: N, D for each rank-1 curve)
- Curves with D ≤ 10 (list them — these are curves where the Heegner point is "cheap")
- Curves with very large D (list the top 10)

### Analysis 5: Generator Heights (Rank 1)
For each rank-1 curve with available generator height:

Tabulate:
- Histogram of heights (buckets of 0.1)
- The 10 curves with smallest generator height
- The 10 curves with largest generator height  
- Scatter plot data: conductor vs height
- Correlation: height vs log(conductor)

### Analysis 6: CM Curves
List all CM curves in the dataset.

For each, record: label, CM discriminant, rank, torsion, Tamagawa, Sha, BSD value (if rank 0), Selmer excess.

Questions:
- Do CM curves systematically differ from non-CM curves in Selmer excess?
- Do CM rank-0 curves have simpler BSD values (smaller denominators)?
- Are CM curves more likely to have selmer_excess = 0?

### Analysis 7: Extrema and Outliers
For each numerical column, find the top 5 and bottom 5 values.

Specifically:
- Largest BSD value (rank 0)
- Smallest nonzero BSD value (rank 0)
- Largest Sha analytic order (any rank)
- Largest Tamagawa product
- Largest selmer_excess
- Smallest generator height (rank 1, nonzero)
- Largest generator height (rank 1)

For each extremum, print the full curve data. Note anything unusual.

### Analysis 8: Congruence Patterns in BSD Values
For rank-0 curves, compute `bsd_rhs_num mod p` for p = 2, 3, 5, 7.

Tabulate the distribution. Is it equidistributed mod p, or biased?

Group by torsion order: for curves with |tors| = n, compute the numerator of n² · bsd_rhs (which is |Sha| · ∏c_p). Look at this integer mod small primes.

### Analysis 9: Isogeny Class Patterns
Group curves by isogeny class.

Within each class:
- How do torsion, Tamagawa, Sha, and BSD value change?
- Is there always a curve in the class with Sha = 1?
- Is there always a curve with torsion = 1?
- For rank-0 classes: is the BSD value constant across the class?

Specific question: within an isogeny class, the product |Sha| · ∏c_p / |tors|² should give the same L(E,1)/Ω⁺ for all curves (since L is invariant under isogeny and Ω⁺ transforms predictably). **Verify this.** If it fails, something is wrong with the data.

### Analysis 10: Root Number Distribution
Tabulate root number vs rank:
- Fraction of w=+1 curves with rank 0, 2, 4...
- Fraction of w=-1 curves with rank 1, 3...
- Any curves violating parity? (rank and root number inconsistent — these would be very interesting or data errors)

---

## Phase 4: Anomaly Report

Produce a single markdown file `bsd_anomalies.md` with:

For each analysis (1–10):
- **Summary:** 2–3 sentence description of findings
- **Data table:** Key numbers
- **Surprise score:** 0 = exactly as theory predicts, 1 = mildly interesting, 2 = unexpected pattern, 3 = potentially significant discovery
- **Notes:** Any caveats about data quality

Final section:
- **Top 5 Most Surprising Findings** — ranked by surprise score, with enough detail that a mathematician could investigate further.
- **Negative Results** — things we checked that showed no pattern. These are also valuable.

---

## Deliverables

1. `bsd_landscape.csv`
2. `bsd_landscape.json`  
3. `bsd_summary.txt`
4. `bsd_anomalies.md` (the main report)
5. A directory `plots/` with any visualizations (optional but encouraged)

---

## Technical Notes

- **Python only.** No Sage, no Magma, no external CAS. Use `requests`, `json`, `csv`, `fractions`, `collections`, `math` from stdlib. `matplotlib` for plots if available.
- **Exact arithmetic:** Use Python's `fractions.Fraction` for all rational number operations. Never lose precision by converting to float prematurely.
- **Rate limiting:** 0.5 second delay between LMFDB API calls. Batch aggressively.
- **Error handling:** Some curves may have missing fields. Skip gracefully, log the skip, continue. Report total skips at the end.
- **Reproducibility:** Record LMFDB query URLs, timestamps, and Python version in the summary file.
- **Priority:** If time is limited, do Phase 1 + Phase 2 + Analyses 1, 2, 3, 7 (the most likely to reveal surprises). Skip 4, 5, 6, 8, 9, 10 if needed.
