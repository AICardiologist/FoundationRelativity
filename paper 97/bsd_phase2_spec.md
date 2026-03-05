# BSD Landscape Survey: Phase 2 Follow-Up
## Conditional Congruence Tests + CM Deep Dive

---

## Context

The Phase 1 survey (2214 curves, conductor ≤ 500) found three potentially interesting patterns:

1. **Congruence bias in sha·tam mod small primes** — 75% even mod 2, quadratic residue bias mod 7
2. **Zero nontrivial Sha for CM curves** — 0/68 CM curves have |Sha| > 1
3. **Heegner discriminant clustering** — D = 23 is most common (95 curves)

We need to determine: which of these are genuine discoveries vs. structural artifacts explained by known theory?

---

## PART A: Conditional Congruence Tests

### Hypothesis to Test

The mod-p bias in sha·tam might be entirely explained by:
- Curves with p dividing the conductor (bad reduction at p constrains Tamagawa c_p)
- Curves with p dividing the torsion order (torsion constrains the BSD formula)

If we remove these curves and the bias vanishes, it's a structural artifact. If it persists, it's potentially interesting.

### Task A1: Conditional mod-2 test

Using the existing dataset (conductor ≤ 500):

```python
# Split rank-0 curves into groups
all_rank0 = [c for c in curves if c['rank'] == 0]

# Group 1: curves with 2 | conductor (bad reduction at 2)
group_2_bad = [c for c in all_rank0 if c['conductor'] % 2 == 0]

# Group 2: curves with 2 | torsion_order  
group_2_tors = [c for c in all_rank0 if c['torsion_order'] % 2 == 0]

# Group 3: curves with NEITHER (the "clean" population)
group_2_clean = [c for c in all_rank0 
                 if c['conductor'] % 2 != 0 and c['torsion_order'] % 2 != 0]

# For each group, compute sha*tam mod 2 distribution
for name, group in [("all", all_rank0), ("2|N", group_2_bad), 
                     ("2|tors", group_2_tors), ("clean", group_2_clean)]:
    values = [c['sha_an'] * c['tamagawa_product'] for c in group]
    even = sum(1 for v in values if v % 2 == 0)
    odd = len(values) - even
    print(f"{name}: n={len(group)}, even={even} ({100*even/len(group):.1f}%), "
          f"odd={odd} ({100*odd/len(group):.1f}%)")
```

**Report:** Does the 75% even bias persist in the clean group? If the clean group is close to 50/50, the bias is explained. If still biased, investigate further.

### Task A2: Conditional mod-7 test

Same structure for mod 7:

```python
# Quadratic residues mod 7: {1, 2, 4}
# Non-residues mod 7: {3, 5, 6}
QR_7 = {1, 2, 4}
NR_7 = {3, 5, 6}

# Group: curves where 7 ∤ conductor AND 7 ∤ torsion_order
group_7_clean = [c for c in all_rank0 
                 if c['conductor'] % 7 != 0 and c['torsion_order'] % 7 != 0]

# Compute sha*tam mod 7 distribution
for name, group in [("all", all_rank0), ("clean_7", group_7_clean)]:
    values = [c['sha_an'] * c['tamagawa_product'] for c in group]
    mod7 = [v % 7 for v in values]
    dist = {r: mod7.count(r) for r in range(7)}
    qr_count = sum(1 for v in mod7 if v in QR_7)
    nr_count = sum(1 for v in mod7 if v in NR_7)
    zero_count = mod7.count(0)
    print(f"{name}: n={len(group)}")
    print(f"  distribution: {dist}")
    print(f"  QR: {qr_count}, NR: {nr_count}, zero: {zero_count}")
```

**Report:** Does the quadratic residue bias persist in the clean group? 

### Task A3: Conditional tests for p = 3, 5

Same structure:

```python
for p in [3, 5]:
    clean = [c for c in all_rank0 
             if c['conductor'] % p != 0 and c['torsion_order'] % p != 0]
    values = [c['sha_an'] * c['tamagawa_product'] for c in clean]
    mod_p = [v % p for v in values]
    dist = {r: mod_p.count(r) for r in range(p)}
    
    # Quadratic residues mod p
    qr = {pow(a, 2, p) for a in range(1, p)}
    qr_count = sum(1 for v in mod_p if v % p in qr)
    
    print(f"p={p}, clean n={len(clean)}: dist={dist}, QR count={qr_count}")
```

### Task A4: Deeper conditioning — by Kodaira type

If the mod-2 bias persists after removing curves with 2 | N and 2 | tors, investigate whether specific Kodaira types at other primes explain it:

```python
# For the "clean" group (2 ∤ N, 2 ∤ tors), 
# is sha*tam even because of specific Kodaira types?
# Tamagawa c_p for various Kodaira types:
#   I_n: c_p = n (split), 1 or 2 (non-split), 1,2,3,4 (additive)
#   I_n even => c_p even => tam even

# Check: for clean curves where sha*tam is even, 
# do they all have at least one prime with even Tamagawa number?
for c in group_2_clean:
    st = c['sha_an'] * c['tamagawa_product']
    if st % 2 == 0:
        # Which factor is even: sha or tam?
        sha_even = c['sha_an'] % 2 == 0
        tam_even = c['tamagawa_product'] % 2 == 0
        print(f"{c['label']}: sha*tam={st}, sha={c['sha_an']} "
              f"({'even' if sha_even else 'odd'}), "
              f"tam={c['tamagawa_product']} ({'even' if tam_even else 'odd'})")
```

**Report:** For curves in the clean group with even sha·tam, is the evenness coming from sha (interesting — means Sha has even order) or from tam (less interesting — means some Kodaira fiber has even component count)?

### Task A5: Expand to conductor ≤ 2000

Fetch additional curves from LMFDB with conductor 501–2000. Apply the same conditional tests. Larger sample will distinguish weak biases from statistical noise.

```python
# Fetch curves with conductor 501-2000
# Same LMFDB API calls as Phase 1, with conductor=501-2000
# This may be ~8000-10000 additional curves
# Apply same analyses A1-A4
```

If the LMFDB rate-limits, fetch in batches of 500 conductors with delays between batches.

---

## PART B: CM Deep Dive

### Motivation

The math consultation (Direction 3) predicted that CM curves form a "BSD palindromic locus" where CLASS content drops. The Phase 1 data shows Sha = 1 for all 68 CM curves. We want to determine: is the *proof* that Sha = 1 for CM curves more constructive?

### Task B1: Complete CM curve inventory

List all CM curves in the dataset with full invariants:

```python
cm_curves = [c for c in curves if c.get('cm_discriminant', 0) != 0]

# For each, record:
# label, conductor, rank, cm_discriminant, torsion_structure, torsion_order,
# tamagawa_product, sha_an, selmer_excess, bsd_rhs (if rank 0),
# gen_height (if rank 1), heegner_disc (if rank 1)

print(f"Total CM curves: {len(cm_curves)}")
print(f"By CM discriminant:")
from collections import Counter
cm_disc_counts = Counter(c['cm_discriminant'] for c in cm_curves)
for disc, count in sorted(cm_disc_counts.items()):
    print(f"  D = {disc}: {count} curves")
```

Expected CM discriminants for rational j-invariants: -3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163.

### Task B2: CM Selmer excess

For all CM curves with available 2-Selmer data:

```python
cm_selmer = [(c['label'], c['rank'], c.get('selmer_excess', None)) 
             for c in cm_curves]

# Question: do ALL CM curves have selmer_excess = 0?
# If yes: 2-descent fully determines rank for CM curves (BISH)
zero_excess = sum(1 for _, _, se in cm_selmer if se == 0)
nonzero_excess = sum(1 for _, _, se in cm_selmer if se is not None and se > 0)
missing = sum(1 for _, _, se in cm_selmer if se is None)

print(f"CM curves selmer_excess = 0: {zero_excess}")
print(f"CM curves selmer_excess > 0: {nonzero_excess}")
print(f"CM curves selmer_excess missing: {missing}")

# If any have nonzero excess, list them
for label, rank, se in cm_selmer:
    if se is not None and se > 0:
        print(f"  NONZERO: {label}, rank={rank}, selmer_excess={se}")
```

**Key result:** If selmer_excess = 0 for all CM curves, then for CM curves:
- Rank bound: BISH (2-descent suffices)
- Sha[2] = 0: BISH (follows from descent)
- Combined with Sha = 1 (empirically): suggests full Sha triviality is provable by algebraic methods

### Task B3: CM vs non-CM comparison table

```python
# Compare CM and non-CM populations across all invariants
cm = [c for c in curves if c.get('cm_discriminant', 0) != 0]
non_cm = [c for c in curves if c.get('cm_discriminant', 0) == 0]

for label, population in [("CM", cm), ("non-CM", non_cm)]:
    ranks = Counter(c['rank'] for c in population)
    sha_vals = Counter(c['sha_an'] for c in population)
    tors_vals = Counter(str(c['torsion_structure']) for c in population)
    mean_tam = sum(c['tamagawa_product'] for c in population) / len(population)
    
    se_vals = [c.get('selmer_excess', 0) for c in population 
               if c.get('selmer_excess') is not None]
    mean_se = sum(se_vals) / len(se_vals) if se_vals else None
    
    print(f"\n{label} (n={len(population)}):")
    print(f"  Ranks: {dict(ranks)}")
    print(f"  Sha values: {dict(sha_vals)}")
    print(f"  Mean Tamagawa: {mean_tam:.2f}")
    print(f"  Mean selmer_excess: {mean_se}")
    print(f"  Torsion structures: {dict(tors_vals)}")
```

### Task B4: CRM component count for CM test case (27a1)

27a1 is y² + y = x³ (conductor 27, rank 0, CM by Z[ζ₃], torsion Z/3Z).

Compute all BSD invariants:

```python
# From LMFDB, fetch 27a1 data
# Expected:
#   conductor = 27
#   rank = 0
#   root_number = +1
#   torsion = Z/3Z, order 3
#   tamagawa = c_3 = 3 (Kodaira type IV* at p=3)
#   sha = 1
#   cm_discriminant = -3
#   L(E,1)/Omega^+ = 1/3
#   BSD check: 1/3 = 1 * 3 / 9 = 1/3 ✓

# Verify this data matches LMFDB
```

Then construct the CRM audit for 27a1:

```
CRM AUDIT: 27a1 (CM curve, rank 0)

BISH components:
  1. Hecke eigenvalue table [native_decide]
  2. Point count verification [native_decide]  
  3. Hecke recurrence [native_decide]
  4. Hecke multiplicativity [native_decide]
  5. Hasse bound [native_decide]
  6. Modular symbol = 1/3 [norm_num]
  7. Modular symbol ≠ 0 [norm_num]
  8. Torsion order = 3 [rfl]
  9. Tamagawa c_3 = 3 [rfl]
  10. BSD formula: 1/3 = 1·3/9 [norm_num]
  11. CM structure: End(E) = Z[ζ₃] [documentary, but algebraic]

CLASS components:
  12. Analytic continuation [CLASS]
  13. Kato/Rubin Euler system [CLASS — but see note]
  14. Sha finiteness [CLASS — but see note]

NOTE: For CM curves, components 13-14 use Rubin's Euler system
(elliptic units) rather than Kato's Euler system. Elliptic units
are EXPLICIT ALGEBRAIC NUMBERS — values of rational functions at
torsion points. The proof that they annihilate Sha is still CLASS
(uses Iwasawa main conjecture), but the OBJECTS are more algebraic
than in the non-CM case.

QUESTION FOR MATHEMATICIANS: Is the proof of Sha = 1 for 27a1 
obtainable by purely algebraic means (2-descent + explicit 
elliptic unit computation), or does it irreducibly require 
the Iwasawa main conjecture?

Score: 11 BISH + 3 CLASS = 14 components (79% BISH)
Compare: 11a1 (non-CM, rank 0): 10 BISH + 3 CLASS = 77%
```

### Task B5: All CM curves — BSD formula check

For every CM curve in the dataset, verify the BSD formula and list the result:

```python
for c in cm_curves:
    if c['rank'] == 0:
        bsd_rhs = Fraction(c['sha_an'] * c['tamagawa_product'], 
                          c['torsion_order']**2)
        print(f"{c['label']}: CM={c['cm_discriminant']}, "
              f"L/Ω = {bsd_rhs}, tors={c['torsion_structure']}, "
              f"tam={c['tamagawa_product']}, sha={c['sha_an']}")
```

---

## PART C: Heegner Discriminant Analysis

### Task C1: Why D = 23?

D = 23 is the most common smallest Heegner discriminant (95 curves). Investigate:

```python
# For which conductors N does D = 23 satisfy the Heegner hypothesis?
# Heegner hyp: every p | N splits in Q(sqrt(-23))
# p splits in Q(sqrt(-23)) iff kronecker(-23, p) = 1

# Compute: for each prime p ≤ 500, does p split in Q(sqrt(-23))?
split_primes_23 = [p for p in primes_up_to(500) 
                   if kronecker_symbol(-23, p) == 1]
print(f"Primes splitting in Q(sqrt(-23)): {split_primes_23[:30]}...")

# For D=7 (76 curves), same analysis
split_primes_7 = [p for p in primes_up_to(500) 
                  if kronecker_symbol(-7, p) == 1]
print(f"Primes splitting in Q(sqrt(-7)): {split_primes_7[:30]}...")

# The density of splitting primes is governed by the class number h(-D)
# and the structure of the class group of Q(sqrt(-D)).
# h(-23) = 3, h(-7) = 1

# For each D, count how many conductors N ≤ 500 have ALL prime factors
# in the splitting set for D
def count_eligible_conductors(D, max_N=500):
    split = set(p for p in primes_up_to(max_N) 
                if kronecker_symbol(-D, p) == 1)
    count = 0
    for N in range(1, max_N + 1):
        pf = prime_factors(N)
        if all(p in split for p in pf):
            count += 1
    return count

# Compare: which D values serve the most conductors?
for D in [3, 4, 7, 8, 11, 15, 19, 20, 23, 24, 31, 35, 39, 40, 43]:
    if is_fundamental_discriminant(D):
        eligible = count_eligible_conductors(D)
        print(f"D={D}: {eligible} eligible conductors")
```

**Report:** Is D = 23's prevalence simply because Q(sqrt(-23)) has many splitting primes? Or is there something deeper?

### Task C2: Heegner discriminant vs generator height

```python
# For rank-1 curves with both heegner_disc and gen_height:
rank1_with_data = [(c['conductor'], c['heegner_disc'], c['gen_height'])
                   for c in curves 
                   if c['rank'] == 1 
                   and c.get('heegner_disc') is not None
                   and c.get('gen_height') is not None]

# Scatter plot data: D vs height
# Also: D vs 1/sqrt(D) * height (the Gross-Zagier constant scales as 1/sqrt(D))
print("conductor, heegner_D, gen_height, height*sqrt(D)")
for N, D, h in rank1_with_data:
    print(f"{N}, {D}, {h:.6f}, {h * D**0.5:.6f}")

# Correlation between D and height
import math
D_vals = [D for _, D, _ in rank1_with_data]
h_vals = [h for _, _, h in rank1_with_data]
# Pearson correlation (manual computation)
n = len(D_vals)
mean_D = sum(D_vals) / n
mean_h = sum(h_vals) / n
cov = sum((D_vals[i] - mean_D) * (h_vals[i] - mean_h) for i in range(n)) / n
std_D = (sum((d - mean_D)**2 for d in D_vals) / n) ** 0.5
std_h = (sum((h - mean_h)**2 for h in h_vals) / n) ** 0.5
corr = cov / (std_D * std_h) if std_D > 0 and std_h > 0 else 0
print(f"\nCorrelation(D, height) = {corr:.4f}")

# Also: does height * sqrt(D) stabilize?
# The GZ formula says L'(E,1) = c_GZ * h(y_K) where c_GZ ~ 1/sqrt(D)
# So if L'(E,1) doesn't depend on the choice of D, then h(y_K) ~ sqrt(D)
# Check: is height * sqrt(D) roughly constant for a fixed curve with
# different possible D values?
```

**Report:** Is there a correlation between Heegner discriminant and generator height? Does h·√D stabilize, as the Gross-Zagier formula would predict?

---

## Deliverables

1. **congruence_conditional.md** — Results of Tasks A1–A5. For each prime p: the full distribution table for the "all" population and the "clean" population (p ∤ N, p ∤ tors). Clear statement of whether the bias persists or vanishes after conditioning. If it persists, flag as surprise score 2+.

2. **cm_deep_dive.md** — Results of Tasks B1–B5. Complete CM curve inventory with all invariants. Selmer excess analysis. CM vs non-CM comparison. CRM audit for 27a1. Clear statement of whether CM curves have systematically lower CLASS content.

3. **heegner_analysis.md** — Results of Tasks C1–C2. Explanation of D=23 prevalence. Correlation analysis between D and generator height.

4. Updated **bsd_landscape.csv** if expanded to conductor ≤ 2000 (Task A5).

5. **phase2_summary.md** — Overall summary with updated surprise scores:
   - Congruence bias: EXPLAINED (score 0) or PERSISTS (score 2-3)
   - CM/Sha: score and implications for CRM
   - Heegner clustering: EXPLAINED (score 0) or UNEXPLAINED (score 1-2)
   - Top findings ranked by significance

---

## Priority

If time is limited:

**MUST DO:** Tasks A1, A2, B1, B2, B3
**SHOULD DO:** Tasks A3, A4, B4, B5, C1
**NICE TO HAVE:** Tasks A5, C2
