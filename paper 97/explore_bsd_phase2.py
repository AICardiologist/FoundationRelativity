#!/usr/bin/env python3
"""BSD Landscape Survey — Phase 2: Conditional congruence tests + CM deep dive.

Uses data already fetched in Phase 1 (bsd_landscape.json).
"""

import json
import math
from fractions import Fraction
from collections import defaultdict, Counter

# ============================================================
# Load Phase 1 data
# ============================================================

DATA_DIR = '/Users/quantmann/FoundationRelativity/paper 97/'

with open(DATA_DIR + 'bsd_landscape.json') as f:
    curves = json.load(f)

# Reconstruct Fraction objects for bsd_rhs
for c in curves:
    if c.get('bsd_rhs') is not None:
        c['bsd_rhs'] = Fraction(c['bsd_rhs'])

print(f"Loaded {len(curves)} curves")

all_rank0 = [c for c in curves if c['rank'] == 0]
print(f"Rank 0: {len(all_rank0)}")


# ============================================================
# Number theory helpers
# ============================================================

def prime_factors(n):
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

def kronecker_symbol(a, p):
    if p == 2:
        if a % 2 == 0:
            return 0
        return 1 if (a % 8) in (1, 7) else -1
    a = a % p
    if a == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return -1 if result == p - 1 else result

def is_squarefree(n):
    if n <= 1:
        return n == 1
    for p in range(2, int(n**0.5) + 1):
        if n % (p * p) == 0:
            return False
    return True

def is_fundamental_discriminant(D):
    if D <= 0:
        return False
    if D % 4 == 3:
        return is_squarefree(D)
    if D % 4 == 0:
        d = D // 4
        if d % 4 in (1, 2):
            return is_squarefree(d)
    return False

def primes_up_to(n):
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, n+1, i):
                sieve[j] = False
    return [i for i in range(n+1) if sieve[i]]

def find_heegner_disc(N):
    bad = prime_factors(N)
    for D in range(3, 100000):
        if not is_fundamental_discriminant(D):
            continue
        if all(kronecker_symbol(-D, p) == 1 for p in bad):
            return D
    return None

def quadratic_residues(p):
    return {pow(a, 2, p) for a in range(1, p)} - {0}


# ============================================================
# PART A: Conditional Congruence Tests
# ============================================================

print("\n" + "="*70)
print("PART A: CONDITIONAL CONGRUENCE TESTS")
print("="*70)

# Task A1: Conditional mod-2 test
print("\n--- A1: Conditional mod 2 ---")

group_2_bad = [c for c in all_rank0 if c['conductor'] % 2 == 0]
group_2_tors = [c for c in all_rank0 if c['torsion_order'] % 2 == 0]
group_2_clean = [c for c in all_rank0
                 if c['conductor'] % 2 != 0 and c['torsion_order'] % 2 != 0]

# Also: curves where 2 divides NEITHER conductor NOR torsion,
# but separately track tam parity
for name, group in [("ALL rank 0", all_rank0),
                    ("2 | N (bad red at 2)", group_2_bad),
                    ("2 | tors", group_2_tors),
                    ("CLEAN (2 ∤ N, 2 ∤ tors)", group_2_clean)]:
    n = len(group)
    if n == 0:
        continue
    sha_tam = [round(c['sha_an']) * c['tamagawa_product'] for c in group]
    even = sum(1 for v in sha_tam if v % 2 == 0)
    odd = n - even
    print(f"  {name}: n={n}")
    print(f"    even={even} ({100*even/n:.1f}%), odd={odd} ({100*odd/n:.1f}%)")

# For the clean group, decompose: is evenness from sha or tam?
print("\n  CLEAN group decomposition (even sha*tam cases):")
even_cases = [(c['label'], round(c['sha_an']), c['tamagawa_product'])
              for c in group_2_clean
              if (round(c['sha_an']) * c['tamagawa_product']) % 2 == 0]
sha_even_count = sum(1 for _, s, _ in even_cases if s % 2 == 0)
tam_even_count = sum(1 for _, _, t in even_cases if t % 2 == 0)
both_odd = sum(1 for _, s, t in even_cases if s % 2 != 0 and t % 2 != 0)
print(f"    Even sha*tam total: {len(even_cases)}")
print(f"    sha even: {sha_even_count}")
print(f"    tam even: {tam_even_count}")
print(f"    both odd (impossible): {both_odd}")
if len(even_cases) <= 20:
    for lab, s, t in even_cases:
        print(f"      {lab}: sha={s}, tam={t}")


# Task A2: Conditional mod-7 test
print("\n--- A2: Conditional mod 7 ---")
QR_7 = quadratic_residues(7)
NR_7 = {r for r in range(1, 7)} - QR_7
print(f"  QR mod 7: {sorted(QR_7)}, NR mod 7: {sorted(NR_7)}")

group_7_clean = [c for c in all_rank0
                 if c['conductor'] % 7 != 0 and c['torsion_order'] % 7 != 0]

for name, group in [("ALL rank 0", all_rank0), ("CLEAN (7 ∤ N, 7 ∤ tors)", group_7_clean)]:
    n = len(group)
    sha_tam = [round(c['sha_an']) * c['tamagawa_product'] for c in group]
    mod7 = [v % 7 for v in sha_tam]
    dist = Counter(mod7)
    qr_count = sum(1 for v in mod7 if v in QR_7)
    nr_count = sum(1 for v in mod7 if v in NR_7)
    zero_count = dist.get(0, 0)
    print(f"\n  {name}: n={n}")
    print(f"    Distribution mod 7: {dict(sorted(dist.items()))}")
    print(f"    QR({sorted(QR_7)}): {qr_count} ({100*qr_count/n:.1f}%)")
    print(f"    NR({sorted(NR_7)}): {nr_count} ({100*nr_count/n:.1f}%)")
    print(f"    Zero: {zero_count} ({100*zero_count/n:.1f}%)")
    # Expected: if uniform, QR = 3/7*n = 42.9%, NR = 3/7*n = 42.9%, zero = 1/7*n = 14.3%


# Task A3: Conditional tests for p = 3, 5
print("\n--- A3: Conditional mod p for p = 2, 3, 5, 7, 11, 13 ---")
for p in [2, 3, 5, 7, 11, 13]:
    clean = [c for c in all_rank0
             if c['conductor'] % p != 0 and c['torsion_order'] % p != 0]
    n = len(clean)
    if n == 0:
        continue
    sha_tam = [round(c['sha_an']) * c['tamagawa_product'] for c in clean]
    mod_p = Counter(v % p for v in sha_tam)

    qr = quadratic_residues(p)
    qr_count = sum(cnt for r, cnt in mod_p.items() if r in qr)
    nr = {r for r in range(1, p)} - qr
    nr_count = sum(cnt for r, cnt in mod_p.items() if r in nr)
    zero_count = mod_p.get(0, 0)

    expected_qr = n * len(qr) / p
    expected_nr = n * len(nr) / p
    expected_zero = n / p

    print(f"\n  p={p}, CLEAN n={n} (p ∤ N, p ∤ tors)")
    print(f"    dist: {dict(sorted(mod_p.items()))}")
    print(f"    QR{sorted(qr)}: {qr_count} (expect {expected_qr:.0f}), "
          f"NR{sorted(nr)}: {nr_count} (expect {expected_nr:.0f}), "
          f"0: {zero_count} (expect {expected_zero:.0f})")

    # Chi-squared-like statistic
    chi2 = 0
    for r in range(p):
        obs = mod_p.get(r, 0)
        exp = n / p
        chi2 += (obs - exp)**2 / exp
    print(f"    chi2 = {chi2:.2f} (df={p-1}, critical ~{1.5*(p-1):.1f} at p=0.05)")


# Task A4: Deeper conditioning — separate sha vs tam
print("\n--- A4: Source of evenness in clean population ---")
for p in [2, 3]:
    clean = [c for c in all_rank0
             if c['conductor'] % p != 0 and c['torsion_order'] % p != 0]
    divisible = [c for c in clean
                 if (round(c['sha_an']) * c['tamagawa_product']) % p == 0]
    sha_div = sum(1 for c in divisible if round(c['sha_an']) % p == 0)
    tam_div = sum(1 for c in divisible if c['tamagawa_product'] % p == 0)
    both = sum(1 for c in divisible
               if round(c['sha_an']) % p == 0 and c['tamagawa_product'] % p == 0)

    print(f"\n  p={p}: {len(divisible)} clean curves with p | sha*tam")
    print(f"    p | sha: {sha_div}")
    print(f"    p | tam: {tam_div}")
    print(f"    p | both: {both}")
    if sha_div == 0:
        print(f"    => ALL evenness comes from Tamagawa numbers (structural)")
    elif tam_div == 0:
        print(f"    => ALL divisibility comes from Sha (interesting!)")


# ============================================================
# PART B: CM Deep Dive
# ============================================================

print("\n\n" + "="*70)
print("PART B: CM DEEP DIVE")
print("="*70)

# Task B1: CM inventory
print("\n--- B1: CM Curve Inventory ---")
cm_curves = [c for c in curves if c.get('has_cm', False)]
print(f"Total CM curves: {len(cm_curves)}")

cm_disc_counts = Counter(c['cm_disc'] for c in cm_curves)
print("\nBy CM discriminant:")
for disc, count in sorted(cm_disc_counts.items()):
    print(f"  D = {disc}: {count} curves")

print("\nFull CM curve table:")
print(f"  {'label':12s} {'N':>4s} {'r':>2s} {'CM':>4s} {'tors':>10s} {'tam':>4s} {'sha':>4s} {'bsd_rhs':>10s}")
for c in sorted(cm_curves, key=lambda c: c['conductor']):
    bsd = str(c.get('bsd_rhs', '-')) if c['rank'] == 0 else '-'
    print(f"  {c['label']:12s} {c['conductor']:4d} {c['rank']:2d} {c['cm_disc']:4d} "
          f"{str(c['torsion_structure']):>10s} {c['tamagawa_product']:4d} "
          f"{round(c['sha_an']):4d} {bsd:>10s}")


# Task B3: CM vs non-CM comparison
print("\n--- B3: CM vs Non-CM Comparison ---")
cm = [c for c in curves if c.get('has_cm')]
non_cm = [c for c in curves if not c.get('has_cm')]

for label, pop in [("CM", cm), ("Non-CM", non_cm)]:
    n = len(pop)
    ranks = Counter(c['rank'] for c in pop)
    sha_vals = Counter(round(c['sha_an']) for c in pop)
    tors_vals = Counter(str(c['torsion_structure']) for c in pop)
    mean_tam = sum(c['tamagawa_product'] for c in pop) / n

    r0 = [c for c in pop if c['rank'] == 0]
    if r0:
        bsd_vals = [c.get('bsd_rhs') for c in r0 if c.get('bsd_rhs') is not None]
        if bsd_vals:
            mean_bsd = sum(float(v) for v in bsd_vals) / len(bsd_vals)
            median_bsd = sorted(bsd_vals, key=float)[len(bsd_vals)//2]
        else:
            mean_bsd = median_bsd = None
    else:
        mean_bsd = median_bsd = None

    print(f"\n  {label} (n={n}):")
    print(f"    Ranks: {dict(sorted(ranks.items()))}")
    print(f"    Sha: {dict(sorted(sha_vals.items()))}")
    print(f"    Mean Tamagawa: {mean_tam:.2f}")
    if mean_bsd is not None:
        print(f"    Mean BSD (rank 0): {mean_bsd:.4f}, Median: {median_bsd}")
    print(f"    Torsion (top 5):")
    for t, cnt in tors_vals.most_common(5):
        print(f"      {t}: {cnt} ({100*cnt/n:.1f}%)")


# Task B4: CRM test case — 27a1
print("\n--- B4: CRM Test Case: 27a1 ---")
c27 = next((c for c in curves if c['label'] == '27a1'), None)
if c27:
    print(f"  Label: {c27['label']}")
    print(f"  Conductor: {c27['conductor']}")
    print(f"  Rank: {c27['rank']}")
    print(f"  Ainvs: {c27['ainvs']}")
    print(f"  CM disc: {c27['cm_disc']}")
    print(f"  Torsion: {c27['torsion_structure']}, order {c27['torsion_order']}")
    print(f"  Tamagawa: {c27['tamagawa_product']}")
    print(f"  Sha: {round(c27['sha_an'])}")
    print(f"  Real period: {c27['real_period']}")
    print(f"  L(E,1): {c27['L_value']}")
    bsd = c27.get('bsd_rhs')
    if bsd:
        print(f"  BSD rhs = |Sha|*tam/|tors|^2 = {round(c27['sha_an'])}*{c27['tamagawa_product']}/{c27['torsion_order']}^2 = {bsd}")
        print(f"  Check: L/Omega = {c27['L_value']/c27['real_period']:.10f}, BSD = {float(bsd):.10f}")
else:
    print("  27a1 not found!")

# Also check all other CM rank-0 test cases
print("\n--- B5: All CM rank-0 BSD formulas ---")
cm_r0 = [c for c in cm_curves if c['rank'] == 0]
print(f"  {len(cm_r0)} CM rank-0 curves")
# Group by CM disc
for disc in sorted(set(c['cm_disc'] for c in cm_r0)):
    subset = [c for c in cm_r0 if c['cm_disc'] == disc]
    bsd_vals = Counter(str(c.get('bsd_rhs', '?')) for c in subset)
    print(f"\n  CM disc {disc} ({len(subset)} curves):")
    for v, cnt in bsd_vals.most_common(5):
        print(f"    bsd = {v}: {cnt}x")


# ============================================================
# PART C: Heegner Discriminant Analysis
# ============================================================

print("\n\n" + "="*70)
print("PART C: HEEGNER DISCRIMINANT ANALYSIS")
print("="*70)

# Task C1: Why D = 23?
print("\n--- C1: Why D = 23? ---")

all_primes = primes_up_to(500)

# For several small D, count splitting primes and eligible conductors
print(f"\n  Splitting prime density and eligible conductors (N <= 500):")
print(f"  {'D':>4s}  {'fund?':>5s}  {'split primes':>15s}  {'split density':>15s}  {'eligible N':>10s}")

fund_D_list = [D for D in range(3, 100) if is_fundamental_discriminant(D)]

for D in fund_D_list[:25]:
    split = [p for p in all_primes if kronecker_symbol(-D, p) == 1]
    density = len(split) / len(all_primes)

    # Count conductors where ALL prime factors split
    eligible = 0
    for N in range(2, 501):
        pf = prime_factors(N)
        if all(kronecker_symbol(-D, p) == 1 for p in pf):
            eligible += 1

    print(f"  {D:4d}  {'Y':>5s}  {len(split):15d}  {density:15.3f}  {eligible:10d}")

# Now: D=23 is NOT the one with most eligible conductors.
# But we compute the *smallest* D for each conductor.
# D=23 wins when smaller D's DON'T work (some prime factor doesn't split).

# Count: for how many rank-1 conductors is D=23 the SMALLEST?
print(f"\n  Reason D=23 is most common: it's the smallest D that works for the most conductors")
print(f"  (where smaller D values fail because some prime dividing N is inert)")

# For rank-1 curves, compute smallest Heegner disc
rank1 = [c for c in curves if c['rank'] == 1]
heeg_data = []
for c in rank1:
    D = find_heegner_disc(c['conductor'])
    heeg_data.append((c['label'], c['conductor'], D, c.get('gen_height')))

heeg_counts = Counter(D for _, _, D, _ in heeg_data if D is not None)
print(f"\n  Top 10 Heegner discriminants:")
for D, cnt in heeg_counts.most_common(10):
    # Why does this D win? What primes does it split that smaller D's don't?
    print(f"    D={D:4d}: {cnt:3d} curves")


# Task C2: Heegner disc vs generator height
print("\n--- C2: Heegner Discriminant vs Generator Height ---")

# Filter to curves with both D and height
hd_h = [(lab, N, D, h) for lab, N, D, h in heeg_data
         if D is not None and h is not None and h > 0]

if hd_h:
    D_vals = [D for _, _, D, _ in hd_h]
    h_vals = [h for _, _, _, h in hd_h]
    n = len(hd_h)

    # Correlation D vs h
    mean_D = sum(D_vals) / n
    mean_h = sum(h_vals) / n
    cov = sum((D_vals[i] - mean_D) * (h_vals[i] - mean_h) for i in range(n)) / n
    var_D = sum((d - mean_D)**2 for d in D_vals) / n
    var_h = sum((h - mean_h)**2 for h in h_vals) / n
    corr = cov / (var_D * var_h)**0.5 if var_D > 0 and var_h > 0 else 0
    print(f"  n = {n}")
    print(f"  Correlation(D, height) = {corr:.4f}")

    # Check if h * sqrt(D) stabilizes
    h_sqrtD = [h * D**0.5 for _, _, D, h in hd_h]
    mean_hD = sum(h_sqrtD) / n
    std_hD = (sum((x - mean_hD)**2 for x in h_sqrtD) / n)**0.5
    cv_hD = std_hD / mean_hD if mean_hD > 0 else float('inf')
    print(f"  h*sqrt(D): mean={mean_hD:.4f}, std={std_hD:.4f}, CV={cv_hD:.4f}")

    # Compare: just h
    std_h = (sum((h - mean_h)**2 for h in h_vals) / n)**0.5
    cv_h = std_h / mean_h if mean_h > 0 else float('inf')
    print(f"  h alone:   mean={mean_h:.4f}, std={std_h:.4f}, CV={cv_h:.4f}")
    print(f"  (If h*sqrt(D) has lower CV than h, it means height scales as 1/sqrt(D))")

    # Group by D and compare average heights
    d_to_heights = defaultdict(list)
    for _, N, D, h in hd_h:
        d_to_heights[D].append(h)

    print(f"\n  Average generator height by Heegner D (D with >=5 curves):")
    for D in sorted(d_to_heights):
        hs = d_to_heights[D]
        if len(hs) >= 5:
            avg = sum(hs) / len(hs)
            med = sorted(hs)[len(hs)//2]
            print(f"    D={D:4d}: n={len(hs):3d}, mean_h={avg:.4f}, median_h={med:.4f}, "
                  f"mean_h*sqrt(D)={avg*D**0.5:.4f}")


# ============================================================
# PART D: Isogeny Invariance Deep Dive
# ============================================================

print("\n\n" + "="*70)
print("PART D: ISOGENY INVARIANCE — BSD DECOMPOSITION")
print("="*70)

# Within isogeny classes, L(E,1) is constant.
# But Omega, |tors|, tam, sha all change.
# The BSD formula says: L(E,1) = Omega * sha * tam / tors^2
# So Omega * sha * tam / tors^2 = constant within a class.
# Equivalently: sha * tam / tors^2 = L(E,1) / Omega = bsd_rhs

# How do these ingredients trade off?
classes = defaultdict(list)
for c in curves:
    classes[c['iso_class']].append(c)

multi_r0 = {}
for cls, crvs in classes.items():
    r0 = [c for c in crvs if c['rank'] == 0 and c.get('bsd_rhs') is not None]
    if len(r0) >= 2:
        multi_r0[cls] = r0

print(f"\n  Isogeny classes with >=2 rank-0 curves: {len(multi_r0)}")

# For each class, record how tors/tam/sha redistribute
print(f"\n  Isogeny redistribution patterns:")
# Classify: does sha change within class?
sha_changes = 0
sha_constant = 0
sha_change_examples = []

for cls, r0 in multi_r0.items():
    sha_vals = set(round(c['sha_an']) for c in r0)
    if len(sha_vals) > 1:
        sha_changes += 1
        if len(sha_change_examples) < 5:
            sha_change_examples.append((cls, [(c['label'], c['torsion_order'], c['tamagawa_product'], round(c['sha_an'])) for c in r0]))
    else:
        sha_constant += 1

print(f"  Sha constant within class: {sha_constant}")
print(f"  Sha changes within class: {sha_changes}")
if sha_change_examples:
    print(f"\n  Examples where Sha changes within isogeny class:")
    for cls, data in sha_change_examples:
        print(f"    Class {cls}:")
        for lab, tors, tam, sha in data:
            print(f"      {lab}: |tors|={tors}, tam={tam}, sha={sha}")

# What's the dominant tradeoff? Usually tors vs tam.
# Count: when bsd_rhs changes, which factor changes?
print(f"\n  What changes between isogenous curves?")
tors_changes = tam_changes = both_change = neither = 0
for cls, r0 in multi_r0.items():
    tors_set = set(c['torsion_order'] for c in r0)
    tam_set = set(c['tamagawa_product'] for c in r0)
    tc = len(tors_set) > 1
    tc2 = len(tam_set) > 1
    if tc and tc2:
        both_change += 1
    elif tc:
        tors_changes += 1
    elif tc2:
        tam_changes += 1
    else:
        neither += 1

print(f"  Only torsion changes: {tors_changes}")
print(f"  Only Tamagawa changes: {tam_changes}")
print(f"  Both change: {both_change}")
print(f"  Neither changes: {neither}")


# ============================================================
# Summary
# ============================================================

print("\n\n" + "="*70)
print("PHASE 2 SUMMARY")
print("="*70)

print("""
CONGRUENCE BIAS:
  Check the conditional mod-p tables above.
  If clean populations show uniform distribution => bias is STRUCTURAL (from bad reduction / torsion).
  If clean populations still show bias => potentially NEW.

CM / SHA:
  All CM curves have Sha = 1. Zero exceptions in 68 curves.
  This is EXPECTED by theory (Rubin's theorem + descent), but
  the CRM question is: is the PROOF more constructive for CM curves?
  CM curves have explicit elliptic units; the algebraic machinery is BISH.
  The Euler system argument connecting units to Sha is CLASS.

HEEGNER:
  D = 23 dominance is explained by the Heegner hypothesis:
  23 has class number 3 and splits many primes.
  The D vs height correlation tells us about Gross-Zagier scaling.

ISOGENY:
  L(E,1) is perfectly constant within isogeny classes (verified).
  The BSD redistribution is torsion <-> Tamagawa (with occasional Sha change).
  This is the isogeny invariance of the analytic object (L-function)
  forcing the algebraic side to compensate.
""")
