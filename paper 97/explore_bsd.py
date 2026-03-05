#!/usr/bin/env python3
"""BSD Landscape Survey — Cremona ecdata exploration.

Data from https://github.com/JohnCremona/ecdata
Format: allbsd has  ID AI R T CP OM L1 REG SHA
        allgens has ID AI R TOR TGENS GENS
"""

import requests
import json
import time
import math
from fractions import Fraction
from collections import defaultdict, Counter

BASE = "https://raw.githubusercontent.com/JohnCremona/ecdata/master"

# ============================================================
# Data fetching
# ============================================================

def fetch_file(path):
    url = f"{BASE}/{path}"
    print(f"  Fetching {url} ...")
    r = requests.get(url, timeout=120)
    r.raise_for_status()
    return r.text

def parse_ainvs(s):
    """Parse [a1,a2,a3,a4,a6] from string."""
    s = s.strip('[]')
    return [int(x) for x in s.split(',')]

def parse_bsd_line(line):
    """Parse one line of allbsd: ID AI R T CP OM L1 REG SHA"""
    parts = line.split()
    if len(parts) < 11:
        return None
    N = int(parts[0])
    cls = parts[1]
    num = int(parts[2])
    ainvs = parse_ainvs(parts[3])
    rank = int(parts[4])
    tors_order = int(parts[5])
    tam_prod = int(parts[6])
    real_period = float(parts[7])
    L_value = float(parts[8])  # L^(r)(E,1)/r!
    regulator = float(parts[9])
    sha_an = float(parts[10])  # might be non-integer if approximate

    label = f"{N}{cls}{num}"
    iso_class = f"{N}{cls}"

    return {
        'label': label,
        'iso_class': iso_class,
        'conductor': N,
        'class_code': cls,
        'curve_num': num,
        'ainvs': ainvs,
        'rank': rank,
        'torsion_order': tors_order,
        'tamagawa_product': tam_prod,
        'real_period': real_period,
        'L_value': L_value,  # L^(r)(E,1)/r!
        'regulator': regulator,
        'sha_an': sha_an,
    }

def parse_gens_line(line):
    """Parse one line of allgens: ID AI R TOR TGENS GENS
    Returns (label, torsion_structure, torsion_gens, gens)"""
    parts = line.split()
    if len(parts) < 6:
        return None
    N = int(parts[0])
    cls = parts[1]
    num = int(parts[2])
    # parts[3] = ainvs
    rank = int(parts[4])
    # parts[5] = torsion structure like [] or [5] or [2,4]
    tors_struct_str = parts[5]
    tors_struct = tors_struct_str.strip('[]')
    if tors_struct:
        tors_struct = [int(x) for x in tors_struct.split(',')]
    else:
        tors_struct = []

    label = f"{N}{cls}{num}"

    # Remaining parts are torsion generators then rank generators
    # Torsion generators: len(tors_struct) points in [x:y:z] format
    # Rank generators: rank points in [x:y:z] format
    rest = parts[6:]  # everything after torsion_structure
    points = [p for p in rest if p.startswith('[') and ':' in p]

    n_tors_gens = len(tors_struct)
    tors_gens = points[:n_tors_gens]
    rank_gens = points[n_tors_gens:]

    return {
        'label': label,
        'torsion_structure': tors_struct,
        'torsion_gens': tors_gens,
        'rank_gens': rank_gens,
    }


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

def find_heegner_disc(N):
    bad = prime_factors(N)
    for D in range(3, 100000):
        if not is_fundamental_discriminant(D):
            continue
        if all(kronecker_symbol(-D, p) == 1 for p in bad):
            return D
    return None

def rationalize(x, max_denom=100000):
    f = Fraction(x).limit_denominator(max_denom)
    if abs(float(f) - x) < 1e-10:
        return f
    return None

def disc_from_ainvs(a):
    """Compute discriminant of E: y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a6"""
    a1, a2, a3, a4, a6 = a
    b2 = a1**2 + 4*a2
    b4 = 2*a4 + a1*a3
    b6 = a3**2 + 4*a6
    b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2
    return -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6

def j_invariant(a):
    a1, a2, a3, a4, a6 = a
    b2 = a1**2 + 4*a2
    b4 = 2*a4 + a1*a3
    c4 = b2**2 - 24*b4
    D = disc_from_ainvs(a)
    if D == 0:
        return None
    return Fraction(c4**3, D)

def has_cm(ainvs):
    """Quick CM check via j-invariant. CM j-invariants for Q: 0, 1728, -3375, 8000, ..."""
    j = j_invariant(ainvs)
    if j is None:
        return 0
    CM_J = {0: -3, 1728: -4, -3375: -7, 8000: -8, -32768: -11,
            54000: -12, 287496: -16, -884736: -19, -12288000: -27,
            16581375: -28, -884736000: -43, -147197952000: -67,
            -262537412640768000: -163}
    j_int = int(j) if j.denominator == 1 else None
    if j_int in CM_J:
        return CM_J[j_int]
    return 0


# ============================================================
# Process & derive
# ============================================================

def process_curves(bsd_curves, gens_dict):
    """Merge bsd + gens data and compute derived quantities."""
    processed = []
    for c in bsd_curves:
        label = c['label']

        # Merge gens data
        g = gens_dict.get(label, {})
        c['torsion_structure'] = g.get('torsion_structure', [])
        c['rank_gens'] = g.get('rank_gens', [])

        # Root number: (-1)^rank for analytic rank = algebraic rank
        c['root_number'] = (-1)**c['rank']

        # CM
        c['cm_disc'] = has_cm(c['ainvs'])
        c['has_cm'] = c['cm_disc'] != 0

        # BSD formula for rank 0:
        # L(E,1)/Omega^+ = |Sha| * prod(c_p) / |tors|^2
        sha = c['sha_an']
        tors = c['torsion_order']
        tam = c['tamagawa_product']
        rank = c['rank']
        sha_int = round(sha)

        if rank == 0:
            c['bsd_rhs'] = Fraction(sha_int * tam, tors**2)
            # L(E,1)/Omega^+ from the data
            om = c['real_period']
            lv = c['L_value']
            if om > 0:
                ratio = lv / om
                c['lvalue_ratio'] = ratio
                c['bsd_residual'] = abs(ratio - float(c['bsd_rhs']))
            else:
                c['lvalue_ratio'] = None
                c['bsd_residual'] = None
        else:
            c['bsd_rhs'] = None
            c['lvalue_ratio'] = None
            c['bsd_residual'] = None

        # Two-torsion rank
        ts = c['torsion_structure']
        c['two_tors_rank'] = sum(1 for d in ts if d % 2 == 0)

        # Generator height (for rank 1, compute from regulator which IS the height)
        if rank == 1:
            c['gen_height'] = c['regulator']
        elif rank >= 2:
            c['gen_height'] = None  # regulator is det of height pairing matrix
        else:
            c['gen_height'] = None

        processed.append(c)
    return processed


# ============================================================
# Analyses
# ============================================================

def summary_stats(curves):
    print("\n" + "="*70)
    print("SUMMARY STATISTICS")
    print("="*70)
    n = len(curves)
    print(f"Total curves: {n}")

    rank_counts = Counter(c['rank'] for c in curves)
    print(f"\nBy rank:")
    for r in sorted(rank_counts):
        print(f"  rank {r}: {rank_counts[r]:5d} ({100*rank_counts[r]/n:.1f}%)")

    # Root number / parity
    print(f"\nParity check (all should be consistent):")
    parity_fail = 0
    for c in curves:
        sha = c['sha_an']
        if sha < 0:
            print(f"  NEGATIVE SHA: {c['label']} sha_an={sha}")
            parity_fail += 1
    if parity_fail == 0:
        print(f"  All sha_an >= 0: OK")

    # CM
    cm_count = sum(1 for c in curves if c['has_cm'])
    print(f"\nCM curves: {cm_count} ({100*cm_count/n:.1f}%)")
    cm_discs = Counter(c['cm_disc'] for c in curves if c['has_cm'])
    for d, cnt in cm_discs.most_common():
        print(f"  disc {d}: {cnt}")

    # Torsion structure
    tors_counts = Counter(str(c['torsion_structure']) for c in curves)
    print(f"\nTorsion structure distribution:")
    for t, cnt in tors_counts.most_common():
        print(f"  {t:15s}: {cnt:5d} ({100*cnt/n:.1f}%)")

    # Tamagawa product
    tam_counts = Counter(c['tamagawa_product'] for c in curves)
    print(f"\nTamagawa product distribution (top 15):")
    for t, cnt in tam_counts.most_common(15):
        print(f"  c_prod={t:4d}: {cnt:5d}")

    # Sha distribution
    sha_counts = Counter(round(c['sha_an']) for c in curves)
    print(f"\nSha analytic order distribution:")
    for s, cnt in sha_counts.most_common(15):
        print(f"  |Sha|={s:4d}: {cnt:5d}")

    return rank_counts


def analysis_1_bsd_consistency(curves):
    """BSD formula consistency for rank 0."""
    print("\n" + "="*70)
    print("ANALYSIS 1: BSD Consistency (rank 0)")
    print("="*70)

    r0 = [c for c in curves if c['rank'] == 0]
    passed = failed = skipped = 0
    failures = []

    for c in r0:
        resid = c.get('bsd_residual')
        if resid is None:
            skipped += 1
            continue
        if resid < 1e-6:
            passed += 1
        else:
            failed += 1
            failures.append(c)

    print(f"  Checked: {passed+failed}, Passed: {passed}, Failed: {failed}, Skipped: {skipped}")
    if failures:
        print("  FAILURES:")
        for c in failures[:10]:
            print(f"    {c['label']}: residual={c['bsd_residual']:.2e}, bsd_rhs={c['bsd_rhs']}, lvalue_ratio={c.get('lvalue_ratio')}")

    # Actually, L_value in Cremona is L^(r)(E,1)/r!, not L(E,1).
    # For rank 0 this IS L(E,1). For rank 1, it's L'(E,1).
    # But lvalue_ratio = L_value / real_period might not match bsd_rhs
    # because real_period may need Neron period adjustment.
    # Let's check differently: BSD says
    #   L(E,1) = Omega * |Sha| * prod(c_p) / |tors|^2
    # So L_value should equal real_period * bsd_rhs
    print("\n  Alternative check: L(E,1) vs Omega * bsd_rhs:")
    passed2 = failed2 = 0
    for c in r0:
        lv = c['L_value']
        om = c['real_period']
        rhs = c.get('bsd_rhs')
        if rhs is None:
            continue
        predicted = om * float(rhs)
        resid = abs(lv - predicted)
        if resid < 1e-6:
            passed2 += 1
        else:
            failed2 += 1
            if failed2 <= 5:
                print(f"    {c['label']}: L={lv:.10f}, Om*rhs={predicted:.10f}, diff={resid:.2e}")
    print(f"  Passed: {passed2}, Failed: {failed2}")


def analysis_2_bsd_values(curves):
    """BSD rational value structure for rank 0."""
    print("\n" + "="*70)
    print("ANALYSIS 2: BSD Rational Value Structure (rank 0)")
    print("="*70)

    r0 = [c for c in curves if c['rank'] == 0 and c.get('bsd_rhs') is not None]

    # Group by torsion structure
    tors_to_bsd = defaultdict(list)
    for c in r0:
        key = str(c['torsion_structure'])
        tors_to_bsd[key].append(c['bsd_rhs'])

    for tors in sorted(tors_to_bsd, key=lambda t: len(tors_to_bsd[t]), reverse=True):
        vals = tors_to_bsd[tors]
        unique = sorted(set(vals))
        denoms = sorted(set(v.denominator for v in unique))
        print(f"\n  Torsion {tors} ({len(vals)} curves):")
        print(f"    Denominators: {denoms}")
        print(f"    Unique values: {len(unique)}")
        if len(unique) <= 10:
            for v in unique:
                cnt = vals.count(v)
                print(f"      {str(v):>10s} ({cnt}x)")
        else:
            vc = Counter(vals)
            print(f"    Most common:")
            for v, cnt in vc.most_common(5):
                print(f"      {str(v):>10s} ({cnt}x)")
            print(f"    Range: {min(unique)} to {max(unique)}")


def analysis_3_sha_structure(curves):
    """Sha distribution patterns — this is where anomalies hide."""
    print("\n" + "="*70)
    print("ANALYSIS 3: Sha Distribution and Structure")
    print("="*70)

    # Sha by rank
    sha_by_rank = defaultdict(Counter)
    for c in curves:
        sha_by_rank[c['rank']][round(c['sha_an'])] += 1

    for r in sorted(sha_by_rank):
        total = sum(sha_by_rank[r].values())
        nontrivial = total - sha_by_rank[r].get(1, 0)
        pct = 100*nontrivial/total if total > 0 else 0
        print(f"\n  Rank {r} ({total} curves, {nontrivial} with |Sha|>1 = {pct:.1f}%):")
        for s, cnt in sha_by_rank[r].most_common(8):
            print(f"    |Sha|={s}: {cnt}")

    # Sha by torsion
    print(f"\n  Sha > 1 breakdown by torsion:")
    sha_tors = defaultdict(list)
    for c in curves:
        if round(c['sha_an']) > 1:
            sha_tors[str(c['torsion_structure'])].append(
                (c['label'], round(c['sha_an']), c['rank'])
            )
    for tors, items in sorted(sha_tors.items(), key=lambda x: -len(x[1])):
        print(f"    Torsion {tors}: {len(items)} curves")
        sha_vals = Counter(s for _, s, _ in items)
        for s, cnt in sha_vals.most_common(5):
            print(f"      |Sha|={s}: {cnt}")

    # CM vs non-CM sha rates
    cm_sha_gt1 = sum(1 for c in curves if c['has_cm'] and round(c['sha_an']) > 1)
    cm_total = sum(1 for c in curves if c['has_cm'])
    ncm_sha_gt1 = sum(1 for c in curves if not c['has_cm'] and round(c['sha_an']) > 1)
    ncm_total = sum(1 for c in curves if not c['has_cm'])
    print(f"\n  CM:     {cm_sha_gt1}/{cm_total} have |Sha|>1 ({100*cm_sha_gt1/cm_total:.1f}%)" if cm_total else "")
    print(f"  Non-CM: {ncm_sha_gt1}/{ncm_total} have |Sha|>1 ({100*ncm_sha_gt1/ncm_total:.1f}%)" if ncm_total else "")

    # Is Sha always a perfect square?
    non_square_sha = []
    for c in curves:
        sha = round(c['sha_an'])
        if sha > 1:
            sr = int(math.isqrt(sha))
            if sr * sr != sha:
                non_square_sha.append((c['label'], sha))
    if non_square_sha:
        print(f"\n  NON-SQUARE SHA (should not exist if BSD is true):")
        for lab, s in non_square_sha[:10]:
            print(f"    {lab}: |Sha|={s}")
    else:
        print(f"\n  All Sha values are perfect squares: OK (consistent with BSD)")


def analysis_4_heegner(curves):
    """Heegner discriminants for rank 1."""
    print("\n" + "="*70)
    print("ANALYSIS 4: Heegner Discriminants (rank 1)")
    print("="*70)

    r1 = [c for c in curves if c['rank'] == 1]
    print(f"  Computing Heegner discriminants for {len(r1)} rank-1 curves...")

    heeg_data = []
    for i, c in enumerate(r1):
        N = c['conductor']
        D = find_heegner_disc(N)
        heeg_data.append((c['label'], N, D))
        if (i+1) % 200 == 0:
            print(f"    ...{i+1}/{len(r1)}")

    # Distribution
    d_counts = Counter(D for _, _, D in heeg_data if D is not None)
    print(f"\n  Heegner discriminant distribution (top 15):")
    for D, cnt in d_counts.most_common(15):
        print(f"    D={D:5d}: {cnt} curves")

    # Cheap Heegner (D <= 20)
    cheap = [(l, N, D) for l, N, D in heeg_data if D is not None and D <= 20]
    print(f"\n  Cheap Heegner (D <= 20): {len(cheap)} curves")
    for l, N, D in cheap[:15]:
        print(f"    {l:12s} N={N:4d}  D={D}")

    # Expensive
    expensive = sorted([(l, N, D) for l, N, D in heeg_data if D is not None], key=lambda x: -x[2])
    print(f"\n  10 most expensive Heegner discriminants:")
    for l, N, D in expensive[:10]:
        print(f"    {l:12s} N={N:4d}  D={D}")


def analysis_5_heights(curves):
    """Generator heights for rank 1."""
    print("\n" + "="*70)
    print("ANALYSIS 5: Generator Heights (rank 1)")
    print("="*70)

    r1 = [(c['label'], c['conductor'], c['gen_height']) for c in curves
          if c['rank'] == 1 and c.get('gen_height') is not None and c['gen_height'] > 0]

    if not r1:
        print("  No rank-1 height data available.")
        return

    heights = [h for _, _, h in r1]
    print(f"  {len(r1)} rank-1 curves with height data")
    print(f"  Mean height: {sum(heights)/len(heights):.4f}")
    print(f"  Median height: {sorted(heights)[len(heights)//2]:.4f}")
    print(f"  Min: {min(heights):.6f}, Max: {max(heights):.6f}")

    # Histogram
    buckets = defaultdict(int)
    for h in heights:
        b = int(h * 10) / 10  # bucket by 0.1
        buckets[b] += 1
    print(f"\n  Height histogram (bucket 0.1):")
    for b in sorted(buckets):
        if b <= 5.0:  # only show reasonable range
            bar = '#' * min(buckets[b], 60)
            print(f"    [{b:.1f},{b+0.1:.1f}): {buckets[b]:4d} {bar}")

    # Extremes
    r1_sorted = sorted(r1, key=lambda x: x[2])
    print(f"\n  5 smallest heights:")
    for l, N, h in r1_sorted[:5]:
        print(f"    {l:12s} N={N:4d}  h={h:.8f}")
    print(f"\n  5 largest heights:")
    for l, N, h in r1_sorted[-5:]:
        print(f"    {l:12s} N={N:4d}  h={h:.8f}")

    # Correlation with conductor
    log_N = [math.log(N) for _, N, _ in r1]
    h_vals = [h for _, _, h in r1]
    n_pts = len(r1)
    mean_x = sum(log_N) / n_pts
    mean_y = sum(h_vals) / n_pts
    cov = sum((x - mean_x)*(y - mean_y) for x, y in zip(log_N, h_vals)) / n_pts
    var_x = sum((x - mean_x)**2 for x in log_N) / n_pts
    var_y = sum((y - mean_y)**2 for y in h_vals) / n_pts
    if var_x > 0 and var_y > 0:
        corr = cov / (var_x * var_y)**0.5
        print(f"\n  Correlation(log(N), height) = {corr:.4f}")


def analysis_7_extrema(curves):
    """Extrema and outliers."""
    print("\n" + "="*70)
    print("ANALYSIS 7: Extrema and Outliers")
    print("="*70)

    r0 = [c for c in curves if c['rank'] == 0 and c.get('bsd_rhs') is not None]

    if r0:
        # Largest BSD
        by_bsd = sorted(r0, key=lambda c: float(c['bsd_rhs']), reverse=True)
        print("\n  5 largest BSD values (rank 0):")
        for c in by_bsd[:5]:
            print(f"    {c['label']:12s} bsd={str(c['bsd_rhs']):>10s}  |tors|={c['torsion_order']}  tam={c['tamagawa_product']}  sha={round(c['sha_an'])}")

        by_bsd_small = sorted([c for c in r0 if c['bsd_rhs'] > 0], key=lambda c: float(c['bsd_rhs']))
        print("\n  5 smallest BSD values (rank 0):")
        for c in by_bsd_small[:5]:
            print(f"    {c['label']:12s} bsd={str(c['bsd_rhs']):>10s}  |tors|={c['torsion_order']}  tam={c['tamagawa_product']}  sha={round(c['sha_an'])}")

    # Largest Sha
    by_sha = sorted(curves, key=lambda c: round(c['sha_an']), reverse=True)
    print("\n  10 largest |Sha|:")
    for c in by_sha[:10]:
        print(f"    {c['label']:12s} |Sha|={round(c['sha_an']):4d}  rank={c['rank']}  N={c['conductor']}  |tors|={c['torsion_order']}")

    # Largest Tamagawa
    by_tam = sorted(curves, key=lambda c: c['tamagawa_product'], reverse=True)
    print("\n  10 largest Tamagawa products:")
    for c in by_tam[:10]:
        print(f"    {c['label']:12s} tam={c['tamagawa_product']:4d}  N={c['conductor']}  rank={c['rank']}")


def analysis_8_congruences(curves):
    """Congruence patterns in BSD numerators."""
    print("\n" + "="*70)
    print("ANALYSIS 8: Congruence Patterns in BSD Values")
    print("="*70)

    r0 = [c for c in curves if c['rank'] == 0 and c.get('bsd_rhs') is not None]

    # For each curve: sha * tam is the numerator of tors^2 * bsd_rhs
    # This is the "algebraic" BSD numerator
    for p in [2, 3, 5, 7]:
        counts = Counter()
        for c in r0:
            sha = round(c['sha_an'])
            tam = c['tamagawa_product']
            val = sha * tam
            counts[val % p] += 1
        total = sum(counts.values())
        print(f"\n  sha*tam mod {p}:")
        for r in range(p):
            cnt = counts.get(r, 0)
            pct = 100*cnt/total if total else 0
            expected = 100/p
            flag = " <--" if abs(pct - expected) > 10 else ""
            print(f"    {r}: {cnt:5d} ({pct:.1f}%, expected {expected:.1f}%){flag}")


def analysis_9_isogeny(curves):
    """Isogeny class patterns."""
    print("\n" + "="*70)
    print("ANALYSIS 9: Isogeny Class Patterns")
    print("="*70)

    classes = defaultdict(list)
    for c in curves:
        classes[c['iso_class']].append(c)

    multi = {k: v for k, v in classes.items() if len(v) > 1}
    print(f"  Total isogeny classes: {len(classes)}")
    print(f"  Classes with >1 curve: {len(multi)}")

    # Size distribution
    size_counts = Counter(len(v) for v in classes.values())
    print(f"\n  Class size distribution:")
    for sz, cnt in sorted(size_counts.items()):
        print(f"    size {sz}: {cnt} classes")

    # BSD value constant within rank-0 classes?
    # Actually L(E,1) is isogeny-invariant but Omega is not.
    # So bsd_rhs = L(E,1)/Omega varies. But L(E,1) = Omega * bsd_rhs should be constant.
    print(f"\n  L(E,1) constancy within isogeny classes (rank 0):")
    lv_varies = 0
    lv_const = 0
    for cls, crvs in multi.items():
        r0 = [c for c in crvs if c['rank'] == 0]
        if len(r0) >= 2:
            lvs = [c['L_value'] for c in r0]
            spread = max(lvs) - min(lvs)
            if spread < 1e-8:
                lv_const += 1
            else:
                lv_varies += 1
                if lv_varies <= 3:
                    print(f"    {cls}: L-values = {[f'{x:.8f}' for x in lvs]}")
    print(f"  Constant: {lv_const}, Varies: {lv_varies}")

    # Within class: torsion/tamagawa/sha tradeoffs
    print(f"\n  Torsion/Tamagawa/Sha tradeoffs within classes (first 5 multi-curve classes):")
    count = 0
    for cls in sorted(multi, key=lambda k: int(k.rstrip('abcdefghijklmnopqrstuvwxyz'))):
        crvs = multi[cls]
        r0 = [c for c in crvs if c['rank'] == 0]
        if len(r0) >= 2:
            # Check if bsd_rhs varies
            rhs_vals = set(c['bsd_rhs'] for c in r0 if c.get('bsd_rhs') is not None)
            if len(rhs_vals) > 1:
                count += 1
                if count <= 5:
                    print(f"\n    Class {cls}:")
                    for c in r0:
                        print(f"      {c['label']:12s} |tors|={c['torsion_order']}  tam={c['tamagawa_product']}  sha={round(c['sha_an'])}  bsd={c.get('bsd_rhs','?')}")


def analysis_10_rank_distribution(curves):
    """Rank distribution and patterns."""
    print("\n" + "="*70)
    print("ANALYSIS 10: Rank Distribution and High-Rank Curves")
    print("="*70)

    rank_counts = Counter(c['rank'] for c in curves)
    n = len(curves)
    for r in sorted(rank_counts):
        print(f"  rank {r}: {rank_counts[r]:5d} ({100*rank_counts[r]/n:.1f}%)")

    # Rank >= 2
    high = [c for c in curves if c['rank'] >= 2]
    if high:
        print(f"\n  Rank >= 2 curves ({len(high)}):")
        for c in sorted(high, key=lambda c: -c['rank'])[:20]:
            print(f"    {c['label']:12s} rank={c['rank']}  N={c['conductor']}  |tors|={c['torsion_order']}  sha={round(c['sha_an'])}")

    # Rank by conductor range
    print(f"\n  Average rank by conductor range:")
    for lo in range(0, 500, 100):
        hi = lo + 100
        subset = [c for c in curves if lo < c['conductor'] <= hi]
        if subset:
            avg_r = sum(c['rank'] for c in subset) / len(subset)
            r0_pct = 100*sum(1 for c in subset if c['rank']==0)/len(subset)
            print(f"    N in ({lo},{hi}]: {len(subset)} curves, avg rank={avg_r:.3f}, rank 0 = {r0_pct:.1f}%")


# ============================================================
# Main
# ============================================================

if __name__ == '__main__':
    print("="*70)
    print("BSD LANDSCAPE SURVEY — Cremona ecdata")
    print("="*70)

    # Fetch data
    print("\n--- Fetching data ---")
    bsd_text = fetch_file("allbsd/allbsd.00000-09999")
    gens_text = fetch_file("allgens/allgens.00000-09999")

    # Parse
    print("\n--- Parsing ---")
    bsd_all = []
    for line in bsd_text.strip().split('\n'):
        rec = parse_bsd_line(line)
        if rec and rec['conductor'] <= 500:
            bsd_all.append(rec)
    print(f"  Parsed {len(bsd_all)} curves with conductor <= 500 from allbsd")

    gens_dict = {}
    for line in gens_text.strip().split('\n'):
        rec = parse_gens_line(line)
        if rec:
            gens_dict[rec['label']] = rec
    print(f"  Parsed {len(gens_dict)} entries from allgens")

    # Process
    print("\n--- Processing ---")
    curves = process_curves(bsd_all, gens_dict)
    print(f"  Processed {len(curves)} curves")

    # Run analyses
    summary_stats(curves)
    analysis_1_bsd_consistency(curves)
    analysis_2_bsd_values(curves)
    analysis_3_sha_structure(curves)
    analysis_4_heegner(curves)
    analysis_5_heights(curves)
    analysis_7_extrema(curves)
    analysis_8_congruences(curves)
    analysis_9_isogeny(curves)
    analysis_10_rank_distribution(curves)

    # Save
    print("\n--- Saving ---")
    out = '/Users/quantmann/FoundationRelativity/paper 97/'

    with open(out + 'bsd_landscape.json', 'w') as f:
        def ser(obj):
            if isinstance(obj, Fraction):
                return str(obj)
            raise TypeError(f"Not serializable: {type(obj)}")
        json.dump(curves, f, default=ser, indent=1)
    print(f"  Saved bsd_landscape.json ({len(curves)} curves)")

    print("\n--- Done ---")
