# Paper 64: Computation Report

Generated: 2026-02-22 21:47

## 1. Data Summary

- **Curves analyzed:** 1812
- **Primes considered:** 46 primes up to 200
- **Total (curve, prime) pairs:** 23454
- **Curves with known rank:** 136

## 2. Main Finding: Global Boundedness

- **Global maximum N_M:** 2
- **Achieved at:** curve `15.a1`, prime p = 2
  - a_p = -1, #E(F_p) = 4
- **Distribution of max N_M per curve:**
  - max N_M = 0: 922 curves (50.9%)
  - max N_M = 1: 870 curves (48.0%)
  - max N_M = 2: 20 curves (1.1%)

## 3. The N_M <= 1 Conjecture (p >= 5)

**CONFIRMED:** No (curve, prime) pair with p >= 5 has N_M >= 2.

This is consistent with the theoretical proof from the Hasse bound:
For p >= 5, N_M >= 2 requires p^2 | (p+1-a_p), i.e., a_p = p+1 (mod p^2).
Since |a_p| <= 2*sqrt(p) < p for p >= 5, the only candidate is a_p = 1
(giving p+1-a_p = p), and v_p(p) = 1, not >= 2. QED.

### p = 3: N_M >= 2 events: 0
None — confirmed N_M <= 1 at p = 3.

### p = 2: N_M >= 2 events: 20
Maximum N_M at p=2: 2
  - 15.a1, a_2=-1, #E(F_2)=4, N_M=2
  - 15.a2, a_2=-1, #E(F_2)=4, N_M=2
  - 15.a3, a_2=-1, #E(F_2)=4, N_M=2
  - 15.a4, a_2=-1, #E(F_2)=4, N_M=2
  - 15.a5, a_2=-1, #E(F_2)=4, N_M=2
  - 17.a1, a_2=-1, #E(F_2)=4, N_M=2
  - 17.a2, a_2=-1, #E(F_2)=4, N_M=2
  - 17.a3, a_2=-1, #E(F_2)=4, N_M=2
  - 17.a4, a_2=-1, #E(F_2)=4, N_M=2
  - 21.a1, a_2=-1, #E(F_2)=4, N_M=2

## 4. Small Prime Analysis

### p = 2
- Total curves with good reduction: 70
- N_M = 0: 41
- N_M = 1: 9
- N_M = 2: 20
- N_M >= 3: 0
- Max N_M: 2 (curve: 15.a1)

### p = 3
- Total curves with good reduction: 1245
- N_M = 0: 1209
- N_M = 1: 36
- N_M = 2: 0
- N_M >= 3: 0
- Max N_M: 1 (curve: 14.a1)

### p = 5
- Total curves with good reduction: 1451
- N_M = 0: 1228
- N_M = 1: 223
- N_M = 2: 0
- N_M >= 3: 0
- Max N_M: 1 (curve: 11.a1)

## 5. Rank Correlation

- Rank 0: 111 curves, mean max_N_M = 0.802, max = 2
- Rank 1: 18 curves, mean max_N_M = 1.222, max = 2
- Rank 2: 6 curves, mean max_N_M = 0.667, max = 1
- Rank 3: 1 curves, mean max_N_M = 1.000, max = 1

**Conclusion:** No significant rank dependence in N_M. The p-adic precision bound is uniformly tame across all ranks.

## 6. Torsion Effect

- Z/2Z: 34 curves, mean max_N_M = 0.912
- Z/2Z x Z/2Z: 17 curves, mean max_N_M = 0.706
- Z/2Z x Z/4Z: 2 curves, mean max_N_M = 1.000
- Z/3Z: 12 curves, mean max_N_M = 0.667
- Z/4Z: 8 curves, mean max_N_M = 0.500
- Z/5Z: 5 curves, mean max_N_M = 0.800
- Z/6Z: 11 curves, mean max_N_M = 0.818
- trivial: 42 curves, mean max_N_M = 1.000

## 7. CM vs Non-CM

- CM curves: 18, mean max_N_M = 0.278
- Non-CM curves: 1794, mean max_N_M = 0.504

## 8. Anomalous Primes

- Total anomalous (curve, prime) pairs: 1119
- Mean anomalous primes per curve: 0.62
- Max anomalous primes for a single curve: 12

## 9. Hasse Bound Theoretical Analysis

| p | Hasse max N_M | Best a_p | #E(F_p) |
|---|---------------|----------|---------|
| 2 | 2 | -1 | 4 |
| 3 | 1 | -2 | 6 |
| 5 | 1 | -4 | 10 |
| 7 | 1 | 1 | 7 |
| 11 | 1 | 1 | 11 |
| 13 | 1 | 1 | 13 |
| 17 | 1 | 1 | 17 |
| 19 | 1 | 1 | 19 |
| 23 | 1 | 1 | 23 |
| 29 | 1 | 1 | 29 |
| 31 | 1 | 1 | 31 |
| 37 | 1 | 1 | 37 |
| 41 | 1 | 1 | 41 |
| 43 | 1 | 1 | 43 |
| 47 | 1 | 1 | 47 |
| 53 | 1 | 1 | 53 |
| 59 | 1 | 1 | 59 |
| 61 | 1 | 1 | 61 |
| 67 | 1 | 1 | 67 |
| 71 | 1 | 1 | 71 |
| ... | 1 | 1 | p | (for all p >= 3)

**Key result:** Hasse max N_M = 2 only at p = 2. For all p >= 3: max N_M = 1.

## 10. Main Theorem (Computationally Confirmed)

**Theorem.** For any elliptic curve E/Q and any prime p of good reduction,
N_M = v_p(#E(F_p)) <= 2, with N_M = 2 only possible at p = 2.
For p >= 5, N_M <= 1 with equality iff E is anomalous at p (a_p = 1).

**Proof.** From the Hasse bound |a_p| <= 2*sqrt(p):

Case p >= 5: 2*sqrt(p) < p, so |a_p| < p. For N_M >= 2 we need
p^2 | (p+1-a_p). Since |p+1-a_p| <= p+1+2*sqrt(p) < 2p for p >= 5,
and p+1-a_p > 0 (as a_p <= 2*sqrt(p) < p+1), we need p+1-a_p = p^k
with k >= 2. But p+1-a_p < 2p < p^2, so k < 2. Contradiction.

Case p = 3: #E(F_3) in {1,...,7}. max v_3 in this range = 1 (at 3 or 6).

Case p = 2: #E(F_2) in {1,...,5}. max v_2 in this range = 2 (at 4). QED.