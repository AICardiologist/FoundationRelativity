# Paper 65: Computation Report

Generated: 2026-02-22

## 1. Data Summary

- **Squarefree d values (d <= 200):** 122
- **Cyclic cubic conductors found:** 10 out of 22 attempted
- **Total (K, F) pairs computed:** 1220
- **Family 1 non-cyclic cubics:** 24

## 2. Class Number Distribution

| h_K | Count | Fraction |
|-----|-------|----------|
| 1 | 9 | 7.4% |
| 2 | 14 | 11.5% |
| 3 | 6 | 4.9% |
| 4 | 27 | 22.1% |
| 5 | 6 | 4.9% |
| 6 | 10 | 8.2% |
| 7 | 2 | 1.6% |
| 8 | 21 | 17.2% |
| 9 | 1 | 0.8% |
| 10 | 9 | 7.4% |
| 11 | 1 | 0.8% |
| 12 | 7 | 5.7% |
| 13 | 1 | 0.8% |
| 14 | 4 | 3.3% |
| 16 | 3 | 2.5% |
| 20 | 1 | 0.8% |

Heegner numbers (h_K = 1): 1, 2, 3, 7, 11, 19, 43, 67, 163

## 3. Cyclic Cubic Polynomials

| f | Polynomial | disc | disc = f^2 |
|---|-----------|------|-----------|
| 7 | x^3+1x^2+(-142)x+(-701) | 49 | Y |
| 9 | x^3+(-3)x+(1) | 81 | Y |
| 13 | x^3+1x^2+(-4)x+(1) | 169 | Y |
| 19 | x^3+1x^2+(-424)x+(3223) | 361 | Y |
| 31 | NOT FOUND | -- | -- |
| 37 | x^3+1x^2+(-12)x+(11) | 1369 | Y |
| 43 | NOT FOUND | -- | -- |
| 61 | x^3+(-61)x+(183) | 3721 | Y |
| 67 | NOT FOUND | -- | -- |
| 73 | NOT FOUND | -- | -- |
| 79 | x^3+1x^2+(-26)x+(41) | 6241 | Y |
| 97 | x^3+1x^2+(-32)x+(-79) | 9409 | Y |
| 103 | NOT FOUND | -- | -- |
| 109 | NOT FOUND | -- | -- |
| 127 | NOT FOUND | -- | -- |
| 139 | x^3+1x^2+(-46)x+(103) | 19321 | Y |
| 151 | NOT FOUND | -- | -- |
| 157 | NOT FOUND | -- | -- |
| 163 | x^3+1x^2+(-54)x+(-169) | 26569 | Y |
| 181 | NOT FOUND | -- | -- |
| 193 | NOT FOUND | -- | -- |
| 199 | NOT FOUND | -- | -- |

## 4. Family 3: Main Finding

**h * Nm(A) = f Identity:**

- **Total pairs:** 1220
- **Determined:** 1220
- **Confirmed h * Nm(A) = f:** 1220
- **Exceptions:** 0
- **Undetermined:** 0

### Breakdown by Lattice Type

- **Free lattice (h = f, Nm(A) = 1):** 738 pairs
- **Steinitz twist (Nm(A) > 1):** 482 pairs
- **Undetermined:** 0 pairs

### Forcing Statistics by Class Number

- h_K = 1: 90 pairs, 90 free, 0 Steinitz, 0 undetermined
- h_K = 2: 140 pairs, 108 free, 32 Steinitz, 0 undetermined
- h_K = 3: 60 pairs, 37 free, 23 Steinitz, 0 undetermined
- h_K = 4: 270 pairs, 167 free, 103 Steinitz, 0 undetermined
- h_K = 5: 60 pairs, 32 free, 28 Steinitz, 0 undetermined
- h_K = 6: 100 pairs, 54 free, 46 Steinitz, 0 undetermined
- h_K = 7: 20 pairs, 13 free, 7 Steinitz, 0 undetermined
- h_K = 8: 210 pairs, 104 free, 106 Steinitz, 0 undetermined
- h_K = 9: 10 pairs, 5 free, 5 Steinitz, 0 undetermined
- h_K = 10: 90 pairs, 46 free, 44 Steinitz, 0 undetermined
- h_K = 11: 10 pairs, 6 free, 4 Steinitz, 0 undetermined
- h_K = 12: 70 pairs, 29 free, 41 Steinitz, 0 undetermined
- h_K = 13: 10 pairs, 6 free, 4 Steinitz, 0 undetermined
- h_K = 14: 40 pairs, 21 free, 19 Steinitz, 0 undetermined
- h_K = 16: 30 pairs, 15 free, 15 Steinitz, 0 undetermined
- h_K = 20: 10 pairs, 5 free, 5 Steinitz, 0 undetermined

## 5. Heegner Field Verification

Known h = f cases from Papers 56-57 (h_K = 1 fields):

- d=7, f=7: h=7, Nm(A)=1, h*Nm(A)=7 [Y]
- d=11, f=11: NOT IN CONDUCTOR LIST (f=11 is conductor: no)
- d=19, f=19: h=19, Nm(A)=1, h*Nm(A)=19 [Y]
- d=43, f=43: NOT IN CONDUCTOR LIST (f=43 is conductor: yes)
- d=67, f=67: NOT IN CONDUCTOR LIST (f=67 is conductor: yes)
- d=163, f=163: h=163, Nm(A)=1, h*Nm(A)=163 [Y]

## 6. Paper 58 Steinitz Example: d=5, f=7

- h_K = 2, status: steinitz (Nm(A)=7, form 1)
- h = 1, Nm(A) = 7, h * Nm(A) = 7
- 7 represented by principal form x^2+5y^2? False

## 7. Family 1: Non-Cyclic Cubics

- **Non-cyclic cubics found:** 24 (disc <= 1000)
- **Gram matrix analyses:** 216 (paired with Heegner fields)

- Cases where h^2 = disc(F): 0 out of 216

### Sample Non-Cyclic Cubics (first 10)

| disc(F) | d | det(G) | #Gram | h values |
|---------|---|--------|-------|----------|
| 148 | 1 | 592 | 11 | [1, 2, 4, 4, 8] |
| 148 | 2 | 1184 | 40 | [1, 2, 3, 4, 4] |
| 148 | 3 | 444 | 20 | [1, 2, 3, 4, 4] |
| 148 | 7 | 1036 | 24 | [1, 2, 4, 4, 5] |
| 148 | 11 | 1628 | 36 | [1, 2, 3, 4, 4] |
| 148 | 19 | 2812 | 32 | [1, 2, 4, 4, 7] |
| 148 | 43 | 6364 | 48 | [1, 2, 4, 4, 5] |
| 148 | 67 | 9916 | 52 | [1, 2, 4, 4, 5] |
| 148 | 163 | 24124 | 104 | [1, 2, 4, 4, 5] |
| 229 | 1 | 916 | 17 | [1, 2, 4, 4, 5] |

## 8. Main Theorem (Computationally Confirmed)

**Theorem.** Let K = Q(sqrt(-d)) be an imaginary quadratic field and F a totally real
cyclic Galois cubic of conductor f. On the CM abelian fourfold A_(K,F), the
self-intersection degree h of the exotic Weil class satisfies:

  h * Nm(A) = f

where A is the Steinitz ideal class of the Weil lattice W_int as an O_K-module.
In particular:
- If h_K = 1: h = f (lattice is free).
- If h_K > 1 and f is represented by the principal form of K: h = f (lattice is free).
- If h_K > 1 and f is NOT represented by the principal form: Steinitz twist is forced.

**Verification:** Confirmed for 1220 out of 1220 determined pairs.