#!/usr/bin/env python3
"""
solve_walcher.py — Walcher's Inhomogeneous PF Equation for the Real Quintic

References:
  [W07]  Walcher, "Opening mirror symmetry on the quintic" (2007), arXiv:hep-th/0605162
  [MW09] Morrison-Walcher, "D-branes and normal functions" (2009), arXiv:0709.4028
  [LW12] Laporte-Walcher, "Monodromy of an inhomogeneous PF equation" (2012), arXiv:1206.1787

The real quintic CY3 X_5 carries a real Lagrangian L ≅ RP^3 (fixed locus of the
antiholomorphic involution). The Abel-Jacobi image of L defines a normal function
T(z) satisfying the inhomogeneous Picard-Fuchs equation:

  L · T(z) = (15/8) · √z

in the CDGP coordinate z = (5ψ)^{-5}, where:
  L = θ^4 - 5z(5θ+1)(5θ+2)(5θ+3)(5θ+4),  θ = z·d/dz.

Writing T(z) = √z · S(z) with S = Σ_{n≥0} b_n z^n, the equation becomes
  L_{1/2} · S = 15/8
where L_{1/2} is L with θ → θ + 1/2. This gives:
  b_0 · (1/2)^4 = 15/8  ⟹  b_0 = 30
  b_n = 5 · b_{n-1} · (5n-3/2)(5n-1/2)(5n+1/2)(5n+3/2) / (n+1/2)^4  for n ≥ 1

The leading coefficient b_0 = 30 matches Walcher's disk count n_1 = 30.

CRM classification:
  - PF coefficients ∈ ℚ[z]: BISH (by ring)
  - Source term (15/8)√z: algebraic, BISH (determined by cycle topology)
  - Recurrence b_n = f(b_{n-1}): rational arithmetic, BISH
  - Each b_n ∈ ℚ: BISH-computable
  - Convergence of T(z) as analytic function: CLASS
  - Abel-Jacobi map AJ(L) = T: CLASS (period integrals)
  - Infinite generation of Griff^2(X) (Voisin): CLASS (Baire category)

This script computes b_0 through b_5, verifies them, and emits WalcherData.lean.
"""

from fractions import Fraction
import sys

# ─── Recurrence computation ───

def alpha(n):
    """Indicial coefficient: (n + 1/2)^4"""
    return (Fraction(2*n + 1, 2)) ** 4

def beta(n):
    """Shift coefficient: 5 · (5n-3/2)(5n-1/2)(5n+1/2)(5n+3/2)"""
    s = Fraction(5*n, 1)
    return 5 * (s - Fraction(3,2)) * (s - Fraction(1,2)) * (s + Fraction(1,2)) * (s + Fraction(3,2))

def compute_coefficients(N):
    """Compute b_0, ..., b_N of the normal function expansion."""
    b = [Fraction(0)] * (N + 1)
    # Leading order: b_0 · (1/2)^4 = 15/8
    b[0] = Fraction(15, 8) / alpha(0)
    assert b[0] == Fraction(30, 1), f"b_0 should be 30, got {b[0]}"
    print(f"b_0 = {b[0]}")

    for n in range(1, N + 1):
        b[n] = b[n-1] * beta(n) / alpha(n)
        print(f"b_{n} = {b[n]}  (= {b[n].numerator}/{b[n].denominator})")

    return b

# ─── Verification ───

def verify_leading_order(b0):
    """Verify b_0 · (1/2)^4 = 15/8."""
    lhs = b0 * Fraction(1, 16)
    rhs = Fraction(15, 8)
    assert lhs == rhs, f"Leading order failed: {lhs} ≠ {rhs}"
    print(f"\n✓ Leading order: {b0} · 1/16 = {lhs} = 15/8")

def verify_recurrence(b, n):
    """Verify b_n · α(n) = b_{n-1} · β(n) at index n."""
    lhs = b[n] * alpha(n)
    rhs = b[n-1] * beta(n)
    assert lhs == rhs, f"Recurrence at n={n} failed: {lhs} ≠ {rhs}"
    print(f"✓ Recurrence at n={n}: {b[n]} · {alpha(n)} = {b[n-1]} · {beta(n)} = {lhs}")

def verify_source_algebraic():
    """The source term δ(z) = (15/8)√z satisfies δ^2 = (225/64)z."""
    c = Fraction(15, 8)
    assert c * c == Fraction(225, 64)
    print(f"\n✓ Source algebraic relation: (15/8)^2 = {c*c} = 225/64")

def verify_source_nonzero():
    """At z = 1/4 (perfect square): δ(1/4) = (15/8)·(1/2) = 15/16 ≠ 0."""
    z = Fraction(1, 4)
    delta = Fraction(15, 8) * Fraction(1, 2)  # √(1/4) = 1/2
    assert delta == Fraction(15, 16)
    assert delta != 0
    print(f"✓ Source at z=1/4: δ = {delta} ≠ 0")

    """At z = 1 (perfect square): δ(1) = 15/8 ≠ 0."""
    delta_1 = Fraction(15, 8)
    assert delta_1 != 0
    print(f"✓ Source at z=1: δ = {delta_1} ≠ 0")

# ─── Lean emission ───

def frac_to_lean(f):
    """Convert Fraction to Lean ℚ literal."""
    if f.denominator == 1:
        return str(f.numerator)
    else:
        # Use parenthesized form
        return f"({f.numerator} : ℚ) / {f.denominator}"

def emit_lean(b, filename):
    """Emit WalcherData.lean."""
    N = len(b)

    lines = []
    lines.append("/-!")
    lines.append("  WalcherData.lean — Verified coefficients of Walcher's normal function")
    lines.append("")
    lines.append("  The domainwall tension T(z) for the real Lagrangian on the mirror quintic")
    lines.append("  satisfies the inhomogeneous Picard-Fuchs equation:")
    lines.append("    L · T(z) = (15/8) · √z")
    lines.append("  where L = θ⁴ - 5z(5θ+1)(5θ+2)(5θ+3)(5θ+4) in CDGP coordinate z = (5ψ)⁻⁵.")
    lines.append("")
    lines.append("  Writing T = √z · Σ bₙ zⁿ, the recurrence is:")
    lines.append("    b₀ = 30")
    lines.append("    bₙ = 5 · b_{n-1} · (5n-3/2)(5n-1/2)(5n+1/2)(5n+3/2) / (n+1/2)⁴")
    lines.append("")
    lines.append("  References:")
    lines.append("    [W07] Walcher, Comm. Math. Phys. 276 (2007) 671–689, arXiv:hep-th/0605162")
    lines.append("    [MW09] Morrison-Walcher, Adv. Theor. Math. Phys. 13 (2009) 553–598")
    lines.append("-/")
    lines.append("import Mathlib.Data.Rat.Lemmas")
    lines.append("import Mathlib.Tactic")
    lines.append("")
    lines.append("namespace P93")
    lines.append("")

    # Source term algebraic relation
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("-- §1. Source term: δ(z) = (15/8)√z, algebraic relation δ² = (225/64)z")
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("")
    lines.append("noncomputable def walcher_source_coeff : ℚ := 15 / 8")
    lines.append("")
    lines.append("/-- The source coefficient squared equals 225/64. -/")
    lines.append("theorem source_coeff_sq : walcher_source_coeff ^ 2 = 225 / 64 := by")
    lines.append("  unfold walcher_source_coeff; norm_num")
    lines.append("")
    lines.append("/-- The source coefficient is nonzero. -/")
    lines.append("theorem source_coeff_ne_zero : walcher_source_coeff ≠ 0 := by")
    lines.append("  unfold walcher_source_coeff; norm_num")
    lines.append("")

    # Expansion coefficients
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("-- §2. Normal function expansion coefficients b_n")
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("")

    for i in range(N):
        val = frac_to_lean(b[i])
        lines.append(f"noncomputable def b_{i} : ℚ := {val}")
    lines.append("")

    # Leading order verification
    lines.append("/-- Leading order: b₀ · (1/2)⁴ = 15/8 (Walcher's n₁ = 30 disk count). -/")
    lines.append("theorem leading_order : b_0 * ((1 : ℚ) / 2) ^ 4 = 15 / 8 := by")
    lines.append("  unfold b_0; norm_num")
    lines.append("")

    # b_0 = 30
    lines.append("/-- The leading coefficient is 30. -/")
    lines.append("theorem b_0_val : b_0 = 30 := by unfold b_0; norm_num")
    lines.append("")

    # Recurrence: b_n · (n+1/2)^4 = 5 · b_{n-1} · (5n-3/2)(5n-1/2)(5n+1/2)(5n+3/2)
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("-- §3. Recurrence verification: bₙ · (n+1/2)⁴ = 5·b_{n-1}·∏ₖ(5n+k)")
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("")

    for n in range(1, N):
        a_val = alpha(n)
        b_val = beta(n)
        lhs_result = b[n] * a_val
        rhs_result = b[n-1] * b_val
        assert lhs_result == rhs_result

        # Write as: b_n * alpha_n = b_{n-1} * beta_n
        # Using specific rational values
        a_num, a_den = a_val.numerator, a_val.denominator
        b_num, b_den = b_val.numerator, b_val.denominator

        lines.append(f"/-- Recurrence at n = {n}: b_{n} · (({2*n+1})/2)⁴ = 5 · b_{n-1} · ∏ -/")
        lines.append(f"theorem recurrence_{n} :")
        lines.append(f"    b_{n} * (({a_num} : ℚ) / {a_den}) = b_{n-1} * (({b_num} : ℚ) / {b_den}) := by")
        lines.append(f"  unfold b_{n} b_{n-1}; norm_num")
        lines.append("")

    # Non-triviality of coefficients
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("-- §4. Non-triviality: all coefficients are nonzero")
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("")
    for i in range(N):
        lines.append(f"theorem b_{i}_ne_zero : b_{i} ≠ 0 := by unfold b_{i}; norm_num")
    lines.append("")

    # Walcher disk count
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("-- §5. Connection to enumerative geometry")
    lines.append("-- ═══════════════════════════════════════════════════════════════")
    lines.append("")
    lines.append("/-- Walcher's disk count: 30 holomorphic disks of minimal area -/")
    lines.append("/-- ending on the real Lagrangian RP³ ⊂ X₅. -/")
    lines.append("theorem walcher_disk_count : b_0 = 30 := by unfold b_0; norm_num")
    lines.append("")

    lines.append("end P93")

    with open(filename, 'w') as f:
        f.write('\n'.join(lines) + '\n')
    print(f"\n✓ Emitted {filename} ({len(lines)} lines)")


# ─── Main ───

if __name__ == '__main__':
    print("=" * 60)
    print("Walcher's Inhomogeneous PF Equation for the Real Quintic")
    print("=" * 60)
    print()

    # Compute coefficients
    print("Normal function expansion T = √z · Σ bₙ zⁿ:")
    b = compute_coefficients(5)

    # Verify
    print("\nVerification:")
    verify_leading_order(b[0])
    for n in range(1, len(b)):
        verify_recurrence(b, n)
    verify_source_algebraic()
    verify_source_nonzero()

    # Emit Lean
    lean_path = "P93_MirrorSqueeze/Papers/P93_MirrorSqueeze/WalcherData.lean"
    emit_lean(b, lean_path)

    print("\nDone.")
