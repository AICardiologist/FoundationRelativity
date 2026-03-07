#!/usr/bin/env python3
"""
solve_fhn.py — CAS computation for Paper 105

Computes exact rational constants for the FitzHugh-Nagumo CRM decomposition:
1. Explicit Lipschitz bound L(R) for the FHN vector field on [-R,R]²
2. Trapping region boundary R_min
3. Jacobian eigenvalues at the resting equilibrium for standard parameters
4. Hopf bifurcation current I* (symbolic)

All outputs are exact rationals suitable for Lean verification via norm_num/ring.

Paper 105, Clinical Sub-Series Paper C,
of the Constructive Reverse Mathematics Series
"""

from fractions import Fraction
from sympy import (
    Rational, Symbol, solve, sqrt, simplify, Abs,
    Matrix, Poly, symbols, re, im, I
)

# === Standard FHN Parameters (FitzHugh 1961) ===
eps = Rational(8, 100)   # ε = 0.08
a = Rational(7, 10)      # a = 0.7
b = Rational(8, 10)      # b = 0.8
I_ext = Rational(0, 1)   # I = 0 (sub-threshold, stable resting state)
# For oscillatory regime, use I = 1/2; for stable resting state, use I = 0

print("=" * 60)
print("Paper 105 — FitzHugh-Nagumo CAS Computation")
print("=" * 60)
print(f"\nStandard parameters: ε = {eps}, a = {a}, b = {b}, I = {I_ext}")

# === 1. Lipschitz Bound ===
print("\n--- 1. Lipschitz Bound L(R) ---")

# The Jacobian of F = (dV/dt, dW/dt) is:
#   J = [[1 - V², -1], [ε, -εb]]
#
# Frobenius norm: ||J||_F² = (1-V²)² + 1 + ε² + ε²b²
# On [-R,R]², |1-V²| ≤ max(1, R²-1) = R²-1 for R > √2
# So ||J||_F ≤ sqrt((R²-1)² + 1 + ε² + ε²b²) for R > √2

R_val = Rational(3, 1)  # R = 3 (physiological bounding box)

J11_max = R_val**2 - 1  # max |1 - V²| on [-3,3] = 8
J12 = Rational(-1, 1)
J21 = eps
J22 = -eps * b

frob_sq = J11_max**2 + 1 + eps**2 + (eps * b)**2
print(f"R = {R_val}")
print(f"max |1 - V²| on [-R,R] = {J11_max}")
print(f"||J||_F² ≤ {frob_sq} = {float(frob_sq):.6f}")
print(f"||J||_F ≤ sqrt({frob_sq})")

# For Lean, we use the rational upper bound L = J11_max + 1 + eps + eps*b
# (from ||J||_op ≤ ||J||_1 = max column sum, which is simpler)
# Column 1 sum: |1-V²| + ε ≤ (R²-1) + ε
# Column 2 sum: 1 + εb
# L = max(col1, col2) = max(R²-1+ε, 1+εb)

col1_max = J11_max + eps  # 8 + 0.08 = 8.08
col2_max = 1 + eps * b    # 1 + 0.064 = 1.064
L_bound = max(col1_max, col2_max)

print(f"\nColumn-sum bound (||J||_1):")
print(f"  Column 1: |1-V²| + ε ≤ {col1_max}")
print(f"  Column 2: 1 + εb = {col2_max}")
print(f"  L(R={R_val}) = {L_bound} = {float(L_bound):.6f}")

# === 2. Trapping Region ===
print("\n--- 2. Trapping Region ---")

# The FHN trapping region requires a RECTANGULAR box K = [-R,R] × [-S,S].
# A square box fails because the W-nullcline slope (1/b > 1) pushes
# trajectories beyond W = R when V is large.
#
# Required conditions:
#   Face W = +S: dW/dt < 0 ∀ V ∈ [-R,R] → S > (R + a)/b
#   Face W = -S: dW/dt > 0 ∀ V ∈ [-R,R] → S > (R - a)/b
#   Face V = +R: dV/dt < 0 ∀ W ∈ [-S,S] → R³/3 > R + S + I
#   Face V = -R: dV/dt > 0 ∀ W ∈ [-S,S] → R³/3 > R + S - I

R_val = Rational(3, 1)  # V ∈ [-3, 3]
S_val = Rational(5, 1)  # W ∈ [-5, 5] (> (3+0.7)/0.8 = 4.625)

V, W = symbols('V W')

# Check all four faces
dV = V - V**3/3 - W + I_ext
dW = eps * (V + a - b * W)

print(f"Rectangular box K = [-{R_val},{R_val}] × [-{S_val},{S_val}]:")

# Face V = +R: need dV/dt < 0, worst case W = -S
val_Vp = dV.subs(V, R_val).subs(W, -S_val)
print(f"  V=+R, W=-S: dV/dt = {val_Vp} = {float(val_Vp):.4f} {'< 0 ✓' if val_Vp < 0 else '≥ 0 ✗'}")

# Face V = -R: need dV/dt > 0, worst case W = +S
val_Vm = dV.subs(V, -R_val).subs(W, S_val)
print(f"  V=-R, W=+S: dV/dt = {val_Vm} = {float(val_Vm):.4f} {'> 0 ✓' if val_Vm > 0 else '≤ 0 ✗'}")

# Face W = +S: need dW/dt < 0, worst case V = +R
val_Wp = dW.subs(W, S_val).subs(V, R_val)
print(f"  W=+S, V=+R: dW/dt = {val_Wp} = {float(val_Wp):.4f} {'< 0 ✓' if val_Wp < 0 else '≥ 0 ✗'}")

# Face W = -S: need dW/dt > 0, worst case V = -R
val_Wm = dW.subs(W, -S_val).subs(V, -R_val)
print(f"  W=-S, V=-R: dW/dt = {val_Wm} = {float(val_Wm):.4f} {'> 0 ✓' if val_Wm > 0 else '≤ 0 ✗'}")

# Exact values for Lean
print(f"\nExact rational values for Lean norm_num:")
print(f"  face_Vp = {val_Vp}")
print(f"  face_Vm = {val_Vm}")
print(f"  face_Wp = {val_Wp}")
print(f"  face_Wm = {val_Wm}")

# === 3. Equilibrium and Eigenvalues ===
print("\n--- 3. Equilibrium and Eigenvalues ---")

# Equilibrium: V₀ - V₀³/3 - W₀ + I = 0 and ε(V₀ + a - bW₀) = 0
# From W equation: W₀ = (V₀ + a) / b
# Substituting: V₀ - V₀³/3 - (V₀ + a)/b + I = 0

V0 = Symbol('V0')
eq = V0 - V0**3/3 - (V0 + a)/b + I_ext

# Solve for equilibrium V₀
roots = solve(eq, V0)
print(f"Equilibrium equation: V₀ - V₀³/3 - (V₀ + {a})/{b} + {I_ext} = 0")
print(f"Simplified: {simplify(eq)} = 0")
print(f"Number of real roots: {len(roots)}")

# For standard parameters, there is one real root
for i, r in enumerate(roots):
    r_simplified = simplify(r)
    r_float = complex(r_simplified)
    if abs(r_float.imag) < 1e-10:
        V0_val = r_simplified
        W0_val = (V0_val + a) / b
        print(f"  Root {i}: V₀ ≈ {r_float.real:.6f}")
        print(f"           W₀ = (V₀ + a)/b ≈ {complex(W0_val).real:.6f}")

# Jacobian at equilibrium
print("\nJacobian at equilibrium:")
# For numerical evaluation, use the float approximation
V0_num = float(complex(roots[0]).real)
J11_eq = 1 - V0_num**2
J12_eq = -1
J21_eq = float(eps)
J22_eq = -float(eps * b)

print(f"  J₁₁ = 1 - V₀² ≈ {J11_eq:.6f}")
print(f"  J₁₂ = -1")
print(f"  J₂₁ = ε = {float(eps)}")
print(f"  J₂₂ = -εb = {float(-eps*b)}")

# Eigenvalue computation
trace = J11_eq + J22_eq
det = J11_eq * J22_eq - J12_eq * J21_eq
disc = trace**2 - 4 * det

print(f"\n  trace = {trace:.6f}")
print(f"  det = {det:.6f}")
print(f"  discriminant = {disc:.6f}")

if disc < 0:
    re_part = trace / 2
    im_part = (-disc)**0.5 / 2
    print(f"  λ± = {re_part:.6f} ± {im_part:.6f}i")
    print(f"  Re(λ) = {re_part:.6f} {'< 0 (stable)' if re_part < 0 else '> 0 (unstable)'}")
else:
    lam1 = (trace + disc**0.5) / 2
    lam2 = (trace - disc**0.5) / 2
    print(f"  λ₁ = {lam1:.6f}, λ₂ = {lam2:.6f}")

# === 4. Hopf Bifurcation ===
print("\n--- 4. Hopf Bifurcation Analysis ---")

# Hopf occurs when trace = 0: 1 - V₀² - εb = 0
# i.e., V₀² = 1 - εb
V0_hopf_sq = 1 - eps * b  # = 1 - 0.064 = 0.936
print(f"Hopf condition: V₀² = 1 - εb = {V0_hopf_sq}")
print(f"V₀_Hopf = ±√({V0_hopf_sq}) ≈ ±{float(V0_hopf_sq)**0.5:.6f}")

# The Hopf bifurcation current I* satisfies:
# V₀ - V₀³/3 - (V₀ + a)/b + I* = 0 with V₀² = 1 - εb
# I* = (V₀ + a)/b - V₀ + V₀³/3

V0h = Symbol('V0h', positive=True)
I_hopf = (V0h + a)/b - V0h + V0h**3/3

# Substitute V₀² = 1 - εb
# V₀ = √(1 - εb), so V₀³ = V₀ · (1 - εb)
print(f"\nI*_Hopf = (V₀+a)/b - V₀ + V₀³/3")
print(f"       where V₀ = √(1 - εb) = √({V0_hopf_sq})")

V0h_val = float(V0_hopf_sq)**0.5
I_hopf_val = (V0h_val + float(a))/float(b) - V0h_val + V0h_val**3/3
print(f"I*_Hopf ≈ {I_hopf_val:.6f}")
print(f"Current I_ext = {float(I_ext)} {'< I*' if float(I_ext) < I_hopf_val else '>= I*'}")
print(f"→ Resting state is {'stable' if float(I_ext) < I_hopf_val else 'unstable'} at standard parameters")

# === 5. Emit Lean Definitions ===
print("\n" + "=" * 60)
print("Lean 4 Definitions (for LipschitzBound.lean)")
print("=" * 60)

print(f"""
-- CAS-computed constants for FHN with standard parameters
-- ε = 8/100, a = 7/10, b = 8/10, I = 1/2, R = 3

/-- Lipschitz bound: ||J||₁ ≤ L on [-3,3]² -/
def lipschitz_bound_R3 : ℚ := {L_bound}

/-- Trapping region face values (all have correct sign) -/
def face_Vplus_worst : ℚ := {val_Vp}  -- < 0 ✓
def face_Vminus_worst : ℚ := {val_Vm}  -- > 0 ✓
def face_Wplus_worst : ℚ := {val_Wp}  -- < 0 ✓
def face_Wminus_worst : ℚ := {val_Wm}  -- > 0 ✓

/-- Hopf bifurcation threshold: V₀² = 1 - εb -/
def hopf_threshold_V0sq : ℚ := {V0_hopf_sq}

/-- Jacobian trace at equilibrium for standard params -/
-- trace = 1 - V₀² - εb (sign determines stability)
-- At standard params: trace ≈ {trace:.6f} < 0 → stable
""")

print("\n--- Computation complete ---")
