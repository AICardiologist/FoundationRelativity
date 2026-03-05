#!/usr/bin/env python3
"""
Verify the monodromy analysis for the genus-4 Gauss-Manin connection.

Each 2x2 block (for eigenspace W_k = span(omega_k, omega_{k+4})) has:
  M_k = c_k * [[-t/2, -1], [1, t/2]]
  c_k = (2k+1) / (4(t^2 - 4))

Compute residues at t = +2, -2, infinity and determine G_gal.
"""
import sympy as sp
from sympy import Matrix, cancel, simplify, eye, pi, I, exp, Rational as Q

t, s = sp.symbols('t s')

def analyze_block(k):
    """Analyze 2x2 block for eigenspace k."""
    c = Q(2*k+1, 1) / (4*(t**2 - 4))
    M = c * Matrix([[-t/2, -1], [1, t/2]])

    # Residue at t=2: lim_{t->2} (t-2)*M
    R_plus = Matrix([
        [cancel(sp.limit((t-2)*M[0,0], t, 2)), cancel(sp.limit((t-2)*M[0,1], t, 2))],
        [cancel(sp.limit((t-2)*M[1,0], t, 2)), cancel(sp.limit((t-2)*M[1,1], t, 2))]
    ])

    # Residue at t=-2: lim_{t->-2} (t+2)*M
    R_minus = Matrix([
        [cancel(sp.limit((t+2)*M[0,0], t, -2)), cancel(sp.limit((t+2)*M[0,1], t, -2))],
        [cancel(sp.limit((t+2)*M[1,0], t, -2)), cancel(sp.limit((t+2)*M[1,1], t, -2))]
    ])

    # Residue at infinity: change s=1/t, nabla_{d/ds} = (-1/s^2)*M(1/s)
    # Res_infty = lim_{s->0} s * (-1/s^2) * M(1/s) = -lim_{s->0} (1/s) * M(1/s)
    M_at_inv_s = M.subs(t, 1/s)
    R_infty = Matrix([
        [cancel(sp.limit(-M_at_inv_s[0,0]/s, s, 0)), cancel(sp.limit(-M_at_inv_s[0,1]/s, s, 0))],
        [cancel(sp.limit(-M_at_inv_s[1,0]/s, s, 0)), cancel(sp.limit(-M_at_inv_s[1,1]/s, s, 0))]
    ])

    # Verify Fuchs relation: R+ + R- + R_infty = 0
    fuchs = R_plus + R_minus + R_infty

    return R_plus, R_minus, R_infty, fuchs

out = open("/Users/quantmann/FoundationRelativity/paper 84/monodromy_output.txt", "w")

for k in range(4):
    Rp, Rm, Ri, F = analyze_block(k)
    out.write(f"Block k={k} (eigenvalue zeta_8^{2*k+1}):\n")
    out.write(f"  R_+2  = {Rp.tolist()},  eigenvalues = {Rp.eigenvals()}\n")
    out.write(f"  R_-2  = {Rm.tolist()},  eigenvalues = {Rm.eigenvals()}\n")
    out.write(f"  R_inf = {Ri.tolist()},  eigenvalues = {Ri.eigenvals()}\n")
    out.write(f"  Fuchs check (R+ + R- + Rinf = 0): {F == sp.zeros(2)}\n")

    # Check: is R_infty semisimple?
    ri_eigs = list(Ri.eigenvals().keys())
    out.write(f"  R_infty eigenvalues: {ri_eigs}\n")

    # Monodromy eigenvalues at infinity
    mono_eigs = [exp(2*pi*I*e) for e in ri_eigs]
    out.write(f"  T_infty eigenvalues: {[simplify(e) for e in mono_eigs]}\n")

    # R+ and R-: check nilpotent (eigenvalues both 0)
    rp_eigs = list(Rp.eigenvals().keys())
    rm_eigs = list(Rm.eigenvals().keys())
    out.write(f"  R+ nilpotent: {all(e == 0 for e in rp_eigs)}\n")
    out.write(f"  R- nilpotent: {all(e == 0 for e in rm_eigs)}\n")

    # Check if R+, R- have a common kernel/image
    ker_p = Rp.nullspace()
    ker_m = Rm.nullspace()
    img_p = Rp.columnspace()
    img_m = Rm.columnspace()
    out.write(f"  ker(R+) = {[v.T.tolist() for v in ker_p]}\n")
    out.write(f"  ker(R-) = {[v.T.tolist() for v in ker_m]}\n")

    # Common invariant line? ker(R+) = ker(R-)?
    if ker_p and ker_m:
        common = cancel(ker_p[0].dot(Matrix([[-ker_m[0][1]], [ker_m[0][0]]])))
        out.write(f"  Common kernel: {'YES' if common == 0 else 'NO'}\n")

    out.write("\n")

# Summary for stdout (minimal)
Rp0, Rm0, Ri0, F0 = analyze_block(0)
print(f"Block k=0:")
print(f"  R+2: nilpotent={all(e==0 for e in Rp0.eigenvals().keys())}")
print(f"  R-2: nilpotent={all(e==0 for e in Rm0.eigenvals().keys())}")
ri_eigs = list(Ri0.eigenvals().keys())
print(f"  Rinf eigenvalues: {ri_eigs}")
print(f"  Fuchs (R++R-+Rinf=0): {F0 == sp.zeros(2)}")
print(f"  Common kernel(R+,R-): ", end="")
kp = Rp0.nullspace()[0]
km = Rm0.nullspace()[0]
common = cancel(kp[0]*km[1] - kp[1]*km[0])
print(f"{'YES (reducible!)' if common == 0 else 'NO (irreducible) => G_gal = SL2'}")
print(f"\nFull output: paper 84/monodromy_output.txt")

out.close()
