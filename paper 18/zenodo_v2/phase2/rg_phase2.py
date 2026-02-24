#!/usr/bin/env python3
"""
Fermion Mass Hierarchy: Phase 2 Investigations
================================================
Five substantive alternatives not tested in Phase 1.

Author: Paul Chun-Kit Lee
Date: February 2026
Status: Exploratory computation — Phase 2

Investigations:
  1. Two-loop beta functions — new QFPs at higher loop order?
  2. Large step-size discrete dynamics — bifurcation structure?
  3. Ratio-space fixed points — QFPs for y_b/y_t, y_τ/y_t?
  4. Threshold-corrected piecewise RG — self-consistency?
  5. Koide phase dynamics in circulant parameterization

Dependencies: numpy, scipy, matplotlib
"""

import warnings
warnings.filterwarnings('ignore', category=RuntimeWarning)

import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import os
import sys
import time

# Force unbuffered output
sys.stdout.reconfigure(line_buffering=True)

# ============================================================================
# CONSTANTS & SETUP (reused from Phase 1)
# ============================================================================

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PLOT_DIR = os.path.join(SCRIPT_DIR, 'plots_phase2')
os.makedirs(PLOT_DIR, exist_ok=True)

# Gauge couplings at M_Z (MSbar scheme)
g1_MZ = 0.3574    # U(1)_Y, GUT normalized
g2_MZ = 0.6518    # SU(2)_L
g3_MZ = 1.221     # SU(3)_C

v = 246.22  # Higgs VEV (GeV)

# Pole masses (PDG 2024) in GeV
MASSES = {
    't': 172.57, 'b': 4.18, 'tau': 1.777,
    'c': 1.27, 's': 0.0934, 'mu': 0.10566,
    'u': 0.00216, 'd': 0.00467, 'e': 0.000511,
}

# Tree-level Yukawa couplings: y_f = sqrt(2) * m_f / v
YUKAWA_MZ = {f: np.sqrt(2) * m / v for f, m in MASSES.items()}

# Scale range
mu_EW = 91.1876       # GeV (M_Z)
mu_Planck = 1.22e19   # GeV
t_range = np.log(mu_Planck / mu_EW)  # ~ 39.4

FERMION_KEYS = ['t', 'b', 'tau', 'c', 's', 'mu', 'u', 'd', 'e']
_16pi2 = 16.0 * np.pi**2

print("=" * 70)
print("Fermion Mass Hierarchy: Phase 2 Investigations")
print("=" * 70)
print(f"t_range = ln(M_Planck/M_Z) = {t_range:.2f}")
print(f"Observed y_t(MZ) = {YUKAWA_MZ['t']:.4f}")
print(f"Observed y_b(MZ) = {YUKAWA_MZ['b']:.6f}")
print(f"Observed y_tau(MZ) = {YUKAWA_MZ['tau']:.6f}")
print(f"Observed r_b = y_b/y_t = {YUKAWA_MZ['b']/YUKAWA_MZ['t']:.6f}")
print(f"Observed r_tau = y_tau/y_t = {YUKAWA_MZ['tau']/YUKAWA_MZ['t']:.6f}")
print()


# ============================================================================
# BETA FUNCTIONS (from Phase 1)
# ============================================================================

def compute_betas_1loop(y, g):
    """One-loop SM beta functions for Yukawa and gauge couplings."""
    g1, g2, g3 = g
    g1sq, g2sq, g3sq = g1**2, g2**2, g3**2
    beta_y = {}
    gen_up = [('t', 'b', 'tau'), ('c', 's', 'mu'), ('u', 'd', 'e')]

    for yu_key, yd_key, ye_key in gen_up:
        yu, yd, ye_val = y[yu_key], y[yd_key], y[ye_key]
        # Up-type
        bracket = (9.0/2 * yu**2 + 3.0/2 * yd**2 + ye_val**2
                   - 8 * g3sq - 9.0/4 * g2sq - 17.0/12 * g1sq)
        beta_y[yu_key] = yu * bracket / _16pi2
        # Down-type
        bracket = (9.0/2 * yd**2 + 3.0/2 * yu**2 + ye_val**2
                   - 8 * g3sq - 9.0/4 * g2sq - 5.0/12 * g1sq)
        beta_y[yd_key] = yd * bracket / _16pi2
        # Charged lepton
        bracket = (5.0/2 * ye_val**2 + 3 * yd**2 + 3 * yu**2
                   - 9.0/4 * g2sq - 15.0/4 * g1sq)
        beta_y[ye_key] = ye_val * bracket / _16pi2

    beta_g = (
        41.0/6 * g1**3 / _16pi2,
        -19.0/6 * g2**3 / _16pi2,
        -7.0 * g3**3 / _16pi2,
    )
    return beta_y, beta_g


def compute_betas_2loop(y, g):
    """Two-loop gauge + leading two-loop Yukawa corrections."""
    g1, g2, g3 = g
    if abs(g1) > 50 or abs(g2) > 50 or abs(g3) > 50:
        return compute_betas_1loop(y, g)
    for f in y:
        if abs(y[f]) > 50:
            return compute_betas_1loop(y, g)
    g1sq, g2sq, g3sq = g1**2, g2**2, g3**2

    b1, b2, b3 = 41.0/6, -19.0/6, -7.0
    B = np.array([
        [199.0/18,  9.0/2,  44.0/3],
        [3.0/2,     35.0/6, 12.0],
        [11.0/18,   9.0/2,  -26.0],
    ])

    Y_trace_u = sum(y[f]**2 for f in ['t', 'c', 'u'])
    Y_trace_d = sum(y[f]**2 for f in ['b', 's', 'd'])
    Y_trace_e = sum(y[f]**2 for f in ['tau', 'mu', 'e'])

    C1_Y = 17.0/6 * Y_trace_u + 5.0/6 * Y_trace_d + 5.0/2 * Y_trace_e
    C2_Y = 3.0/2 * Y_trace_u + 3.0/2 * Y_trace_d + 1.0/2 * Y_trace_e
    C3_Y = 2.0 * Y_trace_u + 2.0 * Y_trace_d

    g_vec = np.array([g1sq, g2sq, g3sq])
    beta_g1 = g1**3 / _16pi2 * (b1 + (B[0] @ g_vec - C1_Y) / _16pi2)
    beta_g2 = g2**3 / _16pi2 * (b2 + (B[1] @ g_vec - C2_Y) / _16pi2)
    beta_g3 = g3**3 / _16pi2 * (b3 + (B[2] @ g_vec - C3_Y) / _16pi2)
    beta_g = (beta_g1, beta_g2, beta_g3)

    beta_y = {}
    gen_up = [('t', 'b', 'tau'), ('c', 's', 'mu'), ('u', 'd', 'e')]
    for yu_key, yd_key, ye_key in gen_up:
        yu, yd, ye_val = y[yu_key], y[yd_key], y[ye_key]

        bracket_1L_u = (9.0/2 * yu**2 + 3.0/2 * yd**2 + ye_val**2
                        - 8 * g3sq - 9.0/4 * g2sq - 17.0/12 * g1sq)
        bracket_2L_u = (
            -12 * yu**4 + 4 * yu**2 * yd**2 - yd**4
            + (223.0/4 + 135.0/4) * g3sq * yu**2
            - 108 * g3**4 + 9 * g3sq * g2sq + 19.0/9 * g3sq * g1sq
            + (225.0/16) * g2**4 + 131.0/16 * g2sq * g1sq
            + 2375.0/144 * g1**4
        ) / _16pi2
        beta_y[yu_key] = yu * (bracket_1L_u + bracket_2L_u) / _16pi2

        bracket_1L_d = (9.0/2 * yd**2 + 3.0/2 * yu**2 + ye_val**2
                        - 8 * g3sq - 9.0/4 * g2sq - 5.0/12 * g1sq)
        bracket_2L_d = (
            -12 * yd**4 + 4 * yd**2 * yu**2 - yu**4
            + (223.0/4 + 135.0/4) * g3sq * yd**2
            - 108 * g3**4 + 9 * g3sq * g2sq + 31.0/9 * g3sq * g1sq
            + (225.0/16) * g2**4 + 175.0/48 * g2sq * g1sq
            + 1435.0/144 * g1**4
        ) / _16pi2
        beta_y[yd_key] = yd * (bracket_1L_d + bracket_2L_d) / _16pi2

        bracket_1L_e = (5.0/2 * ye_val**2 + 3 * yd**2 + 3 * yu**2
                        - 9.0/4 * g2sq - 15.0/4 * g1sq)
        bracket_2L_e = (
            -12 * ye_val**4 + 4 * ye_val**2 * yd**2
            + (225.0/16) * g2**4 + 25.0/16 * g2sq * g1sq
            + 1875.0/144 * g1**4
        ) / _16pi2
        beta_y[ye_key] = ye_val * (bracket_1L_e + bracket_2L_e) / _16pi2

    all_vals = np.array(list(beta_y.values()) + list(beta_g))
    if not np.all(np.isfinite(all_vals)):
        return compute_betas_1loop(y, g)
    return beta_y, beta_g


# ============================================================================
# RG EVOLUTION INFRASTRUCTURE (from Phase 1)
# ============================================================================

def rg_step_euler(y, g, dt, beta_func):
    """One Euler step."""
    beta_y, beta_g = beta_func(y, g)
    y_new = {f: y[f] + beta_y[f] * dt for f in y}
    g_new = tuple(g[i] + beta_g[i] * dt for i in range(3))
    return y_new, g_new


def rg_step_rk4(y, g, dt, beta_func):
    """Fourth-order Runge-Kutta step."""
    k1_y, k1_g = beta_func(y, g)
    y2 = {f: y[f] + 0.5*dt*k1_y[f] for f in y}
    g2 = tuple(g[i] + 0.5*dt*k1_g[i] for i in range(3))
    k2_y, k2_g = beta_func(y2, g2)
    y3 = {f: y[f] + 0.5*dt*k2_y[f] for f in y}
    g3 = tuple(g[i] + 0.5*dt*k2_g[i] for i in range(3))
    k3_y, k3_g = beta_func(y3, g3)
    y4 = {f: y[f] + dt*k3_y[f] for f in y}
    g4 = tuple(g[i] + dt*k3_g[i] for i in range(3))
    k4_y, k4_g = beta_func(y4, g4)
    y_new = {f: y[f] + dt/6*(k1_y[f] + 2*k2_y[f] + 2*k3_y[f] + k4_y[f]) for f in y}
    g_new = tuple(g[i] + dt/6*(k1_g[i] + 2*k2_g[i] + 2*k3_g[i] + k4_g[i]) for i in range(3))
    return y_new, g_new


def evolve(y_init, g_init, t_start, t_end, N_steps, step_func, beta_func):
    """Evolve RG from t_start to t_end in N_steps discrete steps."""
    dt = (t_end - t_start) / N_steps
    y, g = y_init.copy(), tuple(g_init)
    trajectory = [(t_start, y.copy(), tuple(g))]
    for step in range(N_steps):
        y, g = step_func(y, g, dt, beta_func)
        for f in y:
            if y[f] < 0:
                y[f] = 0.0
            if y[f] > 100:
                y[f] = 100.0
        t_current = t_start + (step + 1) * dt
        trajectory.append((t_current, y.copy(), tuple(g)))
    return y, g, trajectory


# ============================================================================
# SETUP: Planck-scale gauge couplings
# ============================================================================

print("Evolving gauge couplings from M_Z to Planck scale...")
g_MZ = (g1_MZ, g2_MZ, g3_MZ)
y_MZ_full = YUKAWA_MZ.copy()
_, g_Planck, _ = evolve(y_MZ_full, g_MZ, 0, t_range, 10000,
                        rg_step_rk4, compute_betas_1loop)
print(f"g_Planck: g1={g_Planck[0]:.4f}, g2={g_Planck[1]:.4f}, g3={g_Planck[2]:.4f}")

# Also get Planck-scale Yukawas by backward evolution from observed EW values
y_Planck_obs, _, _ = evolve(YUKAWA_MZ.copy(), g_MZ, 0, t_range, 10000,
                            rg_step_rk4, compute_betas_1loop)
print(f"y_t(Planck) from backward evolution: {y_Planck_obs['t']:.4f}")
print(f"y_b(Planck) from backward evolution: {y_Planck_obs['b']:.6f}")
print()

# Observed ratios at EW
r_b_obs = YUKAWA_MZ['b'] / YUKAWA_MZ['t']
r_tau_obs = YUKAWA_MZ['tau'] / YUKAWA_MZ['t']


# ============================================================================
# INVESTIGATION 1: Two-Loop Beta Functions — New QFPs?
# ============================================================================

def investigation_1():
    """Two-loop vs one-loop: compare y_b/y_t distributions."""
    print("=" * 70)
    print("INVESTIGATION 1: Two-Loop Beta Functions — New QFPs?")
    print("=" * 70)
    t0 = time.time()

    N_samples = 1000
    N_steps = 1000
    np.random.seed(42)

    rb_1loop = []
    rb_2loop = []
    yt_1loop = []
    yt_2loop = []

    for i in range(N_samples):
        if i % 200 == 0:
            print(f"  Sample {i}/{N_samples}...")

        # Random initial Yukawas at Planck scale
        y_init = {}
        for f in FERMION_KEYS:
            y_init[f] = 10**np.random.uniform(-3, 1)  # 0.001 to 10

        # One-loop
        y_1L, _, _ = evolve(y_init.copy(), g_Planck, t_range, 0, N_steps,
                            rg_step_rk4, compute_betas_1loop)
        if y_1L['t'] > 0.01 and y_1L['b'] > 1e-8:
            rb_1loop.append(y_1L['b'] / y_1L['t'])
            yt_1loop.append(y_1L['t'])

        # Two-loop
        y_2L, _, _ = evolve(y_init.copy(), g_Planck, t_range, 0, N_steps,
                            rg_step_rk4, compute_betas_2loop)
        if y_2L['t'] > 0.01 and y_2L['b'] > 1e-8:
            rb_2loop.append(y_2L['b'] / y_2L['t'])
            yt_2loop.append(y_2L['t'])

    rb_1loop = np.array(rb_1loop)
    rb_2loop = np.array(rb_2loop)

    std_1L = np.std(rb_1loop) if len(rb_1loop) > 0 else np.inf
    std_2L = np.std(rb_2loop) if len(rb_2loop) > 0 else np.inf
    mean_1L = np.mean(rb_1loop) if len(rb_1loop) > 0 else np.nan
    mean_2L = np.mean(rb_2loop) if len(rb_2loop) > 0 else np.nan
    reduction = (1 - std_2L / std_1L) * 100 if std_1L > 0 else 0

    print(f"\n  One-loop y_b/y_t: mean={mean_1L:.4f}, std={std_1L:.4f} ({len(rb_1loop)} samples)")
    print(f"  Two-loop y_b/y_t: mean={mean_2L:.4f}, std={std_2L:.4f} ({len(rb_2loop)} samples)")
    print(f"  Observed y_b/y_t = {r_b_obs:.6f}")
    print(f"  Std reduction: {reduction:.1f}%")

    # Also compare y_t QFP
    yt_std_1L = np.std(yt_1loop) if len(yt_1loop) > 0 else np.inf
    yt_std_2L = np.std(yt_2loop) if len(yt_2loop) > 0 else np.inf
    yt_mean_1L = np.mean(yt_1loop) if len(yt_1loop) > 0 else np.nan
    yt_mean_2L = np.mean(yt_2loop) if len(yt_2loop) > 0 else np.nan
    print(f"  One-loop y_t QFP: mean={yt_mean_1L:.4f}, std={yt_std_1L:.4f}")
    print(f"  Two-loop y_t QFP: mean={yt_mean_2L:.4f}, std={yt_std_2L:.4f}")

    success = "YES" if reduction > 50 else ("PARTIAL" if reduction > 20 else "NO")

    # Plot
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    axes[0].hist(rb_1loop, bins=50, alpha=0.7, color='blue', label='One-loop')
    axes[0].hist(rb_2loop, bins=50, alpha=0.7, color='red', label='Two-loop')
    axes[0].axvline(r_b_obs, color='green', linestyle='--', linewidth=2,
                    label=f'Observed = {r_b_obs:.4f}')
    axes[0].set_xlabel('y_b / y_t at EW scale')
    axes[0].set_ylabel('Count')
    axes[0].set_title('y_b/y_t Distribution: 1-loop vs 2-loop')
    axes[0].legend(fontsize=8)
    axes[0].set_xlim(0, min(2.0, np.percentile(rb_1loop, 99) * 1.5) if len(rb_1loop) > 0 else 2.0)

    axes[1].hist(yt_1loop, bins=50, alpha=0.7, color='blue', label='One-loop')
    axes[1].hist(yt_2loop, bins=50, alpha=0.7, color='red', label='Two-loop')
    axes[1].axvline(YUKAWA_MZ['t'], color='green', linestyle='--', linewidth=2,
                    label=f'Observed = {YUKAWA_MZ["t"]:.3f}')
    axes[1].set_xlabel('y_t at EW scale')
    axes[1].set_ylabel('Count')
    axes[1].set_title('y_t QFP: 1-loop vs 2-loop')
    axes[1].legend(fontsize=8)

    plt.tight_layout()
    fname = os.path.join(PLOT_DIR, 'inv1_two_loop_comparison.png')
    fig.savefig(fname, dpi=150, bbox_inches='tight')
    plt.close(fig)

    print(f"\n=== Investigation 1: Two-Loop QFPs ===")
    print(f"Key finding: std reduction = {reduction:.1f}%")
    print(f"Success criterion met: {success}")
    print(f"Plot saved: inv1_two_loop_comparison.png")
    print(f"Runtime: {time.time()-t0:.1f}s")
    return success


# ============================================================================
# INVESTIGATION 2: Large Step-Size Discrete Dynamics
# ============================================================================

def investigation_2():
    """Euler map at varying step counts — bifurcation structure?"""
    print("\n" + "=" * 70)
    print("INVESTIGATION 2: Large Step-Size Discrete Dynamics")
    print("=" * 70)
    t0 = time.time()

    N_values = [3, 5, 7, 10, 15, 20, 30, 50, 100, 200, 500]

    # Use observed Planck-scale values as starting point
    y_init = y_Planck_obs.copy()

    yt_results = []
    yb_results = []
    ytau_results = []
    rb_results = []
    rtau_results = []

    # Also compute ODE reference
    y_ode, _, _ = evolve(y_init.copy(), g_Planck, t_range, 0, 10000,
                         rg_step_rk4, compute_betas_1loop)
    yt_ode = y_ode['t']
    rb_ode = y_ode['b'] / y_ode['t'] if y_ode['t'] > 0 else np.nan
    rtau_ode = y_ode['tau'] / y_ode['t'] if y_ode['t'] > 0 else np.nan

    for N in N_values:
        y_f, _, _ = evolve(y_init.copy(), g_Planck, t_range, 0, N,
                           rg_step_euler, compute_betas_1loop)
        yt_results.append(y_f['t'])
        yb_results.append(y_f['b'])
        ytau_results.append(y_f['tau'])
        rb = y_f['b'] / y_f['t'] if y_f['t'] > 0 else np.nan
        rtau = y_f['tau'] / y_f['t'] if y_f['t'] > 0 else np.nan
        rb_results.append(rb)
        rtau_results.append(rtau)
        print(f"  N={N:4d}: y_t={y_f['t']:.4f}, y_b={y_f['b']:.6f}, "
              f"r_b={rb:.6f}, r_tau={rtau:.6f}")

    # Check for non-monotone behavior in ratios
    rb_arr = np.array(rb_results)
    rtau_arr = np.array(rtau_results)
    # Non-monotone = at least one pair where ratio increases then decreases (or vice versa)
    rb_diffs = np.diff(rb_arr)
    rtau_diffs = np.diff(rtau_arr)
    rb_sign_changes = np.sum(rb_diffs[:-1] * rb_diffs[1:] < 0)
    rtau_sign_changes = np.sum(rtau_diffs[:-1] * rtau_diffs[1:] < 0)
    nonmonotone = rb_sign_changes > 0 or rtau_sign_changes > 0

    print(f"\n  ODE reference: y_t={yt_ode:.4f}, r_b={rb_ode:.6f}, r_tau={rtau_ode:.6f}")
    print(f"  r_b sign changes in diffs: {rb_sign_changes}")
    print(f"  r_tau sign changes in diffs: {rtau_sign_changes}")
    print(f"  Non-monotone structure: {'YES' if nonmonotone else 'NO'}")

    # Bifurcation diagram: fixed y_t(Planck) = 3.0
    print("\n  Computing bifurcation diagram...")
    N_bif = list(range(2, 101))
    yt_bif = []
    for N in N_bif:
        y_bif_init = {f: 0.01 for f in FERMION_KEYS}
        y_bif_init['t'] = 3.0
        y_f, _, _ = evolve(y_bif_init, g_Planck, t_range, 0, N,
                           rg_step_euler, compute_betas_1loop)
        yt_bif.append(y_f['t'])

    # Plot 1: Couplings vs N
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    axes[0].semilogx(N_values, yt_results, 'bo-', label='y_t (Euler)')
    axes[0].axhline(yt_ode, color='r', linestyle='--', label=f'ODE limit = {yt_ode:.3f}')
    axes[0].axhline(YUKAWA_MZ['t'], color='g', linestyle=':', label=f'Observed = {YUKAWA_MZ["t"]:.3f}')
    axes[0].set_xlabel('N (step count)')
    axes[0].set_ylabel('y_t(EW)')
    axes[0].set_title('y_t(EW) vs Step Count N')
    axes[0].legend(fontsize=8)
    axes[0].grid(True, alpha=0.3)

    axes[1].semilogx(N_values, rb_results, 'bo-', label='r_b (Euler)')
    axes[1].axhline(rb_ode, color='r', linestyle='--', label=f'ODE = {rb_ode:.5f}')
    axes[1].axhline(r_b_obs, color='g', linestyle=':', label=f'Observed = {r_b_obs:.5f}')
    axes[1].semilogx(N_values, rtau_results, 'rs-', label='r_τ (Euler)')
    axes[1].axhline(rtau_ode, color='orange', linestyle='--', alpha=0.7)
    axes[1].axhline(r_tau_obs, color='purple', linestyle=':', alpha=0.7)
    axes[1].set_xlabel('N (step count)')
    axes[1].set_ylabel('Mass ratio')
    axes[1].set_title('Mass Ratios vs Step Count N')
    axes[1].legend(fontsize=7)
    axes[1].grid(True, alpha=0.3)

    axes[2].plot(N_bif, yt_bif, 'k.', markersize=2)
    axes[2].set_xlabel('N (step count)')
    axes[2].set_ylabel('y_t(final)')
    axes[2].set_title('Bifurcation Diagram (y_t(Planck)=3.0)')
    axes[2].grid(True, alpha=0.3)

    plt.tight_layout()
    fname = os.path.join(PLOT_DIR, 'inv2_coupling_vs_N.png')
    fig.savefig(fname, dpi=150, bbox_inches='tight')
    plt.close(fig)

    success = "YES" if nonmonotone else "NO"
    print(f"\n=== Investigation 2: Large Step-Size Dynamics ===")
    print(f"Key finding: Non-monotone structure = {'YES' if nonmonotone else 'NO'}")
    print(f"Success criterion met: {success}")
    print(f"Plot saved: inv2_coupling_vs_N.png")
    print(f"Runtime: {time.time()-t0:.1f}s")
    return success


# ============================================================================
# INVESTIGATION 3: Ratio-Space Fixed Points
# ============================================================================

def investigation_3():
    """Ratio-space QFPs for r_b = y_b/y_t, r_tau = y_tau/y_t."""
    print("\n" + "=" * 70)
    print("INVESTIGATION 3: Ratio-Space Fixed Points")
    print("=" * 70)
    t0 = time.time()

    N_steps = 1000

    # Scan r_b(Planck) for various y_t(Planck)
    rb_planck_vals = np.logspace(-4, 0, 50)  # 10^-4 to 1
    yt_planck_tests = [0.5, 1.0, 2.0, 5.0]

    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    # Plot 1: r_b(EW) vs r_b(Planck)
    for yt_p in yt_planck_tests:
        rb_ew_vals = []
        for rb_p in rb_planck_vals:
            y_init = {f: 0.001 for f in FERMION_KEYS}
            y_init['t'] = yt_p
            y_init['b'] = rb_p * yt_p
            y_init['tau'] = 0.01 * yt_p  # small tau
            y_f, _, _ = evolve(y_init, g_Planck, t_range, 0, N_steps,
                               rg_step_rk4, compute_betas_1loop)
            rb = y_f['b'] / y_f['t'] if y_f['t'] > 0.001 else np.nan
            rb_ew_vals.append(rb)
        axes[0].semilogx(rb_planck_vals, rb_ew_vals, '.-', markersize=3,
                         label=f'y_t(Pl)={yt_p}')

    axes[0].axhline(r_b_obs, color='green', linestyle='--', linewidth=2,
                    label=f'Observed = {r_b_obs:.4f}')
    axes[0].set_xlabel('r_b(Planck)')
    axes[0].set_ylabel('r_b(EW)')
    axes[0].set_title('r_b Convergence')
    axes[0].legend(fontsize=7)
    axes[0].grid(True, alpha=0.3)

    # Plot 2: r_tau(EW) vs r_tau(Planck)
    rtau_planck_vals = np.logspace(-4, 0, 50)
    for yt_p in yt_planck_tests:
        rtau_ew_vals = []
        for rtau_p in rtau_planck_vals:
            y_init = {f: 0.001 for f in FERMION_KEYS}
            y_init['t'] = yt_p
            y_init['b'] = 0.02 * yt_p  # small b
            y_init['tau'] = rtau_p * yt_p
            y_f, _, _ = evolve(y_init, g_Planck, t_range, 0, N_steps,
                               rg_step_rk4, compute_betas_1loop)
            rtau = y_f['tau'] / y_f['t'] if y_f['t'] > 0.001 else np.nan
            rtau_ew_vals.append(rtau)
        axes[1].semilogx(rtau_planck_vals, rtau_ew_vals, '.-', markersize=3,
                         label=f'y_t(Pl)={yt_p}')

    axes[1].axhline(r_tau_obs, color='green', linestyle='--', linewidth=2,
                    label=f'Observed = {r_tau_obs:.4f}')
    axes[1].set_xlabel('r_τ(Planck)')
    axes[1].set_ylabel('r_τ(EW)')
    axes[1].set_title('r_τ Convergence')
    axes[1].legend(fontsize=7)
    axes[1].grid(True, alpha=0.3)

    # Plot 3: 2D ratio-space portrait at y_t = QFP value (~2.0)
    print("  Computing 2D ratio-space portrait...")
    yt_fixed = 2.0
    n_grid = 30
    rb_grid = np.logspace(-4, 0, n_grid)
    rtau_grid = np.logspace(-4, 0, n_grid)
    rb_ew_2d = np.zeros((n_grid, n_grid))
    rtau_ew_2d = np.zeros((n_grid, n_grid))

    for i, rb_p in enumerate(rb_grid):
        if i % 10 == 0:
            print(f"  Grid row {i}/{n_grid}...")
        for j, rtau_p in enumerate(rtau_grid):
            y_init = {f: 0.001 for f in FERMION_KEYS}
            y_init['t'] = yt_fixed
            y_init['b'] = rb_p * yt_fixed
            y_init['tau'] = rtau_p * yt_fixed
            y_f, _, _ = evolve(y_init, g_Planck, t_range, 0, N_steps,
                               rg_step_rk4, compute_betas_1loop)
            rb_ew_2d[i, j] = y_f['b'] / y_f['t'] if y_f['t'] > 0.001 else np.nan
            rtau_ew_2d[i, j] = y_f['tau'] / y_f['t'] if y_f['t'] > 0.001 else np.nan

    # Scatter the endpoints
    axes[2].scatter(rb_ew_2d.flatten(), rtau_ew_2d.flatten(),
                    c='blue', alpha=0.3, s=5)
    axes[2].axvline(r_b_obs, color='green', linestyle='--', alpha=0.7)
    axes[2].axhline(r_tau_obs, color='green', linestyle='--', alpha=0.7)
    axes[2].plot(r_b_obs, r_tau_obs, 'r*', markersize=15, label='Observed')
    axes[2].set_xlabel('r_b(EW)')
    axes[2].set_ylabel('r_τ(EW)')
    axes[2].set_title(f'2D Ratio-Space Portrait (y_t(Pl)={yt_fixed})')
    axes[2].legend(fontsize=8)
    axes[2].grid(True, alpha=0.3)
    # Set reasonable limits
    rb_flat = rb_ew_2d.flatten()
    rtau_flat = rtau_ew_2d.flatten()
    rb_valid = rb_flat[np.isfinite(rb_flat)]
    rtau_valid = rtau_flat[np.isfinite(rtau_flat)]
    if len(rb_valid) > 0:
        axes[2].set_xlim(0, min(1.0, np.percentile(rb_valid, 95) * 2))
    if len(rtau_valid) > 0:
        axes[2].set_ylim(0, min(1.0, np.percentile(rtau_valid, 95) * 2))

    plt.tight_layout()
    fname = os.path.join(PLOT_DIR, 'inv3_ratio_plane.png')
    fig.savefig(fname, dpi=150, bbox_inches='tight')
    plt.close(fig)

    # Check convergence: what fraction of r_b(EW) values are within 50% of observed?
    rb_flat = rb_ew_2d.flatten()
    rb_valid = rb_flat[np.isfinite(rb_flat)]
    if len(rb_valid) > 0:
        rb_converged = np.sum(np.abs(rb_valid - r_b_obs) / r_b_obs < 0.5)
        rb_frac = rb_converged / len(rb_valid)
    else:
        rb_frac = 0

    # Check spread of r_b(EW) — if tight, there's a QFP
    rb_std = np.std(rb_valid) if len(rb_valid) > 0 else np.inf
    rb_mean = np.mean(rb_valid) if len(rb_valid) > 0 else np.nan
    cv = rb_std / rb_mean if rb_mean > 0 else np.inf  # coefficient of variation

    print(f"\n  r_b(EW) statistics: mean={rb_mean:.6f}, std={rb_std:.6f}, CV={cv:.3f}")
    print(f"  Fraction within 50% of observed: {rb_frac:.3f}")
    print(f"  Observed r_b = {r_b_obs:.6f}")

    success = "YES" if rb_frac > 0.2 else ("PARTIAL" if cv < 0.5 else "NO")
    print(f"\n=== Investigation 3: Ratio-Space Fixed Points ===")
    print(f"Key finding: r_b(EW) CV={cv:.3f}, convergence fraction={rb_frac:.3f}")
    print(f"Success criterion met: {success}")
    print(f"Plot saved: inv3_ratio_plane.png")
    print(f"Runtime: {time.time()-t0:.1f}s")
    return success


# ============================================================================
# INVESTIGATION 4: Threshold-Corrected Piecewise RG
# ============================================================================

def compute_betas_piecewise(y, g, mu_scale, active_masses):
    """One-loop beta functions with threshold corrections.
    Only active fermions contribute to loops."""
    g1, g2, g3 = g
    g1sq, g2sq, g3sq = g1**2, g2**2, g3**2
    beta_y = {}

    gen_up = [('t', 'b', 'tau'), ('c', 's', 'mu'), ('u', 'd', 'e')]

    # Count active quarks and leptons for gauge running
    n_active_quarks = sum(1 for f in ['t', 'c', 'u', 'b', 's', 'd']
                         if mu_scale > active_masses.get(f, 0))
    n_active_leptons = sum(1 for f in ['tau', 'mu', 'e']
                          if mu_scale > active_masses.get(f, 0))

    # Gauge beta coefficients with variable flavor number
    # b3 = -11 + 2/3 * n_f (n_f = number of active quark flavors, counted as pairs/2)
    # Standard: b3 = -7 for n_f=6 (all quarks active)
    # n_f here is number of quark flavors (each counted once), so n_f_pairs = n_active_quarks
    b1 = 41.0/6  # This changes with active fermions but the change is small; keep approx
    b2 = -19.0/6
    b3 = -11.0 + 2.0/3 * n_active_quarks

    beta_g = (
        b1 * g1**3 / _16pi2,
        b2 * g2**3 / _16pi2,
        b3 * g3**3 / _16pi2,
    )

    for yu_key, yd_key, ye_key in gen_up:
        yu, yd, ye_val = y[yu_key], y[yd_key], y[ye_key]
        # Zero out couplings for inactive fermions
        yu_active = mu_scale > active_masses.get(yu_key, 0)
        yd_active = mu_scale > active_masses.get(yd_key, 0)
        ye_active = mu_scale > active_masses.get(ye_key, 0)

        if not yd_active:
            yd = 0.0
        if not ye_active:
            ye_val = 0.0

        if not yu_active:
            beta_y[yu_key] = 0.0
        else:
            bracket = (9.0/2 * yu**2 + 3.0/2 * yd**2 + ye_val**2
                       - 8 * g3sq - 9.0/4 * g2sq - 17.0/12 * g1sq)
            beta_y[yu_key] = yu * bracket / _16pi2

        if not yd_active:
            beta_y[yd_key] = 0.0
        else:
            bracket = (9.0/2 * yd**2 + 3.0/2 * yu**2 + ye_val**2
                       - 8 * g3sq - 9.0/4 * g2sq - 5.0/12 * g1sq)
            beta_y[yd_key] = yd * bracket / _16pi2

        if not ye_active:
            beta_y[ye_key] = 0.0
        else:
            bracket = (5.0/2 * ye_val**2 + 3 * yd**2 + 3 * yu**2
                       - 9.0/4 * g2sq - 15.0/4 * g1sq)
            beta_y[ye_key] = ye_val * bracket / _16pi2

    return beta_y, beta_g


def evolve_piecewise(y_init, g_init, masses_guess, N_steps=2000):
    """Evolve from Planck to EW with piecewise beta functions."""
    dt = t_range / N_steps
    y, g = y_init.copy(), tuple(g_init)
    for step in range(N_steps):
        t_current = t_range - step * dt  # running downward
        mu_current = mu_EW * np.exp(t_current)
        # Use default arg to capture mu_current by value
        beta_func = lambda yy, gg, mu=mu_current: compute_betas_piecewise(yy, gg, mu, masses_guess)
        y, g = rg_step_rk4(y, g, -dt, beta_func)
        for f in y:
            if y[f] < 0:
                y[f] = 0.0
            if y[f] > 100:
                y[f] = 100.0
    return y, g


def investigation_4():
    """Threshold-corrected piecewise RG with self-consistency."""
    print("\n" + "=" * 70)
    print("INVESTIGATION 4: Threshold-Corrected Piecewise RG")
    print("=" * 70)
    t0 = time.time()

    # Self-consistency: masses -> thresholds -> RG -> predicted masses -> iterate
    initial_guesses = {
        'all_1GeV': {f: 1.0 for f in FERMION_KEYS},
        'all_10GeV': {f: 10.0 for f in FERMION_KEYS},
        'all_100GeV': {f: 100.0 for f in FERMION_KEYS},
        'observed': MASSES.copy(),
    }

    n_iters = 15
    results = {}

    for label, mass_guess in initial_guesses.items():
        print(f"\n  Initial guess: {label}")
        masses_history = []
        current_masses = mass_guess.copy()

        for it in range(n_iters):
            # Evolve from Planck to EW with current mass thresholds
            y_init = {f: 0.5 for f in FERMION_KEYS}  # generic UV Yukawas
            y_init['t'] = 2.0  # near QFP

            y_ew, _ = evolve_piecewise(y_init, g_Planck, current_masses)

            # Predicted masses from Yukawa couplings
            predicted_masses = {f: y_ew[f] * v / np.sqrt(2) for f in FERMION_KEYS}

            # Record ratios
            if predicted_masses['t'] > 0:
                mt_mb = predicted_masses['t'] / max(predicted_masses['b'], 1e-10)
                mb_mtau = predicted_masses['b'] / max(predicted_masses['tau'], 1e-10)
            else:
                mt_mb = np.nan
                mb_mtau = np.nan

            masses_history.append({
                'm_t/m_b': mt_mb,
                'm_b/m_tau': mb_mtau,
                'masses': predicted_masses.copy()
            })

            if it < 5 or it == n_iters - 1:
                print(f"    Iter {it}: m_t/m_b={mt_mb:.2f}, m_b/m_tau={mb_mtau:.3f}")

            # Update mass guess for next iteration
            current_masses = predicted_masses.copy()
            # Clamp to physical range
            for f in current_masses:
                current_masses[f] = max(current_masses[f], 0.001)
                current_masses[f] = min(current_masses[f], 1000)

        results[label] = masses_history

    # Check convergence
    obs_mt_mb = MASSES['t'] / MASSES['b']
    obs_mb_mtau = MASSES['b'] / MASSES['tau']

    n_converged = 0
    for label, history in results.items():
        final = history[-1]
        mt_mb_err = abs(final['m_t/m_b'] - obs_mt_mb) / obs_mt_mb if np.isfinite(final['m_t/m_b']) else np.inf
        if mt_mb_err < 0.5:  # within 50%
            n_converged += 1
            print(f"\n  {label}: converged (m_t/m_b error = {mt_mb_err*100:.1f}%)")
        else:
            print(f"\n  {label}: not converged (m_t/m_b = {final['m_t/m_b']:.2f}, "
                  f"expected {obs_mt_mb:.2f})")

    # Plot
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    colors = ['blue', 'red', 'green', 'orange']

    for idx, (label, history) in enumerate(results.items()):
        iters = list(range(len(history)))
        mt_mb_vals = [h['m_t/m_b'] for h in history]
        mb_mtau_vals = [h['m_b/m_tau'] for h in history]

        axes[0].plot(iters, mt_mb_vals, '.-', color=colors[idx], label=label, markersize=4)
        axes[1].plot(iters, mb_mtau_vals, '.-', color=colors[idx], label=label, markersize=4)

    axes[0].axhline(obs_mt_mb, color='black', linestyle='--', label=f'Observed = {obs_mt_mb:.1f}')
    axes[0].set_xlabel('Iteration')
    axes[0].set_ylabel('m_t / m_b')
    axes[0].set_title('Self-Consistency: m_t/m_b')
    axes[0].legend(fontsize=7)
    axes[0].grid(True, alpha=0.3)
    axes[0].set_yscale('log')

    axes[1].axhline(obs_mb_mtau, color='black', linestyle='--', label=f'Observed = {obs_mb_mtau:.2f}')
    axes[1].set_xlabel('Iteration')
    axes[1].set_ylabel('m_b / m_τ')
    axes[1].set_title('Self-Consistency: m_b/m_τ')
    axes[1].legend(fontsize=7)
    axes[1].grid(True, alpha=0.3)

    plt.tight_layout()
    fname = os.path.join(PLOT_DIR, 'inv4_self_consistency.png')
    fig.savefig(fname, dpi=150, bbox_inches='tight')
    plt.close(fig)

    success = "YES" if n_converged > 1 else ("PARTIAL" if n_converged == 1 else "NO")
    print(f"\n=== Investigation 4: Threshold Self-Consistency ===")
    print(f"Key finding: {n_converged}/4 initial guesses converged")
    print(f"Success criterion met: {success}")
    print(f"Plot saved: inv4_self_consistency.png")
    print(f"Runtime: {time.time()-t0:.1f}s")
    return success


# ============================================================================
# INVESTIGATION 5: Koide Phase Dynamics
# ============================================================================

def yukawas_to_circulant(y_e, y_mu, y_tau):
    """Extract (mu, delta) from lepton Yukawa couplings via DFT."""
    s = np.array([np.sqrt(max(y_e, 0)), np.sqrt(max(y_mu, 0)), np.sqrt(max(y_tau, 0))])
    mu = np.sum(s) / 3.0
    if mu <= 1e-20:
        return None, None, None

    # DFT to extract phase
    omega = np.exp(-2j * np.pi / 3)
    Z = s[0] + s[1] * omega + s[2] * omega**2
    delta = -np.angle(Z)
    amp = np.abs(Z) / (mu * 3)  # should be sqrt(2) for exact Koide
    return mu, delta, amp


def circulant_to_yukawas(mu, delta):
    """Reconstruct Yukawa couplings from (mu, delta)."""
    s = np.array([
        mu * (1 + np.sqrt(2) * np.cos(delta + 2*np.pi*n/3))
        for n in range(3)
    ])
    # s = sqrt(y), so y = s^2, but only if s > 0
    s = np.maximum(s, 0)
    return s**2  # y_e, y_mu, y_tau


def investigation_5():
    """Koide phase dynamics in circulant parameterization."""
    print("\n" + "=" * 70)
    print("INVESTIGATION 5: Koide Phase Dynamics")
    print("=" * 70)
    t0 = time.time()

    N_steps = 1000
    delta_target = 2.0/9  # ~0.2222

    # First check: what are the observed values?
    mu_obs, delta_obs, amp_obs = yukawas_to_circulant(
        YUKAWA_MZ['e'], YUKAWA_MZ['mu'], YUKAWA_MZ['tau'])
    print(f"  Observed circulant params: mu={mu_obs:.6f}, delta={delta_obs:.4f}, amp={amp_obs:.4f}")
    print(f"  Target delta = 2/9 = {delta_target:.4f}")
    print(f"  Target amplitude = sqrt(2) = {np.sqrt(2):.4f}")

    # Plot 1: delta(EW) vs delta(Planck)
    delta_planck_vals = np.linspace(0, 2*np.pi/3, 40)
    mu_planck_tests = [1e-4, 1e-3, 1e-2, 1e-1]

    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    for mu_p in mu_planck_tests:
        delta_ew_vals = []
        for delta_p in delta_planck_vals:
            # Convert to Yukawa couplings
            ye, ymu, ytau = circulant_to_yukawas(mu_p, delta_p)

            y_init = {f: 0.001 for f in FERMION_KEYS}
            y_init['t'] = 2.0  # near QFP
            y_init['b'] = 0.05
            y_init['e'] = ye
            y_init['mu'] = ymu
            y_init['tau'] = ytau

            y_f, _, _ = evolve(y_init, g_Planck, t_range, 0, N_steps,
                               rg_step_rk4, compute_betas_1loop)

            mu_ew, delta_ew, amp_ew = yukawas_to_circulant(
                y_f['e'], y_f['mu'], y_f['tau'])
            delta_ew_vals.append(delta_ew if delta_ew is not None else np.nan)

        axes[0].plot(delta_planck_vals, delta_ew_vals, '.-', markersize=3,
                     label=f'μ(Pl)={mu_p}')

    axes[0].axhline(delta_target, color='green', linestyle='--', linewidth=2,
                    label=f'δ = 2/9 = {delta_target:.3f}')
    if delta_obs is not None:
        axes[0].axhline(delta_obs, color='red', linestyle=':', linewidth=2,
                        label=f'Observed δ = {delta_obs:.3f}')
    axes[0].set_xlabel('δ(Planck)')
    axes[0].set_ylabel('δ(EW)')
    axes[0].set_title('Koide Phase Convergence')
    axes[0].legend(fontsize=6)
    axes[0].grid(True, alpha=0.3)

    # Plot 2: Flow portrait in (mu, delta) space
    print("  Computing flow portrait...")
    n_flow = 20
    mu_grid = np.logspace(-4, -1, n_flow)
    delta_grid = np.linspace(0.01, 2*np.pi/3 - 0.01, n_flow)

    mu_ew_arr = np.zeros((n_flow, n_flow))
    delta_ew_arr = np.zeros((n_flow, n_flow))

    for i, mu_p in enumerate(mu_grid):
        if i % 5 == 0:
            print(f"  Flow grid row {i}/{n_flow}...")
        for j, delta_p in enumerate(delta_grid):
            ye, ymu, ytau = circulant_to_yukawas(mu_p, delta_p)
            y_init = {f: 0.001 for f in FERMION_KEYS}
            y_init['t'] = 2.0
            y_init['b'] = 0.05
            y_init['e'] = ye
            y_init['mu'] = ymu
            y_init['tau'] = ytau

            y_f, _, _ = evolve(y_init, g_Planck, t_range, 0, N_steps,
                               rg_step_rk4, compute_betas_1loop)
            mu_ew, delta_ew, amp_ew = yukawas_to_circulant(
                y_f['e'], y_f['mu'], y_f['tau'])
            mu_ew_arr[i, j] = mu_ew if mu_ew is not None else np.nan
            delta_ew_arr[i, j] = delta_ew if delta_ew is not None else np.nan

    # Scatter endpoints
    axes[1].scatter(delta_ew_arr.flatten(), mu_ew_arr.flatten(),
                    c='blue', alpha=0.3, s=10)
    if delta_obs is not None and mu_obs is not None:
        axes[1].plot(delta_obs, mu_obs, 'r*', markersize=15, label='Observed')
    axes[1].axvline(delta_target, color='green', linestyle='--', alpha=0.7,
                    label=f'δ = 2/9')
    axes[1].set_xlabel('δ(EW)')
    axes[1].set_ylabel('μ(EW)')
    axes[1].set_title('Flow Portrait in (μ, δ) Space')
    axes[1].legend(fontsize=8)
    axes[1].set_yscale('log')
    axes[1].grid(True, alpha=0.3)

    # Plot 3: Amplitude evolution along a trajectory near observed values
    print("  Computing amplitude evolution...")
    if mu_obs is not None and delta_obs is not None:
        ye0, ymu0, ytau0 = circulant_to_yukawas(mu_obs * 10, delta_obs)
        y_init = {f: 0.001 for f in FERMION_KEYS}
        y_init['t'] = 2.0
        y_init['b'] = 0.05
        y_init['e'] = ye0
        y_init['mu'] = ymu0
        y_init['tau'] = ytau0
        _, _, traj = evolve(y_init, g_Planck, t_range, 0, N_steps,
                            rg_step_rk4, compute_betas_1loop)

        scales = []
        amps = []
        deltas = []
        for t_val, y_snap, g_snap in traj[::10]:  # sample every 10 steps
            mu_s, delta_s, amp_s = yukawas_to_circulant(
                y_snap['e'], y_snap['mu'], y_snap['tau'])
            if mu_s is not None:
                scales.append(t_range - t_val)  # reversed: 0=Planck, t_range=EW
                amps.append(amp_s)
                deltas.append(delta_s)

        ax3 = axes[2]
        ax3_twin = ax3.twinx()
        l1 = ax3.plot(scales, amps, 'b.-', markersize=3, label='Amplitude')
        ax3.axhline(np.sqrt(2), color='blue', linestyle='--', alpha=0.5,
                     label=f'√2 = {np.sqrt(2):.3f}')
        l2 = ax3_twin.plot(scales, deltas, 'r.-', markersize=3, label='Phase δ')
        ax3_twin.axhline(delta_target, color='red', linestyle='--', alpha=0.5)
        ax3.set_xlabel('RG "time" (0=Planck, max=EW)')
        ax3.set_ylabel('Amplitude', color='blue')
        ax3_twin.set_ylabel('Phase δ', color='red')
        ax3.set_title('Koide Parameters vs Scale')
        lines = l1 + l2
        labels = [l.get_label() for l in lines]
        ax3.legend(lines, labels, fontsize=7, loc='center right')
        ax3.grid(True, alpha=0.3)

    plt.tight_layout()
    fname = os.path.join(PLOT_DIR, 'inv5_koide_phase.png')
    fig.savefig(fname, dpi=150, bbox_inches='tight')
    plt.close(fig)

    # Check convergence of delta
    delta_flat = delta_ew_arr.flatten()
    delta_valid = delta_flat[np.isfinite(delta_flat)]
    if len(delta_valid) > 0:
        delta_converged = np.sum(np.abs(delta_valid - delta_target) / delta_target < 0.2)
        delta_frac = delta_converged / len(delta_valid)
        delta_std = np.std(delta_valid)
        delta_mean = np.mean(delta_valid)
    else:
        delta_frac = 0
        delta_std = np.inf
        delta_mean = np.nan

    print(f"\n  δ(EW) statistics: mean={delta_mean:.4f}, std={delta_std:.4f}")
    print(f"  Fraction within 20% of 2/9: {delta_frac:.3f}")

    success = "YES" if delta_frac > 0.2 else ("PARTIAL" if delta_frac > 0.05 else "NO")
    print(f"\n=== Investigation 5: Koide Phase Dynamics ===")
    print(f"Key finding: δ convergence fraction = {delta_frac:.3f}")
    print(f"Success criterion met: {success}")
    print(f"Plot saved: inv5_koide_phase.png")
    print(f"Runtime: {time.time()-t0:.1f}s")
    return success


# ============================================================================
# MAIN: Run all investigations
# ============================================================================

if __name__ == '__main__':
    total_start = time.time()

    results = {}
    results['inv1'] = investigation_1()
    results['inv2'] = investigation_2()
    results['inv3'] = investigation_3()
    results['inv4'] = investigation_4()
    results['inv5'] = investigation_5()

    print("\n" + "=" * 70)
    print("PHASE 2 OVERALL SUMMARY")
    print("=" * 70)
    print(f"Investigation 1 (two-loop QFPs):       {results['inv1']}")
    print(f"Investigation 2 (large step-size):      {results['inv2']}")
    print(f"Investigation 3 (ratio-space):          {results['inv3']}")
    print(f"Investigation 4 (thresholds):           {results['inv4']}")
    print(f"Investigation 5 (Koide phase):          {results['inv5']}")

    n_success = sum(1 for v in results.values() if v in ('YES', 'PARTIAL'))
    print(f"\nNew findings beyond Phase 1: {n_success}/5")
    print(f"Total runtime: {time.time()-total_start:.1f}s")
    print(f"All plots saved to: {PLOT_DIR}")
