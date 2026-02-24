#!/usr/bin/env python3
"""
Finite-Order RG Quasi-Fixed-Point Structure and the Fermion Mass Hierarchy
==========================================================================
A Numerical Investigation

Author: Paul Chun-Kit Lee
Date: February 2026
Status: Exploratory computation

Implements SM beta functions as discrete maps to investigate whether
quasi-fixed-point structure produces the observed fermion mass hierarchy.

Dependencies: numpy, scipy, matplotlib
"""

import warnings
warnings.filterwarnings('ignore', category=RuntimeWarning)

import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')  # non-interactive backend for saving plots
import matplotlib.pyplot as plt
import os
import time

# ============================================================================
# SECTION 0: CONSTANTS & SETUP
# ============================================================================

PLOT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'plots')
os.makedirs(PLOT_DIR, exist_ok=True)

# Gauge couplings at M_Z (MSbar scheme)
g1_MZ = 0.3574    # U(1)_Y, GUT normalized: g1 = sqrt(5/3) g'
g2_MZ = 0.6518    # SU(2)_L
g3_MZ = 1.221     # SU(3)_C

# Higgs VEV
v = 246.22  # GeV

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

# Observed mass ratios (for comparison)
H_OBS = np.array([
    MASSES['t'] / MASSES['b'],    # ~ 41.3
    MASSES['t'] / MASSES['tau'],  # ~ 97.1
    MASSES['t'] / MASSES['c'],    # ~ 135.9
    MASSES['t'] / MASSES['s'],    # ~ 1848
    MASSES['t'] / MASSES['mu'],   # ~ 1634
    MASSES['t'] / MASSES['u'],    # ~ 79894
    MASSES['t'] / MASSES['d'],    # ~ 36954
    MASSES['t'] / MASSES['e'],    # ~ 337710
])

FERMION_KEYS = ['t', 'b', 'tau', 'c', 's', 'mu', 'u', 'd', 'e']
RATIO_LABELS = ['t/b', 't/τ', 't/c', 't/s', 't/μ', 't/u', 't/d', 't/e']

# Prefactor
_16pi2 = 16.0 * np.pi**2

print("=" * 70)
print("Finite-Order RG Quasi-Fixed-Point Structure")
print("and the Fermion Mass Hierarchy")
print("=" * 70)
print(f"\nt_range = ln(M_Planck/M_Z) = {t_range:.2f}")
print(f"Observed y_t(MZ) = {YUKAWA_MZ['t']:.4f}")
print(f"Observed y_b(MZ) = {YUKAWA_MZ['b']:.4f}")
print(f"Observed y_tau(MZ) = {YUKAWA_MZ['tau']:.4f}")
print(f"Observed m_b/m_tau = {MASSES['b']/MASSES['tau']:.3f}")
print()


# ============================================================================
# SECTION 1: ONE-LOOP BETA FUNCTIONS
# ============================================================================

def compute_betas_1loop(y, g):
    """
    One-loop SM beta functions for Yukawa and gauge couplings.

    Parameters:
        y: dict with keys 't','b','tau','c','s','mu','u','d','e'
        g: tuple (g1, g2, g3)

    Returns:
        (beta_y, beta_g): dicts/tuple of derivatives dy/dt, dg/dt
    """
    g1, g2, g3 = g
    g1sq, g2sq, g3sq = g1**2, g2**2, g3**2

    # Trace terms: sum of squared Yukawa couplings
    # Up-type quarks contribute to Tr(Y_u^dag Y_u), etc.
    # At one-loop, each generation's Yukawa runs independently
    # (cross-generation mixing via CKM is negligible)

    beta_y = {}

    # --- Up-type quarks: t, c, u ---
    # 16pi^2 dy_u/dt = y_u [9/2 y_u^2 + 3/2 y_d^2 + y_e^2 - 8 g3^2 - 9/4 g2^2 - 17/12 g1^2]
    # where (y_u, y_d, y_e) are the Yukawa couplings of the same generation
    gen_up = [('t', 'b', 'tau'), ('c', 's', 'mu'), ('u', 'd', 'e')]
    for yu_key, yd_key, ye_key in gen_up:
        yu, yd, ye_val = y[yu_key], y[yd_key], y[ye_key]
        bracket = (9.0/2 * yu**2 + 3.0/2 * yd**2 + ye_val**2
                   - 8 * g3sq - 9.0/4 * g2sq - 17.0/12 * g1sq)
        beta_y[yu_key] = yu * bracket / _16pi2

    # --- Down-type quarks: b, s, d ---
    # 16pi^2 dy_d/dt = y_d [9/2 y_d^2 + 3/2 y_u^2 + y_e^2 - 8 g3^2 - 9/4 g2^2 - 5/12 g1^2]
    for yu_key, yd_key, ye_key in gen_up:
        yu, yd, ye_val = y[yu_key], y[yd_key], y[ye_key]
        bracket = (9.0/2 * yd**2 + 3.0/2 * yu**2 + ye_val**2
                   - 8 * g3sq - 9.0/4 * g2sq - 5.0/12 * g1sq)
        beta_y[yd_key] = yd * bracket / _16pi2

    # --- Charged leptons: tau, mu, e ---
    # 16pi^2 dy_e/dt = y_e [5/2 y_e^2 + 3 y_d^2 + 3 y_u^2 - 9/4 g2^2 - 15/4 g1^2]
    # (no g3 contribution for leptons, factor 3 for color)
    for yu_key, yd_key, ye_key in gen_up:
        yu, yd, ye_val = y[yu_key], y[yd_key], y[ye_key]
        bracket = (5.0/2 * ye_val**2 + 3 * yd**2 + 3 * yu**2
                   - 9.0/4 * g2sq - 15.0/4 * g1sq)
        beta_y[ye_key] = ye_val * bracket / _16pi2

    # --- Gauge couplings ---
    beta_g = (
        41.0/6 * g1**3 / _16pi2,
        -19.0/6 * g2**3 / _16pi2,
        -7.0 * g3**3 / _16pi2,
    )

    return beta_y, beta_g


# ============================================================================
# SECTION 2: TWO-LOOP BETA FUNCTIONS
# ============================================================================

def compute_betas_2loop(y, g):
    """
    Two-loop SM beta functions for gauge and Yukawa couplings.

    Gauge: two-loop from standard SM coefficients.
    Yukawa: one-loop Yukawa + two-loop gauge contributions.

    Reference: Luo, Wang & Xiao, Phys. Rev. D 67, 065019 (2003).
    For this exploratory computation, we implement the dominant two-loop
    gauge corrections and the leading two-loop Yukawa corrections.
    """
    g1, g2, g3 = g
    # Guard against overflow: if any coupling is too large, fall back to 1-loop
    if abs(g1) > 50 or abs(g2) > 50 or abs(g3) > 50:
        return compute_betas_1loop(y, g)
    for f in y:
        if abs(y[f]) > 50:
            return compute_betas_1loop(y, g)
    g1sq, g2sq, g3sq = g1**2, g2**2, g3**2

    # --- Two-loop gauge beta functions ---
    # dg_i/dt = b_i g_i^3/(16pi^2) + g_i^3/(16pi^2)^2 * [sum_j B_ij g_j^2 - C_i*Y_contrib]

    # One-loop coefficients
    b1, b2, b3 = 41.0/6, -19.0/6, -7.0

    # Two-loop gauge-gauge coefficients B_ij (SM with n_g=3 generations)
    # From Machacek & Vaughn 1984; Luo et al 2003
    B = np.array([
        [199.0/18,  9.0/2,  44.0/3],   # B_1j
        [3.0/2,     35.0/6, 12.0],      # B_2j
        [11.0/18,   9.0/2,  -26.0],     # B_3j
    ])

    # Yukawa contributions to two-loop gauge running
    # C_i * Tr(Y_u^dag Y_u + Y_d^dag Y_d + Y_e^dag Y_e)
    # Simplified: dominant contribution from top Yukawa
    yt2 = y['t']**2
    yb2 = y['b']**2
    ytau2 = y['tau']**2

    # Yukawa trace contributions to gauge betas
    # For U(1): C_u = 17/6, C_d = 5/6, C_e = 5/2 (per generation, with color)
    # For SU(2): C_u = 3/2, C_d = 3/2, C_e = 1/2
    # For SU(3): C_u = 2, C_d = 2, C_e = 0
    # Summing over 3 generations (dominant = 3rd gen):
    Y_trace_u = sum(y[f]**2 for f in ['t', 'c', 'u'])  # Tr(Y_u^dag Y_u) ~ 3 * y_t^2
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

    # --- Yukawa: use one-loop structure + two-loop gauge corrections ---
    # The dominant two-loop correction to Yukawa couplings comes from
    # gauge-Yukawa mixing terms. We add the leading O(y*g^4) corrections.

    beta_y = {}

    gen_up = [('t', 'b', 'tau'), ('c', 's', 'mu'), ('u', 'd', 'e')]

    for yu_key, yd_key, ye_key in gen_up:
        yu, yd, ye_val = y[yu_key], y[yd_key], y[ye_key]

        # One-loop bracket for up-type
        bracket_1L_u = (9.0/2 * yu**2 + 3.0/2 * yd**2 + ye_val**2
                        - 8 * g3sq - 9.0/4 * g2sq - 17.0/12 * g1sq)

        # Two-loop gauge correction for up-type quarks (dominant terms)
        # From Luo et al 2003, leading O(g^4) corrections
        bracket_2L_u = (
            -12 * yu**4 + 4 * yu**2 * yd**2 - yd**4
            + (223.0/4 + 135.0/4) * g3sq * yu**2  # QCD enhancement
            - 108 * g3**4 + 9 * g3sq * g2sq + 19.0/9 * g3sq * g1sq
            + (225.0/16) * g2**4 + 131.0/16 * g2sq * g1sq
            + 2375.0/144 * g1**4
        ) / _16pi2

        beta_y[yu_key] = yu * (bracket_1L_u + bracket_2L_u) / _16pi2

        # One-loop bracket for down-type
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

        # One-loop bracket for charged leptons
        bracket_1L_e = (5.0/2 * ye_val**2 + 3 * yd**2 + 3 * yu**2
                        - 9.0/4 * g2sq - 15.0/4 * g1sq)

        bracket_2L_e = (
            -12 * ye_val**4 + 4 * ye_val**2 * yd**2
            + (225.0/16) * g2**4 + 25.0/16 * g2sq * g1sq
            + 1875.0/144 * g1**4
        ) / _16pi2

        beta_y[ye_key] = ye_val * (bracket_1L_e + bracket_2L_e) / _16pi2

    # NaN safety: if any beta is NaN/inf, return zeros (safe fallback)
    all_vals = np.array(list(beta_y.values()) + list(beta_g))
    if not np.all(np.isfinite(all_vals)):
        return compute_betas_1loop(y, g)

    return beta_y, beta_g


# ============================================================================
# SECTION 3: RG STEP FUNCTIONS (Euler, RK4, scipy)
# ============================================================================

def _y_to_array(y):
    """Convert dict to array in canonical order."""
    return np.array([y[k] for k in FERMION_KEYS])

def _array_to_y(arr):
    """Convert array back to dict."""
    return {k: arr[i] for i, k in enumerate(FERMION_KEYS)}

def _pack(y, g):
    """Pack (y_dict, g_tuple) into a single array for scipy."""
    return np.concatenate([_y_to_array(y), np.array(g)])

def _unpack(state):
    """Unpack array into (y_dict, g_tuple)."""
    y = _array_to_y(state[:9])
    g = tuple(state[9:12])
    return y, g


def rg_step_euler(y, g, dt, beta_func):
    """One Euler step: y_new = y + beta*dt. This is BISH."""
    beta_y, beta_g = beta_func(y, g)
    y_new = {f: y[f] + beta_y[f] * dt for f in y}
    g_new = tuple(g[i] + beta_g[i] * dt for i in range(3))
    return y_new, g_new


def rg_step_rk4(y, g, dt, beta_func):
    """Fourth-order Runge-Kutta step. Still BISH — finite arithmetic."""
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
    """
    Evolve RG from t_start to t_end in N_steps discrete steps.

    Returns: (y_final, g_final, trajectory)
    trajectory is a list of (t, y, g) snapshots.
    """
    dt = (t_end - t_start) / N_steps
    y, g = y_init.copy(), tuple(g_init)
    trajectory = [(t_start, y.copy(), tuple(g))]

    for step in range(N_steps):
        y, g = step_func(y, g, dt, beta_func)
        # Clamp Yukawa couplings to prevent blowup
        for f in y:
            if y[f] < 0:
                y[f] = 0.0
            if y[f] > 100:
                y[f] = 100.0
        t_current = t_start + (step + 1) * dt
        trajectory.append((t_current, y.copy(), tuple(g)))

    return y, g, trajectory


def evolve_scipy(y_init, g_init, t_start, t_end, beta_func):
    """
    Evolve RG using scipy.integrate.solve_ivp (continuous flow reference).
    """
    state0 = _pack(y_init, g_init)

    def deriv(t, state):
        y, g = _unpack(state)
        beta_y, beta_g = beta_func(y, g)
        dy = np.array([beta_y[k] for k in FERMION_KEYS])
        dg = np.array(beta_g)
        return np.concatenate([dy, dg])

    sol = solve_ivp(deriv, [t_start, t_end], state0,
                    method='DOP853', rtol=1e-10, atol=1e-12,
                    max_step=0.1)

    if not sol.success:
        print(f"  WARNING: scipy solve_ivp failed: {sol.message}")

    y_final, g_final = _unpack(sol.y[:, -1])
    return y_final, g_final


def evolve_gauge_only(g_init, t_start, t_end, N_steps, beta_func):
    """Evolve only gauge couplings (for getting Planck-scale values)."""
    dt = (t_end - t_start) / N_steps
    g = list(g_init)
    for _ in range(N_steps):
        _, beta_g = beta_func({'t':0,'b':0,'tau':0,'c':0,'s':0,'mu':0,'u':0,'d':0,'e':0},
                               tuple(g))
        g = [g[i] + beta_g[i] * dt for i in range(3)]
    return tuple(g)


# ============================================================================
# Get Planck-scale gauge couplings by evolving upward from M_Z
# ============================================================================

print("Evolving gauge couplings from M_Z to Planck scale...")
g_MZ = (g1_MZ, g2_MZ, g3_MZ)

# Use a full evolution (with Yukawa) for gauge couplings at Planck
y_MZ_full = YUKAWA_MZ.copy()
_, g_Planck, _ = evolve(y_MZ_full, g_MZ, 0, t_range, 10000, rg_step_rk4, compute_betas_1loop)

print(f"Gauge couplings at Planck scale: g1={g_Planck[0]:.4f}, g2={g_Planck[1]:.4f}, g3={g_Planck[2]:.4f}")

# Round-trip test
y_dummy = {f: 0.01 for f in FERMION_KEYS}
y_dummy['t'] = 1.0
_, g_roundtrip, _ = evolve(y_dummy, g_Planck, t_range, 0, 10000, rg_step_rk4, compute_betas_1loop)
print(f"Round-trip gauge (should ~ MZ): g1={g_roundtrip[0]:.4f}, g2={g_roundtrip[1]:.4f}, g3={g_roundtrip[2]:.4f}")
print(f"Round-trip error: g1={abs(g_roundtrip[0]-g1_MZ)/g1_MZ*100:.2f}%, "
      f"g2={abs(g_roundtrip[1]-g2_MZ)/g2_MZ*100:.2f}%, "
      f"g3={abs(g_roundtrip[2]-g3_MZ)/g3_MZ*100:.2f}%")
print()


# ============================================================================
# SECTION 4: PHASE 1 — TOP QUASI-FIXED-POINT (Q1)
# ============================================================================

def run_phase1():
    """Q1: Validate the top quark quasi-fixed-point."""
    print("=" * 70)
    print("PHASE 1: Top Quasi-Fixed-Point Validation (Q1)")
    print("=" * 70)

    yt_planck_vals = np.logspace(np.log10(0.1), np.log10(10), 50)
    yt_ew_vals = []

    for yt_p in yt_planck_vals:
        y_init = {f: 0.01 for f in FERMION_KEYS}
        y_init['t'] = yt_p
        y_final, _, _ = evolve(y_init, g_Planck, t_range, 0, 1000,
                               rg_step_rk4, compute_betas_1loop)
        yt_ew_vals.append(y_final['t'])

    yt_ew_vals = np.array(yt_ew_vals)

    # Find the quasi-fixed-point value (median of plateau)
    plateau = yt_ew_vals[yt_planck_vals > 0.5]
    qfp_value = np.median(plateau)
    qfp_std = np.std(plateau)

    # Basin: range of initial y_t that converges within 10% of QFP
    in_basin = np.abs(yt_ew_vals - qfp_value) / qfp_value < 0.10
    basin_min = yt_planck_vals[in_basin].min() if in_basin.any() else np.nan
    basin_max = yt_planck_vals[in_basin].max() if in_basin.any() else np.nan

    print(f"\nTop QFP value: y_t(EW) = {qfp_value:.4f} ± {qfp_std:.4f}")
    print(f"Observed y_t(MZ) = {YUKAWA_MZ['t']:.4f}")
    print(f"Attraction basin (within 10%): y_t(Planck) ∈ [{basin_min:.2f}, {basin_max:.2f}]")
    print(f"Fraction in basin: {in_basin.sum()}/{len(yt_planck_vals)}")

    # Plot 1: y_t(EW) vs y_t(Planck)
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.semilogx(yt_planck_vals, yt_ew_vals, 'b.-', markersize=4)
    ax.axhline(YUKAWA_MZ['t'], color='r', linestyle='--', label=f'Observed y_t = {YUKAWA_MZ["t"]:.3f}')
    ax.axhline(qfp_value, color='g', linestyle=':', label=f'QFP = {qfp_value:.3f}')
    ax.set_xlabel('y_t(Planck)')
    ax.set_ylabel('y_t(EW)')
    ax.set_title('Phase 1: Top Quasi-Fixed-Point (Pendleton-Ross)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.savefig(os.path.join(PLOT_DIR, 'plot01_top_qfp.png'), dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  → Saved plot01_top_qfp.png")

    return {
        'qfp_value': qfp_value,
        'qfp_std': qfp_std,
        'basin_min': basin_min,
        'basin_max': basin_max,
        'basin_fraction': in_basin.sum() / len(yt_planck_vals),
        'yt_planck_vals': yt_planck_vals,
        'yt_ew_vals': yt_ew_vals,
    }


# ============================================================================
# SECTION 5: PHASE 2 — COUPLED SYSTEM ATTRACTOR SEARCH (Q2, Q3)
# ============================================================================

def run_phase2_q2():
    """Q2: Bottom and tau quasi-fixed-points."""
    print("\n" + "=" * 70)
    print("PHASE 2a: Bottom/Tau Quasi-Fixed-Points (Q2)")
    print("=" * 70)

    N_yt = 15
    N_yb = 15
    N_ytau = 15
    total = N_yt * N_yb * N_ytau

    yt_vals = np.linspace(0.5, 5.0, N_yt)
    yb_vals = np.logspace(np.log10(0.001), np.log10(1.0), N_yb)
    ytau_vals = np.logspace(np.log10(0.001), np.log10(1.0), N_ytau)

    ratio_btau = []
    all_yt_init = []
    all_yb_init = []
    all_ytau_init = []
    all_yt_ew = []
    all_yb_ew = []
    all_ytau_ew = []

    print(f"  Scanning {total} points ({N_yt}×{N_yb}×{N_ytau})...")
    t0 = time.time()

    count = 0
    for yt_p in yt_vals:
        for yb_p in yb_vals:
            for ytau_p in ytau_vals:
                y_init = {f: 0.001 for f in FERMION_KEYS}
                y_init['t'] = yt_p
                y_init['b'] = yb_p
                y_init['tau'] = ytau_p

                y_final, _, _ = evolve(y_init, g_Planck, t_range, 0, 1000,
                                       rg_step_rk4, compute_betas_1loop)

                if y_final['tau'] > 1e-10:
                    r = y_final['b'] / y_final['tau']
                    ratio_btau.append(r)
                    all_yt_init.append(yt_p)
                    all_yb_init.append(yb_p)
                    all_ytau_init.append(ytau_p)
                    all_yt_ew.append(y_final['t'])
                    all_yb_ew.append(y_final['b'])
                    all_ytau_ew.append(y_final['tau'])

                count += 1
                if count % 500 == 0:
                    print(f"    {count}/{total} done...")

    elapsed = time.time() - t0
    print(f"  Completed in {elapsed:.1f}s")

    ratio_btau = np.array(ratio_btau)
    observed_btau = MASSES['b'] / MASSES['tau']

    # Filter finite values
    valid = np.isfinite(ratio_btau) & (ratio_btau > 0) & (ratio_btau < 100)
    ratio_valid = ratio_btau[valid]

    within_20 = np.abs(ratio_valid - observed_btau) / observed_btau < 0.20
    print(f"\n  Observed m_b/m_tau = {observed_btau:.3f}")
    print(f"  Median y_b(EW)/y_tau(EW) = {np.median(ratio_valid):.3f}")
    print(f"  Mean = {np.mean(ratio_valid):.3f}, Std = {np.std(ratio_valid):.3f}")
    print(f"  Fraction within 20% of observed: {within_20.sum()}/{len(ratio_valid)} "
          f"({within_20.sum()/len(ratio_valid)*100:.1f}%)")

    # Plot 2: Histogram of y_b/y_tau
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.hist(ratio_valid, bins=50, alpha=0.7, color='steelblue', edgecolor='black')
    ax.axvline(observed_btau, color='r', linestyle='--', linewidth=2,
               label=f'Observed m_b/m_τ = {observed_btau:.2f}')
    ax.set_xlabel('y_b(EW) / y_τ(EW)')
    ax.set_ylabel('Count')
    ax.set_title('Phase 2a: Bottom/Tau Mass Ratio at EW Scale')
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.savefig(os.path.join(PLOT_DIR, 'plot02_btau_ratio_hist.png'), dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  → Saved plot02_btau_ratio_hist.png")

    # Plot 3: Heat map for fixed y_t (middle value)
    mid_yt = yt_vals[N_yt // 2]
    yt_init_arr = np.array(all_yt_init)
    yb_init_arr = np.array(all_yb_init)
    ytau_init_arr = np.array(all_ytau_init)
    mask = np.abs(yt_init_arr[valid] - mid_yt) < 0.01

    if mask.sum() > 10:
        fig, ax = plt.subplots(figsize=(8, 6))
        sc = ax.scatter(np.log10(yb_init_arr[valid][mask]),
                        np.log10(ytau_init_arr[valid][mask]),
                        c=ratio_valid[mask], cmap='viridis',
                        vmin=0, vmax=10, s=20)
        plt.colorbar(sc, label='y_b(EW)/y_τ(EW)')
        ax.set_xlabel('log10 y_b(Planck)')
        ax.set_ylabel('log10 y_τ(Planck)')
        ax.set_title(f'b/τ ratio at EW scale (y_t(Planck)={mid_yt:.1f})')
        fig.savefig(os.path.join(PLOT_DIR, 'plot03_btau_heatmap.png'), dpi=150, bbox_inches='tight')
        plt.close(fig)
        print(f"  → Saved plot03_btau_heatmap.png")

    return {
        'median_btau': np.median(ratio_valid),
        'mean_btau': np.mean(ratio_valid),
        'std_btau': np.std(ratio_valid),
        'observed_btau': observed_btau,
        'fraction_within_20pct': within_20.sum() / len(ratio_valid) if len(ratio_valid) > 0 else 0,
    }


def run_phase2_q3():
    """Q3: Mass hierarchy attractor (full 9-coupling system)."""
    print("\n" + "=" * 70)
    print("PHASE 2b: Mass Hierarchy Attractor (Q3)")
    print("=" * 70)

    N_samples = 3000
    print(f"  Random scan: {N_samples} points, log-uniform [0.01, 10]...")
    t0 = time.time()

    rng = np.random.RandomState(42)

    H_results = []
    yt_inits = []
    valid_count = 0

    for i in range(N_samples):
        # Log-uniform initial conditions
        y_init = {}
        for f in FERMION_KEYS:
            y_init[f] = 10**(rng.uniform(np.log10(0.01), np.log10(10)))

        y_final, _, _ = evolve(y_init, g_Planck, t_range, 0, 1000,
                               rg_step_rk4, compute_betas_1loop)

        # Check for valid output (no zeros, no infinities)
        vals = np.array([y_final[f] for f in FERMION_KEYS])
        if np.all(vals > 1e-15) and np.all(np.isfinite(vals)):
            yt = y_final['t']
            H = np.array([yt / y_final[f] for f in FERMION_KEYS[1:]])  # 8 ratios
            H_results.append(H)
            yt_inits.append(y_init['t'])
            valid_count += 1

        if (i + 1) % 500 == 0:
            print(f"    {i+1}/{N_samples} done (valid: {valid_count})...")

    elapsed = time.time() - t0
    print(f"  Completed in {elapsed:.1f}s ({valid_count} valid)")

    H_results = np.array(H_results)
    yt_inits = np.array(yt_inits)

    if len(H_results) > 0:
        # Compute relative distance to observed
        log_H = np.log10(np.abs(H_results) + 1e-30)
        log_H_obs = np.log10(H_OBS)
        rel_err = np.sqrt(np.mean((log_H - log_H_obs)**2, axis=1))  # RMS log-ratio error

        print(f"\n  Observed H_obs (log10): {np.log10(H_OBS).round(2)}")
        print(f"  Median log10(H) at EW: {np.median(log_H, axis=0).round(2)}")
        print(f"  Median RMS log-ratio error: {np.median(rel_err):.2f}")
        print(f"  Min RMS log-ratio error: {np.min(rel_err):.2f}")
        print(f"  Fraction within 0.5 dex: {(rel_err < 0.5).sum()}/{len(rel_err)}")
        print(f"  Fraction within 1.0 dex: {(rel_err < 1.0).sum()}/{len(rel_err)}")

        # Check clustering
        spread = np.std(log_H, axis=0)
        print(f"  Spread (std of log10 ratios): {spread.round(2)}")
        clustered = spread < 0.5
        print(f"  Clustered ratios (spread < 0.5): {[RATIO_LABELS[i] for i in range(8) if clustered[i]]}")

        # Plot 4: Scatter of log10(y_t/y_b) vs log10(y_t/y_tau)
        fig, ax = plt.subplots(figsize=(8, 6))
        sc = ax.scatter(log_H[:, 0], log_H[:, 1], c=np.log10(yt_inits),
                        cmap='plasma', alpha=0.5, s=10)
        ax.plot(np.log10(H_OBS[0]), np.log10(H_OBS[1]), 'r*', markersize=15,
                label='Observed', zorder=10)
        plt.colorbar(sc, label='log10 y_t(Planck)')
        ax.set_xlabel('log10(y_t/y_b) at EW')
        ax.set_ylabel('log10(y_t/y_τ) at EW')
        ax.set_title('Phase 2b: Mass Hierarchy at EW Scale')
        ax.legend()
        ax.grid(True, alpha=0.3)
        fig.savefig(os.path.join(PLOT_DIR, 'plot04_hierarchy_scatter.png'), dpi=150, bbox_inches='tight')
        plt.close(fig)
        print(f"  → Saved plot04_hierarchy_scatter.png")

        # Plot 5: Distribution of RMS log-ratio error
        fig, ax = plt.subplots(figsize=(8, 5))
        ax.hist(rel_err, bins=50, alpha=0.7, color='steelblue', edgecolor='black')
        ax.axvline(0.5, color='g', linestyle='--', label='0.5 dex threshold')
        ax.axvline(1.0, color='orange', linestyle='--', label='1.0 dex threshold')
        ax.set_xlabel('RMS log-ratio error (dex)')
        ax.set_ylabel('Count')
        ax.set_title('Distance to Observed Mass Hierarchy')
        ax.legend()
        ax.grid(True, alpha=0.3)
        fig.savefig(os.path.join(PLOT_DIR, 'plot05_hierarchy_error.png'), dpi=150, bbox_inches='tight')
        plt.close(fig)
        print(f"  → Saved plot05_hierarchy_error.png")

        return {
            'median_rms_err': np.median(rel_err),
            'min_rms_err': np.min(rel_err),
            'frac_05dex': (rel_err < 0.5).sum() / len(rel_err),
            'frac_1dex': (rel_err < 1.0).sum() / len(rel_err),
            'spread': spread,
            'clustered_ratios': [RATIO_LABELS[i] for i in range(8) if clustered[i]],
        }
    else:
        print("  No valid results!")
        return None


# ============================================================================
# SECTION 6: PHASE 3 — TWO-LOOP EFFECTS
# ============================================================================

def run_phase3(phase1_results):
    """Phase 3: Two-loop effects comparison."""
    print("\n" + "=" * 70)
    print("PHASE 3: Two-Loop Effects")
    print("=" * 70)

    # Get Planck-scale gauge couplings with 2-loop
    print("  Evolving gauge couplings (2-loop) from M_Z to Planck...")
    _, g_Planck_2L, _ = evolve(YUKAWA_MZ.copy(), g_MZ, 0, t_range, 10000,
                                rg_step_rk4, compute_betas_2loop)
    print(f"  g_Planck (2L): g1={g_Planck_2L[0]:.4f}, g2={g_Planck_2L[1]:.4f}, g3={g_Planck_2L[2]:.4f}")

    # --- Phase 1 repeat with 2-loop ---
    print("\n  Repeating top QFP scan with 2-loop betas...")
    yt_planck_vals = np.logspace(np.log10(0.1), np.log10(10), 50)
    yt_ew_2L = []

    for yt_p in yt_planck_vals:
        y_init = {f: 0.01 for f in FERMION_KEYS}
        y_init['t'] = yt_p
        y_final, _, _ = evolve(y_init, g_Planck_2L, t_range, 0, 1000,
                               rg_step_rk4, compute_betas_2loop)
        yt_ew_2L.append(y_final['t'])

    yt_ew_2L = np.array(yt_ew_2L)
    qfp_2L = np.median(yt_ew_2L[yt_planck_vals > 0.5])

    print(f"  Top QFP (1-loop): {phase1_results['qfp_value']:.4f}")
    print(f"  Top QFP (2-loop): {qfp_2L:.4f}")
    print(f"  Shift: {(qfp_2L - phase1_results['qfp_value'])/phase1_results['qfp_value']*100:.2f}%")

    # Plot 6: 1-loop vs 2-loop top QFP
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.semilogx(yt_planck_vals, phase1_results['yt_ew_vals'], 'b.-', markersize=4, label='1-loop')
    ax.semilogx(yt_planck_vals, yt_ew_2L, 'r.-', markersize=4, label='2-loop')
    ax.axhline(YUKAWA_MZ['t'], color='k', linestyle='--', label=f'Observed y_t = {YUKAWA_MZ["t"]:.3f}')
    ax.set_xlabel('y_t(Planck)')
    ax.set_ylabel('y_t(EW)')
    ax.set_title('Top QFP: 1-Loop vs 2-Loop')
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.savefig(os.path.join(PLOT_DIR, 'plot06_1loop_vs_2loop_qfp.png'), dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  → Saved plot06_1loop_vs_2loop_qfp.png")

    # --- Q2 repeat with 2-loop (reduced grid) ---
    print("\n  Repeating b/τ scan with 2-loop betas (reduced grid)...")
    N_yt, N_yb, N_ytau = 10, 10, 10
    yt_vals = np.linspace(0.5, 5.0, N_yt)
    yb_vals = np.logspace(np.log10(0.001), np.log10(1.0), N_yb)
    ytau_vals = np.logspace(np.log10(0.001), np.log10(1.0), N_ytau)

    ratio_1L = []
    ratio_2L = []

    for yt_p in yt_vals:
        for yb_p in yb_vals:
            for ytau_p in ytau_vals:
                y_init = {f: 0.001 for f in FERMION_KEYS}
                y_init['t'] = yt_p
                y_init['b'] = yb_p
                y_init['tau'] = ytau_p

                # 1-loop
                y1, _, _ = evolve(y_init.copy(), g_Planck, t_range, 0, 1000,
                                  rg_step_rk4, compute_betas_1loop)
                if y1['tau'] > 1e-10:
                    ratio_1L.append(y1['b'] / y1['tau'])

                # 2-loop
                y2, _, _ = evolve(y_init.copy(), g_Planck_2L, t_range, 0, 1000,
                                  rg_step_rk4, compute_betas_2loop)
                if y2['tau'] > 1e-10:
                    ratio_2L.append(y2['b'] / y2['tau'])

    ratio_1L = np.array(ratio_1L)
    ratio_2L = np.array(ratio_2L)

    # Filter
    v1 = ratio_1L[np.isfinite(ratio_1L) & (ratio_1L > 0) & (ratio_1L < 100)]
    v2 = ratio_2L[np.isfinite(ratio_2L) & (ratio_2L > 0) & (ratio_2L < 100)]

    print(f"  b/τ ratio median: 1L={np.median(v1):.3f}, 2L={np.median(v2):.3f}")

    # Plot 7: 1-loop vs 2-loop b/tau histograms
    fig, ax = plt.subplots(figsize=(8, 5))
    bins = np.linspace(0, 10, 40)
    ax.hist(v1, bins=bins, alpha=0.5, color='blue', label='1-loop', edgecolor='blue')
    ax.hist(v2, bins=bins, alpha=0.5, color='red', label='2-loop', edgecolor='red')
    ax.axvline(MASSES['b']/MASSES['tau'], color='k', linestyle='--', linewidth=2,
               label=f'Observed = {MASSES["b"]/MASSES["tau"]:.2f}')
    ax.set_xlabel('y_b(EW) / y_τ(EW)')
    ax.set_ylabel('Count')
    ax.set_title('b/τ Ratio: 1-Loop vs 2-Loop')
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.savefig(os.path.join(PLOT_DIR, 'plot07_btau_1L_vs_2L.png'), dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  → Saved plot07_btau_1L_vs_2L.png")

    return {
        'qfp_1L': phase1_results['qfp_value'],
        'qfp_2L': qfp_2L,
        'btau_median_1L': np.median(v1),
        'btau_median_2L': np.median(v2),
    }


# ============================================================================
# SECTION 7: PHASE 4 — KOIDE TEST (Q4)
# ============================================================================

def run_phase4():
    """Q4: The Koide ratio under RG flow."""
    print("\n" + "=" * 70)
    print("PHASE 4: Koide Test (Q4)")
    print("=" * 70)

    N_samples = 3000
    print(f"  Random scan: {N_samples} points...")
    rng = np.random.RandomState(123)

    koide_vals = []
    passed_filter = 0
    t0 = time.time()

    for i in range(N_samples):
        y_init = {}
        for f in FERMION_KEYS:
            y_init[f] = 10**(rng.uniform(np.log10(0.01), np.log10(10)))

        y_final, _, _ = evolve(y_init, g_Planck, t_range, 0, 1000,
                               rg_step_rk4, compute_betas_1loop)

        # Check if 3rd generation is roughly right (within factor 3)
        yt_obs, yb_obs, ytau_obs = YUKAWA_MZ['t'], YUKAWA_MZ['b'], YUKAWA_MZ['tau']
        yt_ok = 0.33 < y_final['t'] / yt_obs < 3.0
        yb_ok = 0.33 < y_final['b'] / yb_obs < 3.0 if y_final['b'] > 1e-10 else False
        ytau_ok = 0.33 < y_final['tau'] / ytau_obs < 3.0 if y_final['tau'] > 1e-10 else False

        if yt_ok and yb_ok and ytau_ok:
            passed_filter += 1
            # Compute lepton masses from Yukawa
            m_e_rg = y_final['e'] * v / np.sqrt(2)
            m_mu_rg = y_final['mu'] * v / np.sqrt(2)
            m_tau_rg = y_final['tau'] * v / np.sqrt(2)

            if m_e_rg > 0 and m_mu_rg > 0 and m_tau_rg > 0:
                numerator = m_e_rg + m_mu_rg + m_tau_rg
                denominator = (np.sqrt(m_e_rg) + np.sqrt(m_mu_rg) + np.sqrt(m_tau_rg))**2
                Q = numerator / denominator
                koide_vals.append(Q)

        if (i + 1) % 500 == 0:
            print(f"    {i+1}/{N_samples} done (passed filter: {passed_filter})...")

    elapsed = time.time() - t0
    print(f"  Completed in {elapsed:.1f}s")
    print(f"  Passed 3rd-gen filter: {passed_filter}/{N_samples}")

    koide_vals = np.array(koide_vals)

    if len(koide_vals) > 0:
        valid = np.isfinite(koide_vals) & (koide_vals > 0) & (koide_vals < 2)
        kv = koide_vals[valid]

        print(f"  Valid Koide values: {len(kv)}")
        print(f"  Mean Q = {np.mean(kv):.4f}")
        print(f"  Median Q = {np.median(kv):.4f}")
        print(f"  Std Q = {np.std(kv):.4f}")
        print(f"  Observed Q = {2/3:.4f}")
        within_1pct = np.abs(kv - 2/3) / (2/3) < 0.01
        within_5pct = np.abs(kv - 2/3) / (2/3) < 0.05
        print(f"  Within 1% of 2/3: {within_1pct.sum()}/{len(kv)} ({within_1pct.sum()/len(kv)*100:.1f}%)")
        print(f"  Within 5% of 2/3: {within_5pct.sum()}/{len(kv)} ({within_5pct.sum()/len(kv)*100:.1f}%)")

        # Plot 8: Koide histogram
        fig, ax = plt.subplots(figsize=(8, 5))
        ax.hist(kv, bins=50, alpha=0.7, color='steelblue', edgecolor='black')
        ax.axvline(2/3, color='r', linestyle='--', linewidth=2, label='Q = 2/3')
        ax.axvline(1/3, color='gray', linestyle=':', label='Q = 1/3 (lower bound)')
        ax.set_xlabel('Koide ratio Q')
        ax.set_ylabel('Count')
        ax.set_title('Phase 4: Koide Ratio at EW Scale')
        ax.legend()
        ax.grid(True, alpha=0.3)
        fig.savefig(os.path.join(PLOT_DIR, 'plot08_koide.png'), dpi=150, bbox_inches='tight')
        plt.close(fig)
        print(f"  → Saved plot08_koide.png")

        return {
            'mean_Q': np.mean(kv),
            'median_Q': np.median(kv),
            'std_Q': np.std(kv),
            'frac_1pct': within_1pct.sum() / len(kv) if len(kv) > 0 else 0,
            'frac_5pct': within_5pct.sum() / len(kv) if len(kv) > 0 else 0,
            'n_valid': len(kv),
        }
    else:
        print("  No valid Koide values!")
        return None


# ============================================================================
# SECTION 8: Q5 — DISCRETE MAP VS CONTINUOUS FLOW
# ============================================================================

def run_q5():
    """Q5: Compare discrete map (various N) with continuous flow."""
    print("\n" + "=" * 70)
    print("Q5: Discrete Map vs Continuous Flow")
    print("=" * 70)

    # Initial conditions: moderate y_t at Planck
    y_init = {f: 0.01 for f in FERMION_KEYS}
    y_init['t'] = 3.0  # well within QFP basin

    # --- (a)-(d): Discrete steps at various N ---
    N_values = [10, 50, 100, 500, 1000, 5000, 10000]
    yt_euler = []
    yt_rk4 = []

    for N in N_values:
        # Euler
        y_e, _, _ = evolve(y_init.copy(), g_Planck, t_range, 0, N,
                           rg_step_euler, compute_betas_1loop)
        yt_euler.append(y_e['t'] if np.isfinite(y_e['t']) else np.nan)

        # RK4
        y_r, _, _ = evolve(y_init.copy(), g_Planck, t_range, 0, N,
                           rg_step_rk4, compute_betas_1loop)
        yt_rk4.append(y_r['t'] if np.isfinite(y_r['t']) else np.nan)

    yt_euler = np.array(yt_euler)
    yt_rk4 = np.array(yt_rk4)

    # --- (e): scipy continuous ---
    print("  Running scipy solve_ivp (continuous reference)...")
    y_scipy, _ = evolve_scipy(y_init.copy(), g_Planck, t_range, 0,
                              compute_betas_1loop)
    yt_scipy = y_scipy['t']

    print(f"\n  y_t(EW) results for y_t(Planck) = 3.0:")
    print(f"  {'N':>8s}  {'Euler':>10s}  {'RK4':>10s}")
    print(f"  {'-'*8}  {'-'*10}  {'-'*10}")
    for i, N in enumerate(N_values):
        print(f"  {N:>8d}  {yt_euler[i]:>10.4f}  {yt_rk4[i]:>10.4f}")
    print(f"  {'scipy':>8s}  {'—':>10s}  {yt_scipy:>10.4f}")
    print(f"  Observed: {YUKAWA_MZ['t']:.4f}")

    # Convergence of RK4 to scipy
    rk4_errors = np.abs(yt_rk4 - yt_scipy) / yt_scipy * 100
    print(f"\n  RK4 error vs scipy:")
    for i, N in enumerate(N_values):
        print(f"    N={N}: {rk4_errors[i]:.4f}%")

    # Plot 9: y_t(EW) vs N
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.semilogx(N_values, yt_euler, 'ro-', label='Euler')
    ax.semilogx(N_values, yt_rk4, 'bs-', label='RK4')
    ax.axhline(yt_scipy, color='g', linestyle='--', linewidth=2, label=f'scipy = {yt_scipy:.4f}')
    ax.axhline(YUKAWA_MZ['t'], color='k', linestyle=':', label=f'Observed = {YUKAWA_MZ["t"]:.4f}')
    ax.set_xlabel('Number of discrete steps N')
    ax.set_ylabel('y_t(EW)')
    ax.set_title('Q5: Discrete Map Convergence to Continuous Flow')
    ax.legend()
    ax.grid(True, alpha=0.3)
    fig.savefig(os.path.join(PLOT_DIR, 'plot09_discrete_vs_continuous.png'), dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  → Saved plot09_discrete_vs_continuous.png")

    # --- QFP basin at various N ---
    print("\n  Computing QFP basin at N = 10, 100, 1000, 10000...")
    yt_planck_scan = np.logspace(np.log10(0.1), np.log10(10), 40)
    N_basin = [10, 100, 1000, 10000]
    basins = {}

    for N in N_basin:
        yt_ew_list = []
        for yt_p in yt_planck_scan:
            y_i = {f: 0.01 for f in FERMION_KEYS}
            y_i['t'] = yt_p
            y_f, _, _ = evolve(y_i, g_Planck, t_range, 0, N,
                               rg_step_rk4, compute_betas_1loop)
            yt_ew_list.append(y_f['t'] if np.isfinite(y_f['t']) and y_f['t'] < 100 else np.nan)
        basins[N] = np.array(yt_ew_list)

    # Plot 10: QFP basin at various N
    fig, ax = plt.subplots(figsize=(8, 5))
    colors = ['red', 'orange', 'blue', 'green']
    for N, c in zip(N_basin, colors):
        valid = np.isfinite(basins[N])
        ax.semilogx(yt_planck_scan[valid], basins[N][valid], '.-', color=c,
                     markersize=4, label=f'N={N}')
    ax.axhline(YUKAWA_MZ['t'], color='k', linestyle='--', label=f'Observed y_t = {YUKAWA_MZ["t"]:.3f}')
    ax.set_xlabel('y_t(Planck)')
    ax.set_ylabel('y_t(EW)')
    ax.set_title('Q5: QFP Basin at Various Discrete Step Counts')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_ylim(0, 3)
    fig.savefig(os.path.join(PLOT_DIR, 'plot10_qfp_basin_N.png'), dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  → Saved plot10_qfp_basin_N.png")

    # Determine at what N the QFP becomes visible
    # QFP "visible" = plateau region has spread < 20% of mean
    qfp_visible_N = None
    for N in N_basin:
        vals = basins[N]
        plateau = vals[yt_planck_scan > 0.5]
        plateau = plateau[np.isfinite(plateau)]
        if len(plateau) > 3:
            spread = np.std(plateau) / np.mean(plateau)
            if spread < 0.20:
                qfp_visible_N = N
                break

    if qfp_visible_N:
        print(f"\n  QFP becomes visible (spread < 20%) at N = {qfp_visible_N}")
    else:
        print(f"\n  QFP not clearly visible even at N = {N_basin[-1]}")

    return {
        'yt_scipy': yt_scipy,
        'yt_rk4_N1000': yt_rk4[N_values.index(1000)] if 1000 in N_values else np.nan,
        'yt_euler_N10': yt_euler[0],
        'qfp_visible_N': qfp_visible_N,
        'N_values': N_values,
        'yt_euler': yt_euler,
        'yt_rk4': yt_rk4,
    }


# ============================================================================
# SECTION 9: MAIN EXECUTION AND SUMMARY
# ============================================================================

if __name__ == '__main__':

    t_total_start = time.time()

    # Phase 1: Top QFP (Q1)
    results_q1 = run_phase1()

    # Phase 2a: b/tau QFP (Q2)
    results_q2 = run_phase2_q2()

    # Phase 2b: Mass hierarchy attractor (Q3)
    results_q3 = run_phase2_q3()

    # Phase 3: Two-loop effects
    results_phase3 = run_phase3(results_q1)

    # Phase 4: Koide test (Q4)
    results_q4 = run_phase4()

    # Q5: Discrete vs continuous
    results_q5 = run_q5()

    t_total = time.time() - t_total_start

    # ========================================================================
    # SUMMARY
    # ========================================================================
    print("\n")
    print("=" * 70)
    print("SUMMARY: ANSWERS TO Q1-Q5")
    print("=" * 70)

    print(f"\nTotal runtime: {t_total:.1f}s")
    print()

    # Q1
    print("Q1: Top Quasi-Fixed-Point (Validation)")
    print("-" * 40)
    print(f"  QFP value: y_t(EW) = {results_q1['qfp_value']:.4f}")
    print(f"  Observed:  y_t(EW) = {YUKAWA_MZ['t']:.4f}")
    print(f"  Basin: y_t(Planck) ∈ [{results_q1['basin_min']:.2f}, {results_q1['basin_max']:.2f}]")
    print(f"  Basin fraction: {results_q1['basin_fraction']*100:.0f}%")
    qfp_match = abs(results_q1['qfp_value'] - YUKAWA_MZ['t']) / YUKAWA_MZ['t'] < 0.2
    print(f"  VALIDATED: {'YES' if qfp_match else 'PARTIAL'} (within {'20%' if qfp_match else '>20%'} of observed)")
    print()

    # Q2
    print("Q2: Bottom/Tau Quasi-Fixed-Point")
    print("-" * 40)
    print(f"  Median y_b/y_tau: {results_q2['median_btau']:.3f}")
    print(f"  Observed m_b/m_tau: {results_q2['observed_btau']:.3f}")
    print(f"  Fraction within 20%: {results_q2['fraction_within_20pct']*100:.1f}%")
    btau_qfp = results_q2['std_btau'] / results_q2['mean_btau'] < 0.3 if results_q2['mean_btau'] > 0 else False
    print(f"  QFP structure: {'YES (clustering)' if btau_qfp else 'WEAK or NO clustering'}")
    print()

    # Q3
    print("Q3: Mass Hierarchy Attractor")
    print("-" * 40)
    if results_q3:
        print(f"  Median RMS log-ratio error: {results_q3['median_rms_err']:.2f} dex")
        print(f"  Fraction within 0.5 dex: {results_q3['frac_05dex']*100:.1f}%")
        print(f"  Fraction within 1.0 dex: {results_q3['frac_1dex']*100:.1f}%")
        print(f"  Clustered ratios: {results_q3['clustered_ratios']}")
        attractor = results_q3['frac_1dex'] > 0.3
        print(f"  ATTRACTOR: {'POSSIBLE (>30% within 1 dex)' if attractor else 'NOT FOUND'}")
    else:
        print("  No valid results")
    print()

    # Q4
    print("Q4: Koide Ratio Under RG Flow")
    print("-" * 40)
    if results_q4:
        print(f"  Mean Q = {results_q4['mean_Q']:.4f}")
        print(f"  Std Q = {results_q4['std_Q']:.4f}")
        print(f"  Expected Q = {2/3:.4f}")
        print(f"  Within 1% of 2/3: {results_q4['frac_1pct']*100:.1f}%")
        print(f"  Within 5% of 2/3: {results_q4['frac_5pct']*100:.1f}%")
        koide_generic = results_q4['frac_5pct'] > 0.3
        print(f"  KOIDE Q≈2/3: {'GENERIC' if koide_generic else 'REQUIRES TUNING'}")
    else:
        print("  No valid results")
    print()

    # Q5
    print("Q5: Discrete Map vs Continuous Flow")
    print("-" * 40)
    print(f"  scipy (continuous): y_t(EW) = {results_q5['yt_scipy']:.4f}")
    print(f"  RK4 N=1000:        y_t(EW) = {results_q5['yt_rk4_N1000']:.4f}")
    print(f"  Euler N=10:         y_t(EW) = {results_q5['yt_euler_N10']:.4f}")
    if results_q5['qfp_visible_N']:
        print(f"  QFP visible at N = {results_q5['qfp_visible_N']}")
        finite_bish = results_q5['qfp_visible_N'] <= 100
        print(f"  BISH STRUCTURE: {'YES (visible at N≤100)' if finite_bish else 'REQUIRES MANY STEPS'}")
    else:
        print(f"  QFP not clearly visible — may require larger N")
    print()

    # Overall verdict
    print("=" * 70)
    print("OVERALL ASSESSMENT")
    print("=" * 70)
    successes = []
    if qfp_match:
        successes.append("Top QFP validated")
    if btau_qfp:
        successes.append("b/τ QFP structure found")
    if results_q3 and results_q3['frac_1dex'] > 0.3:
        successes.append("Mass hierarchy attractor structure")
    if results_q4 and results_q4['frac_5pct'] > 0.3:
        successes.append("Koide Q≈2/3 generic")
    if results_q5['qfp_visible_N'] and results_q5['qfp_visible_N'] <= 100:
        successes.append("Finite-N BISH structure")

    if successes:
        print(f"  Positive findings ({len(successes)}/5):")
        for s in successes:
            print(f"    ✓ {s}")
    else:
        print("  No success criteria met — mass hierarchy requires UV input")

    failures = []
    if not qfp_match:
        failures.append("Top QFP does not match observed y_t")
    if results_q3 and results_q3['frac_1dex'] < 0.1:
        failures.append("Mass ratios highly sensitive to initial conditions")
    if not failures:
        failures.append("(none)")
    print(f"\n  Negative findings:")
    for f_item in failures:
        print(f"    ✗ {f_item}")

    print(f"\n  Plots saved to: {PLOT_DIR}/")
    print("=" * 70)
