# Paper 5 Development Roadmap

## 🎉 Sprint 3 Complete!

**Major Achievement**: Schwarzschild vacuum solution fully verified with CI green!
- ✅ All Christoffel symbols computed
- ✅ Ricci tensor vanishing proved (R_μν = 0)
- ✅ Tricky issues solved: trace freezing, symbolic ∂ᵣ, φ-θ trigonometry
- ✅ Clean, deterministic proof state achieved

---

## Sprint 4: Stabilize, Document, and Raise the Bar on Invariants (P0)

### P0.1 Eliminate Remaining Warnings & Tighten Proof Surface

**Why**: Warnings hide regressions and slow CI triage.

**What to do**:
- Remove/rename unused variables flagged in warnings (e.g., `coords`, `hM`, etc.)
- Scope `attribute [-simp]` only where needed (local sections)
- Add short docstrings explaining why certain symbols are frozen (e.g., to prevent ∂ᵣ Γ collapsing)
- Audit simp blocks: keep "dangerous" rules out of Pass 2

**Acceptance Criteria**:
- [ ] `lake build` with no warnings
- [ ] No global `[-simp]` on "dangerous" symbols outside reduction sections

### P0.2 Prove Curvature Invariants on Schwarzschild

**Why**: Invariants are robust smoke tests.

**Targets**:
1. **Ricci scalar**: R = 0 (vacuum)
2. **Kretschmann scalar**: K = R_{abcd}R^{abcd} = 48M²/r⁶

**Implementation Sketch**:
```lean
/-- R = 0 for Schwarzschild (exterior). -/
theorem ScalarCurvature_Schwarzschild_zero
  (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) : 
  ScalarCurvature M r θ = 0 := by
  -- use R_{μν}=0 + contraction pipeline
  -- finish with simp & ring
```

**Acceptance Criteria**:
- [ ] New lemmas under section `Invariants`
- [ ] CI time stays roughly unchanged
- [ ] No new global simp rules introduced

### P0.3 Guardrail Tests to Prevent Regression on "Symbolic ∂ᵣ"

**Why**: The "-1 appearing from ∂ᵣ Γ^r_{θθ}" was the root cause before.

**What to do**:
- Add tiny "expect no-eval" tests that fail if simp turns `deriv (fun s => Γ_r_θθ … s) r` into a constant
- Add `simp?` or `simpNF` audit on critical blocks

**Acceptance Criteria**:
- [ ] Breaking a guardrail produces clear CI error
- [ ] Tests point directly to regressed blocks

---

## Sprint 5: Physics Deliverables - Geodesics & Orbits (P0/P1)

### P0.4 Timelike & Null Geodesics (Equatorial Plane)

**Why**: These are the headline physics results people expect.

**What to do**:
- Derive constants of motion (E, L) from Killing vectors
- Reduce to effective potential V_eff(r) for equatorial orbits
- Prove standard radii:
  - **Photon sphere**: r = 3M (null circular)
  - **ISCO**: r = 6M (timelike stable/unstable transition)
- Keep derivations symbolic first, substitute late

**Acceptance Criteria**:
- [ ] Lemmas: `photonSphere_radius`, `isco_radius`
- [ ] Clear hypotheses (exterior, nonzero sinθ, etc.)
- [ ] Doc comments with physical interpretation

### P1.1 Light Deflection & Perihelion Precession (First-Order)

**Why**: Classic GR tests; good PR in docs.

**What to do**:
- First-order expansion results
- Keep self-contained and optional if calculus overhead is high

---

## Sprint 6: Coordinate Sophistication (P1)

### P1.2 Eddington-Finkelstein & Horizon Regularity

**Why**: Shows understanding of chart pathology vs. curvature.

**What to do**:
- Coordinate transform: (t,r,θ,φ) → (v,r,θ,φ) (advanced EF)
- Show metric components regular at r = 2M in EF
- Prove invariants match across coordinate systems

### P1.3 Kruskal-Szekeres (Stretch Goal)

**Why**: Full maximal extension is a strong deliverable.

**What to do**:
- Stage after EF completion
- Keep structure modular to reuse EF work

---

## Engineering & CI Hygiene (Continuous)

### Documentation & Narrative
- Every reduction lemma gets a "why this shape" comment
- Add "How to add a new metric" guide in `/Papers/P5/CONTRIBUTING.md`
- Explain the two-pass pattern

### Modularize "Reduction Kit"
- Extract reduction combinators into `GR/ReductionKit.lean`:
  - `sumIdx_expand`, `sumIdx2_expand`
  - Trace equalities
  - "Freeze under deriv" helpers
- Keep Schwarzschild files lean, encourage reuse

### CI Matrix & Reproducibility
- Add second Lean toolchain in CI (previous rc) for version-sensitivity
- Cache mathlib build for practical CI times
- Capture proof time deltas for heaviest lemmas
- Add 1-line "time report" in CI artifacts

---

## Nice-to-Have Follow-ups (Post Sprint 6)

1. **Interior Schwarzschild** (constant density)
   - Junction at surface
   - Match first & second fundamental forms
   - Demonstrate continuity of g and extrinsic curvature

2. **Reissner-Nordström** 
   - Maxwell T_{μν} ≠ 0
   - Shows non-vacuum pipeline is sound

3. **Bianchi Identities**
   - ∇_μ G^{μν} = 0 as internal consistency check

---

## Quick Win (Immediate)

### Release Notes for PR #214
**Highlights**:
- "New CI-stable reductions for R_{θθ}, R_{φφ} with protected symbolic derivatives"
- "Vacuum Einstein equations R_{μν} = 0 fully formalized for Schwarzschild"
- "Deterministic two-pass simplification pattern documented and enforced"

### Tag Minor Release (v1.1)
- Reference PR #214
- Link to rendered PDF
- Include short "How to run" for build

---

## Priority Order

### Sprint 4 (Immediate)
1. **P0.1**: Eliminate warnings ⚡
2. **P0.2**: Prove curvature invariants 🎯
3. **P0.3**: Add guardrail tests 🛡️

### Sprint 5 (Next)
1. **P0.4**: Geodesics & orbits 🌍
2. **P1.1**: Classic GR tests (optional)

### Sprint 6 (Future)
1. **P1.2**: Eddington-Finkelstein
2. **P1.3**: Kruskal-Szekeres (stretch)

---

## Success Metrics

- **Sprint 4**: Zero warnings, invariants proven, regression guards in place
- **Sprint 5**: Key physics results (photon sphere, ISCO) verified
- **Sprint 6**: Coordinate independence demonstrated

---

## Notes

- Keep the "symbolic first, evaluate late" pattern throughout
- Maintain CI stability as top priority
- Document the "why" behind each technical decision
- Each sprint should be mergeable and releasable

---

*Last Updated: September 2025 (Sprint 3 Complete)*