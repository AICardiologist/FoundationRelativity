# Schwarzschild Vacuum Engine Roadmap

## High-level goals
1. Stabilize the metric layer as indexed objects (g, gInv) with exterior domain side-conditions centralized and reusable.
2. Compute the Christoffel symbols from the diagonal, static, spherically symmetric metric, using only height-0 algebra/calculus.
3. Assemble the Ricci tensor and show all components vanish, then R = 0.
4. Conclude the Einstein tensor vanishes and bridge to VacuumEFE S.
5. Harden & document: local simp sets, file layout, CI, and proof patterns to resist mathlib drift.

---

## Sprint breakdown (each sprint ends with zero sorry, green build, and a smoke test)

### ✅ Sprint 0 (done): "Back to green"
**Outcome:** File compiles, zero sorry, photon-sphere section robust.
- Cleaned algebra (use field_simp where appropriate).
- Fixed g_tt_deriv_comp (now using exact … .deriv).
- Removed partial, unstable sections that blocked builds.

**Definition of done:** ✔ green build; ✔ rg 'sorry|admit' returns none; ✔ photon-sphere tests pass.

---

### Sprint 1: Metric layer made precise & reusable

**Objective:** Re-introduce the indexed metric cleanly and prove g ⋅ gInv = I componentwise on the exterior.

**Work items:**
- Finalize Idx with deriving DecidableEq, Repr, Fintype.
- Re-establish g and gInv as diagonal functions of (r, θ), using Real.sin/Real.cos.
- Centralize exterior facts once:
  - r_ne_zero_of_exterior, f_pos_of_hr, sinθ_ne_zero : 0 < θ ∧ θ < π → sin θ ≠ 0.
- Prove metric_inverse_id by exhaustive cases μ; cases ν, with:
  - Off-diagonal: simp [g, gInv] → 0.
  - Diagonal tt/rr/θθ: simp [g, gInv, pow_two, inv_mul_cancel …] → 1.
  - Diagonal φφ: use hx : r * sin θ ≠ 0 then simp [pow_two, mul_comm, mul_left_comm, mul_assoc, inv_mul_cancel hx] → 1.

**Acceptance criteria:**
- metric_inverse_id … (μ ν) proven without sorry.
- Single local simp set @[local simp] or simp? bundle for metric identities.
- Green build; Smoke.lean imports the indexed metric and checks a few simp sanity goals.

---

### Sprint 2: Christoffel symbols (nonzero components only)

**Objective:** Compute the handful of nonzero Γ's from first principles and prove the named formulas.

**Work items:**
- Provide just-enough derivative lemmas:
  - deriv (fun r => g_tt M r) = -(2M / r^2) (already in file as g_tt_derivative).
  - deriv (fun r => g_rr M r) = -(2M / r^2) / (f M r)^2 (you already have).
  - deriv (fun r => r^2) = 2r; deriv (fun θ => (sin θ)^2) = 2 sin θ cos θ.
- Specialize the Levi-Civita expression to diagonal, static metric.
- Prove the named formulas:
  - Γ_t_tr = M / (r^2 * f)
  - Γ_r_tt = M * f / r^2
  - Γ_r_rr = -M / (r^2 * f)
  - Γ_r_θθ = -(r - 2M)
  - Γ_r_φφ = -(r - 2M) * (sin θ)^2
  - Γ_θ_rθ = 1/r
  - Γ_θ_φφ = -sin θ * cos θ
  - Γ_φ_rφ = 1/r
  - Γ_φ_θφ = cot θ = cos θ / sin θ

**Pattern:**
- Freeze each derivative once.
- Clear positive denominators exactly once.
- Reduce to balanced polynomials; finish with ring.

**Acceptance criteria:**
- Each nonzero Γ-formula has a lemma proven.
- A single lemma Christoffel_zero_else to capture the diagonal/static sparsity.
- Green build; no sorry.

---

### Sprint 3: Ricci tensor = 0

**Objective:** Assemble R_{μν} using the Γ's, exploit sparsity & symmetry, and reduce each component to 0.

**Work items:**
- Encode the minimal contraction needed for a diagonal 4D metric.
- For each component in {tt, rr, θθ, φφ}:
  - Summation over indices reduces to 2–4 nonzero terms via Γ sparsity lemmas.
  - Freeze, clear denominators, reduce to a polynomial identity.
  - Close with ring or small linarith/norm_num facts.
- Prove off-diagonals vanish by sparsity + cancellations.

**Acceptance criteria:**
- Lemmas Ricci_tt_vanishes, Ricci_rr_vanishes, Ricci_θθ_vanishes, Ricci_φφ_vanishes, and Ricci_off_diagonal_vanish proven.
- Ricci_scalar_vanishes follows from diagonal contraction.
- Green build; no sorry.

---

### Sprint 4: Einstein tensor & bridge to VacuumEFE

**Objective:** Package the result into the Spacetime abstraction and prove the goal theorem.

**Work items:**
- Define Einstein tensor G_{μν} = R_{μν} - ½ g_{μν} R.
- Use Ricci_* = 0 and R = 0 to get G_{μν} = 0.
- Replace the current "True" placeholders.

**Acceptance criteria:**
- VacuumEFE S is proven from the constructed metric when IsPinnedSchwarzschild S.
- Smoke test imports the result and checks a tiny end-to-end statement.

---

### Sprint 5: Hardening & documentation

**Objective:** Make the proofs fast, readable, and stable against mathlib changes.

**Work items:**
- File layout:
  ```
  Papers/P5_GeneralRelativity/GR/Schwarzschild/
    Metric.lean            -- g, gInv, exterior lemmas, metric_inverse_id
    Christoffel.lean       -- nonzero Γ components
    Ricci.lean             -- Ricci components, scalar
    Einstein.lean          -- Einstein tensor, VacuumEFE
    EffectivePotential.lean -- (current photon-sphere work, already robust)
    Smoke.lean
  ```
- Local simp set: @[local simp] for f, g, gInv, pow_two, etc.
- Wrapper lemmas for mildly unstable names.
- CI checklist.

**Acceptance criteria:**
- No sorry.
- lake build is green on a clean checkout with cache.
- Basic docs/comments describe the freeze → clear → balance → ring pattern.

---

## Engineering conventions
- Freeze once, clear denominators once, then work in balanced polynomials.
- Prefer one_le_div_iff/div_lt_one style lemmas for monotonicity/positivity proofs.
- Keep partial derivative lemmas local to the file using them.
- Use case-split + simp for diagonal metric algebra.

---

## Risk register & mitigations
- **Algebra blow-ups / slow field_simp:** Clear denominators manually with calc + ring.
- **Mathlib lemma renames:** Define thin wrappers that call the current canonical lemma.
- **Angle side-conditions (sin θ ≠ 0):** Always carry 0 < θ ∧ θ < π.
- **Index bookkeeping:** Keep Idx diagonalization facts and single cases μ; cases ν; proof skeleton.

---

## Task board (live checklist)
- [ ] S1: metric_inverse_id complete (no sorry), plus exterior side-condition lemmas.
- [ ] S2: All nonzero Γ formulas proven; zero-else lemma in place.
- [ ] S3: Ricci_*_vanishes and Ricci_scalar_vanishes as equalities.
- [ ] S4: Einstein_tensor_vanishes and Schwarzschild_Vacuum_Check.
- [ ] S5: Refactor, docs, local simp sets, CI hooks.

---

## Ready-to-paste skeletons

### metric_inverse_id core (φφ case)
```lean
have hr0  : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
have hfpos : 0 < f M r := f_pos_of_hr M r hM hr
have hfnz : f M r ≠ 0 := ne_of_gt hfpos
have hsθ : Real.sin θ ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_mem_Ioo ⟨hθ.1, hθ.2⟩)

-- in the φφ branch:
have hx : r * Real.sin θ ≠ 0 := mul_ne_zero hr0 hsθ
simp [g, gInv, pow_two, inv_mul_cancel hx]
```

### A Christoffel sample (Γ_r_θθ)
```lean
/-- Γ^r_{θθ} = -(r - 2M) on the exterior. -/
theorem christoffel_r_θθ (hM : 0 < M) (hr : 2*M < r) :
  Γ_r_θθ M r = -(r - 2*M) := by
  -- diagonal static metric → only ∂_r g_θθ = 2r contributes
  -- g^rr = f, so Γ^r_{θθ} = (1/2) f * ( - ∂_r g_θθ ) = -r f = -(r - 2M).
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have : deriv (fun r => g_θθ r) r = 2*r := by
    simp [g_θθ]
  simp [Γ_r_θθ, g_inv_rr, f, this]  -- then close with `field_simp; ring` if needed
```