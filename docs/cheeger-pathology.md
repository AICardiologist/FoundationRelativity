# Cheeger–Bottleneck Pathology (ρ ≈ 3½)

*Location in code*: `SpectralGap/Cheeger.lean`

| Item | Lean symbol | Status |
|------|-------------|--------|
| Operator definition | `cheeger β b` | ✅ |
| Spectral gap lemma | `cheeger_has_gap` | ✅ |
| Constructive impossibility | `wlpo_of_sel_cheeger` | ✅ |
| Classical witness | `chiWitness_eigen` | ✅ |
| Bridge theorem | `Cheeger_requires_ACω` | ✅ |

The operator is diagonal on the ℓ² basis with eigenvalues  
`β` (on the bottleneck coordinates) and `1` otherwise.
Choosing `β := 0` yields a uniform gap of width ≥ ½, yet constructively no
eigen‑vector at 0 can be selected without WLPO.  
Classically, the vector `e 0` witnesses the zero eigen‑space.

This realises a "half‑step" beyond ρ = 3 (SpectralGap) while remaining below the
RNP failures at ρ = 4.

*Author*: Math‑Coder AI, Sprint 35 Day 1–6.