# Weight-Monodromy Conjecture: Lean 4 Formalization Specification

## Lefschetz Pencil Reduction via Strategy A

**Target:** Formalize the reduction of the Weight-Monodromy Conjecture (WMC)
for smooth projective varieties in mixed characteristic to the
Arithmetic Kashiwara Conjecture (Sub-lemma 5), then apply constructive
reverse mathematics to calibrate the logical strength of Sub-lemma 5
and identify the precise constructive obstruction.

**Status:** Sub-lemmas 1–4 are known results. Sub-lemma 5 is open.
The goal is to produce a machine-checkable proof that
WMC ⟸ (Sub-lemma 1 + Sub-lemma 2 + Sub-lemma 3 + Sub-lemma 4 + Sub-lemma 5),
state Sub-lemma 5 as a formal conjecture with explicit type signatures,
and formalize the constructive calibration showing that geometric origin
acts as a "de-omniscientizing" descent from LPO to decidable equality.

**Dependencies:** Mathlib4 (current), potential extensions to étale cohomology,
perverse sheaves, p-adic Hodge theory, and constructive logic libraries.

---

## 1. Mathematical Context

### 1.1 The Weight-Monodromy Conjecture

Let K be a finite extension of ℚ_p with residue field 𝔽_q,
ring of integers 𝒪_K, and uniformizer π.
Let X be a smooth projective variety of dimension n over K.

The ℓ-adic étale cohomology H^i_ét(X_{K̄}, ℚ_ℓ) carries two filtrations:

**Weight filtration W_•:**
Defined via the eigenvalues of geometric Frobenius φ.
  W_k H^i = subspace where eigenvalues α of φ satisfy |ι(α)| ≤ q^{k/2}
  for every embedding ι: ℚ̄_ℓ → ℂ.

**Monodromy filtration M_•:**
Defined via the nilpotent monodromy operator N: H^i → H^i(-1),
which arises from the action of the pro-p part of inertia.
  M_k is the unique filtration such that N(M_k) ⊆ M_{k-2} and
  N^k: Gr^M_{k} → Gr^M_{-k} is an isomorphism for all k ≥ 0.

**Conjecture (Deligne, 1970):** M_{k+i} = W_k for all k.

Equivalently: the monodromy filtration centered at weight i
coincides with the weight filtration.

### 1.2 Known Cases

- dim X = 1: Classical (Grothendieck, SGA 7)
- Abelian varieties: Grothendieck
- Surfaces: Rapoport-Zink
- Complete intersections in toric varieties: Scholze (2012)
- Complete intersections in abelian varieties: Wear (2023)
- All smooth proper varieties in equal characteristic: Deligne (1980), Ito (2005)

### 1.3 Why the General Mixed-Characteristic Case is Hard

Scholze's perfectoid method requires algebraic approximation of
tilted analytic spaces. For non-complete-intersection varieties,
the approximation undergoes Krull dimension collapse:

If X is cut out by k equations in ℙ^N with k > N - n = codim(X),
then generic polynomial approximation yields dimension N - k < n.
Poincaré duality fails and the cohomological transfer breaks.

Strategy A bypasses this by reducing to a 1-dimensional base.

---

## 2. The Five Sub-Lemmas

### Sub-lemma 1: Semistable Lefschetz Pencil

**Statement:**
Let X be a smooth projective variety of dimension n over K.
There exists:
  (a) A finite extension K'/K,
  (b) A strictly semistable model 𝒳 over 𝒪_{K'},
  (c) A Lefschetz pencil structure f: 𝒳̃ → ℙ¹_{𝒪_{K'}}
      obtained by blowing up the base locus,
such that the generic fiber of f is X_{K'} and
the special fiber has at worst ordinary quadratic singularities.

**Status:** Known (Jannsen-Saito; Esnault-Kerz 2023).

**References:**
- Jannsen, U., Saito, S. "Lefschetz pencils and semistable reduction"
- Esnault, H., Kerz, M. "Arithmetic Lefschetz theorems" (2023)

**Lean formalization notes:**
This sub-lemma is existential. The formalization requires:
  - Definition of strictly semistable scheme over a DVR
  - Definition of Lefschetz pencil (base locus, blowup, fibral singularities)
  - The statement that such a structure exists after base change
No constructive content is needed; the proof is pure existence via
semistable reduction theorems.

```lean
/-- A strictly semistable model over a DVR -/
structure StrictlySemistableModel (R : ValuationRing) where
  total_space : Scheme
  structure_map : total_space ⟶ Spec R
  is_proper : IsProper structure_map
  is_strictly_semistable : IsStrictlySemistable structure_map

/-- A Lefschetz pencil structure on a semistable model -/
structure LefschetzPencil (R : ValuationRing) extends StrictlySemistableModel R where
  pencil_map : total_space ⟶ ℙ¹_R
  generic_fiber_smooth : IsSmooth (pencil_map.genericFiber)
  singularities_ODP : ∀ s ∈ specialFiber.singLocus,
    IsOrdinaryDoublePoint s

/-- Sub-lemma 1: Existence of semistable Lefschetz pencil -/
axiom sublemma_1 {K : pAdicField} {X : SmoothProjectiveVariety K}
    (hdim : X.dim ≥ 2) :
    ∃ (K' : FiniteExtension K) (𝒳 : LefschetzPencil 𝒪_K'),
      𝒳.genericFiber ≅ X.baseChange K'
```

---

### Sub-lemma 2: Perverse Pushforward via Nearby Cycles

**Statement:**
Let f: 𝒳̃ → ℙ¹_{𝒪_K} be the Lefschetz pencil from Sub-lemma 1.
Let η̄ be the geometric generic point of Spec 𝒪_K and
let s be the closed point (special fiber).

The nearby cycles functor RΨ applied to the relative cohomology
of f produces a perverse sheaf 𝒫 on the special fiber ℙ¹_s = ℙ¹_{𝔽_q}.

More precisely:
  (a) The complex Rf_* RΨ(ℚ_ℓ) on ℙ¹_{𝔽_q} can be decomposed via
      the BBDG decomposition theorem into shifted perverse sheaves.
  (b) The tame inertia I_t of Gal(K̄/K) acts on 𝒫 via a
      nilpotent monodromy operator N_𝒫: 𝒫 → 𝒫(-1).
  (c) The global monodromy operator N on H^i(X_{K̄}, ℚ_ℓ) is
      recovered from N_𝒫 via the hypercohomology spectral sequence.

**Status:** Known (Beilinson-Bernstein-Deligne-Gabber; Grothendieck SGA 7).

**References:**
- Beilinson, A. et al. "Faisceaux pervers" (Astérisque 100, 1982)
- Illusie, L. "Autour du théorème de monodromie locale" (Astérisque 223, 1994)

**Lean formalization notes:**
This requires:
  - Nearby cycles functor RΨ (not yet in Mathlib)
  - Perverse t-structure on D^b_c(ℙ¹_{𝔽_q}, ℚ_ℓ)
  - BBDG decomposition theorem
  - Nilpotent operator from tame inertia action
These are major formalizations. For the proof document, they may
initially be axiomatized with explicit type signatures.

```lean
/-- The nearby cycles functor -/
axiom NearbyCycles {R : DVR} {f : Scheme.Morphism 𝒳 (ℙ¹_R)} :
    D_bc (𝒳.genericFiber) ℚ_ℓ → D_bc (𝒳.specialFiber) ℚ_ℓ

/-- Perverse t-structure on bounded derived category -/
axiom PerversetStructure {k : FiniteField} :
    tStructure (D_bc (ℙ¹_k) ℚ_ℓ)

/-- The Picard-Lefschetz perverse sheaf -/
structure PicardLefschetzSheaf {k : FiniteField} where
  sheaf : Perverse (ℙ¹_k) ℚ_ℓ
  monodromy : sheaf ⟶ sheaf.TateTwist (-1)
  monodromy_nilpotent : IsNilpotent monodromy

/-- Sub-lemma 2: Existence of perverse pushforward -/
axiom sublemma_2 {K : pAdicField} {𝒳 : LefschetzPencil 𝒪_K} :
    ∃ (𝒫 : PicardLefschetzSheaf (residueField K)),
      -- (a) BBDG decomposition holds
      IsPerverseDecomposition (Rf_star_RΨ 𝒳) 𝒫 ∧
      -- (b) Tame inertia acts via nilpotent N
      𝒫.monodromy = tameInertiaAction 𝒳 ∧
      -- (c) Global monodromy recovers from hypercohomology
      ∀ i, monodromyOperator (H_ét i X) =
        hypercohomologyMonodromy 𝒫 i
```

---

### Sub-lemma 3: Stalkwise Purity (Inductive Hypothesis)

**Statement:**
Assume the WMC holds for all smooth projective varieties of
dimension n-1 over finite extensions of K.

Then for the perverse sheaf 𝒫 from Sub-lemma 2:
  (a) The stalks 𝒫_x at each point x ∈ ℙ¹_{𝔽_q} carry weight
      and monodromy filtrations inherited from the fiber X_x.
  (b) These filtrations satisfy the WMC: M_{k+(n-1)} = W_k
      on each stalk.
  (c) Consequently, the graded pieces Gr^M_k(𝒫) are
      pointwise pure perverse sheaves of weight k.

**Status:** Known — this is the inductive hypothesis.

**Lean formalization notes:**
This is the key inductive step. The formalization states that
WMC(n-1) implies stalkwise purity of 𝒫.

```lean
/-- Stalkwise weight-monodromy for perverse sheaf -/
def StalkwiseWMC (𝒫 : PicardLefschetzSheaf k) : Prop :=
  ∀ (x : ℙ¹_k), WMC_holds (𝒫.stalk x) (𝒫.monodromy.stalk x)

/-- Pointwise purity of graded pieces -/
def GradedPiecesArePure (𝒫 : PicardLefschetzSheaf k) : Prop :=
  ∀ (m : ℤ), IsPointwisePure (Gr_M m 𝒫) m

/-- Sub-lemma 3: WMC for fibers implies stalkwise purity -/
axiom sublemma_3 {K : pAdicField} {𝒫 : PicardLefschetzSheaf (residueField K)}
    (h_inductive : ∀ (Y : SmoothProjectiveVariety K),
      Y.dim = n - 1 → WMC_holds_for Y) :
    StalkwiseWMC 𝒫 ∧ GradedPiecesArePure 𝒫
```

---

### Sub-lemma 4: Global Purity via Weil II

**Statement:**
Let 𝒫 be the perverse sheaf from Sub-lemma 2 with stalkwise
purity established by Sub-lemma 3.

Because the base ℙ¹_{𝔽_q} is a smooth projective curve over
a finite field, Deligne's Weil II theorem implies:

  The hypercohomology H^j(ℙ¹_{𝔽_q}, Gr^M_k(𝒫)) is
  Frobenius-pure of weight j + k.

That is, the Frobenius eigenvalues on this cohomology group
have absolute value q^{(j+k)/2}.

**Status:** Known (Deligne, Weil II, 1980).

**References:**
- Deligne, P. "La conjecture de Weil II" (Publ. Math. IHES 52, 1980)

**Lean formalization notes:**
The core content is Deligne's purity theorem for perverse sheaves
on varieties over finite fields. This is a deep result but its
*statement* is clean.

```lean
/-- Frobenius purity for cohomology over finite fields -/
def FrobeniusPure (V : GaloisRepresentation 𝔽_q ℚ_ℓ) (w : ℤ) : Prop :=
  ∀ (α : ℚ̄_ℓ), α ∈ eigenvalues (Frobenius.action V) →
    ∀ (ι : ℚ̄_ℓ →+* ℂ), Complex.abs (ι α) = Real.sqrt (q ^ w)

/-- Sub-lemma 4: Weil II gives global Frobenius purity -/
axiom sublemma_4 {q : ℕ} [Fact (IsPrimePow q)]
    {𝒫 : PicardLefschetzSheaf 𝔽_q}
    (h_stalkwise : GradedPiecesArePure 𝒫) :
    ∀ (j k : ℤ),
      FrobeniusPure (H_hypercohomology j (Gr_M k 𝒫)) (j + k)
```

---

### Sub-lemma 5: The Arithmetic Kashiwara Conjecture [OPEN]

**Statement:**
Let 𝒫 be the Picard-Lefschetz perverse sheaf on ℙ¹_{𝔽_q}
with nilpotent monodromy operator N: 𝒫 → 𝒫(-1),
satisfying stalkwise WMC (Sub-lemma 3) and
global Frobenius purity of graded pieces (Sub-lemma 4).

Consider the weight spectral sequence:

  E₁^{p,q} = H^{p+q}(ℙ¹_{𝔽_q}, Gr^M_{-p}(𝒫)) ⟹ H^{p+q}(ℙ¹_{𝔽_q}, 𝒫)

**Conjecture:**
  (a) This spectral sequence degenerates at E₂.
  (b) The abutment filtration on H^*(ℙ¹, 𝒫) induced by the
      spectral sequence coincides with the monodromy filtration
      induced by the global nilpotent operator
      N_global: H^*(ℙ¹, 𝒫) → H^*(ℙ¹, 𝒫)(-1).

Equivalently: the global monodromy filtration on total
hypercohomology equals the global weight filtration,
i.e., the WMC holds for H^i(X_{K̄}, ℚ_ℓ).

**Status:** OPEN. This is the single remaining obstruction.

**Why this is hard — three independent difficulties:**

(H1) Arithmetic-Geometric Disconnect:
  The Frobenius eigenvalues (controlling weight) live on
  the special fiber over 𝔽_q. The monodromy operator N
  comes from the p-adic inertia group of K. Deligne's
  point-counting machinery on ℙ¹_{𝔽_q} has no mechanism
  to detect or constrain the arithmetic operator N.

(H2) Counterexample for Abstract Sheaves:
  There exist perverse sheaves on curves over finite fields
  with nilpotent endomorphisms satisfying stalkwise WMC
  where the global WMC FAILS. Therefore 𝒫 must carry
  additional geometric structure ("geometric memory") that
  forces the global statement. No algebraic characterization
  of this additional structure is known.

(H3) Missing Arithmetic Polarization:
  Over ℂ, the analogous theorem (Kashiwara's theorem) is
  proved using Saito's Mixed Hodge Module theory, which
  provides a polarization (positive-definite Hermitian metric)
  forcing spectral sequence degeneration. Over 𝔽_q, no
  p-adic analogue of this polarization theory exists.

```lean
/-- Weight spectral sequence for perverse sheaf with monodromy -/
structure WeightSpectralSequence (𝒫 : PicardLefschetzSheaf k) where
  E₁ : ℤ → ℤ → GaloisRepresentation k ℚ_ℓ
  E₁_def : ∀ p q, E₁ p q ≅ H_hypercohomology (p + q) (Gr_M (-p) 𝒫)
  abutment : ℤ → GaloisRepresentation k ℚ_ℓ
  abutment_def : ∀ n, abutment n ≅ H_hypercohomology n 𝒫.sheaf

/-- Sub-lemma 5: The Arithmetic Kashiwara Conjecture [OPEN] -/
conjecture sublemma_5 {q : ℕ} [Fact (IsPrimePow q)]
    {𝒫 : PicardLefschetzSheaf 𝔽_q}
    (h_stalkwise : StalkwiseWMC 𝒫)
    (h_pure_graded : GradedPiecesArePure 𝒫)
    (h_global_purity : ∀ j k, FrobeniusPure (H_hypercohomology j (Gr_M k 𝒫)) (j + k))
    (SS : WeightSpectralSequence 𝒫) :
    -- (a) E₂ degeneration
    SS.degeneratesAt 2 ∧
    -- (b) Abutment filtration = monodromy filtration
    ∀ (n k : ℤ),
      SS.abutmentFiltration n k =
        monodromyFiltration (𝒫.globalMonodromy n) k
```

---

## 3. The Main Theorem: Reduction

**Theorem (Conditional):**
Sub-lemmas 1–5 together imply the Weight-Monodromy Conjecture
for all smooth projective varieties over p-adic fields,
by induction on dimension.

**Proof sketch:**

Base case: dim X = 1 (curves). Known classically.

Inductive step: Assume WMC for all varieties of dimension ≤ n-1.
Let X be smooth projective of dimension n over K.

1. By Sub-lemma 1, after base change to K', obtain a Lefschetz
   pencil f: 𝒳̃ → ℙ¹_{𝒪_{K'}} with generic fiber X_{K'}.

2. By Sub-lemma 2, the relative nearby cycles produce a
   Picard-Lefschetz perverse sheaf 𝒫 on ℙ¹_{𝔽_q} with
   nilpotent monodromy N_𝒫, and the global monodromy on
   H^i(X_{K̄}) is recovered from hypercohomology of 𝒫.

3. By Sub-lemma 3 and the inductive hypothesis (WMC for
   dimension n-1 fibers), 𝒫 has stalkwise WMC and its
   graded pieces Gr^M_k(𝒫) are pointwise pure.

4. By Sub-lemma 4 (Deligne's Weil II), the hypercohomology
   of these graded pieces is Frobenius-pure.

5. By Sub-lemma 5 (Arithmetic Kashiwara), the weight spectral
   sequence degenerates at E₂ and the abutment filtration
   equals the monodromy filtration on total hypercohomology.

6. Combining: the monodromy filtration on H^i(X_{K̄})
   (recovered from 𝒫 by step 2) equals the weight filtration
   (established by steps 4–5). This is the WMC for X.

7. Base change compatibility: WMC for X_{K'} implies WMC for X
   (the filtrations are compatible with finite base change).

```lean
/-- The Weight-Monodromy Conjecture for a variety -/
def WMC (X : SmoothProjectiveVariety K) : Prop :=
  ∀ (i k : ℤ),
    monodromyFiltration (H_ét i X) (k + i) =
      weightFiltration (H_ét i X) k

/-- Main theorem: conditional proof of WMC by induction -/
theorem WMC_from_five_sublemmas
    -- Assume Sub-lemma 5 (the open conjecture)
    (h5 : ∀ {q : ℕ} [Fact (IsPrimePow q)]
      {𝒫 : PicardLefschetzSheaf 𝔽_q}
      (hw : StalkwiseWMC 𝒫) (hp : GradedPiecesArePure 𝒫)
      (hf : ∀ j k, FrobeniusPure (H_hypercohomology j (Gr_M k 𝒫)) (j + k))
      (SS : WeightSpectralSequence 𝒫),
      SS.degeneratesAt 2 ∧
      ∀ n k, SS.abutmentFiltration n k = monodromyFiltration (𝒫.globalMonodromy n) k) :
    -- Then WMC holds for all smooth projective varieties
    ∀ (K : pAdicField) (X : SmoothProjectiveVariety K), WMC X := by
  intro K X
  induction X.dim using Nat.strong_rec_on with
  | base => exact WMC_curves X  -- dim 1: classical
  | step n ih =>
    -- Step 1: Obtain Lefschetz pencil (Sub-lemma 1)
    obtain ⟨K', 𝒳, h_generic⟩ := sublemma_1 (by omega)
    -- Step 2: Obtain perverse sheaf (Sub-lemma 2)
    obtain ⟨𝒫, h_decomp, h_mono, h_recover⟩ := sublemma_2 (𝒳 := 𝒳)
    -- Step 3: Stalkwise purity from inductive hypothesis (Sub-lemma 3)
    have h_stalk : StalkwiseWMC 𝒫 ∧ GradedPiecesArePure 𝒫 :=
      sublemma_3 (fun Y hY => ih Y.dim (by omega) Y)
    -- Step 4: Global Frobenius purity (Sub-lemma 4)
    have h_frob := sublemma_4 h_stalk.2
    -- Step 5: Arithmetic Kashiwara (Sub-lemma 5 — the axiom)
    obtain ⟨h_degen, h_filt⟩ := h5 h_stalk.1 h_stalk.2 h_frob (SS 𝒫)
    -- Step 6: Combine to get WMC for X_{K'}
    have h_WMC_K' := combine_filtrations h_recover h_filt
    -- Step 7: Descend from K' to K
    exact WMC_base_change_descent h_WMC_K' h_generic

```

---

## 4. Formalization Roadmap

### Phase 1: Type Signatures and Axioms (Immediate)

Formalize all definitions and state all five sub-lemmas as axioms.
This produces a machine-checkable *specification* of the reduction.

**Required new Lean/Mathlib definitions:**
- `pAdicField` (extends existing Mathlib p-adic infrastructure)
- `SmoothProjectiveVariety` over a p-adic field
- `EtaleCohomology` with Galois action
- `WeightFiltration` on ℓ-adic cohomology
- `MonodromyFiltration` from nilpotent operator
- `NearbyCycles` functor (axiomatized)
- `Perverset Structure` on D^b_c (axiomatized)
- `PicardLefschetzSheaf` with monodromy
- `WeightSpectralSequence`
- `FrobeniusPure` for Galois representations

**Estimated effort:** 2–4 weeks for experienced Lean/Mathlib contributor.

### Phase 2: Formalize Sub-lemmas 1–4 (Medium-term)

Replace axioms with proofs for the four known sub-lemmas.

**Sub-lemma 1:** Requires formalized semistable reduction.
  Depends on: resolution of singularities (partially in Mathlib),
  DVR theory (well-developed in Mathlib).
  Estimated effort: 3–6 months.

**Sub-lemma 2:** Requires formalized derived categories and
  perverse sheaves. This is a major Mathlib extension.
  Estimated effort: 6–12 months (may overlap with ongoing projects).

**Sub-lemma 3:** Relatively straightforward once Sub-lemma 2
  infrastructure exists — it's essentially an application of
  definitions plus the inductive hypothesis.
  Estimated effort: 1–2 months (after Sub-lemma 2).

**Sub-lemma 4:** Requires formalized Weil II. This is one of
  the deepest results in algebraic geometry. Full formalization
  is a multi-year project, but the *statement* can be axiomatized
  cleanly and the *application* to pure perverse sheaves on curves
  is relatively direct.
  Estimated effort: Axiomatize statement (1 month);
  full proof (2–5 years, likely a separate project).

### Phase 3: Attack Sub-lemma 5 (Research frontier)

With Sub-lemmas 1–4 formalized, Sub-lemma 5 stands as a
precisely typed open conjecture. Possible AI-assisted approaches:

**(A) Formal search within existing frameworks:**
  State candidate lemmas that would imply Sub-lemma 5 and use
  automated theorem provers to check their consistency and
  explore consequences. The type system prevents false proofs
  from going undetected.

**(B) Explore the counterexample space:**
  Formally construct examples of perverse sheaves with nilpotent
  operators where global WMC fails (difficulty H2). Characterize
  the precise algebraic property that distinguishes geometric
  sheaves from abstract counterexamples.

**(C) Formalize the complex-analytic analogue:**
  Formalize Kashiwara's theorem via Saito's MHM theory over ℂ.
  Identify exactly which steps use the Hodge metric.
  This produces a formal "proof with holes" where each hole
  corresponds to a missing p-adic ingredient.

**(D) Constructive calibration (NEW — see Section 7):**
  Formalize Theorems C1–C4 establishing that:
  - Polarization-based proofs are impossible over p-adic fields (C3)
  - Abstract degeneration is equivalent to LPO (C2)
  - Geometric origin descends coefficients to ℚ̄ where LPO is trivial (C4)
  Then pursue the weight purity propagation attack (Section 7.7,
  direction 2): show that weight incompatibility forces the
  ℚ̄-valued spectral sequence differentials to vanish.

  This is the RECOMMENDED primary attack vector because:
  (i)   C1 and C2 are fully provable with existing Mathlib
  (ii)  C3 requires only standard quadratic form theory
  (iii) The weight purity argument is closest to existing
        formalized infrastructure
  (iv)  It produces publishable results even if the full
        conjecture remains open

---

## 5. Dependency Graph

```
WMC (all smooth projective varieties, mixed characteristic)
  │
  ├── Sub-lemma 1: Semistable Lefschetz pencil [KNOWN]
  │     └── Semistable reduction theorem
  │     └── Lefschetz pencil theory
  │
  ├── Sub-lemma 2: Perverse pushforward [KNOWN]
  │     └── Nearby cycles functor (SGA 7)
  │     └── BBDG decomposition theorem
  │     └── Tame inertia action
  │
  ├── Sub-lemma 3: Stalkwise purity [KNOWN, inductive]
  │     └── WMC for dimension n-1 (inductive hypothesis)
  │     └── Fiber cohomology computation
  │
  ├── Sub-lemma 4: Global Frobenius purity [KNOWN]
  │     └── Deligne's Weil II (1980)
  │     └── Purity for perverse sheaves on curves/𝔽_q
  │
  └── Sub-lemma 5: Arithmetic Kashiwara [OPEN]
        │
        ├── Difficulty H1: Arithmetic-geometric disconnect
        ├── Difficulty H2: Fails for abstract sheaves
        ├── Difficulty H3: No arithmetic polarization
        │     └── Missing: p-adic Mixed Hodge Modules
        │     └── Missing: Arithmetic polarization theory
        │     └── Analogue: Saito MHM / Kashiwara theorem over ℂ
        │
        └── CONSTRUCTIVE CALIBRATION (Section 7)
              │
              ├── Theorem C1: Polarization ⟹ degeneration in BISH
              │     └── Hodge Laplacian identity
              │     └── Positive-definite ⟹ equational d_r = 0
              │     └── No omniscience principle required
              │
              ├── Theorem C2: Abstract degeneration ↔ LPO(ℚ_ℓ)
              │     └── (⟸) LPO gives decidable zero-testing
              │     └── (⟹) Degeneration oracle decides x = 0 ∨ x ≠ 0
              │     └── Decidability question: "is this ℓ-adic cycle
              │           boundary exactly homologous to zero?"
              │
              ├── Theorem C3: Archimedean Positivity Obstruction
              │     └── u-invariant of ℚ_p is 4
              │     └── Hermitian forms dim ≥ 3 are isotropic over ℚ_p
              │     └── Polarization strategy algebraically impossible
              │     └── Kashiwara's metric argument cannot be adapted
              │
              └── Theorem C4: Geometric origin as de-omniscientizing descent
                    └── Algebraic cycles force coefficients to ℚ̄
                    └── ℚ̄ has decidable equality (in BISH)
                    └── Geometry replaces LPO with discrete decidability
                    └── KEY INSIGHT: "geometric memory" = algebraicity
```

---

## 6. Key Literature

### Foundational

1. Deligne, P. "La conjecture de Weil I" (Publ. Math. IHES 43, 1974)
2. Deligne, P. "La conjecture de Weil II" (Publ. Math. IHES 52, 1980)
3. Beilinson, A., Bernstein, J., Deligne, P., Gabber, O.
   "Faisceaux pervers" (Astérisque 100, 1982)
4. Grothendieck, A. et al. SGA 7 "Groupes de monodromie en
   géométrie algébrique" (Springer LNM 288/340, 1972-73)
5. Saito, M. "Modules de Hodge polarisables" (Publ. RIMS 24, 1988)
6. Saito, M. "Mixed Hodge modules" (Publ. RIMS 26, 1990)

### Scholze's Perfectoid Architecture

7. Scholze, P. "Perfectoid spaces" (Publ. Math. IHES 116, 2012)
8. Scholze, P. "Perfectoid spaces: A survey" (Proc. ICM 2014)
9. Fargues, L., Scholze, P. "Geometrization of the local
   Langlands correspondence" (Annals of Math. Studies, 2024)

### Strategy A (Lefschetz Pencil Reduction)

10. Esnault, H., Kerz, M. "Arithmetic Lefschetz theorems" (2023)
11. Ito, T. "Weight-monodromy conjecture for p-adically uniformized
    varieties" (Invent. Math. 159, 2005)
12. Rapoport, M., Zink, T. "Über die lokale Zetafunktion von
    Shimuravarietäten" (Invent. Math. 68, 1982)

### Recent Advances

13. Wear, P. "Weight-monodromy for complete intersections in
    abelian varieties" (2023)
14. Binda, F., Kato, H., Vezzani, A. "The p-adic weight-monodromy
    conjecture for complete intersections" (2022)
15. Ito, K. "Torsion weight-monodromy for complete intersections" (2021)

### Constructive Mathematics and Logical Calibration

16. Bishop, E., Bridges, D. "Constructive Analysis" (Springer, 1985)
17. Bridges, D., Richman, F. "Varieties of Constructive Mathematics"
    (LMS Lecture Notes 97, Cambridge, 1987)
18. Ishihara, H. "Reverse mathematics in Bishop's constructive
    mathematics" (Philosophia Scientiae, 2006)
19. Bridges, D., Vita, L. "Techniques of Constructive Analysis"
    (Springer, 2006)

### Quadratic Forms and Local Fields

20. Lam, T.Y. "Introduction to Quadratic Forms over Fields"
    (AMS Graduate Studies in Mathematics 67, 2005)
21. Serre, J.-P. "A Course in Arithmetic" (Springer GTM 7, 1973)
    — Chapters IV-V on quadratic forms over ℚ_p
22. O'Meara, O.T. "Introduction to Quadratic Forms" (Springer, 1963)

### Prismatic Cohomology

23. Bhatt, B., Scholze, P. "Prisms and prismatic cohomology"
    (Annals of Math. 196, 2022)
24. Bhatt, B., Scholze, P. "Prismatic F-crystals and crystalline
    Galois representations" (Cambridge J. Math. 11, 2023)

---

## 7. Constructive Calibration of Sub-lemma 5

### 7.1 Overview

Constructive Reverse Mathematics (CRM) calibrates mathematical
statements against logical principles of increasing strength:

  BISH ⊂ BISH+MP ⊂ BISH+LLPO ⊂ BISH+LPO ⊂ CLASS (full EM)

where:
  BISH  = Bishop's constructive mathematics (no omniscience)
  MP    = Markov's Principle (¬¬P → P for decidable P)
  LLPO  = Lesser Limited Principle of Omniscience
  LPO   = Limited Principle of Omniscience (∀x∈K, x=0 ∨ x≠0)
  EM    = Excluded Middle (full classical logic)

The key insight: when a theorem requires more logical strength than
expected, it signals hidden non-constructive content. Identifying
this content often reveals the structural essence of the difficulty.

Applied to Sub-lemma 5, this methodology produces four theorems (C1–C4)
that together reframe "geometric memory" as a constructive phenomenon:
algebraicity of coefficients.

### 7.2 Theorem C1: Polarization Implies Degeneration in BISH

**Statement:**
Let (V, d_r, H) be a filtered cochain complex over ℂ where:
  - V is a finite-dimensional ℂ-vector space with filtration
  - d_r: E_r^{p,q} → E_r^{p+r, q-r+1} are spectral sequence differentials
  - H is a positive-definite Hermitian form compatible with the filtration
  - Weight grading constraints force the Hodge Laplacian Δ = d_r d_r* + d_r* d_r
    to satisfy Δ = 0 on weight-pure subspaces

Then d_r = 0 for all r ≥ 2 (E₂ degeneration), and this is provable
in BISH with no omniscience principles.

**Proof sketch:**
The Hodge Laplacian identity gives:
  H(Δx, x) = H(d_r x, d_r x) + H(d_r* x, d_r* x) = 0

Because H is positive-definite:
  H(v, v) = 0  ⟹  v = 0    (for all v)

This is an equational deduction, not a decidability question.
From H(d_r x, d_r x) = 0 we get d_r x = 0 for all x.
No zero-testing is required. The positive-definite metric
converts what would be a decidability problem into an
equational identity.

**Constructive content:** The polarization is a COMPUTATIONAL BYPASS
around the need for omniscience. It replaces "decide whether d_r = 0"
with "compute H(d_r x, d_r x) and observe it equals 0 by algebra."

```lean
/-- A polarized filtered complex -/
structure PolarizedComplex (V : Type) [AddCommGroup V] [Module ℂ V] where
  d : V →ₗ[ℂ] V
  H : V →ₗ[ℂ] V →ₗ[ℂ] ℂ
  H_pos_def : ∀ v, v ≠ 0 → 0 < (H v v).re
  H_hermitian : ∀ u v, H u v = starRingEnd ℂ (H v u)
  d_adjoint : V →ₗ[ℂ] V  -- d* with respect to H
  adjoint_prop : ∀ u v, H (d u) v = H u (d_adjoint v)

/-- Theorem C1: Polarization forces degeneration constructively -/
theorem polarization_forces_degeneration_BISH
    (C : PolarizedComplex V)
    (h_laplacian_zero : ∀ x, C.d (C.d_adjoint x) + C.d_adjoint (C.d x) = 0) :
    C.d = 0 := by
  ext x
  -- From Laplacian identity: H(d x, d x) + H(d* x, d* x) = 0
  -- Both terms are non-negative reals (H is positive-definite)
  -- Therefore both are zero
  -- H(d x, d x) = 0 and H positive-definite ⟹ d x = 0
  sorry -- Full proof requires Mathlib Hermitian form API
```

### 7.3 Theorem C2: Abstract Degeneration ↔ LPO

**Statement:**
Let K be a complete non-Archimedean field (e.g., ℚ_ℓ).
Define:

  LPO(K) := ∀ x : K, x = 0 ∨ x ≠ 0

  DecidesDegeneration(K) := for any abstract filtered perverse sheaf
    over K with nilpotent endomorphism satisfying stalkwise WMC,
    there exists an algorithm that determines whether the weight
    spectral sequence degenerates at E₂.

Then: DecidesDegeneration(K) ↔ LPO(K).

**Proof sketch (⟸):**
If LPO(K) holds, equality in K is decidable. Given the spectral
sequence differential d₁ as a matrix with entries in K, we can:
  1. Decide whether each entry is zero or nonzero
  2. Compute exact rank via Gaussian elimination
  3. Compute ker(d₁) and im(d₁) as explicit subspaces
  4. Construct E₂ = ker(d₁)/im(d₁) as a finite-dimensional space
  5. Represent d₂ as a matrix and decide whether d₂ = 0
All steps are constructive given LPO.

**Proof sketch (⟹):**
Let x ∈ K be arbitrary. Construct a 1-dimensional abstract
filtered complex where d₂ is the 1×1 matrix [x].
An algorithm that decides "d₂ = 0" for arbitrary such complexes
gives an oracle for "x = 0 ∨ x ≠ 0", which is LPO(K).

**The decidability question LPO resolves:**
"Is this specific ℓ-adic cycle boundary exactly homologous to zero?"

```lean
/-- LPO for a field K -/
def LPO (K : Type) [Zero K] : Prop :=
  ∀ x : K, x = 0 ∨ x ≠ 0

/-- An abstract weight spectral sequence over K -/
structure AbstractWSS (K : Type) [Field K] where
  E₁ : Type
  [E₁_mod : Module K E₁]
  [E₁_fin : FiniteDimensional K E₁]
  d₁ : E₁ →ₗ[K] E₁
  d₁_sq_zero : d₁ ∘ₗ d₁ = 0

/-- Decidability of E₂ degeneration -/
def DecidesDegeneration (K : Type) [Field K] : Prop :=
  ∀ (wss : AbstractWSS K), Decidable (wss.d₁ = 0)

/-- Theorem C2: Abstract degeneration decidability ↔ LPO -/
theorem abstract_degeneration_iff_LPO (K : Type) [Field K] :
    DecidesDegeneration K ↔ LPO K := by
  constructor
  · -- (⟹) Degeneration oracle gives LPO
    intro h_decides x
    -- Construct 1-dim complex with d = [x]
    let wss : AbstractWSS K := ⟨K, x • LinearMap.id, by ring⟩
    -- h_decides wss tells us d = 0 or d ≠ 0, which is x = 0 or x ≠ 0
    sorry
  · -- (⟸) LPO gives degeneration decidability
    intro h_lpo wss
    -- With decidable equality, use Gaussian elimination
    sorry
```

### 7.4 Theorem C3: Archimedean Positivity Obstruction

**Statement:**
Let K be a finite extension of ℚ_p. The u-invariant of K is 4,
meaning every quadratic form over K of dimension ≥ 5 is isotropic.
For Hermitian forms over quadratic extensions L/K, forms of
dimension ≥ 3 are isotropic.

Consequence: For any smooth projective variety X/K with
dim H^n_ét(X, ℚ_ℓ) ≥ 3 (which holds for all non-trivial
cases of the WMC), there exists NO positive-definite
Hermitian form on the cohomology compatible with the
Galois action.

Therefore, Saito/Kashiwara's polarization strategy for proving
spectral sequence degeneration is algebraically impossible in
the p-adic setting. Any proof of the Arithmetic Kashiwara
Conjecture must use a fundamentally different mechanism.

**Proof sketch:**
By the Hasse-Minkowski theorem and local class field theory:
  u(ℚ_p) = 4 for all primes p.

For a Hermitian form H: V × V → L over a quadratic extension L/K:
  If dim_L(V) ≥ 3, then H is isotropic.
  That is, ∃ v ≠ 0 such that H(v,v) = 0.

If H(v,v) = 0 for some nonzero v, then the argument in Theorem C1
fails: from H(d_r x, d_r x) = 0 we CANNOT conclude d_r x = 0.
The equational bypass that works over ℂ (where positive-definiteness
is possible in all dimensions) collapses over ℚ_p.

**Significance:** This is not a failure of technique but an
algebraic impossibility. It permanently eliminates one entire
class of proof strategies for the WMC.

```lean
/-- The u-invariant of a field -/
def uInvariant (K : Type) [Field K] : ℕ :=
  sSup { n | ∃ Q : QuadraticForm K (Fin n → K), Q.IsAnisotropic }

/-- Theorem C3: u-invariant of ℚ_p is 4 -/
axiom u_invariant_Qp (p : ℕ) [Fact (Nat.Prime p)] :
    uInvariant (PadicField p) = 4

/-- Consequence: No positive-definite Hermitian form in high dimension -/
theorem no_pos_def_hermitian_padic
    {p : ℕ} [Fact (Nat.Prime p)]
    {L : Type} [Field L] [Algebra (PadicField p) L]
    (hL : FiniteDimensional.finrank (PadicField p) L = 2)
    {V : Type} [AddCommGroup V] [Module L V]
    (hV : FiniteDimensional.finrank L V ≥ 3)
    (H : V →ₗ[L] V →ₗ[L] L)
    (hH : IsHermitian H) :
    ∃ v : V, v ≠ 0 ∧ H v v = 0 := by
  sorry -- Follows from Hasse-Minkowski + u-invariant bound
```

### 7.5 Theorem C4: Geometric Origin as De-Omniscientizing Descent

**Statement:**
Let 𝒫 be a perverse sheaf on ℙ¹_{𝔽_q} arising from the nearby
cycles of a smooth projective variety X over K (a p-adic field).

Then the spectral sequence differentials d_r of the weight spectral
sequence for 𝒫 have matrix entries in ℚ̄ (the algebraic closure
of ℚ inside ℚ̄_ℓ), not merely in ℚ_ℓ.

Over ℚ̄, equality is decidable in BISH: given two algebraic numbers,
there exists a finite algorithm to determine whether they are equal
(compute minimal polynomials and compare).

Consequently, for geometric perverse sheaves, the decidability question
"is d_r = 0?" does NOT require LPO(ℚ_ℓ). It reduces to decidable
equality in ℚ̄, which is available in BISH.

**The key insight:**
Geometric origin provides a DE-OMNISCIENTIZING DESCENT:

  Abstract sheaves over ℚ_ℓ: degeneration requires LPO(ℚ_ℓ)
  Geometric sheaves:          coefficients descend to ℚ̄
  Over ℚ̄:                    equality decidable in BISH
  Therefore:                  degeneration decidable in BISH

"Geometric memory" IS algebraicity of coefficients.

The reason the Arithmetic Kashiwara Conjecture fails for abstract
sheaves but (conjecturally) holds for geometric ones is precisely
that geometric sheaves live in a decidable sub-universe (ℚ̄) of
the undecidable ambient field (ℚ_ℓ).

**Why this doesn't immediately prove the conjecture:**
Knowing that the matrix entries of d_r are algebraic numbers
(and hence decidably testable for zero) tells us that the
QUESTION "is d_r = 0?" is decidable. It does NOT tell us that
the ANSWER is "yes." We still need to prove that d_r actually
equals zero, which requires understanding the arithmetic geometry
that forces these algebraic numbers to vanish.

However, this reframing transforms the problem:
  OLD: "Prove d_r = 0 using a polarization argument"
       (impossible by Theorem C3)
  NEW: "Prove that the algebraic numbers appearing as matrix entries
       of d_r are forced to vanish by the arithmetic geometry of X"

The new formulation suggests specific attack vectors:
  (a) Use Galois symmetry constraints on ℚ̄-valued matrices
  (b) Use motivic weight arguments to show entries lie in specific
      number fields with constrained Galois action
  (c) Use Langlands functoriality to relate the spectral sequence
      to automorphic L-functions whose special values are known

```lean
/-- Algebraic closure of ℚ inside ℚ_ℓ -/
axiom QBar_in_Ql : Subalgebra ℚ ℚ_ℓ

/-- Decidable equality in ℚ̄ (constructively valid) -/
axiom QBar_decidable_eq : DecidableEq QBar_in_Ql

/-- Geometric perverse sheaves have algebraic coefficients -/
axiom geometric_sheaf_algebraic
    {𝒫 : PicardLefschetzSheaf 𝔽_q}
    (h_geometric : IsGeometric 𝒫)
    (SS : WeightSpectralSequence 𝒫) :
    ∀ (r : ℕ) (p q : ℤ),
      MatrixEntries (SS.differential r p q) ⊆ QBar_in_Ql

/-- Theorem C4: For geometric sheaves, degeneration is decidable in BISH -/
theorem geometric_degeneration_decidable_BISH
    {𝒫 : PicardLefschetzSheaf 𝔽_q}
    (h_geometric : IsGeometric 𝒫)
    (SS : WeightSpectralSequence 𝒫)
    (h_alg : ∀ r p q, MatrixEntries (SS.differential r p q) ⊆ QBar_in_Ql) :
    Decidable (∀ r ≥ 2, SS.differential r = 0) := by
  -- Matrix entries are in ℚ̄ where equality is decidable
  -- Finite matrix, finitely many entries, each decidably zero or not
  -- Therefore the conjunction "all entries zero" is decidable
  exact decidable_of_iff _ (by sorry)

/-- The de-omniscientizing descent: what geometric origin provides -/
theorem de_omniscientizing_descent
    {𝒫 : PicardLefschetzSheaf 𝔽_q}
    (h_geometric : IsGeometric 𝒫) :
    -- Abstract version requires LPO
    -- Geometric version is decidable in BISH
    -- The gap is precisely algebraicity of coefficients
    (DecidesDegeneration ℚ_ℓ ↔ LPO ℚ_ℓ) ∧
    (∀ SS : WeightSpectralSequence 𝒫,
      Decidable (∀ r ≥ 2, SS.differential r = 0)) := by
  exact ⟨abstract_degeneration_iff_LPO ℚ_ℓ,
         fun SS => geometric_degeneration_decidable_BISH h_geometric SS
           (geometric_sheaf_algebraic h_geometric SS)⟩
```

### 7.6 Summary: The Constructive Landscape

```
Degeneration of weight spectral sequence
  │
  ├── Over ℂ (Kashiwara's theorem) ──── PROVED
  │     │
  │     └── Mechanism: Hodge polarization (positive-definite metric)
  │     └── Constructive strength: BISH (no omniscience needed)
  │     └── Key property: anisotropy in all dimensions over ℝ
  │
  ├── Over ℚ_ℓ, ABSTRACT sheaves ──── FALSE (counterexamples exist)
  │     │
  │     └── Obstruction: requires LPO(ℚ_ℓ) to even decide
  │     └── Constructive strength: equivalent to LPO
  │     └── Decidability question: "is this ℓ-adic boundary zero?"
  │
  ├── Over ℚ_ℓ, GEOMETRIC sheaves ──── OPEN (Arithmetic Kashiwara)
  │     │
  │     └── Decidability: BISH (coefficients descend to ℚ̄)
  │     └── Missing: proof that the decidable answer is "yes"
  │     └── Geometric memory = algebraicity of coefficients
  │     └── Polarization strategy IMPOSSIBLE (Theorem C3)
  │
  └── NEW ATTACK VECTORS (from constructive reframing)
        ├── (a) Galois symmetry constraints on ℚ̄-valued matrices
        ├── (b) Motivic weight arguments for coefficient number fields
        └── (c) Langlands functoriality → L-function special values
```

### 7.7 Actionable Research Program

The constructive calibration reduces the Arithmetic Kashiwara
Conjecture to the following concrete question:

**Central Question:** Let d_r be the r-th differential of the
weight spectral sequence for a geometric perverse sheaf 𝒫 on
ℙ¹_{𝔽_q}. The matrix entries of d_r are algebraic numbers
(elements of ℚ̄). PROVE THEY ARE ALL ZERO.

This is a question about specific algebraic numbers, not about
abstract linear algebra over ℚ_ℓ. It can be attacked by:

1. **Galois constraints:** The matrix d_r is equivariant for the
   action of Gal(ℚ̄/ℚ) on the coefficients. If the representation-
   theoretic constraints from this Galois action force the only
   equivariant map to be zero, we are done. This reduces to a
   (possibly tractable) representation theory computation.

2. **Weight purity propagation:** The E₁ page has pure weights
   (by Sub-lemma 4). If d_r maps between spaces of different
   weight and we can show the algebraic numbers in d_r must
   respect weight, then weight incompatibility forces d_r = 0.
   This is close to Deligne's original argument in Weil II and
   may be formalizable.

3. **L-function connection:** By Grothendieck's trace formula,
   the spectral sequence differentials are related to special
   values of L-functions. If these special values are known to
   vanish (by automorphic methods or Langlands functoriality),
   this directly gives d_r = 0.

Each of these is a well-defined research direction that an AI
proof assistant could explore systematically, especially
direction (2) which is closest to existing Lean/Mathlib
infrastructure for weight arguments.

---

## 8. Notes for AI Agent

### What this document is

This is a specification for formally verifying that the general
Weight-Monodromy Conjecture in mixed characteristic REDUCES to
a single open conjecture (Sub-lemma 5 / Arithmetic Kashiwara),
AND that constructive reverse mathematics calibrates this
conjecture's logical strength, identifying geometric origin
as a de-omniscientizing descent from LPO to decidable equality.

### What success looks like

A Lean 4 file that:
1. Defines all relevant mathematical structures
2. States Sub-lemmas 1–4 (initially as axioms, eventually as theorems)
3. States Sub-lemma 5 as a conjecture with full type signature
4. Proves: Sub-lemma 1 ∧ 2 ∧ 3 ∧ 4 ∧ 5 → WMC (by induction on dimension)
5. Formalizes Theorems C1–C4 (constructive calibration):
   - C1: Polarization ⟹ degeneration in BISH (prove fully)
   - C2: Abstract degeneration ↔ LPO (prove fully)
   - C3: u-invariant obstruction (axiomatize Hasse-Minkowski, prove consequence)
   - C4: Geometric descent to ℚ̄ (axiomatize algebraicity, prove decidability)
6. States the de-omniscientizing descent as a formal theorem
7. Type-checks against Mathlib4

### Priority ordering for formalization

Phase 1 (immediate): Type signatures and axioms for everything.
Phase 2a (high priority): Theorems C1 and C2 — these are
  self-contained and provable with existing Mathlib infrastructure
  for linear algebra, Hermitian forms, and decidability.
Phase 2b (medium priority): Sub-lemmas 1–4 as axioms, main
  reduction theorem.
Phase 3a (research): Theorem C3 — requires formalizing
  u-invariant theory (partially in Mathlib via quadratic forms).
Phase 3b (research): Theorem C4 — requires formalizing the
  algebraicity of geometric sheaf coefficients (deep, but the
  STATEMENT is clean).
Phase 4 (frontier): Attack the Central Question from Section 7.7
  using the three identified vectors.

### What is NOT expected

- A proof of Sub-lemma 5 (this is a major open problem)
- Full formalization of Weil II or BBDG (these are multi-year projects)
- Constructive content for existential sub-lemmas (classical logic is fine)
- A proof that the algebraic numbers in d_r vanish (this IS the open problem)

### Key conceptual point for the AI agent

The constructive calibration is NOT merely a philosophical gloss.
It provides a concrete new proof strategy:

  OLD strategy (blocked by Theorem C3):
    Find a p-adic polarization → force degeneration by metric rigidity

  NEW strategy (opened by Theorem C4):
    Show coefficients are algebraic → use weight/Galois constraints
    on algebraic numbers → prove they vanish

The AI agent should prioritize exploring direction (2) from Section 7.7
(weight purity propagation) as the most tractable: if d_r maps between
pure spaces of different weight, and the matrix entries respect weight,
then d_r = 0 by weight incompatibility. This is close to arguments
already formalized in weight filtration libraries.

### Recommended starting point

Begin with Phase 2a: formalize Theorems C1 and C2. These are the
cleanest results, require only standard linear algebra, and produce
the foundational calibration that the rest depends on. The equivalence
C2 (abstract degeneration ↔ LPO) in particular is a publishable
result in constructive mathematics independent of the WMC context.
