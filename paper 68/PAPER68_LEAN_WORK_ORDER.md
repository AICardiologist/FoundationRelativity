# PAPER 68 LEAN AGENT WORK ORDER
## Verification of the Logical Architecture of Wiles's Proof
### Two targets. Do them in order.

---

## CONTEXT

Paper 68 performs a constructive reverse mathematics (CRM) audit of Wiles's proof of Fermat's Last Theorem (the modularity of semistable elliptic curves over ℚ). The audit classifies each stage of the Taylor-Wiles method against the hierarchy BISH ⊂ MP ⊂ WLPO ⊂ LPO ⊂ CLASS.

The deep theorems (Brochard, Langlands-Tunnell, effective Chebotarev, etc.) are AXIOMATISED and clearly flagged. The Lean code verifies the LOGICAL ASSEMBLY — the conditional implications that produce the final classification from the axiomatised inputs.

This is the same methodology as Papers 56–62 in the CRM series: axiomatise deep inputs, verify logical structure on top, zero sorry.

---

## TARGET 1: Stage 5 is BISH (200–400 lines)

### What to prove

The Taylor-Wiles patching step (Stage 5) is a BISH-decidable finite computation, given three axiomatised inputs.

### Axioms to declare

```lean
-- Axiom B1: Brochard's finite-level criterion (de Smit's conjecture)
-- If the Artinian quotient at level n=2 satisfies the embedding
-- dimension condition, then the patched module is free (R ≅ T).
-- Reference: Brochard, Compositio Math. 153 (2017), Theorem 1.1.
axiom brochard_finite_criterion
  (A B : ArtinLocalRing) (M : Module B)
  (hflat : IsFlat A M)
  (hedim : embDim B ≤ embDim A) :
  IsFree B M

-- Axiom B2: Effective Chebotarev (unconditional)
-- For a finite Galois extension L/ℚ with computable absolute
-- discriminant d_L, and a conjugacy class C in Gal(L/ℚ),
-- there exists a prime q ≤ d_L^K with Frob(q) ∈ C,
-- where K = 12577 is an absolute constant (Ahn-Kwon 2019).
-- Reference: Lagarias-Montgomery-Odlyzko (1979); Ahn-Kwon (2019).
axiom effective_chebotarev
  (L : NumberField) (C : ConjClass (Gal L ℚ))
  (d_L : ℕ) (hdisc : absDisc L = d_L) :
  ∃ q : ℕ, q.Prime ∧ q ≤ d_L ^ 12577 ∧ frob L q ∈ C

-- Axiom B3: Discriminant computability
-- The splitting field L_2 for the Taylor-Wiles application at
-- level n=2 has discriminant computable from (N, p, ρ̄).
-- Reference: Standard algebraic number theory (Hensel bounds).
axiom tw_disc_computable
  (N p : ℕ) (ρbar : ResidualRep N p) :
  ∃ d : ℕ, absDisc (tw_splitting_field N p 2 ρbar) = d
```

### What the proof should establish

1. Define a `TWPrimeSearch` structure: input (N, p, ρ̄), output a set Q of r primes satisfying the TW conditions, with a computable search bound.

2. Prove `tw_prime_search_terminates`: the search for TW primes at level n=2 terminates within d_L^12577 steps. This is a direct application of B2 and B3.

3. Prove `stage5_is_bish`: combining B1 (finite-level criterion eliminates infinite patching) with `tw_prime_search_terminates` (prime search is bounded), the entire Stage 5 is a finite computation.

### Structural notes

- You will need to define placeholder types for `ArtinLocalRing`, `NumberField`, `ResidualRep`, etc. These are opaque types — the Lean code does not need their internals, only the axiomatised properties.
- The proof that Stage 5 is BISH should be a CONDITIONAL theorem: "Given axioms B1–B3, Stage 5 is decidable by a terminating algorithm with precomputed bound."
- Use `Decidable` or a custom `BISHDecidable` predicate to formalise "BISH-decidable."
- The key logical step: B1 reduces the infinite patching to a finite check → B3 computes the discriminant → B2 bounds the prime search → the composition is a finite algorithm.

### Guardrails

- Do NOT attempt to formalise Brochard's proof, effective Chebotarev, or discriminant bounds. These are axioms.
- Do NOT use `sorry`. If a step is unclear, add an axiom and flag it.
- Do NOT import heavy Mathlib dependencies unless strictly necessary. This is lightweight logic over opaque types.
- Every axiom must have a comment with the precise mathematical reference (author, year, theorem number).
- Test that the file compiles with zero errors, zero warnings, zero sorries before delivering.

---

## TARGET 2: The Asymmetry Theorem (100–200 lines)

### What to prove

The overall classification of Wiles's proof is BISH + WLPO, and the WLPO is localised entirely in Stage 1 (Langlands-Tunnell).

### Axioms to declare

```lean
-- The CRM hierarchy as an inductive type
inductive CRMLevel where
  | BISH : CRMLevel
  | MP   : CRMLevel
  | LLPO : CRMLevel
  | WLPO : CRMLevel
  | LPO  : CRMLevel
  | CLASS : CRMLevel
  deriving DecidableEq, Repr

-- Order on the hierarchy
instance : LE CRMLevel where
  le a b := -- BISH ≤ MP ≤ LLPO ≤ WLPO ≤ LPO ≤ CLASS
  ...

-- Axiom: Stage 1 (Langlands-Tunnell) requires WLPO
axiom stage1_classification : CRMLevel := CRMLevel.WLPO

-- Axiom: Stages 2–5 are BISH
-- (Stage 5 from Target 1; Stages 2–3 by inspection;
--  Stage 4 collapsed into Stage 5)
axiom stage2_classification : CRMLevel := CRMLevel.BISH
axiom stage3_classification : CRMLevel := CRMLevel.BISH
axiom stage4_cm_classification : CRMLevel := CRMLevel.BISH
axiom stage5_classification : CRMLevel := CRMLevel.BISH

-- The join (maximum) operation on CRM levels
def crmJoin : CRMLevel → CRMLevel → CRMLevel := max
```

### What the proof should establish

1. `wiles_proof_classification`: the join of all stage classifications is WLPO.
   ```lean
   theorem wiles_proof_classification :
     crmJoin stage1_classification
       (crmJoin stage2_classification
         (crmJoin stage3_classification
           (crmJoin stage4_cm_classification
             stage5_classification))) = CRMLevel.WLPO
   ```

2. `wlpo_localisation`: removing Stage 1 drops the classification to BISH.
   ```lean
   theorem wlpo_localisation :
     crmJoin stage2_classification
       (crmJoin stage3_classification
         (crmJoin stage4_cm_classification
           stage5_classification)) = CRMLevel.BISH
   ```

3. `asymmetry_theorem`: the non-constructive content is entirely in Stage 1.
   ```lean
   theorem asymmetry_theorem :
     wiles_proof_classification = CRMLevel.WLPO ∧
     wlpo_localisation_result = CRMLevel.BISH
   ```

### Guardrails

- This is lightweight. The CRM hierarchy is a finite enum with a total order. The proof is `rfl` or `simp` after the definitions are set up.
- The VALUE of formalising this is not the difficulty of the proof but the CLARITY of the statement: it makes the asymmetry machine-checkable and unambiguous.
- Include doc-strings on every axiom explaining the mathematical justification.
- Include a comment block at the top listing all axiomatised deep theorems with references.
- Zero sorry, zero warnings, zero errors.

---

## DELIVERABLES

1. `Paper68_Stage5.lean` — Target 1 (Stage 5 is BISH)
2. `Paper68_Asymmetry.lean` — Target 2 (asymmetry theorem)
3. `Paper68_Axioms.lean` — Shared axiom file imported by both
4. Brief text summary: list of all axioms with references, total line count, confirmation of 0 sorry

---

## WHAT NOT TO DO

- Do not formalise any deep theorem (Brochard, Chebotarev, trace formula, Langlands-Tunnell)
- Do not attempt to define number fields, Galois groups, or modular forms in Lean from scratch
- Do not import Mathlib modules unless you need a specific lemma (e.g., `Order.max`)
- Do not spend time on elegance — correctness and clarity are the only goals
- Do not produce more than 600 lines total across all files
