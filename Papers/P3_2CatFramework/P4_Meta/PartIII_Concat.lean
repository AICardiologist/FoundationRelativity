/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_Concat.lean

  Two‑phase composition of ladders:
  concatSteps k A B takes the first k steps from A, then continues with B.
  We prove stage equalities and provide certificate transformers.
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductSup

namespace Papers.P4Meta

/-- Concatenate two step functions: first k steps from A, then B. -/
def concatSteps (k : Nat) (A B : Nat → Formula) : Nat → Formula :=
  fun i => if i < k then A i else B (i - k)

@[simp] theorem concatSteps_lt {k i : Nat} {A B : Nat → Formula} (h : i < k) :
  concatSteps k A B i = A i := by
  simp [concatSteps, h]

@[simp] theorem concatSteps_ge {k i : Nat} {A B : Nat → Formula} (h : k ≤ i) :
  concatSteps k A B i = B (i - k) := by
  have : ¬ i < k := Nat.not_lt.mpr h
  simp [concatSteps, this]

/-- Up to stage `i ≤ k`, the concatenated ladder *is* the A‑ladder. -/
theorem concat_prefix_eq
  (T : Theory) (A B : Nat → Formula) (k : Nat) :
  ∀ i, i ≤ k → ExtendIter T (concatSteps k A B) i = ExtendIter T A i
| 0, _ => rfl
| i+1, h => by
  have hi : i < k := Nat.lt_of_succ_le h
  have ih := concat_prefix_eq (T:=T) (A:=A) (B:=B) (k:=k) i (Nat.le_of_lt hi)
  -- unfold one step on both sides and use the branch i < k
  simpa [ExtendIter_succ, ih, concatSteps_lt (k:=k) (A:=A) (B:=B) hi]

/-- After finishing A at k, the stage `k + m` of the concatenation
    equals running B for `m` steps *starting from* `ExtendIter T A k`. -/
theorem concat_tail_eq
  (T : Theory) (A B : Nat → Formula) (k m : Nat) :
  ExtendIter T (concatSteps k A B) (k + m) =
  ExtendIter (ExtendIter T A k) B m := by
  induction m with
  | zero =>
      -- k + 0 = k, and the prefix up to k is exactly A.
      have h := concat_prefix_eq (T:=T) (A:=A) (B:=B) (k:=k) k (Nat.le_refl _)
      simpa [Nat.add_comm, ExtendIter_zero] using h
  | succ m ih =>
      -- expand one step on the concatenated side at index k+m
      have hk : k ≤ k + m := Nat.le_add_right _ _
      have step_eq : concatSteps k A B (k + m) = B m := by
        simpa [Nat.add_sub_cancel_left] using
          concatSteps_ge (k:=k) (i:=k+m) (A:=A) (B:=B) hk
      -- Need to carefully handle the index algebra
      calc ExtendIter T (concatSteps k A B) (k + (m + 1))
        = ExtendIter T (concatSteps k A B) (k + m + 1) := by rw [Nat.add_assoc]
        _ = (ExtendIter T (concatSteps k A B) (k + m)).Extend (concatSteps k A B (k + m)) := by
            rw [ExtendIter_succ]
        _ = (ExtendIter (ExtendIter T A k) B m).Extend (B m) := by
            rw [ih, step_eq]
        _ = ExtendIter (ExtendIter T A k) B (m + 1) := by
            rw [← ExtendIter_succ]

/-- Lift a *prefix* A‑certificate (stage `i ≤ k`) into the concatenation at the same stage. -/
def prefixLiftCert
  {T : Theory} {A B : Nat → Formula} {φ : Formula}
  (k : Nat) (c : HeightCertificate T A φ) (hk : c.n ≤ k) :
  HeightCertificate T (concatSteps k A B) φ :=
{ n     := c.n
, upper := by
    -- rewrite goal to the A-ladder using the prefix equality at i = c.n
    have h := concat_prefix_eq (T:=T) (A:=A) (B:=B) (k:=k) c.n hk
    simpa [h] using c.upper
, note  := c.note ++ s!" (prefix ≤ {k})"
}

/-- Lift a *tail* B‑certificate (built after finishing A) into the concatenation at stage `k + m`. -/
def tailLiftCert
  {T : Theory} {A B : Nat → Formula} {φ : Formula}
  (k : Nat) (c : HeightCertificate (ExtendIter T A k) B φ) :
  HeightCertificate T (concatSteps k A B) φ :=
{ n     := k + c.n
, upper := by
    -- rewrite the concatenated stage k+m into "A finished, then m steps of B"
    have h := concat_tail_eq (T:=T) (A:=A) (B:=B) (k:=k) c.n
    simpa [h] using c.upper
, note  := c.note ++ s!" (tail after {k})"
}

/-- Build a pair certificate on the concatenation from:
    * a prefix A-certificate (at `i ≤ k`) and
    * a tail B-certificate (measured from `ExtendIter T A k`).
    The resulting stage is `k + cB.n`. -/
def concatPairCert
  {T : Theory} {A B : Nat → Formula} {φ ψ : Formula}
  (k : Nat)
  (cA : HeightCertificate T A φ) (hAk : cA.n ≤ k)
  (cB : HeightCertificate (ExtendIter T A k) B ψ) :
  HeightCertificatePair T (concatSteps k A B) ⟨φ, ψ⟩ :=
by
  -- prefix phase, at stage cA.n (same n), on the concatenated ladder
  let cA' : HeightCertificate T (concatSteps k A B) φ :=
    prefixLiftCert (T := T) (A := A) (B := B) k cA hAk
  -- lift A-part up to the tail stage k + cB.n
  have hAtoTail : cA'.n ≤ k + cB.n := by
    -- cA'.n = cA.n by construction; then cA.n ≤ k ≤ k + cB.n
    have : cA.n ≤ k + cB.n := Nat.le_trans hAk (Nat.le_add_right _ _)
    simpa using this
  let cA'' := HeightCertificate.lift (T := T) (step := concatSteps k A B)
                (φ := φ) cA' (k + cB.n) hAtoTail
  -- tail phase, already at stage k + cB.n on the concatenated ladder
  let cB' : HeightCertificate T (concatSteps k A B) ψ :=
    tailLiftCert (T := T) (A := A) (B := B) k cB
  -- package as a pair at the common stage k + cB.n
  exact
    { n := k + cB.n
    , upper_left  := cA''.upper
    , upper_right := cB'.upper
    , note := cA''.note ++ " ∧ " ++ cB'.note
    }

/-- Left identity for `concatSteps` at the level of stages:
    splicing at `k = 0` simply yields the tail ladder `B`. -/
@[simp] theorem concat_zero_left
  (T : Theory) (A B : Nat → Formula) (n : Nat) :
  ExtendIter T (concatSteps 0 A B) n = ExtendIter T B n := by
  -- Specialize the tail equality at `k = 0` and simplify.
  simpa using
    (concat_tail_eq (T := T) (A := A) (B := B) (k := 0) (m := n))

/-- Associativity (tail form): composing `A` then `B` then `C`
    by two concatenations matches the expected staged composition. -/
theorem concat_assoc_tail_eq
  (T : Theory) (A B C : Nat → Formula) (k ℓ n : Nat) :
  ExtendIter T (concatSteps k A (concatSteps ℓ B C)) (k + (ℓ + n))
    = ExtendIter (ExtendIter (ExtendIter T A k) B ℓ) C n := by
  -- First peel off the `A`-prefix of length `k`, then peel off the `B`-prefix of length `ℓ`.
  calc
    ExtendIter T (concatSteps k A (concatSteps ℓ B C)) (k + (ℓ + n))
        = ExtendIter (ExtendIter T A k) (concatSteps ℓ B C) (ℓ + n) := by
            -- Tail equality at the outer boundary `k`
            simpa [Nat.add_assoc] using
              (concat_tail_eq (T := T) (A := A) (B := concatSteps ℓ B C)
                (k := k) (m := ℓ + n))
    _   = ExtendIter (ExtendIter (ExtendIter T A k) B ℓ) C n := by
            -- Tail equality at the inner boundary `ℓ`
            simpa using
              (concat_tail_eq (T := ExtendIter T A k) (A := B) (B := C)
                (k := ℓ) (m := n))

/-- Prefix equality at *any* `i ≤ k`:
    up to index `i`, the concatenation behaves exactly like `A`. -/
theorem concat_prefix_le_eq
  (T : Theory) (A B : Nat → Formula) {k i : Nat} (hik : i ≤ k) :
  ExtendIter T (concatSteps k A B) i = ExtendIter T A i := by
  -- Use pointwise congruence on all steps `< i`.
  apply ExtendIter_congr (T := T)
    (A := concatSteps k A B) (B := A) i
  intro j hj
  have hjk : j < k := Nat.lt_of_lt_of_le hj hik
  -- Below `k` the concatenation picks from `A`.
  simpa using (concatSteps_lt (k := k) (i := j) (A := A) (B := B) hjk)

/-- Tail equality at *any* `i ≥ k`:
    from index `k` onwards, concatenation is just `B` running on the tail. -/
theorem concat_tail_ge_eq
  (T : Theory) (A B : Nat → Formula) {k i : Nat} (hk : k ≤ i) :
  ExtendIter T (concatSteps k A B) i
    = ExtendIter (ExtendIter T A k) B (i - k) := by
  -- Reduce to your `concat_tail_eq` by writing `i = k + (i - k)`.
  have : k + (i - k) = i := Nat.add_sub_of_le hk
  -- `concat_tail_eq` says: `ExtendIter … (k + m) = … m`.
  simpa [this] using
    (concat_tail_eq (T := T) (A := A) (B := B) (k := k) (m := i - k))

/-- The stage of a prefix lift is definitionally the original stage. -/
@[simp] theorem prefixLiftCert_n
  {T : Theory} {A B : Nat → Formula} {φ : Formula}
  (k : Nat) (c : HeightCertificate T A φ) (hAk : c.n ≤ k) :
  (prefixLiftCert (T := T) (A := A) (B := B) k c hAk).n = c.n := rfl

/-- The stage of a tail lift is `k + c.n` by construction. -/
@[simp] theorem tailLiftCert_n
  {T : Theory} {A B : Nat → Formula} {ψ : Formula}
  (k : Nat) (c : HeightCertificate (ExtendIter T A k) B ψ) :
  (tailLiftCert (T := T) (A := A) (B := B) k c).n = k + c.n := rfl

/-- For concatenation, the "at‑the‑cut" stage rewrites definitionally. -/
@[simp] theorem concat_prefix_at_cut
  (T : Theory) (A B : Nat → Formula) (k : Nat) :
  ExtendIter T (concatSteps k A B) k = ExtendIter T A k := by
  simpa using concat_prefix_le_eq (T := T) (A := A) (B := B)
    (k := k) (i := k) (hik := Nat.le_refl k)

/-- Tail equality specialized to `k + n` is `simp`-friendly. -/
@[simp] theorem concat_tail_at (T : Theory) (A B : Nat → Formula) (k n : Nat) :
  ExtendIter T (concatSteps k A B) (k + n)
    = ExtendIter (ExtendIter T A k) B n := by
  simpa using concat_tail_eq (T := T) (A := A) (B := B) (k := k) (m := n)

/-- Step-level identity: splicing at `k = 0` just returns the tail ladder. -/
@[simp] theorem concatSteps_zero (A B : Nat → Formula) :
  concatSteps 0 A B = B := by
  funext i
  simp [concatSteps]

/-- The combined pair certificate over a concatenation lives at `k + cB.n`. -/
@[simp] theorem concatPairCert_n
  {T : Theory} {A B : Nat → Formula} {φ ψ : Formula}
  (k : Nat) (cA : HeightCertificate T A φ) (hAk : cA.n ≤ k)
  (cB : HeightCertificate (ExtendIter T A k) B ψ) :
  (concatPairCert (T := T) (A := A) (B := B) k cA hAk cB).n = k + cB.n := rfl

end Papers.P4Meta