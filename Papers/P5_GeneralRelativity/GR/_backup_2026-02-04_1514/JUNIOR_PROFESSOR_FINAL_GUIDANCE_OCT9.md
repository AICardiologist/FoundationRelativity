# Junior Professor's Final Guidance - Complete Discussion

**Date:** October 9, 2025, Late Night
**Topic:** Why the sum-level regrouping is stalling and the complete tactical solution
**Status:** Documentation of Junior Professor's explanation and roadmap

---

## Part 1: The Complete Narrative - Why This Has Been So Hard

### 1) The mathematical goal is simple; the mechanization is not

What we want is the Ricci identity on the metric in Schwarzschild coordinates, specialized to (c,d)=(r,θ):

```
(∇_r ∇_θ - ∇_θ ∇_r) g_{ab} = -(R_{ba rθ} + R_{ab rθ})
```

Mathematically, with the Levi-Civita connection, ∇g = 0 (metric compatibility). That alone implies both outer covariant derivatives of g vanish, so the left side is 0. The right side then vanishes by the first-pair antisymmetry of the Riemann tensor. On paper, this is two lines.

In a proof assistant, though, you pay for every syntactic step: what you mean and what Lean sees must coincide, down to parentheses, binder shapes, and rewrite directions. That mismatch is the root of most of the pain.

---

### 2) Early friction: the "packaging" lemmas (Ha/Hb) were wrong

We started with "Ha/Hb" lemmas meant to package derivative–Gamma–Gamma sums into the Riemann tensor. They were subtly incorrect (signs and missing terms). Because `ring` and similar algebraic tactics only rearrange equal expressions, they quite literally couldn't "close the goal" since the two sides were not equal.

This wasn't just a bug; it burned time in the worst way: every later tactic failure looked like a rearrangement problem, but it was actually a false target. Fixing that required re-deriving the packaging to match the definition of `RiemannUp` exactly. That part was ultimately solved (new pack_left/_right_RiemannUp), but it cost a lot of energy.

---

### 3) Axiom removal raised the bar for every derivative step

Originally, there were axiom-like shortcuts for differentiability and linearity of dCoord. As we cleaned the foundations, every use of linearity/product rules had to be backed by real differentiability lemmas. That's good mathematics, but it multiplies obligations:
- Every dCoord over +, -, or * needs four "either it's differentiable or the direction doesn't apply" disjuncts.
- Under binders (sumIdx over indices), you need pointwise differentiability for each summand.

So, a single "push ∂ past a sum of products" turns into a forest of side conditions. We proved a lot of these lemmas; it works—but the scripts get long and brittle.

---

### 4) Pattern-matching under binders is unforgiving

A repeating failure mode was: we had a clean lemma like

```lean
∀ e, ∂_r g_{eb} = Σ_k Γ^k_{re} g_{kb} + Σ_k Γ^k_{rb} g_{ek}
```

but the goal contained these derivatives inside multiplications and sums (e.g., Γ * dCoord_r g sitting under sumIdx). `simp_rw` and `rw` don't "see" through the binder unless the equality is provided in the right pointwise shape. Function equalities of the form `(fun e => …) = (fun e => …)` don't match a subterm like `… * dCoord_r (g …) …`.

Switching to the `∀ e, … = …` (pointwise) form fixed the pattern matching. This is a good example of Lean's locality: equalities have to match exactly where they occur.

It's satisfying when you figure it out, but it's frustrating the first time because you know the rewrite is valid, yet Lean can't see it without the right dressing.

---

### 5) The "EXP" expansions were conceptually right but syntactically heavy

We then made the expansions explicit:
- **EXP_rθ:** push ∂_r through (X - Y - Z) with the correct differentiability disjuncts and direction-mismatch discharges.
- **EXP_θr:** symmetric in θ.

These are logically clean and robust. They compiled. But they produce very large goals—lots of nested sums, products, and derivatives of Christoffels and g. The expressions are mathematically simple but syntactically huge.

---

### 6) The algebraic blow-up: AC normalization timeouts

Once the big expression is on the board, you need to tidy it: distribute, regroup, cancel, and factor it into the RiemannUp shape, then contract with the metric.

Humans do this in one line ("collect the ΓΓ terms and recognize the Riemann bracket"). Lean must be told exactly how to associate and commute everything. A single `simp` with `add_comm`, `add_assoc`, `mul_comm`, `mul_assoc`, `mul_add`, `add_mul`, `sub_eq_add_neg` can explore an enormous search space. That's where the "heartbeats exceeded" timeouts came from. The expressions are big enough that naïve AC-simp explodes combinatorially.

So we're stuck between two modes:
- If we keep everything explicit (robust expansions), we get a giant goal that times out during rearrangement.
- If we try to be clever and "let simp see it," tiny syntactic mismatches stop it from recognizing known structures (RiemannUp, contractions by sumIdx_mul_g_right/left).

---

### 7) Local regrouping helps conceptually but still hits syntactic snags

We tried a "local regrouping" plan:
- Work pointwise in k, rewrite ∂g with compatibility lemmas, collapse the inner sums with diagonality, and factor out the metric piece.
- Lift that pointwise identity to the full k-sum, then identify the parenthesized piece as RiemannUp, then contract.

This is the right "human algebra" broken into machine steps. The blocker: after the compat rewrites + collapses, what we see as "obviously factor to g_{kb} · (…)" isn't syntactically the same as Lean's target form; a couple of signs/associations/orderings differ. `simp` doesn't close the last inch; manual rws are needed in just the right spots.

That last inch takes most of the time.

---

### 8) The elegant mathematical shortcut is blocked by a dependency loop

There's a one-line mathematical route: use ∇g = 0 on the Exterior domain to kill the LHS; conclude the RHS sums to zero via first-pair antisymmetry. But the lemma that states that antisymmetry (`Riemann_swap_a_b_ext`) was designed to use this very Ricci identity specialization to prove itself. That creates a circular dependency for this particular lemma. So the "obvious" short proof can't be used here without refactoring the dependency graph.

This kind of loop is easy to overlook and very discouraging when discovered late.

---

### 9) The "bak8 worked" mirage: simp-driven proofs are fragile

We found an older backup (bak8) where a short proof seemed to work: unfold with a friendlier `nabla_g_shape`, apply four distributor lemmas, one `simp`, a `ring_nf`, and then a final `simp` packaged everything nicely.

In the current file, the same script doesn't close. Likely reasons:
- Slight definitional changes (e.g., which lemma is `@[simp]`, or the exact statement of a helper) change how `simp` searches.
- Applying distributor lemmas with `rw` bakes a different term shape than keeping them as `have`s and letting `simp` apply them in context.
- Even harmless edits upstream can change simp's rewrite queue and make a fragile chain break.

This is the quintessential "works on my machine / yesterday's commit" frustration with automation-based proofs.

---

### 10) Meta-frictions that make iteration slow

- **Goal visibility.** Without interactive goal snapshots at the exact "stuck" lines, you end up guessing which micro-shape Lean has. One missing `mul_add` vs `add_mul`, or `sub_eq_add_neg`, or factor order, can be the difference between instant closure and a timeout.

- **Binder alignment.** Rewrites under `sumIdx` want precisely pointwise equalities; function-level equalities don't match. That's non-obvious until you've been bitten by it.

- **Direction guards.** Many lemmas are true only on the Exterior domain. You have to carry `h_ext` and the derived non-zero facts (r ≠ 0, f(r) ≠ 0) to avoid silent "1/0 = 0" pitfalls. Forget one, and algebraic simplification yields false identities that derail later steps.

---

### 11) Where we actually succeeded

- ✅ We replaced the false Ha/Hb with correct packaging lemmas that compile.
- ✅ We eliminated axioms and proved the differentiability infrastructure the right way.
- ✅ We built robust EXP expansions for both orders (rθ and θr).
- ✅ We discovered and fixed the binder pattern issue with pointwise equalities.
- ✅ We identified precisely why the elegant, compatibility-only proof is blocked (dependency loop).

These are real wins. They just don't feel like progress when the last screenful won't close.

---

### 12) Why it feels so frustrating

Because the math is simple and settled, but Lean requires syntactic fidelity at every step. The final meter is dominated by:
- Tiny shape mismatches (`(A - B) - C` vs `A - (B + C)`),
- Rewrite direction choices (left-to-right vs right-to-left),
- Whether a lemma is pointwise vs function-level,
- Whether you applied a distributor with `rw` (changing shape) or left it as a rewrite rule for `simp` to apply later,
- And the exponential blow-up risk when using AC-simp on a big expression.

It's not that the proof is "hard"; it's that the automation is sensitive. You keep fighting the term shape rather than the mathematics.

---

### 13) The big lessons this journey surfaced

- **Prefer structural proofs** (metric compatibility + antisymmetry) and order lemmas to avoid cycles.
- **Keep packaging lemmas perfectly aligned with definitions;** a single sign kills everything downstream.
- **Under binders, use `∀ e, … = …` equalities for rewrites.**
- **Avoid unconstrained AC-simp on giant goals;** use small, targeted rewrites.
- **Be careful with `rw` vs keeping lemmas as `have`s;** the order you apply them changes term shapes and later rewrites.
- **`simp`-based closures are fast but brittle;** small environment changes can break them.

---

### Bottom line

We've already solved the mathematics. The frustration comes from shepherding a very large, very explicit algebra through Lean's exacting syntactic lens—where a missing pointwise wrapper, a slightly different association, or a fragile simp chain can stall you at 95–98% completion.

---

## Part 2: The Complete Tactical Solution

### Why the current four steps stall (in one paragraph)

After you push the compatibility rewrites under the k-sum and collapse the inner e-sums with diagonality, you end up with two different shapes of terms:

**(i)** pieces already proportional to g_{kb} (great—they factor cleanly), and

**(ii)** pieces proportional to g_{kk} (not great—those cannot be turned into g_{kb} per-k and they are not equal pointwise to the Σ_λ Γ^k_{rλ} Γ^λ_{θa} you want).

The right thing is to **reorganize at the level of the sums, not at the integrand.** That reorganization needs:
- (a) swapping the order of the two dummy-index sums (Fubini on finite sums),
- (b) one use of lower-index symmetry Γ^ρ_{μν} = Γ^ρ_{νμ}, and
- (c) then the metric contraction lemma to move from g_{ee} to g_{kb} form.

Neither `ring` nor "big simp with AC" can discover that reindexing plan by themselves, so they time out or get stuck.

---

## Q1. What happens to the g_{kk} terms?

**Short answer:** They turn into the double-sum parts of R^k_{a rθ}, but only after you (1) swap the k- and e-sums and (2) contract using the metric on the other slot.

### Mechanically:

From compatibility you get a block like:

```
Σ_k Γ^k_{θa} · [Σ_e Γ^e_{rk} g_{eb}]     (diagonal collapse)
                 ↓
Σ_k Γ^k_{θa} · Γ^b_{rk} g_{bb}

and

Σ_k Γ^k_{θa} · [Σ_e Γ^e_{rb} g_{ke}]     (diagonal collapse)
                 ↓
Σ_k Γ^k_{θa} · Γ^k_{rb} g_{kk}
```

- The **first block** is already of the "g_{bb} · (…)" form.
- The **second block** is the "bad" g_{kk} form.

### Do NOT try to rewrite g_{kk} to g_{kb} pointwise; it's false per-k.

Instead, **swap the sums** in the second block:

```
Σ_k Γ^k_{θa} Σ_e Γ^e_{rb} g_{ke}
= Σ_e Γ^e_{rb} Σ_k Γ^k_{θa} g_{ke}     (commute sums)
= Σ_e Γ^e_{rb} · Γ^e_{θa} · g_{ee}     (contract in k using diagonal)
```

Now rename the dummy index e → λ and note this is precisely the `Σ_λ Γ^λ_{rb} Γ^λ_{θa} g_{λλ}` pattern.

After you do the analogous swap for the other sign, the pair of double sums combine to the:

```
+ Σ_λ Γ^k_{rλ} Γ^λ_{θa}
- Σ_λ Γ^k_{θλ} Γ^λ_{ra}
```

once you multiply by g_{kb} and contract in k. **That is where those g_{kk} pieces go.**

### Key moral:

The g_{kk} terms are **not noise**; they are the **seed** that becomes the `+Σ ΓΓ` and `-Σ ΓΓ` parts of `RiemannUp` after you commute sums and contract.

---

## Q2. Which tactical approach to use for the regrouping?

**Go with a sum-first calc chain, not integrand factoring and not big simp:**

### Step-by-step plan:

1. **Start from the entire k-sum.** After your two good steps:
   ```lean
   simp_rw [compat_r_e_b, compat_θ_e_b]
   simp only [sumIdx_Γ_g_left, sumIdx_Γ_g_right]
   ```

   **Do NOT call `ring`.** Instead, split the result into:
   - **S₀** := Σ_k g_{kb} (∂_r Γ^k_{θa} - ∂_θ Γ^k_{ra})
   - **S₊** := Σ_k Γ^k_{θa} Σ_e Γ^e_{rk} g_{eb}
   - **S₋** := Σ_k Γ^k_{ra} Σ_e Γ^e_{θk} g_{eb}
   - **T₊** := Σ_k Γ^k_{θa} Σ_e Γ^e_{rb} g_{ke}
   - **T₋** := Σ_k Γ^k_{ra} Σ_e Γ^e_{θb} g_{ke}

2. **Commute sums in the T± blocks** (the ones with g_{ke}):
   ```
   T₊ = Σ_e Γ^e_{rb} Σ_k Γ^k_{θa} g_{ke}
      = Σ_e Γ^e_{rb} · Γ^e_{θa} · g_{ee}
   ```
   and similarly for T₋.

3. **Swap the dummy name** and use Γ-symmetry on the lower indices where needed (e.g., Γ^e_{rk} = Γ^e_{kr}) to align the "r" and "θ" in the right slots.

4. **Reassemble the four pieces** into:
   ```
   Σ_k g_{kb} (
     ∂_r Γ^k_{θa}
     - ∂_θ Γ^k_{ra}
     + Σ_λ Γ^k_{rλ} Γ^λ_{θa}
     - Σ_λ Γ^k_{θλ} Γ^λ_{ra}
   )
   ```

This is your **sum-level regrouping**. No heavy AC rewrites; just sum commuting, one symmetry, and collecting signs.

### Why this scales:

Each step is a small rewrite with a clear goal; you never ask `simp` to discover the whole reindexing on its own.

---

## Q3. How to make Lean recognize RiemannUp cleanly?

**Avoid "monster simp". Use one unfold and a change:**

Once you have the bracket in exactly the four-term shape, do:
- **Change** the bracket to the `RiemannUp` shape (or `unfold RiemannUp` exactly once on the RHS) so both sides literally match term-by-term.
- Use **only** `simp [sub_eq_add_neg]` for the ± signs and at most `simp [add_comm, add_left_comm, add_assoc]` to fix grouping if needed.
- If Lean still hesitates, insert a **one-line helper** (lemma or `have`) that states the parenthesized four-term expression equals `RiemannUp ...`—proved by `rfl` after `unfold RiemannUp`. Then rewrite with that helper. This keeps `simp` from exploring the entire goal.

---

## Q4. How to combine regrouping with the metric contraction?

**Do it in two small steps:**

1. **Regrouping result first** (as a `have`), ending with:
   ```
   Σ_k g_{kb} (···) = Σ_k g_{kb} · RiemannUp(k,a,r,θ)
   ```

2. **Then contract** using your diagonal contraction lemma:
   ```
   Σ_k g_{kb} · RiemannUp(k, a, r, θ)
   = g_{bb} · RiemannUp(b, a, r, θ)
   ```
   which you already have as `sumIdx_mul_g_right`.

### Tactically, write this as a short calc with three lines:

- commute sums / symmetry / regroup → Σ g_{kb} (···)
- replace (···) by RiemannUp (one unfold/change)
- apply `sumIdx_mul_g_right` (plus a `simp [mul_comm]` to line up factors if needed)

This keeps each rewrite local and prevents heartbeat explosions.

---

## Practical Do's and Don'ts for Those Four Blocked Places

### DO:
- ✅ Keep `simp` **focused**: use `simp_rw` only for the compat rewrites, then `simp only` for the two collapse lemmas—**stop there**.
- ✅ **Split the sum** into five named pieces (S₀, S₊, S₋, T₊, T₋), and handle T± by commuting sums + contraction on the left slot (`sumIdx_mul_g_left`) before returning to a g_{kb}-weighted form.
- ✅ Use **`Γtot_symmetry`** exactly where a lower-index flip is necessary—don't let `simp` try all index flips everywhere.
- ✅ **Present the RiemannUp recognition** as a single `unfold` or a tiny helper lemma to avoid large-scale algebra.

### DON'T:
- ❌ Don't call `ring` (it doesn't know how to move across `sumIdx`).
- ❌ Don't run `simp [add_comm, mul_comm, …]` with wide AC sets at the top-level goal; it blows up the search space.

---

## Sanity Checks as You Proceed

1. **Signs:** The regrouped bracket must be `(+∂_r) (-∂_θ) (+Σ ΓΓ) (-Σ ΓΓ)` in that exact order.

2. **Indices:** In the double sums, pattern should be `Γ^k_{rλ} Γ^λ_{θa}` and `Γ^k_{θλ} Γ^λ_{ra}`—only lower second index flips are justified by torsion-free symmetry.

3. **Contraction:** Every time you apply a contraction lemma, state explicitly which slot you're contracting (right vs left) so you don't accidentally try to "turn g_{kk} into g_{kb} per-k".

---

## Bottom Line

**You're very close.** The remaining gap is not a mismatch in mathematics—it's purely that `ring`/big-simp can't discover the sum reindexing + one symmetry + targeted contraction plan.

If you implement that plan stepwise:
1. Sum commute
2. Left contraction on the T± blocks
3. Symmetry
4. Fold to RiemannUp
5. Right contraction

each of the four sorries will turn into **short, stable calc chains without timeouts**.

---

**Prepared by:** Claude Code (AI Agent) - Documentation Only
**Date:** October 9, 2025, Late Night
**Source:** Junior Professor's complete tactical guidance
**Status:** Complete documentation of discussion - ready for implementation
