import GAC.ComplexBalanced.Regroup

/-!
# Complex balance implies weak reversibility (Lemma F)

New file (not part of the upstream BitMiracle / OpenAI code). It reuses the upstream
`WeaklyReversible` and `HasReaction` from `GAC.Persistence.Model.Network`.

Suppose some reaction `y₀ → y₀'` has no path back from `y₀'` to `y₀`. Let `g` be the indicator
of the set of complexes reachable from `y₀'`. That set is closed under reactions, so every term
`wₑ (g(y'ₑ) - g(yₑ))` is nonnegative, and the term of `y₀ → y₀'` equals `w₀ > 0`. This
contradicts Lemma B, which says the terms sum to zero.
-/

namespace GAC

open GAC.Persistence

noncomputable section

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ} {xs : Fin d → ℝ}

/-- **Lemma F.** A complex-balanced system with positive rates is weakly reversible. -/
theorem IsComplexBalanced.weaklyReversible (hκ : ∀ e, 0 < κ e)
    (hcb : IsComplexBalanced N κ xs) : WeaklyReversible N := by
  classical
  intro e₀
  by_contra hno
  -- `P η`: the complex `η` is reachable from the target of `e₀`
  set P : (Fin d → ℕ) → Prop := fun η => Relation.ReflTransGen (HasReaction N) e₀.val.2 η
    with hP
  set g : (Fin d → ℕ) → ℝ := fun η => if P η then 1 else 0 with hg
  have hw : ∀ e : Reaction N, 0 < κ e * monomial xs e.val.1 :=
    fun e => mul_pos (hκ e) (monomial_pos hcb.pos _)
  -- every reaction `y → y'` is a step `HasReaction N y y'`
  have hstep : ∀ e : Reaction N, HasReaction N e.val.1 e.val.2 := fun e => e.property
  -- reachability is closed under reactions, so `g` never decreases along a reaction
  have hmono : ∀ e : Reaction N, g e.val.1 ≤ g e.val.2 := by
    intro e
    by_cases hs : P e.val.1
    · have ht : P e.val.2 := Relation.ReflTransGen.tail hs (hstep e)
      simp [hg, hs, ht]
    · by_cases ht : P e.val.2 <;> simp [hg, hs, ht]
  have hterm : ∀ e ∈ (Finset.univ : Finset (Reaction N)),
      0 ≤ κ e * monomial xs e.val.1 * (g e.val.2 - g e.val.1) :=
    fun e _ => mul_nonneg (hw e).le (sub_nonneg.mpr (hmono e))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
    (hcb.sum_flux_mul_sub_eq_zero g) e₀ (Finset.mem_univ _)
  -- the target of `e₀` is reachable from itself, its source is not
  have ht₀ : P e₀.val.2 := Relation.ReflTransGen.refl
  have hs₀ : ¬ P e₀.val.1 := by
    intro h
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with h | h
    · exact N.source_ne_target _ e₀.property h
    · exact hno h
  have hgap : g e₀.val.2 - g e₀.val.1 = 1 := by simp [hg, hs₀, ht₀]
  rw [hgap, mul_one] at hzero
  exact (hw e₀).ne' hzero

end

end GAC
