import GAC.ComplexBalanced.Regroup

/-!
# The Horn–Jackson dissipation under complex balance (Lemmas C–E)

New file (not part of the upstream BitMiracle / OpenAI code). It reuses the upstream
Lyapunov function `lyap`, its derivative along the field `dissip`, and `logRatio`, together
with `dissip_eq_sum` and `monomial_ratio` from `GAC.DetailedBalance`.

Write `wₑ = κₑ xs^{yₑ}`, `aₑ = logRatio xs x yₑ` and `bₑ = logRatio xs x y'ₑ`. Then
`κₑ x^{yₑ} = wₑ e^{aₑ}` and `dissip = ∑ₑ wₑ e^{aₑ} (bₑ - aₑ)`.
Since `e^a (b - a) ≤ e^b - e^a`, the dissipation is at most `∑ₑ wₑ (e^{bₑ} - e^{aₑ})`,
which vanishes by Lemma B. This replaces the forward/reverse pairing of the
detailed-balanced proof (`two_dissip`, `dissip_nonpos`).
-/

namespace GAC

open GAC.Persistence

noncomputable section

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ} {xs : Fin d → ℝ}

/-- `e^a (b - a) ≤ e^b - e^a`, from `t + 1 ≤ e^t` at `t = b - a`. -/
lemma exp_mul_sub_le_exp_sub_exp (a b : ℝ) :
    Real.exp a * (b - a) ≤ Real.exp b - Real.exp a := by
  have h := Real.add_one_le_exp (b - a)
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos a).le
  rw [← Real.exp_add, add_sub_cancel] at hmul
  linarith

/-- The dissipation written with the fluxes at `xs`:
`dissip = ∑ₑ κₑ xs^{yₑ} · (e^{aₑ} (bₑ - aₑ))`. -/
lemma dissip_eq_sum_flux (hxs : PositiveState xs) {x : Fin d → ℝ} (hx : PositiveState x) :
    dissip N κ xs x = ∑ e : Reaction N, κ e * monomial xs e.val.1 *
      (Real.exp (logRatio xs x e.val.1) *
        (logRatio xs x e.val.2 - logRatio xs x e.val.1)) := by
  rw [dissip_eq_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [monomial_ratio hxs hx]
  ring

/-- **Lemma C.** Under complex balance at `xs` with positive rates, `dV/dt ≤ 0` at every
positive state. -/
theorem IsComplexBalanced.dissip_nonpos (hκ : ∀ e, 0 < κ e) (hcb : IsComplexBalanced N κ xs)
    {x : Fin d → ℝ} (hx : PositiveState x) : dissip N κ xs x ≤ 0 := by
  have hB := hcb.sum_flux_mul_sub_eq_zero (fun y => Real.exp (logRatio xs x y))
  rw [dissip_eq_sum_flux hcb.pos hx, ← hB]
  refine Finset.sum_le_sum fun e _ => ?_
  have hw : 0 ≤ κ e * monomial xs e.val.1 := (mul_pos (hκ e) (monomial_pos hcb.pos _)).le
  exact mul_le_mul_of_nonneg_left (exp_mul_sub_le_exp_sub_exp _ _) hw

/-- The strict version: `e^a (b - a) < e^b - e^a` when `a ≠ b`. -/
lemma exp_mul_sub_lt_exp_sub_exp {a b : ℝ} (hab : a ≠ b) :
    Real.exp a * (b - a) < Real.exp b - Real.exp a := by
  have h := Real.add_one_lt_exp (sub_ne_zero.mpr hab.symm)
  have hmul := mul_lt_mul_of_pos_left h (Real.exp_pos a)
  rw [← Real.exp_add, add_sub_cancel] at hmul
  linarith

/-- **Lemma D.** Under complex balance at `xs` with positive rates, if `dV/dt = 0` at a positive
state `x`, then every log-gap vanishes: `logRatio xs x y = logRatio xs x y'` for each reaction
`y → y'`. -/
theorem IsComplexBalanced.gap_zero_of_dissip_eq_zero (hκ : ∀ e, 0 < κ e)
    (hcb : IsComplexBalanced N κ xs) {x : Fin d → ℝ} (hx : PositiveState x)
    (h0 : dissip N κ xs x = 0) :
    ∀ e : Reaction N, logRatio xs x e.val.1 = logRatio xs x e.val.2 := by
  -- the slack of the inequality `e^a (b - a) ≤ e^b - e^a`, weighted by the flux at `xs`
  set T : Reaction N → ℝ := fun e => κ e * monomial xs e.val.1 *
    ((Real.exp (logRatio xs x e.val.2) - Real.exp (logRatio xs x e.val.1)) -
      Real.exp (logRatio xs x e.val.1) * (logRatio xs x e.val.2 - logRatio xs x e.val.1))
    with hT
  have hw : ∀ e : Reaction N, 0 < κ e * monomial xs e.val.1 :=
    fun e => mul_pos (hκ e) (monomial_pos hcb.pos _)
  have hT_nonneg : ∀ e ∈ (Finset.univ : Finset (Reaction N)), 0 ≤ T e := fun e _ =>
    mul_nonneg (hw e).le (sub_nonneg.mpr (exp_mul_sub_le_exp_sub_exp _ _))
  have hT_sum : ∑ e : Reaction N, T e = 0 := by
    have hB := hcb.sum_flux_mul_sub_eq_zero (fun y => Real.exp (logRatio xs x y))
    have hD := dissip_eq_sum_flux (N := N) (κ := κ) hcb.pos hx
    simp only [hT, mul_sub, Finset.sum_sub_distrib] at hB hD ⊢
    linarith
  have hT_zero := (Finset.sum_eq_zero_iff_of_nonneg hT_nonneg).mp hT_sum
  intro e
  by_contra hne
  have hpos : 0 < T e :=
    mul_pos (hw e) (sub_pos.mpr (exp_mul_sub_lt_exp_sub_exp hne))
  exact hpos.ne' (hT_zero e (Finset.mem_univ e))

end

end GAC
