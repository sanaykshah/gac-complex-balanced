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

end

end GAC
