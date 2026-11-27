import GAC.ComplexBalanced.Defs

/-!
# Regrouping reaction sums by complex (Lemma B)

New file (not part of the upstream BitMiracle / OpenAI code).

Complex balance is a statement about sums over the reactions leaving or entering one complex.
Its main consequence is that for *any* function `g` on complexes,
`∑ₑ κₑ xs^{yₑ} (g(y'ₑ) - g(yₑ)) = 0`: group the reactions by target complex and by source
complex, and compare the two groupings complex by complex.
This is the identity that replaces the forward/reverse pairing of the detailed-balanced proof.
-/

namespace GAC

open GAC.Persistence

noncomputable section

variable {d : ℕ}

/-- A sum over reactions of `F e * g (h e)`, where `h e` is always a complex of `N`,
regrouped as a sum over complexes `η` of `g η` times the sum of `F` over the fibre `h e = η`. -/
lemma sum_mul_comp_eq_sum_complexes (N : ReactionNetwork d) (F : Reaction N → ℝ)
    (g : (Fin d → ℕ) → ℝ) (h : Reaction N → (Fin d → ℕ)) (hh : ∀ e, h e ∈ N.complexes) :
    ∑ e : Reaction N, F e * g (h e) =
      ∑ η ∈ N.complexes, g η * ∑ e ∈ Finset.univ.filter (fun e : Reaction N => h e = η), F e := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := N.complexes) (g := h)
    (fun e _ => hh e)]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [(Finset.mem_filter.1 he).2, mul_comm]

/-- **Lemma B.** Under complex balance at `xs`, for every function `g` on complexes,
`∑ₑ κₑ xs^{yₑ} (g(y'ₑ) - g(yₑ)) = 0`. -/
theorem IsComplexBalanced.sum_flux_mul_sub_eq_zero {N : ReactionNetwork d}
    {κ : Reaction N → ℝ} {xs : Fin d → ℝ} (hcb : IsComplexBalanced N κ xs)
    (g : (Fin d → ℕ) → ℝ) :
    ∑ e : Reaction N, κ e * monomial xs e.val.1 * (g e.val.2 - g e.val.1) = 0 := by
  have htgt := sum_mul_comp_eq_sum_complexes N (fun e => κ e * monomial xs e.val.1) g
    (fun e => e.val.2) (fun e => N.target_mem _ e.property)
  have hsrc := sum_mul_comp_eq_sum_complexes N (fun e => κ e * monomial xs e.val.1) g
    (fun e => e.val.1) (fun e => N.source_mem _ e.property)
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [htgt, hsrc, sub_eq_zero]
  exact Finset.sum_congr rfl fun η _ => by rw [hcb.balance η]

end

end GAC
