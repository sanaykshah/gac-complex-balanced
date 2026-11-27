import GAC.ComplexBalanced.Convergence

/-!
# The Global Attractor Conjecture for complex-balanced systems (statement)

New file. Approved by Sanay; SACRED (rule 1 of CLAUDE.md). The proof is
`GAC.IsComplexBalanced.global_convergence` in `GAC/ComplexBalanced/Convergence.lean`.

The statement has exactly the shape of `GAC.detailed_balanced_global_convergence`
(`lean/GAC/DetailedBalance.lean`), with `IsComplexBalanced` in place of `IsDetailedBalanced`.
All definitions are upstream except `IsComplexBalanced` (`GAC/ComplexBalanced/Defs.lean`).
There is no hypothesis `0 < d`.
-/

open Filter Topology GAC.Persistence

noncomputable section

namespace GAC

variable {d : ℕ}

/-- **Global Attractor Conjecture, complex-balanced case.**
Let a mass-action system have positive rate constants and be complex balanced at some positive
state `xs`. Then for every positive initial state `x0`: the positive compatibility class
`(x0 + S) ∩ ℝ^d_{>0}` contains exactly one equilibrium `xbar`; a solution from `x0` exists for all
`t ≥ 0`; and every such solution converges to `xbar`. -/
theorem global_attractor_conjecture_complex_balanced
    (N : ReactionNetwork d) (κ : Reaction N → ℝ) (hκ : ∀ e, 0 < κ e)
    {xs : Fin d → ℝ} (hcb : IsComplexBalanced N κ xs)
    (x0 : Fin d → ℝ) (hx0 : PositiveState x0) :
    ∃ xbar : Fin d → ℝ,
      PositiveState xbar ∧ massAction N κ xbar = 0 ∧ xbar - x0 ∈ stoichSubspace N ∧
      (∀ z : Fin d → ℝ, PositiveState z → massAction N κ z = 0 →
        z - x0 ∈ stoichSubspace N → z = xbar) ∧
      (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
      ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        Tendsto x atTop (𝓝 xbar) := by
  exact IsComplexBalanced.global_convergence N κ hκ hcb x0 hx0

end GAC
