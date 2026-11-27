import GAC.DetailedBalance

/-!
# Complex balance

New file (not part of the upstream BitMiracle / OpenAI code). It reuses the upstream
`ReactionNetwork`, `Reaction`, `monomial` and `PositiveState` from
`GAC.Persistence.Model.Network`.

A mass-action system is *complex balanced* at a positive state `xs` when, for every complex
`η`, the total flux of reactions with source `η` equals the total flux of reactions with
target `η`, all evaluated at `xs`. The flux of reaction `y → y'` at `xs` is `κ e * xs ^ y`.
-/

namespace GAC

open GAC.Persistence

noncomputable section

variable {d : ℕ}

/-- Complex balance at `xs`: `xs` is positive, and for every complex `η`,
outflow from `η` (reactions with source `η`) equals inflow to `η` (reactions with target `η`),
where reaction `e : y → y'` carries flux `κ e * monomial xs y`. -/
structure IsComplexBalanced (N : ReactionNetwork d) (κ : Reaction N → ℝ) (xs : Fin d → ℝ) :
    Prop where
  pos : PositiveState xs
  balance : ∀ η : Fin d → ℕ,
    ∑ e ∈ Finset.univ.filter (fun e : Reaction N => e.val.1 = η),
        κ e * monomial xs e.val.1 =
      ∑ e ∈ Finset.univ.filter (fun e : Reaction N => e.val.2 = η),
        κ e * monomial xs e.val.1

end

end GAC
