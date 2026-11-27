import GAC.ComplexBalanced.Statement
import GAC.Example

/-!
# Sanity checks for the complex-balanced theorem

New file.

(a) `A ⇌ B` with both rates 1, reusing the upstream network `GAC.Example.net` and its
    detailed-balance proof `GAC.Example.net_detailed_balanced`: detailed balanced, hence
    complex balanced by Lemma A, so the new theorem applies.

(b) The cycle `A → B → C → A` with all rates 1, at `xs = (1, 1, 1)`. It is complex balanced
    but not reversible, so no state is detailed balanced and BitMiracle's
    `detailed_balanced_global_convergence` cannot be applied to it. The new theorem can.
-/

open Filter Topology GAC.Persistence

namespace GAC.Sanity

/-! ### (a) `A ⇌ B` -/

/-- `A ⇌ B` is complex balanced at `(1, 1)` (via Lemma A). -/
theorem twoSpecies_complexBalanced :
    IsComplexBalanced GAC.Example.net GAC.Example.rate (fun _ => 1) :=
  GAC.Example.net_detailed_balanced.isComplexBalanced

/-- The complex-balanced GAC applied to `A ⇌ B`. -/
theorem twoSpecies_convergence (x0 : Fin 2 → ℝ) (hx0 : PositiveState x0) :
    ∃ xbar : Fin 2 → ℝ,
      PositiveState xbar ∧ massAction GAC.Example.net GAC.Example.rate xbar = 0 ∧
      xbar - x0 ∈ stoichSubspace GAC.Example.net ∧
      (∀ z : Fin 2 → ℝ, PositiveState z → massAction GAC.Example.net GAC.Example.rate z = 0 →
        z - x0 ∈ stoichSubspace GAC.Example.net → z = xbar) ∧
      (∃ x : ℝ → (Fin 2 → ℝ), IsGlobalForwardSolution GAC.Example.net GAC.Example.rate x0 x) ∧
      ∀ x : ℝ → (Fin 2 → ℝ), IsGlobalForwardSolution GAC.Example.net GAC.Example.rate x0 x →
        Tendsto x atTop (𝓝 xbar) :=
  global_attractor_conjecture_complex_balanced GAC.Example.net GAC.Example.rate
    (fun _ => one_pos) twoSpecies_complexBalanced x0 hx0

/-! ### (b) The cycle `A → B → C → A` -/

/-- The complexes `A = (1,0,0)`, `B = (0,1,0)`, `C = (0,0,1)`. -/
def cA : Fin 3 → ℕ := ![1, 0, 0]
def cB : Fin 3 → ℕ := ![0, 1, 0]
def cC : Fin 3 → ℕ := ![0, 0, 1]

/-- The cycle `A → B → C → A`. -/
def cycle : ReactionNetwork 3 where
  complexes := {cA, cB, cC}
  reactions := {(cA, cB), (cB, cC), (cC, cA)}
  source_mem := by decide
  target_mem := by decide
  source_ne_target := by decide

/-- All three rate constants equal 1. -/
def cycleRate : Reaction cycle → ℝ := fun _ => 1

lemma monomial_one3 (y : Fin 3 → ℕ) : monomial (fun _ => (1 : ℝ)) y = 1 := by
  simp [monomial]

/-- A sum over the reactions of `cycle` is the sum of the three terms. -/
lemma sum_cycle (f : (Fin 3 → ℕ) × (Fin 3 → ℕ) → ℝ) :
    ∑ e : Reaction cycle, f e.val = f (cA, cB) + f (cB, cC) + f (cC, cA) := by
  rw [Finset.sum_coe_sort cycle.reactions f]
  show ∑ e ∈ ({(cA, cB), (cB, cC), (cC, cA)} : Finset _), f e = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The cycle is complex balanced at `(1, 1, 1)`: each complex has exactly one outgoing and
one incoming reaction, each with flux `1`. -/
theorem cycle_complexBalanced : IsComplexBalanced cycle cycleRate (fun _ => 1) where
  pos := fun _ => one_pos
  balance := fun η => by
    simp only [cycleRate, monomial_one3, mul_one, Finset.sum_filter]
    rw [sum_cycle (fun e => if e.1 = η then (1 : ℝ) else 0),
      sum_cycle (fun e => if e.2 = η then (1 : ℝ) else 0)]
    ring

/-- The cycle is not reversible: `B → A` is not a reaction. -/
theorem cycle_not_reversible : ¬ IsReversible cycle := by
  intro h
  have hBA : (cB, cA) ∈ cycle.reactions := h (cA, cB) (by decide)
  revert hBA
  decide

/-- Hence no state is detailed balanced for the cycle, for any rates: BitMiracle's
`detailed_balanced_global_convergence` cannot be applied to it. -/
theorem cycle_not_detailedBalanced (κ : Reaction cycle → ℝ) (xs : Fin 3 → ℝ) :
    ¬ IsDetailedBalanced cycle κ xs :=
  fun h => cycle_not_reversible h.reversible

/-- The complex-balanced GAC applied to the cycle. -/
theorem cycle_convergence (x0 : Fin 3 → ℝ) (hx0 : PositiveState x0) :
    ∃ xbar : Fin 3 → ℝ,
      PositiveState xbar ∧ massAction cycle cycleRate xbar = 0 ∧
      xbar - x0 ∈ stoichSubspace cycle ∧
      (∀ z : Fin 3 → ℝ, PositiveState z → massAction cycle cycleRate z = 0 →
        z - x0 ∈ stoichSubspace cycle → z = xbar) ∧
      (∃ x : ℝ → (Fin 3 → ℝ), IsGlobalForwardSolution cycle cycleRate x0 x) ∧
      ∀ x : ℝ → (Fin 3 → ℝ), IsGlobalForwardSolution cycle cycleRate x0 x →
        Tendsto x atTop (𝓝 xbar) :=
  global_attractor_conjecture_complex_balanced cycle cycleRate (fun _ => one_pos)
    cycle_complexBalanced x0 hx0

end GAC.Sanity
