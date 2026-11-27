# The Global Attractor Conjecture for complex-balanced systems, in Lean 4

[![Build and axiom check](https://github.com/sanaykshah/gac-complex-balanced/actions/workflows/build.yml/badge.svg?branch=complex-balanced)](https://github.com/sanaykshah/gac-complex-balanced/actions/workflows/build.yml)

A machine-checked proof, in Lean 4 with Mathlib, of the Global Attractor Conjecture for
complex-balanced mass-action systems. It extends
[BitMiracle-AI/detailed-balance-gac](https://github.com/BitMiracle-AI/detailed-balance-gac)
(v1.0, detailed-balanced case), which builds on OpenAI's boundedness and persistence theorem
for weakly reversible networks ([openai/math](https://github.com/openai/math)).

Paper: *[title and link to come]*.

## The theorem

**In plain English.** Take a mass-action reaction network on `d` species, with positive rate
constants, and suppose it is complex balanced at some positive state `xs`: at every complex, the
total flux of reactions leaving it equals the total flux of reactions arriving at it. Then, for
every positive initial state `x0`:

1. the positive part of its stoichiometric compatibility class, `(x0 + S) ∩ ℝ^d_{>0}`, contains
   exactly one equilibrium `xbar`;
2. a solution of the mass-action ODE starting at `x0` exists for all `t ≥ 0`;
3. every such solution converges to `xbar` as `t → ∞`.

There is no assumption `0 < d`, and no structural assumption on the network: weak reversibility
is not assumed but proved from complex balance (`IsComplexBalanced.weaklyReversible`).

**In Lean** (`lean/GAC/ComplexBalanced/Statement.lean`):

```lean
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
        Tendsto x atTop (𝓝 xbar)
```

The only new definition is `IsComplexBalanced` (`lean/GAC/ComplexBalanced/Defs.lean`):

```lean
structure IsComplexBalanced (N : ReactionNetwork d) (κ : Reaction N → ℝ) (xs : Fin d → ℝ) :
    Prop where
  pos : PositiveState xs
  balance : ∀ η : Fin d → ℕ,
    ∑ e ∈ Finset.univ.filter (fun e : Reaction N => e.val.1 = η),
        κ e * monomial xs e.val.1 =
      ∑ e ∈ Finset.univ.filter (fun e : Reaction N => e.val.2 = η),
        κ e * monomial xs e.val.1
```

Everything else in the statement (`ReactionNetwork`, `Reaction`, `massAction`, `monomial`,
`PositiveState`, `IsGlobalForwardSolution`, `stoichSubspace`) is upstream and unchanged.
Its shape is exactly that of BitMiracle's `GAC.detailed_balanced_global_convergence`, with
`IsComplexBalanced` in place of `IsDetailedBalanced`.

`lean/GAC/ComplexBalanced/Sanity.lean` applies the theorem to two networks:
`A ⇌ B`, and the cycle `A → B → C → A`. The cycle is complex balanced but not reversible, so it
is not detailed balanced for any rates and the upstream theorem does not cover it.

## Build and check

Requires [elan](https://github.com/leanprover/elan). Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` are pinned; do not run `lake update`.

```sh
cd lean
lake exe cache get
lake build
lake env lean GAC/ComplexBalanced/Audit.lean
```

The last command prints the axioms of the main theorem, of
`IsComplexBalanced.global_convergence`, and of the six theorems in `Sanity.lean`. Each one is

```
'GAC.global_attractor_conjecture_complex_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only Lean's three standard axioms: no `sorry`, no added axioms.
`lean/GAC/ComplexBalanced/SORRIES.md` is empty.

What has been checked:

| Check | Result |
| --- | --- |
| CI (`.github/workflows/build.yml`): clean checkout, cache, full `lake build`, exact-match check of the axiom line | passes |
| `leanchecker` kernel replay, one module at a time: the 8 `GAC.ComplexBalanced` modules and the 73 upstream modules they import (71 `GAC.Persistence`, `GAC.DetailedBalance`, `GAC.Example`) | all pass |
| `leanchecker --fresh GAC.ComplexBalanced.Statement` (replays every declaration, Lean core and Mathlib included, from an empty environment) | passes |
| Search of `GAC/ComplexBalanced/` for `sorry`, `axiom`, `native_decide`, `implemented_by`, `unsafe` | none |
| `git diff --stat v1.0 -- . ':!lean/GAC/ComplexBalanced'` | only `README.md`, `CLAUDE.md` and the CI workflow: no upstream Lean file is changed |

All replays use Lean's own kernel. No independent kernel (such as lean4lean) has been run.
The upstream persistence proof (about 7,900 lines) is trusted through the kernel check, not
through a line-by-line review.

## Which files are ours

Everything we wrote is in `lean/GAC/ComplexBalanced/`. The lakefile already picks it up
(``globs := #[.andSubmodules `GAC]``), so no upstream file needed an import.

| File | Content |
| --- | --- |
| `Defs.lean` | `IsComplexBalanced`; detailed balance implies complex balance (Lemma A) |
| `Regroup.lean` | under complex balance, `∑ₑ κₑ xs^{yₑ} (g(y'ₑ) − g(yₑ)) = 0` for every `g` (Lemma B) |
| `Dissipation.lean` | the Horn–Jackson function is non-increasing; it is stationary only where the log-gaps vanish, which forces an equilibrium (Lemmas C–E) |
| `WeakReversibility.lean` | complex balanced implies weakly reversible (Lemma F) |
| `Convergence.lean` | LaSalle-type step and the convergence theorem (adapted from BitMiracle's detailed-balance proof) |
| `Statement.lean` | the main theorem |
| `Sanity.lean` | `A ⇌ B` and the cycle `A → B → C → A` |
| `Audit.lean` | `#print axioms` |
| `SORRIES.md` | tracked placeholders (none) |

Also ours: this `README.md`, `CLAUDE.md` (working rules for the formalization) and the CI
workflow `.github/workflows/build.yml`.

Everything else is upstream and unchanged, except that BitMiracle's README has been moved
unchanged to [`docs/BITMIRACLE_README.md`](docs/BITMIRACLE_README.md):

| Path | Origin |
| --- | --- |
| `lean/GAC/Persistence/` (71 modules) | OpenAI, adapted by BitMiracle; provenance in `lean/docs/SOURCE_MAP.md` |
| `lean/GAC/*.lean`, `lean/GAC/Reformulated/`, `lean/docs/`, `lean/scripts/`, `lean/GAC.lean`, `lean/Audit.lean`, `lean/lakefile.lean`, `lean/lake-manifest.json`, `lean/lean-toolchain` | BitMiracle |
| `LICENSE`, `NOTICE`, `lean/GAC/Persistence/LICENSE` | upstream license files, unchanged |

## Credits

- **OpenAI**, [openai/math](https://github.com/openai/math), commit
  `1581d4cbdd69a0faf34b2089614fe2a814316a6a`: the boundedness and persistence theorem for
  weakly reversible mass-action systems (`GAC.Persistence.bounded_persistent_of_weaklyReversible`).
  It is the hard analytic core that this result relies on.
- **BitMiracle AI Lab**,
  [BitMiracle-AI/detailed-balance-gac](https://github.com/BitMiracle-AI/detailed-balance-gac)
  v1.0: the adaptation of OpenAI's modules, the reaction-network API and the Horn–Jackson
  convergence argument for detailed-balanced systems, which `Convergence.lean` follows closely.
  See their README in [`docs/BITMIRACLE_README.md`](docs/BITMIRACLE_README.md).

## License

Licensed under the Apache License, Version 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
Upstream code keeps its license headers and attribution, and the provenance of the adapted
OpenAI modules is listed in `lean/docs/SOURCE_MAP.md`. The new files under
`lean/GAC/ComplexBalanced/` are additions to this work, released under the same license.

Unless required by applicable law or agreed to in writing, software distributed under the
License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
express or implied. See the License for the specific language governing permissions and
limitations under the License.
