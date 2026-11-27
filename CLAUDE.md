# GAC for complex-balanced systems: project instructions

Goal: a machine-checked proof, in Lean 4 with Mathlib, of the Global Attractor Conjecture
for complex-balanced mass-action systems. We build on BitMiracle-AI/detailed-balance-gac
(tag v1.0, Apache-2.0), which proves global convergence for detailed-balanced systems on top
of OpenAI's boundedness-and-persistence theorem for weakly reversible networks
(openai/math @ 1581d4c, Apache-2.0). Craciun's toric-differential-inclusion route is off the
roadmap for now.

We work on the git branch `complex-balanced`.

## Non-negotiable rules

1. **The statement is sacred.** `lean/GAC/ComplexBalanced/Statement.lean` holds the theorem
   statement. Never weaken, reword or "fix" it to make a proof go through. Propose any change
   to Sanay in chat and wait for an explicit yes.
2. **No cheating.** Never use `native_decide`, `axiom`, `@[implemented_by]`, `unsafe`,
   `sorryAx` tricks, or `set_option` that disables checks. `sorry` is allowed only as a
   tracked placeholder: every one gets a row in `lean/GAC/ComplexBalanced/SORRIES.md`.
3. **Check axioms.** After finishing any main theorem, run `#print axioms <name>`. The only
   acceptable output is `propext`, `Classical.choice`, `Quot.sound`.
4. **Build after every change.** `lake build` (run in `lean/`) must pass before you move on.
   Never leave the project in a broken state.
5. **Search before you define.** Before writing any new definition or lemma, search Mathlib
   and the existing `GAC.*` code (lean_local_search, loogle, or `rg`). Reuse the existing
   API. Report what you found.
6. **Commit often.** One git commit per finished lemma or definition, with a clear message.
7. **Be honest about status.** Never say something is proved if it contains `sorry` anywhere
   in its dependency tree. When summarizing progress, list open sorries.
8. **Do not modify upstream files.** Everything outside `lean/GAC/ComplexBalanced/` (and this
   CLAUDE.md) belongs to BitMiracle or OpenAI. Do not edit it. Keep all license headers,
   `NOTICE`, `LICENSE`, `lean/GAC/Persistence/LICENSE` and `lean/docs/SOURCE_MAP.md` intact.
9. **Toolchain is pinned.** Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
   Never run `lake update`. elan lives in `~/.elan/bin` (add it to PATH).

## Reused upstream API (do not redefine)

- `GAC.Persistence.ReactionNetwork`, `Reaction`, `HasReaction`, `WeaklyReversible`,
  `monomial`, `massAction`, `PositiveState`, `IsGlobalForwardSolution`
  (`lean/GAC/Persistence/Model/Network.lean`)
- `GAC.Persistence.bounded_persistent_of_weaklyReversible` (boundedness + persistence)
- `GAC.stoichSubspace`, `GAC.logRatio`, `GAC.lyap`, `GAC.dissip` and the detailed-balance-free
  lemmas in `lean/GAC/DetailedBalance.lean` (`dissip_eq_sum`, `hasDerivAt_lyap`, `lyap_nonneg`,
  `sol_mem_class`, `eq_of_gap_zero`, `continuous_massAction`, ...)

## File layout (new files only)

```
lean/GAC/ComplexBalanced/Defs.lean          IsComplexBalanced; detailed balance implies it (A)
lean/GAC/ComplexBalanced/Regroup.lean       sum over reactions of w_e (g(y') - g(y)) = 0 (B)
lean/GAC/ComplexBalanced/Dissipation.lean   dV/dt <= 0, = 0 iff log-gaps vanish, => equilibrium (C-E)
lean/GAC/ComplexBalanced/WeakReversibility.lean  complex balanced => weakly reversible (F)
lean/GAC/ComplexBalanced/Convergence.lean   LaSalle-type step, complex-balanced main theorem (G)
lean/GAC/ComplexBalanced/Statement.lean     the GAC statement (sacred, see rule 1) (H)
lean/GAC/ComplexBalanced/Sanity.lean        A <=> B example (H)
lean/GAC/ComplexBalanced/Audit.lean         #print axioms for the main theorem and examples
lean/GAC/ComplexBalanced/SORRIES.md         tracked sorries
lean/GAC/ComplexBalanced/GAPS.md            anything that could not be justified
```

New files are picked up by `globs := #[.andSubmodules `GAC]` in the lakefile, so no upstream
file needs an import added.

## Milestones

- [x] M0. Branch, this file, first build
- [x] A. `IsComplexBalanced` definition (approved by Sanay), detailed balance implies it
- [x] B. Regrouping lemma
- [x] C-E. Dissipation under complex balance
- [x] F. Complex balanced implies weakly reversible
- [x] G. Convergence theorem for complex-balanced systems
- [x] H. `Statement.lean` (approved by Sanay), `Sanity.lean`, assembly, `#print axioms`

## Working style

- Work one lemma at a time. State it, check it compiles with `sorry`, then prove it.
- If a step looks wrong or underspecified, stop and write it up in GAPS.md with the exact
  location, what is claimed, and what you could not justify. Do not guess past it.
- Keep proofs readable: name intermediate facts with `have`, avoid 200-line tactic blocks.
