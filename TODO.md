# TODOs

## General

- [ ] Make generated constants more robust by placing them inside modules?

## Sulfur Syntax

- [ ] Support user-provided preprocessors for syntax (typically evaluation strategy, tactic)
- [ ] Parameters for syntax
- [ ] Mutual sorts
- [ ] Scoped syntax
- [ ] Phantom names
- [X] Declare existing instance for the signature.

## Sulfur Judgment

- [ ] Make sure the examples work properly. See `Admitted` in `examples/ghosts/Typing.v`.
- [ ] Improve `⟨ x : A ⊢ t ⟩` notation to be n-ary.
- [ ] Have a special notation for `x : tt`.
- [ ] Maybe replace `x : A` with `x ↦ A` or something.
- [ ] Be more friendly towards non-Unicode users.
- [ ] Renaming and weakening lemmas.
- [ ] Optimise obligations.
- [ ] Support notations for judgments being defined (seems hard).
- [ ] Support for defined expressions over syntax in judgments (such as `glength` in `examples/ghosts/Typing.v`).
- [ ] Fix "Warning: hjp does not respect the uniform inheritance condition."

## Sulfur Judgment Internals/Theory

- [ ] Unify syntax with and without metavariables, or find a good reason for having both.
- [ ] Names of mctx, mterm are a bit confusing. In BiTTs and Andromeda, mctx means metavariable context (= lists of premises).
- [ ] Better understand naturality conditions, and if there's a way to rephrase necessary conditions that is more in line with the prior work. More generally, make sure we are not "reinventing the wheel", and that any new concepts are justified by examples that couldn't be handled by existing frameworks.
- [ ] Better understand if we really cannot handle typing judgements which presuppose the context is well-typed. Investigate if the presupositive version could be derived somehow autuomatically from the non-presupositive one.


## Extension ideas

- We could implement a `Sulfur SOGAT` command to define syntax and typing at once.
- We could have a way to extend a signature (syntax or judgment) since the theory side has no issue about this.
