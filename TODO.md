# TODOs

## Sulfur Syntax

- [ ] Support user-provided preprocessors for syntax (typically evaluation strategy, tactic)
- [ ] Parameters for syntax
- [ ] Mutual sorts
- [ ] Scoped syntax
- [ ] Phantom names

## Sulfur Judgment

- [ ] Improve `⟨ x : A ⊢ t ⟩` notation to be n-ary.
- [ ] Have a special notation for `x : tt`.
- [ ] Maybe replace `x : A` with `x ↦ A` or something.
- [ ] Be more friendly towards non-Unicode users.
- [ ] Renaming and weakening lemmas.
- [ ] Optimise obligations.
- [ ] Support notations for judgments being defined (seems hard).
- [ ] Support for defined expressions over syntax in judgments (such as `glength` in `examples/ghosts/Typing.v`).

## Extension ideas

- We could implement a `Sulfur SOGAT` command to define syntax and typing at once.
- We could have a way to extend a signature (syntax or judgment) since the theory side has no issue about this.
