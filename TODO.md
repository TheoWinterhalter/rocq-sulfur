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
- [ ] Do not force the context name to be `Γ` in `{{ _ }}`.
- [ ] Be more friendly towards non-Unicode users.

## Extension ideas

- We could implement a `Sulfur SOGAT` command to define syntax and typing at once.
