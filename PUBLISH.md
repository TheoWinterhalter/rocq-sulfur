# Publishing on `opam`

1. Change the version number in `dune-project` and run
`dune build` to update the `opam` file, then push.

2. Make a release on Github with a new tag corresponding to the release number
such as `v1.0`.

3. Run the following command (with the appropriate version number):
```sh
opam publish --repo=rocq-prover/opam --packages-directory=released/packages --tag=v1.0
```
It will show you the generated `opam` file for the patch, you may check it and
press `q` when satisfied. It will then ask you if you want to proceed.
Say `Y` and you're done!

> [!NOTE]
> You need to install `opam-publish` (on `opam`) and to give it access to some
> Github thingy, it will tell you what you need.
