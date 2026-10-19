(lang dune 3.21)

(using rocq 0.11)

(name rocq-sulfur)

(generate_opam_files true)

(package
 (name rocq-sulfur)
 (maintainers "Théo Winterhalter (theo.winterhalter@inria.fr)")
 (authors "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (source (github TheoWinterhalter/rocq-sulfur))
 (synopsis "A Rocq plugin to automate reasoning about languages with binders")
 (description
  "Sulfur generates, from a signature, the syntax of a language with binders\
  \ntogether with renaming, substitution, and a tactic (ssimpl) that normalises\
  \nterms and substitutions.")
 (depends
  (rocq-prover
   (>= 9.3.0))
  rocq-equations))
