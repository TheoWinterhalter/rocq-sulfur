(lang dune 3.21)

(using rocq 0.11)

(name rocq-sulfur)
(version 0.1.0)

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
 (tags
  ("keyword:binders"
   "keyword:substitution"
   "category:Miscellaneous/Rocq Extensions"
   "logpath:Sulfur"
   "date:2026-10-19"))
 (depends
  (rocq-prover (and (>= 9.3.0) (< 9.4~)))
  rocq-equations))
