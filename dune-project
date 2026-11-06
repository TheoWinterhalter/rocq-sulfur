(lang dune 3.21)

(using rocq 0.11)

(name rocq-sulfur)
(version 0.2)

(generate_opam_files true)

(package
 (name rocq-sulfur)
 (maintainers "Théo Winterhalter <theo.winterhalter@inria.fr>")
 (authors
  "Mathis Bouverot-Dupuis"
  "Thiago Felicissimo"
  "Théa Hervier"
  "Kenji Maillard"
  "Kathrin Stark"
  "Théo Winterhalter")
 (source (github TheoWinterhalter/rocq-sulfur))
 (synopsis "A Rocq plugin to automate reasoning about languages with binders")
 (description
  "Sulfur generates, from a signature, the syntax of a language with binders\
  \ntogether with renaming, substitution, and a tactic (ssimpl) that normalises\
  \nterms and substitutions.\
  \nIt also supports the generation of judgments together with their\
  \nsubstitution lemma.")
 (license MIT)
 (tags
  ("keyword:binders"
   "keyword:substitution"
   "keyword:type-theory"
   "keyword:programming-languages"
   "keyword:automation"
   "category:Miscellaneous/Rocq Extensions"
   "logpath:Sulfur"
   "date:2026-10-19"))
 (depends
  (rocq-core (and (>= 9.3.0) (< 9.4~)))
  rocq-stdlib
  rocq-equations))
