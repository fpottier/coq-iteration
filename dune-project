(lang dune 3.8)
(using coq 0.8)

(generate_opam_files true)

(package
  (name coq-iteration)
  (authors
     "François Pottier"
   )
  (maintainers
    "François Pottier"
  )
  (homepage https://gitlab.inria.fr/fpottier/coq-iteration/)
  (bug_reports francois.pottier@inria.fr)
  (synopsis "Mathematical concepts related to iteration")
  (depends
     dune
     (coq-stdpp (= 1.9.0))
  )
)
