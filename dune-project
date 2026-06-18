(lang dune 3.21)
(using rocq 0.11)

(name lstar-rocq)

(generate_opam_files true)

(source
 (github CharlesAverill/lstar-rocq))

(authors
 "Charles Averill <charlesaverill20@gmail.com>")

(maintainers
 "Charles Averill <charlesaverill20@gmail.com>")

(license MIT)

(documentation https://github.com/CharlesAverill/lstar-rocq)

(package
 (name lstar-rocq)
 (synopsis "Formally-verified automata learning in Rocq")
 (description "Formally-verified implementations of L* and similar algorithms in Rocq")
 (depends
   (rocq-core (>= 9.1.0))
   rocq-prover
   rocq-stdlib
   rocq-runtime))

(package
 (name lstar)
 (synopsis "Automata learning with lstar-rocq")
 (description "Formally-verified implementations of L* and similar algorithms")
 (depends
   (rocq-core (>= 9.1.0))
   rocq-prover
   rocq-stdlib
   rocq-runtime
   (lstar-rocq (= :version))))

