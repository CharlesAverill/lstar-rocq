(lang dune 3.21)
(using rocq 0.11)

(name lstar)

(generate_opam_files true)

(source
 (github CharlesAverill/lstar))

(authors
 "Charles Averill <charlesaverill20@gmail.com>")

(maintainers
 "Charles Averill <charlesaverill20@gmail.com>")

(license MIT)

(documentation https://github.com/CharlesAverill/lstar)

(package
 (name lstar)
 (synopsis "L* implemented in Rocq")
 (description "An implementation of the L* algorithm")
 (depends
   (dune (>= 3.21.0))
   (rocq (>= 9.0.0))))
