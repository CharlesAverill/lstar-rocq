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
 (synopsis "L* implemented in Rocq")
 (description "An implementation of the L* algorithm")
 (depends
   (dune (>= 3.21.0))
   (rocq (>= 9.0.0))))

(package
 (name lstar)
 (synopsis "L* extracted from lstar-rocq")
 (description "An implementation of the L* algorithm")
 (depends
   (dune (>= 3.21.0))))
