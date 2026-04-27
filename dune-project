(lang dune 3.21)
(using rocq 0.11)

(name PROJECT)

(generate_opam_files true)

(source
 (github GH_USERNAME/PROJECT))

(authors
 "NAME <EMAIL>")

(maintainers
 "NAME <EMAIL>")

(license LICENSE)

(documentation https://github.com/GH_USERNAME/PROJECT)

(package
 (name PROJECT)
 (synopsis "SYNOPSIS")
 (description "DESCRIPTION")
 (depends
   (dune (>= 3.21.0))
   (rocq (>= 9.0.0))))
