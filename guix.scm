;; SPDX-License-Identifier: MPL-2.0
;; Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
;;
;; Guix development environment for tropical-types. Replaces flake.nix (Guix-only policy).
;; Usage: guix shell -D -f guix.scm

(use-modules (guix packages)
             (guix build-system gnu)
             (gnu packages lean)
             (gnu packages maths)
             (gnu packages base)
             (gnu packages bash))

(package
  (name "tropical-types")
  (version "0.1.0")
  (source #f)
  (build-system gnu-build-system)
  (inputs (list lean isabelle coreutils bash make))
  (synopsis "tropical-types")
  (description "tropical-types — part of the hyperpolymath ecosystem.")
  (home-page "https://github.com/hyperpolymath/tropical-types")
  (license ((@@ (guix licenses) license) "MPL-2.0" "https://github.com/hyperpolymath/palimpsest-license")))
