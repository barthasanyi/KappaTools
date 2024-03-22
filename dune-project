(lang dune 2.9)
(generate_opam_files)

(name kappa-tool-suite)
(version 4.1~dev) ; could be removed and generated at release time instead using dune-release
(source (github Kappa-Dev/KappaTools)) ; no need to specifybug-reports and dev-repo
(license LGPL-3.0-only)
(authors
  "Jean Krivine" "Jérôme Feret" "Pierre Boutillier"
  "Ioana Cristescu" "Mutaamba Maasha" "Lý Kim Quyên" "Antoine Pouille")
(maintainers "Antoine Pouille <antoine.a.pouille@inria.fr>"
             "Pierre Boutillier <pierre.boutillier@laposte.net>")
(homepage https://kappalanguage.org/)
(documentation https://kappalanguage.org/sites/kappalanguage.org/files/inline-files/Kappa_Manual.pdf)

(package
  (name kappa-library)
  (synopsis "Public internals of the Kappa tool suite")
  (depends
   (ocaml ( >= 4.05.0 ))
   (yojson ( >= 2.0 ))
   (lwt ( >= 4.2.0 ))
   num
   re
   stdlib-shims
   fmt
   logs
   result
   )
   ; no need to declare dependancies in `dune` files: generated automatically
)

(package
  (name kappa-binaries)
  (synopsis "Command line interfaces of the Kappa tool suite")
  (depends
   (ocaml ( >= 4.05.0 ))
   (yojson ( = 2.1.0 ))
   (lwt ( = 5.7.0 ))
   (num ( = 1.5))
   (re ( = 1.11.0))
   (fmt ( = 0.9.0))
   (logs ( = 0.7.0))
   kappa-library
   )
  (depopts
    labltk)
)

(package
  (name kappa-agents)
  (synopsis "Backends for an interactive use of the Kappa tool suite")
  (depends
   (ocaml ( >= 4.05.0 ))
   (yojson ( = 2.1.0 ))
   (lwt ( = 5.7.0 ))
   (num ( = 1.5))
   (re ( = 1.11.0))
   (fmt ( = 0.9.0))
   (logs ( = 0.7.0))
   (atdgen-runtime ( = 2.15.0))
   (atdgen ( = 2.15.0)) ; TODO: find a way to specify as build dependency only, as with the `build` package variable in opam
   kappa-library
   )
)

(package
  (name kappa-server)
  (synopsis "Browser app for an interactive use of the Kappa tool suite")
  (depends
   (ocaml ( >= 4.05.0 ))
   (yojson ( = 2.1.0 ))
   (lwt ( = 5.7.0 ))
   (js_of_ocaml ( = 5.7.0))
   (num ( = 1.5))
   (re ( = 1.11.0))
   (fmt ( = 0.9.0))
   (logs ( = 0.7.0))
   (atdgen-runtime ( = 2.15.0))
   (atdgen ( = 2.15.0)) ; TODO: find a way to specify as build dependency only, as with the `build` package variable in opam
   (lwt_react ( = 1.2.0))
   (tyxml-ppx ( = 4.6.0))
   (js_of_ocaml-ppx ( = 5.7.0))
   (js_of_ocaml-lwt ( = 5.7.0))
   (js_of_ocaml-tyxml ( = 5.7.0))
   kappa-binaries
   kappa-agents
   cohttp-lwt-unix
   atdgen-runtime
   atdgen ; TODO: find a way to specify as build dependency only, as with the `build` package variable in opam
   )
  ; does not build executables as there seem to be no way to build js exes in a package
)

(package
  (name kappa-webapp)
  (synopsis "Browser app for an interactive use of the Kappa tool suite")
  (depends
   (ocaml ( >= 4.05.0 ))
   (yojson ( = 2.1.0 ))
   (lwt ( = 5.7.0 ))
   (js_of_ocaml ( = 5.7.0))
   (num ( = 1.5))
   (re ( = 1.11.0))
   (fmt ( = 0.9.0))
   (logs ( = 0.7.0))
   (atdgen-runtime ( = 2.15.0))
   (atdgen ( = 2.15.0)) ; TODO: find a way to specify as build dependency only, as with the `build` package variable in opam
   (lwt_react ( = 1.2.0))
   (tyxml-ppx ( = 4.6.0))
   (js_of_ocaml-ppx ( = 5.7.0))
   (js_of_ocaml-lwt ( = 5.7.0))
   (js_of_ocaml-tyxml ( = 5.7.0))
   (atdgen-runtime ( = 2.15.0))
   (atdgen ( = 2.15.0)) ; TODO: find a way to specify as build dependency only, as with the `build` package variable in opam
   kappa-binaries
   kappa-agents
   )
  ; does not build executables as there seem to be no way to build js exes in a package
)
