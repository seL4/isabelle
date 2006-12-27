(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Tests and examples for code generator *}

theory Codegenerator
imports ExecutableContent
begin

code_gen "*" (SML #) (Haskell -)

ML {* set Toplevel.debug *}
code_gen (OCaml "~/projects/codegen/test/OCaml/ROOT.ocaml")

code_gen "*"(OCaml "~/projects/codegen/test/OCaml/ROOT.ocaml")

end