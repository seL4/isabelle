(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Tests and examples for code generator *}

theory Codegenerator
imports ExecutableContent
begin

ML {* (*FIXME get rid of this*)
nonfix union;
nonfix inter;
*}

export_code * in SML module_name CodegenTest
  in OCaml file -
  in Haskell file -

ML {*
infix union;
infix inter;
*}

end
