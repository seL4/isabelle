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
nonfix upto;
*}

export_code "RType.*" -- "workaround for cache problem"
export_code * in SML module_name CodegenTest
  in OCaml module_name CodegenTest file -
  in Haskell file -

ML {*
infix union;
infix inter;
infix 4 upto;
*}

end
