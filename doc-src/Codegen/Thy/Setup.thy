theory Setup
imports
  Complex_Main
  "~~/src/HOL/Library/Dlist"
  "~~/src/HOL/Library/RBT"
  "~~/src/HOL/Library/Mapping"
uses
  "../../antiquote_setup.ML"
  "../../more_antiquote.ML"
begin

setup {*
  Antiquote_Setup.setup #>
  More_Antiquote.setup #>
let
  val typ = Simple_Syntax.read_typ;
in
  Sign.del_modesyntax_i (Symbol.xsymbolsN, false)
   [("_constrain", typ "logic => type => logic", Mixfix ("_\<Colon>_", [4, 0], 3)),
    ("_constrain", typ "prop' => type => prop'", Mixfix ("_\<Colon>_", [4, 0], 3))] #>
  Sign.add_modesyntax_i (Symbol.xsymbolsN, false)
   [("_constrain", typ "logic => type => logic", Mixfix ("_ \<Colon>  _", [4, 0], 3)),
    ("_constrain", typ "prop' => type => prop'", Mixfix ("_ \<Colon> _", [4, 0], 3))]
end
*}

setup {* Code_Target.set_default_code_width 74 *}

declare [[names_unique = false]]

end

