theory Setup
imports
  Complex_Main
  More_List RBT Dlist Mapping
uses
  "../../antiquote_setup.ML"
  "../../more_antiquote.ML"
begin

setup {*
let
  val typ = Simple_Syntax.read_typ;
  val typeT = Syntax.typeT;
  val spropT = Syntax.spropT;
in
  Sign.del_modesyntax_i (Symbol.xsymbolsN, false) [
    ("_constrain", typ "logic => type => logic", Mixfix ("_\<Colon>_", [4, 0], 3)),
    ("_constrain", [spropT, typeT] ---> spropT, Mixfix ("_\<Colon>_", [4, 0], 3))]
  #> Sign.add_modesyntax_i (Symbol.xsymbolsN, false) [
      ("_constrain", typ "logic => type => logic", Mixfix ("_ \<Colon>  _", [4, 0], 3)),
      ("_constrain", [spropT, typeT] ---> spropT, Mixfix ("_ \<Colon> _", [4, 0], 3))]
end
*}

setup {* Code_Target.set_default_code_width 74 *}

ML_command {* unique_names := false *}

end
