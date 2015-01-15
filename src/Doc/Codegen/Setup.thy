theory Setup
imports
  Complex_Main
  "~~/src/HOL/Library/Dlist"
  "~~/src/HOL/Library/RBT"
  "~~/src/HOL/Library/Mapping"
  "~~/src/HOL/Library/IArray"
begin

ML \<open>
  Isabelle_System.mkdirs (File.tmp_path (Path.basic "examples"))
\<close>

ML_file "../antiquote_setup.ML"
ML_file "../more_antiquote.ML"

setup \<open>
let
  val typ = Simple_Syntax.read_typ;
in
  Sign.del_syntax (Symbol.xsymbolsN, false)
   [("_constrain", typ "logic => type => logic", Mixfix ("_\<Colon>_", [4, 0], 3)),
    ("_constrain", typ "prop' => type => prop'", Mixfix ("_\<Colon>_", [4, 0], 3))] #>
  Sign.add_syntax (Symbol.xsymbolsN, false)
   [("_constrain", typ "logic => type => logic", Mixfix ("_ \<Colon>  _", [4, 0], 3)),
    ("_constrain", typ "prop' => type => prop'", Mixfix ("_ \<Colon> _", [4, 0], 3))]
end
\<close>

declare [[default_code_width = 74]]

declare [[names_unique = false]]

end
