theory Setup
imports
  Complex_Main
  "HOL-Library.Dlist"
  "HOL-Library.RBT"
  "HOL-Library.Mapping"
  "HOL-Library.IArray"
begin

ML_file \<open>../antiquote_setup.ML\<close>
ML_file \<open>../more_antiquote.ML\<close>

no_syntax (output)
  "_constrain" :: "logic => type => logic"  (\<open>_::_\<close> [4, 0] 3)
  "_constrain" :: "prop' => type => prop'"  (\<open>_::_\<close> [4, 0] 3)

syntax (output)
  "_constrain" :: "logic => type => logic"  (\<open>_ :: _\<close> [4, 0] 3)
  "_constrain" :: "prop' => type => prop'"  (\<open>_ :: _\<close> [4, 0] 3)

declare [[default_code_width = 74]]

declare [[names_unique = false]]

end
