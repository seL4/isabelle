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

unbundle constrain_space_syntax

declare [[default_code_width = 74]]

declare [[names_unique = false]]

end
