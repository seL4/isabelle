(* Author: Alexander Krauss, TU Muenchen
   Author: Christian Sternagel, University of Innsbruck
*)

section \<open>Adhoc overloading of constants based on their types\<close>

theory Adhoc_Overloading
imports Pure
keywords
  "adhoc_overloading" "no_adhoc_overloading" :: thy_decl
begin

ML_file "adhoc_overloading.ML"

end

