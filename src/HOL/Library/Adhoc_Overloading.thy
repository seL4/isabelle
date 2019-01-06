(*  Title:      HOL/Library/Adhoc_Overloading.thy
    Author:     Alexander Krauss, TU Muenchen
    Author:     Christian Sternagel, University of Innsbruck
*)

section \<open>Adhoc overloading of constants based on their types\<close>

theory Adhoc_Overloading
  imports Main
  keywords "adhoc_overloading" "no_adhoc_overloading" :: thy_decl
begin

ML_file \<open>adhoc_overloading.ML\<close>

end
