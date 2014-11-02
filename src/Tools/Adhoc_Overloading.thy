(* Author: Alexander Krauss, TU Muenchen
   Author: Christian Sternagel, University of Innsbruck
*)

section {* Adhoc overloading of constants based on their types *}

theory Adhoc_Overloading
imports Pure
keywords "adhoc_overloading" :: thy_decl and  "no_adhoc_overloading" :: thy_decl
begin

ML_file "adhoc_overloading.ML"

end

