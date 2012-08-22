(* Author: Alexander Krauss, TU Muenchen
   Author: Christian Sternagel, University of Innsbruck
*)

header {* Ad-hoc overloading of constants based on their types *}

theory Adhoc_Overloading
imports Pure
begin

ML_file "adhoc_overloading.ML"
setup Adhoc_Overloading.setup

end

