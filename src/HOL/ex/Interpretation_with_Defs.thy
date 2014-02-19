(*  Title:      HOL/ex/Interpretation_with_Defs.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Interpretation accompanied with mixin definitions.  EXPERIMENTAL. *}

theory Interpretation_with_Defs
imports Pure
keywords "defining" and "permanent_interpretation" :: thy_goal
begin

ML_file "~~/src/Tools/interpretation_with_defs.ML"

end
