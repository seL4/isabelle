(* Author: Tobias Nipkow *)

theory Util imports Main
begin

subsection "Show sets of variables as lists"

text {* Sets are functions and are not displayed by element if
computed as values: *}
value "{''x'', ''y''}"

text {* Lists do not have this problem *}
value "[''x'', ''y'']"

text {* We define a function @{text show} that converts a set of
  variable names into a list. To keep things simple, we rely on
  the convention that we only use single letter names.
*}
definition 
  letters :: "string list" where
  "letters = map (\<lambda>c. [c]) chars"

definition 
  "show" :: "string set \<Rightarrow> string list" where
  "show S = filter S letters" 

value "show {''x'', ''z''}"

end
