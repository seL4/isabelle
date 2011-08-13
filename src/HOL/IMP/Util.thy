(* Author: Tobias Nipkow *)

theory Util imports Main
begin

subsection "Show sets of variables as lists"

text {* Sets may be infinite and are not always displayed by element 
  if computed as values. Lists do not have this problem. 

  We define a function @{text show} that converts a set of
  variable names into a list. To keep things simple, we rely on
  the convention that we only use single letter names.
*}
definition 
  letters :: "string list" where
  "letters = map (\<lambda>c. [c]) chars"

definition 
  "show" :: "string set \<Rightarrow> string list" where
  "show S = filter (\<lambda>x. x \<in> S) letters" 

value "show {''x'', ''z''}"

end
