(*  Title:      HOL/MicroJava/BV/Typing_Framework.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

header {* \isaheader{Typing and Dataflow Analysis Framework} *}

theory Typing_Framework = Listn:

text {* 
  The relationship between dataflow analysis and a welltyped-instruction predicate. 
*}
types
  's step_type = "nat \<Rightarrow> 's \<Rightarrow> (nat \<times> 's) list"

constdefs
 stable :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> bool"
"stable r step ss p == !(q,s'):set(step p (ss!p)). s' <=_r ss!q"

 stables :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
"stables r step ss == !p<size ss. stable r step ss p"

 wt_step ::
"'s ord \<Rightarrow> 's \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
"wt_step r T step ts ==
 !p<size(ts). ts!p ~= T & stable r step ts p"

 is_bcv :: "'s ord \<Rightarrow> 's \<Rightarrow> 's step_type 
           \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> bool"  
"is_bcv r T step n A bcv == !ss : list n A.
   (!p<n. (bcv ss)!p ~= T) =
   (? ts: list n A. ss <=[r] ts & wt_step r T step ts)"

end
