(*  Title:      HOL/MicroJava/BV/Typing_Framework.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

header "Typing and Dataflow Analysis Framework"

theory Typing_Framework = Listn:

text {* 
  The relationship between dataflow analysis and a welltyped-insruction predicate. 
*}
types
  's step_type = "nat \<Rightarrow> 's \<Rightarrow> (nat \<times> 's) list"

constdefs
 bounded :: "'s step_type => nat => bool"
"bounded step n == !p<n. !s. !(q,t):set(step p s). q<n"  

 stable :: "'s ord => 's step_type => 's list => nat => bool"
"stable r step ss p == !(q,s'):set(step p (ss!p)). s' <=_r ss!q"

 stables :: "'s ord => 's step_type => 's list => bool"
"stables r step ss == !p<size ss. stable r step ss p"

 is_bcv :: "'s ord => 's => 's step_type 
           => nat => 's set => ('s list => 's list) => bool"  
"is_bcv r T step n A bcv == !ss : list n A.
   (!p<n. (bcv ss)!p ~= T) =
   (? ts: list n A. ss <=[r] ts & wt_step r T step ts)"

 wt_step ::
"'s ord => 's => 's step_type => 's list => bool"
"wt_step r T step ts ==
 !p<size(ts). ts!p ~= T & stable r step ts p"

end
