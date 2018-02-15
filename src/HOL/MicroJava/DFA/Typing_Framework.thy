(*  Title:      HOL/MicroJava/DFA/Typing_Framework.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

section \<open>Typing and Dataflow Analysis Framework\<close>

theory Typing_Framework
imports Listn
begin

text \<open>
  The relationship between dataflow analysis and a welltyped-instruction predicate. 
\<close>
type_synonym 's step_type = "nat \<Rightarrow> 's \<Rightarrow> (nat \<times> 's) list"

definition stable :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> bool" where
"stable r step ss p == \<forall>(q,s')\<in>set(step p (ss!p)). s' <=_r ss!q"

definition stables :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool" where
"stables r step ss == !p<size ss. stable r step ss p"

definition wt_step ::
"'s ord \<Rightarrow> 's \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool" where
"wt_step r T step ts ==
 !p<size(ts). ts!p ~= T & stable r step ts p"

definition is_bcv :: "'s ord \<Rightarrow> 's \<Rightarrow> 's step_type 
           \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> bool" where
"is_bcv r T step n A bcv == \<forall>ss \<in> list n A.
   (\<forall>p<n. (bcv ss)!p ~= T) =
   (\<exists>ts \<in> list n A. ss <=[r] ts & wt_step r T step ts)"

end
