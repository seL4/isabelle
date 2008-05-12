(*  Title:      HOL/Library/SCT_Examples.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Examples for Size-Change Termination *}

theory Examples
imports Size_Change_Termination
begin

function f :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "f n 0 = n"
| "f 0 (Suc m) = f (Suc m) m"
| "f (Suc n) (Suc m) = f m n"
by pat_completeness auto


termination
  unfolding f_rel_def lfp_const
  apply (rule SCT_on_relations)
  apply (tactic "Sct.abs_rel_tac") (* Build call descriptors *)
  apply (rule ext, rule ext, simp) (* Show that they are correct *)
  apply (tactic "Sct.mk_call_graph @{context}") (* Build control graph *)
  apply (rule SCT_Main)                 (* Apply main theorem *)
  apply (simp add:finite_acg_simps) (* show finiteness *)
  oops (*FIXME by eval*) (* Evaluate to true *)

function p :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "p m n r = (if r>0 then p m (r - 1) n else
              if n>0 then p r (n - 1) m 
                     else m)"
by pat_completeness auto

termination
  unfolding p_rel_def lfp_const
  apply (rule SCT_on_relations)
  apply (tactic "Sct.abs_rel_tac") 
  apply (rule ext, rule ext, simp) 
  apply (tactic "Sct.mk_call_graph @{context}")
  apply (rule SCT_Main)
  apply (simp add:finite_acg_ins finite_acg_empty finite_graph_def) (* show finiteness *)
  oops (* FIXME by eval *)

function foo :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "foo True (Suc n) m = foo True n (Suc m)"
| "foo True 0 m = foo False 0 m"
| "foo False n (Suc m) = foo False (Suc n) m"
| "foo False n 0 = n"
by pat_completeness auto

termination
  unfolding foo_rel_def lfp_const
  apply (rule SCT_on_relations)
  apply (tactic "Sct.abs_rel_tac") 
  apply (rule ext, rule ext, simp) 
  apply (tactic "Sct.mk_call_graph @{context}")
  apply (rule SCT_Main)
  apply (simp add:finite_acg_ins finite_acg_empty finite_graph_def) (* show finiteness *)
  oops (* FIXME by eval *)


function (sequential) 
  bar :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "bar 0 (Suc n) m = bar m m m"
| "bar k n m = 0"
by pat_completeness auto

termination
  unfolding bar_rel_def lfp_const
  apply (rule SCT_on_relations)
  apply (tactic "Sct.abs_rel_tac") 
  apply (rule ext, rule ext, simp) 
  apply (tactic "Sct.mk_call_graph @{context}")
  apply (rule SCT_Main)
  apply (simp add:finite_acg_ins finite_acg_empty finite_graph_def) (* show finiteness *)
  by (simp only:sctTest_simps cong: sctTest_congs)

end
