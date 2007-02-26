theory SCT_Examples
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
  apply (tactic "SCT.abs_rel_tac") (* Build call descriptors *)
  apply (rule ext, rule ext, simp) (* Show that they are correct *)
  apply (tactic "SCT.mk_call_graph") (* Build control graph *)
  apply (rule LJA_apply)                 (* Apply main theorem *)
  apply (simp add:finite_acg_ins finite_acg_empty) (* show finiteness *)
  apply (rule SCT'_exec)
  by eval (* Evaluate to true *)


function p :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "p m n r = (if r>0 then p m (r - 1) n else
              if n>0 then p r (n - 1) m 
                     else m)"
by pat_completeness auto

termination
  unfolding p_rel_def lfp_const
  apply (rule SCT_on_relations)
  apply (tactic "SCT.abs_rel_tac") 
  apply (rule ext, rule ext, simp) 
  apply (tactic "SCT.mk_call_graph")
  apply (rule LJA_apply)            
  apply (simp add:finite_acg_ins finite_acg_empty) 
  apply (rule SCT'_exec)
  by eval

function foo :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "foo True (Suc n) m = foo True n (Suc m)"
  "foo True 0 m = foo False 0 m"
  "foo False n (Suc m) = foo False (Suc n) m"
  "foo False n 0 = n"
by pat_completeness auto

termination
  unfolding foo_rel_def lfp_const
  apply (rule SCT_on_relations)
  apply (tactic "SCT.abs_rel_tac") 
  apply (rule ext, rule ext, simp) 
  apply (tactic "SCT.mk_call_graph")
  apply (rule LJA_apply)            
  apply (simp add:finite_acg_ins finite_acg_empty) 
  apply (rule SCT'_exec)
  by eval


function (sequential) 
  bar :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "bar 0 (Suc n) m = bar m m m"
| "bar k n m = 0"
by pat_completeness auto

termination
  unfolding bar_rel_def lfp_const
  apply (rule SCT_on_relations)
  apply (tactic "SCT.abs_rel_tac") 
  apply (rule ext, rule ext, simp) 
  apply (tactic "SCT.mk_call_graph")
  apply (rule LJA_apply)            
  apply (simp add:finite_acg_ins finite_acg_empty) 
  by (rule SCT'_empty)


end