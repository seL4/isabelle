(*  Title:      HOL/Statespace/StateSpaceLocale.thy
    Author:     Norbert Schirmer, TU Muenchen
*)

section \<open>Setup for State Space Locales \label{sec:StateSpaceLocale}\<close>

theory StateSpaceLocale imports StateFun 
keywords "statespace" :: thy_defn
begin

ML_file \<open>state_space.ML\<close>
ML_file \<open>state_fun.ML\<close>

text \<open>For every type that is to be stored in a state space, an
instance of this locale is imported in order convert the abstract and
concrete values.\<close>


locale project_inject =
 fixes project :: "'value \<Rightarrow> 'a"
  and inject :: "'a \<Rightarrow> 'value"
 assumes project_inject_cancel [statefun_simp]: "project (inject x) = x"
begin

lemma ex_project [statefun_simp]: "\<exists>v. project v = x"
proof
  show "project (inject x) = x"
    by (rule project_inject_cancel)
qed

lemma project_inject_comp_id [statefun_simp]: "project \<circ> inject = id"
  by (rule ext) (simp add: project_inject_cancel)

lemma project_inject_comp_cancel[statefun_simp]: "f \<circ> project \<circ> inject = f"
  by (rule ext) (simp add: project_inject_cancel)

end

end
