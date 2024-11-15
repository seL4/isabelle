(*  Title:      HOL/HOLCF/Discrete_Cpo.thy
    Author:     Tobias Nipkow
*)

section \<open>Discrete cpo types\<close>

theory Discrete_Cpo
  imports Cont
begin

datatype 'a discr = Discr "'a :: type"

subsection \<open>Discrete cpo class instance\<close>

instantiation discr :: (type) discrete_cpo
begin

definition "((\<sqsubseteq>) :: 'a discr \<Rightarrow> 'a discr \<Rightarrow> bool) = (=)"

instance
  by standard (simp add: below_discr_def)

end


subsection \<open>\emph{undiscr}\<close>

definition undiscr :: "('a::type)discr \<Rightarrow> 'a"
  where "undiscr x = (case x of Discr y \<Rightarrow> y)"

lemma undiscr_Discr [simp]: "undiscr (Discr x) = x"
  by (simp add: undiscr_def)

lemma Discr_undiscr [simp]: "Discr (undiscr y) = y"
  by (induct y) simp

end
