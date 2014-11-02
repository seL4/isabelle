(*  Title:      HOL/HOLCF/Discrete.thy
    Author:     Tobias Nipkow
*)

section {* Discrete cpo types *}

theory Discrete
imports Cont
begin

datatype 'a discr = Discr "'a :: type"

subsection {* Discrete cpo class instance *}

instantiation discr :: (type) discrete_cpo
begin

definition
  "(op \<sqsubseteq> :: 'a discr \<Rightarrow> 'a discr \<Rightarrow> bool) = (op =)"

instance
by default (simp add: below_discr_def)

end

subsection {* \emph{undiscr} *}

definition
  undiscr :: "('a::type)discr => 'a" where
  "undiscr x = (case x of Discr y => y)"

lemma undiscr_Discr [simp]: "undiscr (Discr x) = x"
by (simp add: undiscr_def)

lemma Discr_undiscr [simp]: "Discr (undiscr y) = y"
by (induct y) simp

end
