header {* Main HOL *}

theory Main
imports Plain Predicate_Compile Nitpick
begin

text {*
  Classical Higher-order Logic -- only ``Main'', excluding real and
  complex numbers etc.
*}

text {* See further \cite{Nipkow-et-al:2002:tutorial} *}

text {* Compatibility layer -- to be dropped *}

lemma Inf_bool_def:
  "Inf A \<longleftrightarrow> (\<forall>x\<in>A. x)"
  by (auto intro: bool_induct)

lemma Sup_bool_def:
  "Sup A \<longleftrightarrow> (\<exists>x\<in>A. x)"
  by auto

declare Complete_Lattice.Inf_bool_def [simp del]
declare Complete_Lattice.Sup_bool_def [simp del]

end
