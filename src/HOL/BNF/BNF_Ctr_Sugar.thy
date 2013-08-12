(*  Title:      HOL/BNF/BNF_Ctr_Sugar.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Wrapping existing freely generated type's constructors.
*)

header {* Wrapping Existing Freely Generated Type's Constructors *}

theory BNF_Ctr_Sugar
imports BNF_Util
keywords
  "wrap_free_constructors" :: thy_goal and
  "no_discs_sels" and
  "rep_compat"
begin

lemma iffI_np: "\<lbrakk>x \<Longrightarrow> \<not> y; \<not> x \<Longrightarrow> y\<rbrakk> \<Longrightarrow> \<not> x \<longleftrightarrow> y"
by (erule iffI) (erule contrapos_pn)

lemma iff_contradict:
"\<not> P \<Longrightarrow> P \<longleftrightarrow> Q \<Longrightarrow> Q \<Longrightarrow> R"
"\<not> Q \<Longrightarrow> P \<longleftrightarrow> Q \<Longrightarrow> P \<Longrightarrow> R"
by blast+

ML_file "Tools/bnf_ctr_sugar_tactics.ML"
ML_file "Tools/bnf_ctr_sugar.ML"

end
