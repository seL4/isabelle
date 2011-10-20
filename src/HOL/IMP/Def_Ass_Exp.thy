(* Author: Tobias Nipkow *)

theory Def_Ass_Exp imports Vars
begin

subsection "Initialization-Sensitive Expressions Evaluation"

type_synonym state = "vname \<Rightarrow> val option"


fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val option" where
"aval (N i) s = Some i" |
"aval (V x) s = s x" |
"aval (Plus a\<^isub>1 a\<^isub>2) s =
  (case (aval a\<^isub>1 s, aval a\<^isub>2 s) of
     (Some i\<^isub>1,Some i\<^isub>2) \<Rightarrow> Some(i\<^isub>1+i\<^isub>2) | _ \<Rightarrow> None)"


fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool option" where
"bval (Bc v) s = Some v" |
"bval (Not b) s = (case bval b s of None \<Rightarrow> None | Some bv \<Rightarrow> Some(\<not> bv))" |
"bval (And b\<^isub>1 b\<^isub>2) s = (case (bval b\<^isub>1 s, bval b\<^isub>2 s) of
  (Some bv\<^isub>1, Some bv\<^isub>2) \<Rightarrow> Some(bv\<^isub>1 & bv\<^isub>2) | _ \<Rightarrow> None)" |
"bval (Less a\<^isub>1 a\<^isub>2) s = (case (aval a\<^isub>1 s, aval a\<^isub>2 s) of
 (Some i\<^isub>1, Some i\<^isub>2) \<Rightarrow> Some(i\<^isub>1 < i\<^isub>2) | _ \<Rightarrow> None)"


lemma aval_Some: "vars a \<subseteq> dom s \<Longrightarrow> \<exists> i. aval a s = Some i"
by (induct a) auto

lemma bval_Some: "vars b \<subseteq> dom s \<Longrightarrow> \<exists> bv. bval b s = Some bv"
by (induct b) (auto dest!: aval_Some)

end
