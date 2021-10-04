(*  Title:      CCL/Trancl.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Transitive closure of a relation\<close>

theory Trancl
imports CCL
begin

definition trans :: "i set \<Rightarrow> o"  (*transitivity predicate*)
  where "trans(r) == (ALL x y z. <x,y>:r \<longrightarrow> <y,z>:r \<longrightarrow> <x,z>:r)"

definition id :: "i set"  (*the identity relation*)
  where "id == {p. EX x. p = <x,x>}"

definition relcomp :: "[i set,i set] \<Rightarrow> i set"  (infixr "O" 60)  (*composition of relations*)
  where "r O s == {xz. EX x y z. xz = <x,z> \<and> <x,y>:s \<and> <y,z>:r}"

definition rtrancl :: "i set \<Rightarrow> i set"  ("(_^*)" [100] 100)
  where "r^* == lfp(\<lambda>s. id Un (r O s))"

definition trancl :: "i set \<Rightarrow> i set"  ("(_^+)" [100] 100)
  where "r^+ == r O rtrancl(r)"


subsection \<open>Natural deduction for \<open>trans(r)\<close>\<close>

lemma transI: "(\<And>x y z. \<lbrakk><x,y>:r; <y,z>:r\<rbrakk> \<Longrightarrow> <x,z>:r) \<Longrightarrow> trans(r)"
  unfolding trans_def by blast

lemma transD: "\<lbrakk>trans(r); <a,b>:r; <b,c>:r\<rbrakk> \<Longrightarrow> <a,c>:r"
  unfolding trans_def by blast


subsection \<open>Identity relation\<close>

lemma idI: "<a,a> : id"
  apply (unfold id_def)
  apply (rule CollectI)
  apply (rule exI)
  apply (rule refl)
  done

lemma idE: "\<lbrakk>p: id;  \<And>x. p = <x,x> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (unfold id_def)
  apply (erule CollectE)
  apply blast
  done


subsection \<open>Composition of two relations\<close>

lemma compI: "\<lbrakk><a,b>:s; <b,c>:r\<rbrakk> \<Longrightarrow> <a,c> : r O s"
  unfolding relcomp_def by blast

(*proof requires higher-level assumptions or a delaying of hyp_subst_tac*)
lemma compE: "\<lbrakk>xz : r O s; \<And>x y z. \<lbrakk>xz = <x,z>; <x,y>:s; <y,z>:r\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding relcomp_def by blast

lemma compEpair: "\<lbrakk><a,c> : r O s; \<And>y. \<lbrakk><a,y>:s; <y,c>:r\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (erule compE)
  apply (simp add: pair_inject)
  done

lemmas [intro] = compI idI
  and [elim] = compE idE

lemma comp_mono: "\<lbrakk>r'<=r; s'<=s\<rbrakk> \<Longrightarrow> (r' O s') <= (r O s)"
  by blast


subsection \<open>The relation rtrancl\<close>

lemma rtrancl_fun_mono: "mono(\<lambda>s. id Un (r O s))"
  apply (rule monoI)
  apply (rule monoI subset_refl comp_mono Un_mono)+
  apply assumption
  done

lemma rtrancl_unfold: "r^* = id Un (r O r^*)"
  by (rule rtrancl_fun_mono [THEN rtrancl_def [THEN def_lfp_Tarski]])

(*Reflexivity of rtrancl*)
lemma rtrancl_refl: "<a,a> : r^*"
  apply (subst rtrancl_unfold)
  apply blast
  done

(*Closure under composition with r*)
lemma rtrancl_into_rtrancl: "\<lbrakk><a,b> : r^*; <b,c> : r\<rbrakk> \<Longrightarrow> <a,c> : r^*"
  apply (subst rtrancl_unfold)
  apply blast
  done

(*rtrancl of r contains r*)
lemma r_into_rtrancl: "<a,b> : r \<Longrightarrow> <a,b> : r^*"
  apply (rule rtrancl_refl [THEN rtrancl_into_rtrancl])
  apply assumption
  done


subsection \<open>standard induction rule\<close>

lemma rtrancl_full_induct:
  "\<lbrakk><a,b> : r^*;
      \<And>x. P(<x,x>);
      \<And>x y z. \<lbrakk>P(<x,y>); <x,y>: r^*; <y,z>: r\<rbrakk>  \<Longrightarrow> P(<x,z>)\<rbrakk>
   \<Longrightarrow>  P(<a,b>)"
  apply (erule def_induct [OF rtrancl_def])
   apply (rule rtrancl_fun_mono)
  apply blast
  done

(*nice induction rule*)
lemma rtrancl_induct:
  "\<lbrakk><a,b> : r^*;
      P(a);
      \<And>y z. \<lbrakk><a,y> : r^*; <y,z> : r;  P(y)\<rbrakk> \<Longrightarrow> P(z) \<rbrakk>
    \<Longrightarrow> P(b)"
(*by induction on this formula*)
  apply (subgoal_tac "ALL y. <a,b> = <a,y> \<longrightarrow> P(y)")
(*now solve first subgoal: this formula is sufficient*)
  apply blast
(*now do the induction*)
  apply (erule rtrancl_full_induct)
   apply blast
  apply blast
  done

(*transitivity of transitive closure!! -- by induction.*)
lemma trans_rtrancl: "trans(r^*)"
  apply (rule transI)
  apply (rule_tac b = z in rtrancl_induct)
    apply (fast elim: rtrancl_into_rtrancl)+
  done

(*elimination of rtrancl -- by induction on a special formula*)
lemma rtranclE:
  "\<lbrakk><a,b> : r^*; a = b \<Longrightarrow> P; \<And>y. \<lbrakk><a,y> : r^*; <y,b> : r\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (subgoal_tac "a = b | (EX y. <a,y> : r^* \<and> <y,b> : r)")
   prefer 2
   apply (erule rtrancl_induct)
    apply blast
   apply blast
  apply blast
  done


subsection \<open>The relation trancl\<close>

subsubsection \<open>Conversions between trancl and rtrancl\<close>

lemma trancl_into_rtrancl: "<a,b> : r^+ \<Longrightarrow> <a,b> : r^*"
  apply (unfold trancl_def)
  apply (erule compEpair)
  apply (erule rtrancl_into_rtrancl)
  apply assumption
  done

(*r^+ contains r*)
lemma r_into_trancl: "<a,b> : r \<Longrightarrow> <a,b> : r^+"
  unfolding trancl_def by (blast intro: rtrancl_refl)

(*intro rule by definition: from rtrancl and r*)
lemma rtrancl_into_trancl1: "\<lbrakk><a,b> : r^*; <b,c> : r\<rbrakk> \<Longrightarrow> <a,c> : r^+"
  unfolding trancl_def by blast

(*intro rule from r and rtrancl*)
lemma rtrancl_into_trancl2: "\<lbrakk><a,b> : r; <b,c> : r^*\<rbrakk> \<Longrightarrow> <a,c> : r^+"
  apply (erule rtranclE)
   apply (erule subst)
   apply (erule r_into_trancl)
  apply (rule trans_rtrancl [THEN transD, THEN rtrancl_into_trancl1])
    apply (assumption | rule r_into_rtrancl)+
  done

(*elimination of r^+ -- NOT an induction rule*)
lemma tranclE:
  "\<lbrakk><a,b> : r^+;
    <a,b> : r \<Longrightarrow> P;
    \<And>y. \<lbrakk><a,y> : r^+; <y,b> : r\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (subgoal_tac "<a,b> : r | (EX y. <a,y> : r^+ \<and> <y,b> : r)")
   apply blast
  apply (unfold trancl_def)
  apply (erule compEpair)
  apply (erule rtranclE)
   apply blast
  apply (blast intro!: rtrancl_into_trancl1)
  done

(*Transitivity of r^+.
  Proved by unfolding since it uses transitivity of rtrancl. *)
lemma trans_trancl: "trans(r^+)"
  apply (unfold trancl_def)
  apply (rule transI)
  apply (erule compEpair)+
  apply (erule rtrancl_into_rtrancl [THEN trans_rtrancl [THEN transD, THEN compI]])
    apply assumption+
  done

lemma trancl_into_trancl2: "\<lbrakk><a,b> : r; <b,c> : r^+\<rbrakk> \<Longrightarrow> <a,c> : r^+"
  by (rule r_into_trancl [THEN trans_trancl [THEN transD]])

end
