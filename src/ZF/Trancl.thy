(*  Title:      ZF/Trancl.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section\<open>Relations: Their General Properties and Transitive Closure\<close>

theory Trancl imports Fixedpt Perm begin

definition
  refl     :: "[i,i]=>o"  where
    "refl(A,r) \<equiv> (\<forall>x\<in>A. <x,x> \<in> r)"

definition
  irrefl   :: "[i,i]=>o"  where
    "irrefl(A,r) \<equiv> \<forall>x\<in>A. <x,x> \<notin> r"

definition
  sym      :: "i=>o"  where
    "sym(r) \<equiv> \<forall>x y. <x,y>: r \<longrightarrow> <y,x>: r"

definition
  asym     :: "i=>o"  where
    "asym(r) \<equiv> \<forall>x y. <x,y>:r \<longrightarrow> \<not> <y,x>:r"

definition
  antisym  :: "i=>o"  where
    "antisym(r) \<equiv> \<forall>x y.<x,y>:r \<longrightarrow> <y,x>:r \<longrightarrow> x=y"

definition
  trans    :: "i=>o"  where
    "trans(r) \<equiv> \<forall>x y z. <x,y>: r \<longrightarrow> <y,z>: r \<longrightarrow> <x,z>: r"

definition
  trans_on :: "[i,i]=>o"  (\<open>trans[_]'(_')\<close>)  where
    "trans[A](r) \<equiv> \<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A.
                          <x,y>: r \<longrightarrow> <y,z>: r \<longrightarrow> <x,z>: r"

definition
  rtrancl :: "i=>i"  (\<open>(_^*)\<close> [100] 100)  (*refl/transitive closure*)  where
    "r^* \<equiv> lfp(field(r)*field(r), %s. id(field(r)) \<union> (r O s))"

definition
  trancl  :: "i=>i"  (\<open>(_^+)\<close> [100] 100)  (*transitive closure*)  where
    "r^+ \<equiv> r O r^*"

definition
  equiv    :: "[i,i]=>o"  where
    "equiv(A,r) \<equiv> r \<subseteq> A*A \<and> refl(A,r) \<and> sym(r) \<and> trans(r)"


subsection\<open>General properties of relations\<close>

subsubsection\<open>irreflexivity\<close>

lemma irreflI:
    "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> <x,x> \<notin> r\<rbrakk> \<Longrightarrow> irrefl(A,r)"
by (simp add: irrefl_def)

lemma irreflE: "\<lbrakk>irrefl(A,r);  x \<in> A\<rbrakk> \<Longrightarrow>  <x,x> \<notin> r"
by (simp add: irrefl_def)

subsubsection\<open>symmetry\<close>

lemma symI:
     "\<lbrakk>\<And>x y.<x,y>: r \<Longrightarrow> <y,x>: r\<rbrakk> \<Longrightarrow> sym(r)"
by (unfold sym_def, blast)

lemma symE: "\<lbrakk>sym(r); <x,y>: r\<rbrakk>  \<Longrightarrow>  <y,x>: r"
by (unfold sym_def, blast)

subsubsection\<open>antisymmetry\<close>

lemma antisymI:
     "\<lbrakk>\<And>x y.\<lbrakk><x,y>: r;  <y,x>: r\<rbrakk> \<Longrightarrow> x=y\<rbrakk> \<Longrightarrow> antisym(r)"
by (simp add: antisym_def, blast)

lemma antisymE: "\<lbrakk>antisym(r); <x,y>: r;  <y,x>: r\<rbrakk>  \<Longrightarrow>  x=y"
by (simp add: antisym_def, blast)

subsubsection\<open>transitivity\<close>

lemma transD: "\<lbrakk>trans(r);  <a,b>:r;  <b,c>:r\<rbrakk> \<Longrightarrow> <a,c>:r"
by (unfold trans_def, blast)

lemma trans_onD:
    "\<lbrakk>trans[A](r);  <a,b>:r;  <b,c>:r;  a \<in> A;  b \<in> A;  c \<in> A\<rbrakk> \<Longrightarrow> <a,c>:r"
by (unfold trans_on_def, blast)

lemma trans_imp_trans_on: "trans(r) \<Longrightarrow> trans[A](r)"
by (unfold trans_def trans_on_def, blast)

lemma trans_on_imp_trans: "\<lbrakk>trans[A](r); r \<subseteq> A*A\<rbrakk> \<Longrightarrow> trans(r)"
by (simp add: trans_on_def trans_def, blast)


subsection\<open>Transitive closure of a relation\<close>

lemma rtrancl_bnd_mono:
     "bnd_mono(field(r)*field(r), %s. id(field(r)) \<union> (r O s))"
by (rule bnd_monoI, blast+)

lemma rtrancl_mono: "r<=s \<Longrightarrow> r^* \<subseteq> s^*"
apply (unfold rtrancl_def)
apply (rule lfp_mono)
apply (rule rtrancl_bnd_mono)+
apply blast
done

(* @{term"r^* = id(field(r)) \<union> ( r O r^* )"}    *)
lemmas rtrancl_unfold =
     rtrancl_bnd_mono [THEN rtrancl_def [THEN def_lfp_unfold]]

(** The relation rtrancl **)

(*  @{term"r^* \<subseteq> field(r) * field(r)"}  *)
lemmas rtrancl_type = rtrancl_def [THEN def_lfp_subset]

lemma relation_rtrancl: "relation(r^*)"
apply (simp add: relation_def)
apply (blast dest: rtrancl_type [THEN subsetD])
done

(*Reflexivity of rtrancl*)
lemma rtrancl_refl: "\<lbrakk>a \<in> field(r)\<rbrakk> \<Longrightarrow> <a,a> \<in> r^*"
apply (rule rtrancl_unfold [THEN ssubst])
apply (erule idI [THEN UnI1])
done

(*Closure under composition with r  *)
lemma rtrancl_into_rtrancl: "\<lbrakk><a,b> \<in> r^*;  <b,c> \<in> r\<rbrakk> \<Longrightarrow> <a,c> \<in> r^*"
apply (rule rtrancl_unfold [THEN ssubst])
apply (rule compI [THEN UnI2], assumption, assumption)
done

(*rtrancl of r contains all pairs in r  *)
lemma r_into_rtrancl: "<a,b> \<in> r \<Longrightarrow> <a,b> \<in> r^*"
by (rule rtrancl_refl [THEN rtrancl_into_rtrancl], blast+)

(*The premise ensures that r consists entirely of pairs*)
lemma r_subset_rtrancl: "relation(r) \<Longrightarrow> r \<subseteq> r^*"
by (simp add: relation_def, blast intro: r_into_rtrancl)

lemma rtrancl_field: "field(r^*) = field(r)"
by (blast intro: r_into_rtrancl dest!: rtrancl_type [THEN subsetD])


(** standard induction rule **)

lemma rtrancl_full_induct [case_names initial step, consumes 1]:
  "\<lbrakk><a,b> \<in> r^*;
      \<And>x. x \<in> field(r) \<Longrightarrow> P(<x,x>);
      \<And>x y z.\<lbrakk>P(<x,y>); <x,y>: r^*; <y,z>: r\<rbrakk>  \<Longrightarrow>  P(<x,z>)\<rbrakk>
   \<Longrightarrow>  P(<a,b>)"
by (erule def_induct [OF rtrancl_def rtrancl_bnd_mono], blast)

(*nice induction rule.
  Tried adding the typing hypotheses y,z \<in> field(r), but these
  caused expensive case splits!*)
lemma rtrancl_induct [case_names initial step, induct set: rtrancl]:
  "\<lbrakk><a,b> \<in> r^*;
      P(a);
      \<And>y z.\<lbrakk><a,y> \<in> r^*;  <y,z> \<in> r;  P(y)\<rbrakk> \<Longrightarrow> P(z)
\<rbrakk> \<Longrightarrow> P(b)"
(*by induction on this formula*)
apply (subgoal_tac "\<forall>y. <a,b> = <a,y> \<longrightarrow> P (y) ")
(*now solve first subgoal: this formula is sufficient*)
apply (erule spec [THEN mp], rule refl)
(*now do the induction*)
apply (erule rtrancl_full_induct, blast+)
done

(*transitivity of transitive closure\<And>-- by induction.*)
lemma trans_rtrancl: "trans(r^*)"
apply (unfold trans_def)
apply (intro allI impI)
apply (erule_tac b = z in rtrancl_induct, assumption)
apply (blast intro: rtrancl_into_rtrancl)
done

lemmas rtrancl_trans = trans_rtrancl [THEN transD]

(*elimination of rtrancl -- by induction on a special formula*)
lemma rtranclE:
    "\<lbrakk><a,b> \<in> r^*;  (a=b) \<Longrightarrow> P;
        \<And>y.\<lbrakk><a,y> \<in> r^*;   <y,b> \<in> r\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
apply (subgoal_tac "a = b | (\<exists>y. <a,y> \<in> r^* \<and> <y,b> \<in> r) ")
(*see HOL/trancl*)
apply blast
apply (erule rtrancl_induct, blast+)
done


(**** The relation trancl ****)

(*Transitivity of r^+ is proved by transitivity of r^*  *)
lemma trans_trancl: "trans(r^+)"
apply (unfold trans_def trancl_def)
apply (blast intro: rtrancl_into_rtrancl
                    trans_rtrancl [THEN transD, THEN compI])
done

lemmas trans_on_trancl = trans_trancl [THEN trans_imp_trans_on]

lemmas trancl_trans = trans_trancl [THEN transD]

(** Conversions between trancl and rtrancl **)

lemma trancl_into_rtrancl: "<a,b> \<in> r^+ \<Longrightarrow> <a,b> \<in> r^*"
apply (unfold trancl_def)
apply (blast intro: rtrancl_into_rtrancl)
done

(*r^+ contains all pairs in r  *)
lemma r_into_trancl: "<a,b> \<in> r \<Longrightarrow> <a,b> \<in> r^+"
apply (unfold trancl_def)
apply (blast intro!: rtrancl_refl)
done

(*The premise ensures that r consists entirely of pairs*)
lemma r_subset_trancl: "relation(r) \<Longrightarrow> r \<subseteq> r^+"
by (simp add: relation_def, blast intro: r_into_trancl)


(*intro rule by definition: from r^* and r  *)
lemma rtrancl_into_trancl1: "\<lbrakk><a,b> \<in> r^*;  <b,c> \<in> r\<rbrakk>   \<Longrightarrow>  <a,c> \<in> r^+"
by (unfold trancl_def, blast)

(*intro rule from r and r^*  *)
lemma rtrancl_into_trancl2:
    "\<lbrakk><a,b> \<in> r;  <b,c> \<in> r^*\<rbrakk>   \<Longrightarrow>  <a,c> \<in> r^+"
apply (erule rtrancl_induct)
 apply (erule r_into_trancl)
apply (blast intro: r_into_trancl trancl_trans)
done

(*Nice induction rule for trancl*)
lemma trancl_induct [case_names initial step, induct set: trancl]:
  "\<lbrakk><a,b> \<in> r^+;
      \<And>y.  \<lbrakk><a,y> \<in> r\<rbrakk> \<Longrightarrow> P(y);
      \<And>y z.\<lbrakk><a,y> \<in> r^+;  <y,z> \<in> r;  P(y)\<rbrakk> \<Longrightarrow> P(z)
\<rbrakk> \<Longrightarrow> P(b)"
apply (rule compEpair)
apply (unfold trancl_def, assumption)
(*by induction on this formula*)
apply (subgoal_tac "\<forall>z. <y,z> \<in> r \<longrightarrow> P (z) ")
(*now solve first subgoal: this formula is sufficient*)
 apply blast
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_into_trancl1)+
done

(*elimination of r^+ -- NOT an induction rule*)
lemma tranclE:
    "\<lbrakk><a,b> \<in> r^+;
        <a,b> \<in> r \<Longrightarrow> P;
        \<And>y.\<lbrakk><a,y> \<in> r^+; <y,b> \<in> r\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
apply (subgoal_tac "<a,b> \<in> r | (\<exists>y. <a,y> \<in> r^+ \<and> <y,b> \<in> r) ")
apply blast
apply (rule compEpair)
apply (unfold trancl_def, assumption)
apply (erule rtranclE)
apply (blast intro: rtrancl_into_trancl1)+
done

lemma trancl_type: "r^+ \<subseteq> field(r)*field(r)"
apply (unfold trancl_def)
apply (blast elim: rtrancl_type [THEN subsetD, THEN SigmaE2])
done

lemma relation_trancl: "relation(r^+)"
apply (simp add: relation_def)
apply (blast dest: trancl_type [THEN subsetD])
done

lemma trancl_subset_times: "r \<subseteq> A * A \<Longrightarrow> r^+ \<subseteq> A * A"
by (insert trancl_type [of r], blast)

lemma trancl_mono: "r<=s \<Longrightarrow> r^+ \<subseteq> s^+"
by (unfold trancl_def, intro comp_mono rtrancl_mono)

lemma trancl_eq_r: "\<lbrakk>relation(r); trans(r)\<rbrakk> \<Longrightarrow> r^+ = r"
apply (rule equalityI)
 prefer 2 apply (erule r_subset_trancl, clarify)
apply (frule trancl_type [THEN subsetD], clarify)
apply (erule trancl_induct, assumption)
apply (blast dest: transD)
done


(** Suggested by Sidi Ould Ehmety **)

lemma rtrancl_idemp [simp]: "(r^*)^* = r^*"
apply (rule equalityI, auto)
 prefer 2
 apply (frule rtrancl_type [THEN subsetD])
 apply (blast intro: r_into_rtrancl )
txt\<open>converse direction\<close>
apply (frule rtrancl_type [THEN subsetD], clarify)
apply (erule rtrancl_induct)
apply (simp add: rtrancl_refl rtrancl_field)
apply (blast intro: rtrancl_trans)
done

lemma rtrancl_subset: "\<lbrakk>R \<subseteq> S; S \<subseteq> R^*\<rbrakk> \<Longrightarrow> S^* = R^*"
apply (drule rtrancl_mono)
apply (drule rtrancl_mono, simp_all, blast)
done

lemma rtrancl_Un_rtrancl:
     "\<lbrakk>relation(r); relation(s)\<rbrakk> \<Longrightarrow> (r^* \<union> s^*)^* = (r \<union> s)^*"
apply (rule rtrancl_subset)
apply (blast dest: r_subset_rtrancl)
apply (blast intro: rtrancl_mono [THEN subsetD])
done

(*** "converse" laws by Sidi Ould Ehmety ***)

(** rtrancl **)

lemma rtrancl_converseD: "<x,y>:converse(r)^* \<Longrightarrow> <x,y>:converse(r^*)"
apply (rule converseI)
apply (frule rtrancl_type [THEN subsetD])
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_refl)
apply (blast intro: r_into_rtrancl rtrancl_trans)
done

lemma rtrancl_converseI: "<x,y>:converse(r^*) \<Longrightarrow> <x,y>:converse(r)^*"
apply (drule converseD)
apply (frule rtrancl_type [THEN subsetD])
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_refl)
apply (blast intro: r_into_rtrancl rtrancl_trans)
done

lemma rtrancl_converse: "converse(r)^* = converse(r^*)"
apply (safe intro!: equalityI)
apply (frule rtrancl_type [THEN subsetD])
apply (safe dest!: rtrancl_converseD intro!: rtrancl_converseI)
done

(** trancl **)

lemma trancl_converseD: "<a, b>:converse(r)^+ \<Longrightarrow> <a, b>:converse(r^+)"
apply (erule trancl_induct)
apply (auto intro: r_into_trancl trancl_trans)
done

lemma trancl_converseI: "<x,y>:converse(r^+) \<Longrightarrow> <x,y>:converse(r)^+"
apply (drule converseD)
apply (erule trancl_induct)
apply (auto intro: r_into_trancl trancl_trans)
done

lemma trancl_converse: "converse(r)^+ = converse(r^+)"
apply (safe intro!: equalityI)
apply (frule trancl_type [THEN subsetD])
apply (safe dest!: trancl_converseD intro!: trancl_converseI)
done

lemma converse_trancl_induct [case_names initial step, consumes 1]:
"\<lbrakk><a, b>:r^+; \<And>y. <y, b> :r \<Longrightarrow> P(y);
      \<And>y z. \<lbrakk><y, z> \<in> r; <z, b> \<in> r^+; P(z)\<rbrakk> \<Longrightarrow> P(y)\<rbrakk>
       \<Longrightarrow> P(a)"
apply (drule converseI)
apply (simp (no_asm_use) add: trancl_converse [symmetric])
apply (erule trancl_induct)
apply (auto simp add: trancl_converse)
done

end
