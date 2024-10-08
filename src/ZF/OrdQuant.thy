(*  Title:      ZF/OrdQuant.thy
    Authors:    Krzysztof Grabczewski and L C Paulson
*)

section \<open>Special quantifiers\<close>

theory OrdQuant imports Ordinal begin

subsection \<open>Quantifiers and union operator for ordinals\<close>

definition
  (* Ordinal Quantifiers *)
  oall :: "[i, i \<Rightarrow> o] \<Rightarrow> o"  where
    "oall(A, P) \<equiv> \<forall>x. x<A \<longrightarrow> P(x)"

definition
  oex :: "[i, i \<Rightarrow> o] \<Rightarrow> o"  where
    "oex(A, P)  \<equiv> \<exists>x. x<A \<and> P(x)"

definition
  (* Ordinal Union *)
  OUnion :: "[i, i \<Rightarrow> i] \<Rightarrow> i"  where
    "OUnion(i,B) \<equiv> {z: \<Union>x\<in>i. B(x). Ord(i)}"

syntax
  "_oall"     :: "[idt, i, o] \<Rightarrow> o"  (\<open>(\<open>indent=3 notation=\<open>binder \<forall><\<close>\<close>\<forall>_<_./ _)\<close> 10)
  "_oex"      :: "[idt, i, o] \<Rightarrow> o"  (\<open>(\<open>indent=3 notation=\<open>binder \<exists><\<close>\<close>\<exists>_<_./ _)\<close> 10)
  "_OUNION"   :: "[idt, i, i] \<Rightarrow> i"  (\<open>(\<open>indent=3 notation=\<open>binder \<Union><\<close>\<close>\<Union>_<_./ _)\<close> 10)
syntax_consts
  "_oall" \<rightleftharpoons> oall and
  "_oex" \<rightleftharpoons> oex and
  "_OUNION" \<rightleftharpoons> OUnion
translations
  "\<forall>x<a. P" \<rightleftharpoons> "CONST oall(a, \<lambda>x. P)"
  "\<exists>x<a. P" \<rightleftharpoons> "CONST oex(a, \<lambda>x. P)"
  "\<Union>x<a. B" \<rightleftharpoons> "CONST OUnion(a, \<lambda>x. B)"


subsubsection \<open>simplification of the new quantifiers\<close>


(*MOST IMPORTANT that this is added to the simpset BEFORE Ord_atomize
  is proved.  Ord_atomize would convert this rule to
    x < 0 \<Longrightarrow> P(x) \<equiv> True, which causes dire effects!*)
lemma [simp]: "(\<forall>x<0. P(x))"
by (simp add: oall_def)

lemma [simp]: "\<not>(\<exists>x<0. P(x))"
by (simp add: oex_def)

lemma [simp]: "(\<forall>x<succ(i). P(x)) <-> (Ord(i) \<longrightarrow> P(i) \<and> (\<forall>x<i. P(x)))"
apply (simp add: oall_def le_iff)
apply (blast intro: lt_Ord2)
done

lemma [simp]: "(\<exists>x<succ(i). P(x)) <-> (Ord(i) \<and> (P(i) | (\<exists>x<i. P(x))))"
apply (simp add: oex_def le_iff)
apply (blast intro: lt_Ord2)
done

subsubsection \<open>Union over ordinals\<close>

lemma Ord_OUN [intro,simp]:
     "\<lbrakk>\<And>x. x<A \<Longrightarrow> Ord(B(x))\<rbrakk> \<Longrightarrow> Ord(\<Union>x<A. B(x))"
by (simp add: OUnion_def ltI Ord_UN)

lemma OUN_upper_lt:
     "\<lbrakk>a<A;  i < b(a);  Ord(\<Union>x<A. b(x))\<rbrakk> \<Longrightarrow> i < (\<Union>x<A. b(x))"
by (unfold OUnion_def lt_def, blast )

lemma OUN_upper_le:
     "\<lbrakk>a<A;  i\<le>b(a);  Ord(\<Union>x<A. b(x))\<rbrakk> \<Longrightarrow> i \<le> (\<Union>x<A. b(x))"
apply (unfold OUnion_def, auto)
apply (rule UN_upper_le )
apply (auto simp add: lt_def)
done

lemma Limit_OUN_eq: "Limit(i) \<Longrightarrow> (\<Union>x<i. x) = i"
by (simp add: OUnion_def Limit_Union_eq Limit_is_Ord)

(* No < version of this theorem: consider that @{term"(\<Union>i\<in>nat.i)=nat"}! *)
lemma OUN_least:
     "(\<And>x. x<A \<Longrightarrow> B(x) \<subseteq> C) \<Longrightarrow> (\<Union>x<A. B(x)) \<subseteq> C"
by (simp add: OUnion_def UN_least ltI)

lemma OUN_least_le:
     "\<lbrakk>Ord(i);  \<And>x. x<A \<Longrightarrow> b(x) \<le> i\<rbrakk> \<Longrightarrow> (\<Union>x<A. b(x)) \<le> i"
by (simp add: OUnion_def UN_least_le ltI Ord_0_le)

lemma le_implies_OUN_le_OUN:
     "\<lbrakk>\<And>x. x<A \<Longrightarrow> c(x) \<le> d(x)\<rbrakk> \<Longrightarrow> (\<Union>x<A. c(x)) \<le> (\<Union>x<A. d(x))"
by (blast intro: OUN_least_le OUN_upper_le le_Ord2 Ord_OUN)

lemma OUN_UN_eq:
     "(\<And>x. x \<in> A \<Longrightarrow> Ord(B(x)))
      \<Longrightarrow> (\<Union>z < (\<Union>x\<in>A. B(x)). C(z)) = (\<Union>x\<in>A. \<Union>z < B(x). C(z))"
by (simp add: OUnion_def)

lemma OUN_Union_eq:
     "(\<And>x. x \<in> X \<Longrightarrow> Ord(x))
      \<Longrightarrow> (\<Union>z < \<Union>(X). C(z)) = (\<Union>x\<in>X. \<Union>z < x. C(z))"
by (simp add: OUnion_def)

(*So that rule_format will get rid of this quantifier...*)
lemma atomize_oall [symmetric, rulify]:
     "(\<And>x. x<A \<Longrightarrow> P(x)) \<equiv> Trueprop (\<forall>x<A. P(x))"
by (simp add: oall_def atomize_all atomize_imp)

subsubsection \<open>universal quantifier for ordinals\<close>

lemma oallI [intro!]:
    "\<lbrakk>\<And>x. x<A \<Longrightarrow> P(x)\<rbrakk> \<Longrightarrow> \<forall>x<A. P(x)"
by (simp add: oall_def)

lemma ospec: "\<lbrakk>\<forall>x<A. P(x);  x<A\<rbrakk> \<Longrightarrow> P(x)"
by (simp add: oall_def)

lemma oallE:
    "\<lbrakk>\<forall>x<A. P(x);  P(x) \<Longrightarrow> Q;  \<not>x<A \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (simp add: oall_def, blast)

lemma rev_oallE [elim]:
    "\<lbrakk>\<forall>x<A. P(x);  \<not>x<A \<Longrightarrow> Q;  P(x) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (simp add: oall_def, blast)


(*Trival rewrite rule.  @{term"(\<forall>x<a.P)<->P"} holds only if a is not 0!*)
lemma oall_simp [simp]: "(\<forall>x<a. True) <-> True"
by blast

(*Congruence rule for rewriting*)
lemma oall_cong [cong]:
    "\<lbrakk>a=a';  \<And>x. x<a' \<Longrightarrow> P(x) <-> P'(x)\<rbrakk>
     \<Longrightarrow> oall(a, \<lambda>x. P(x)) <-> oall(a', \<lambda>x. P'(x))"
by (simp add: oall_def)


subsubsection \<open>existential quantifier for ordinals\<close>

lemma oexI [intro]:
    "\<lbrakk>P(x);  x<A\<rbrakk> \<Longrightarrow> \<exists>x<A. P(x)"
apply (simp add: oex_def, blast)
done

(*Not of the general form for such rules... *)
lemma oexCI:
   "\<lbrakk>\<forall>x<A. \<not>P(x) \<Longrightarrow> P(a);  a<A\<rbrakk> \<Longrightarrow> \<exists>x<A. P(x)"
apply (simp add: oex_def, blast)
done

lemma oexE [elim!]:
    "\<lbrakk>\<exists>x<A. P(x);  \<And>x. \<lbrakk>x<A; P(x)\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (simp add: oex_def, blast)
done

lemma oex_cong [cong]:
    "\<lbrakk>a=a';  \<And>x. x<a' \<Longrightarrow> P(x) <-> P'(x)\<rbrakk>
     \<Longrightarrow> oex(a, \<lambda>x. P(x)) <-> oex(a', \<lambda>x. P'(x))"
apply (simp add: oex_def cong add: conj_cong)
done


subsubsection \<open>Rules for Ordinal-Indexed Unions\<close>

lemma OUN_I [intro]: "\<lbrakk>a<i;  b \<in> B(a)\<rbrakk> \<Longrightarrow> b: (\<Union>z<i. B(z))"
by (unfold OUnion_def lt_def, blast)

lemma OUN_E [elim!]:
    "\<lbrakk>b \<in> (\<Union>z<i. B(z));  \<And>a.\<lbrakk>b \<in> B(a);  a<i\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
apply (unfold OUnion_def lt_def, blast)
done

lemma OUN_iff: "b \<in> (\<Union>x<i. B(x)) <-> (\<exists>x<i. b \<in> B(x))"
by (unfold OUnion_def oex_def lt_def, blast)

lemma OUN_cong [cong]:
    "\<lbrakk>i=j;  \<And>x. x<j \<Longrightarrow> C(x)=D(x)\<rbrakk> \<Longrightarrow> (\<Union>x<i. C(x)) = (\<Union>x<j. D(x))"
by (simp add: OUnion_def lt_def OUN_iff)

lemma lt_induct:
    "\<lbrakk>i<k;  \<And>x.\<lbrakk>x<k;  \<forall>y<x. P(y)\<rbrakk> \<Longrightarrow> P(x)\<rbrakk>  \<Longrightarrow>  P(i)"
apply (simp add: lt_def oall_def)
apply (erule conjE)
apply (erule Ord_induct, assumption, blast)
done


subsection \<open>Quantification over a class\<close>

definition
  "rall"     :: "[i\<Rightarrow>o, i\<Rightarrow>o] \<Rightarrow> o"  where
    "rall(M, P) \<equiv> \<forall>x. M(x) \<longrightarrow> P(x)"

definition
  "rex"      :: "[i\<Rightarrow>o, i\<Rightarrow>o] \<Rightarrow> o"  where
    "rex(M, P) \<equiv> \<exists>x. M(x) \<and> P(x)"

syntax
  "_rall"     :: "[pttrn, i\<Rightarrow>o, o] \<Rightarrow> o"  (\<open>(\<open>indent=3 notation=\<open>binder \<forall>[]\<close>\<close>\<forall>_[_]./ _)\<close> 10)
  "_rex"      :: "[pttrn, i\<Rightarrow>o, o] \<Rightarrow> o"  (\<open>(\<open>indent=3 notation=\<open>binder \<exists>[]\<close>\<close>\<exists>_[_]./ _)\<close> 10)
syntax_consts
  "_rall" \<rightleftharpoons> rall and
  "_rex" \<rightleftharpoons> rex
translations
  "\<forall>x[M]. P" \<rightleftharpoons> "CONST rall(M, \<lambda>x. P)"
  "\<exists>x[M]. P" \<rightleftharpoons> "CONST rex(M, \<lambda>x. P)"


subsubsection\<open>Relativized universal quantifier\<close>

lemma rallI [intro!]: "\<lbrakk>\<And>x. M(x) \<Longrightarrow> P(x)\<rbrakk> \<Longrightarrow> \<forall>x[M]. P(x)"
by (simp add: rall_def)

lemma rspec: "\<lbrakk>\<forall>x[M]. P(x); M(x)\<rbrakk> \<Longrightarrow> P(x)"
by (simp add: rall_def)

(*Instantiates x first: better for automatic theorem proving?*)
lemma rev_rallE [elim]:
    "\<lbrakk>\<forall>x[M]. P(x);  \<not> M(x) \<Longrightarrow> Q;  P(x) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (simp add: rall_def, blast)

lemma rallE: "\<lbrakk>\<forall>x[M]. P(x);  P(x) \<Longrightarrow> Q;  \<not> M(x) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by blast

(*Trival rewrite rule;   (\<forall>x[M].P)<->P holds only if A is nonempty!*)
lemma rall_triv [simp]: "(\<forall>x[M]. P) \<longleftrightarrow> ((\<exists>x. M(x)) \<longrightarrow> P)"
by (simp add: rall_def)

(*Congruence rule for rewriting*)
lemma rall_cong [cong]:
    "(\<And>x. M(x) \<Longrightarrow> P(x) <-> P'(x)) \<Longrightarrow> (\<forall>x[M]. P(x)) <-> (\<forall>x[M]. P'(x))"
by (simp add: rall_def)


subsubsection\<open>Relativized existential quantifier\<close>

lemma rexI [intro]: "\<lbrakk>P(x); M(x)\<rbrakk> \<Longrightarrow> \<exists>x[M]. P(x)"
by (simp add: rex_def, blast)

(*The best argument order when there is only one M(x)*)
lemma rev_rexI: "\<lbrakk>M(x);  P(x)\<rbrakk> \<Longrightarrow> \<exists>x[M]. P(x)"
by blast

(*Not of the general form for such rules... *)
lemma rexCI: "\<lbrakk>\<forall>x[M]. \<not>P(x) \<Longrightarrow> P(a); M(a)\<rbrakk> \<Longrightarrow> \<exists>x[M]. P(x)"
by blast

lemma rexE [elim!]: "\<lbrakk>\<exists>x[M]. P(x);  \<And>x. \<lbrakk>M(x); P(x)\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (simp add: rex_def, blast)

(*We do not even have (\<exists>x[M]. True) <-> True unless A is nonempty\<And>*)
lemma rex_triv [simp]: "(\<exists>x[M]. P) \<longleftrightarrow> ((\<exists>x. M(x)) \<and> P)"
by (simp add: rex_def)

lemma rex_cong [cong]:
    "(\<And>x. M(x) \<Longrightarrow> P(x) <-> P'(x)) \<Longrightarrow> (\<exists>x[M]. P(x)) <-> (\<exists>x[M]. P'(x))"
by (simp add: rex_def cong: conj_cong)

lemma rall_is_ball [simp]: "(\<forall>x[\<lambda>z. z\<in>A]. P(x)) <-> (\<forall>x\<in>A. P(x))"
by blast

lemma rex_is_bex [simp]: "(\<exists>x[\<lambda>z. z\<in>A]. P(x)) <-> (\<exists>x\<in>A. P(x))"
by blast

lemma atomize_rall: "(\<And>x. M(x) \<Longrightarrow> P(x)) \<equiv> Trueprop (\<forall>x[M]. P(x))"
by (simp add: rall_def atomize_all atomize_imp)

declare atomize_rall [symmetric, rulify]

lemma rall_simps1:
     "(\<forall>x[M]. P(x) \<and> Q)   <-> (\<forall>x[M]. P(x)) \<and> ((\<forall>x[M]. False) | Q)"
     "(\<forall>x[M]. P(x) | Q)   <-> ((\<forall>x[M]. P(x)) | Q)"
     "(\<forall>x[M]. P(x) \<longrightarrow> Q) <-> ((\<exists>x[M]. P(x)) \<longrightarrow> Q)"
     "(\<not>(\<forall>x[M]. P(x))) <-> (\<exists>x[M]. \<not>P(x))"
by blast+

lemma rall_simps2:
     "(\<forall>x[M]. P \<and> Q(x))   <-> ((\<forall>x[M]. False) | P) \<and> (\<forall>x[M]. Q(x))"
     "(\<forall>x[M]. P | Q(x))   <-> (P | (\<forall>x[M]. Q(x)))"
     "(\<forall>x[M]. P \<longrightarrow> Q(x)) <-> (P \<longrightarrow> (\<forall>x[M]. Q(x)))"
by blast+

lemmas rall_simps [simp] = rall_simps1 rall_simps2

lemma rall_conj_distrib:
    "(\<forall>x[M]. P(x) \<and> Q(x)) <-> ((\<forall>x[M]. P(x)) \<and> (\<forall>x[M]. Q(x)))"
by blast

lemma rex_simps1:
     "(\<exists>x[M]. P(x) \<and> Q) <-> ((\<exists>x[M]. P(x)) \<and> Q)"
     "(\<exists>x[M]. P(x) | Q) <-> (\<exists>x[M]. P(x)) | ((\<exists>x[M]. True) \<and> Q)"
     "(\<exists>x[M]. P(x) \<longrightarrow> Q) <-> ((\<forall>x[M]. P(x)) \<longrightarrow> ((\<exists>x[M]. True) \<and> Q))"
     "(\<not>(\<exists>x[M]. P(x))) <-> (\<forall>x[M]. \<not>P(x))"
by blast+

lemma rex_simps2:
     "(\<exists>x[M]. P \<and> Q(x)) <-> (P \<and> (\<exists>x[M]. Q(x)))"
     "(\<exists>x[M]. P | Q(x)) <-> ((\<exists>x[M]. True) \<and> P) | (\<exists>x[M]. Q(x))"
     "(\<exists>x[M]. P \<longrightarrow> Q(x)) <-> (((\<forall>x[M]. False) | P) \<longrightarrow> (\<exists>x[M]. Q(x)))"
by blast+

lemmas rex_simps [simp] = rex_simps1 rex_simps2

lemma rex_disj_distrib:
    "(\<exists>x[M]. P(x) | Q(x)) <-> ((\<exists>x[M]. P(x)) | (\<exists>x[M]. Q(x)))"
by blast


subsubsection\<open>One-point rule for bounded quantifiers\<close>

lemma rex_triv_one_point1 [simp]: "(\<exists>x[M]. x=a) <-> ( M(a))"
by blast

lemma rex_triv_one_point2 [simp]: "(\<exists>x[M]. a=x) <-> ( M(a))"
by blast

lemma rex_one_point1 [simp]: "(\<exists>x[M]. x=a \<and> P(x)) <-> ( M(a) \<and> P(a))"
by blast

lemma rex_one_point2 [simp]: "(\<exists>x[M]. a=x \<and> P(x)) <-> ( M(a) \<and> P(a))"
by blast

lemma rall_one_point1 [simp]: "(\<forall>x[M]. x=a \<longrightarrow> P(x)) <-> ( M(a) \<longrightarrow> P(a))"
by blast

lemma rall_one_point2 [simp]: "(\<forall>x[M]. a=x \<longrightarrow> P(x)) <-> ( M(a) \<longrightarrow> P(a))"
by blast


subsubsection\<open>Sets as Classes\<close>

definition
  setclass :: "[i,i] \<Rightarrow> o"  (\<open>(\<open>open_block notation=\<open>prefix setclass\<close>\<close>##_)\<close> [40] 40)  where
   "setclass(A) \<equiv> \<lambda>x. x \<in> A"

lemma setclass_iff [simp]: "setclass(A,x) <-> x \<in> A"
by (simp add: setclass_def)

lemma rall_setclass_is_ball [simp]: "(\<forall>x[##A]. P(x)) <-> (\<forall>x\<in>A. P(x))"
by auto

lemma rex_setclass_is_bex [simp]: "(\<exists>x[##A]. P(x)) <-> (\<exists>x\<in>A. P(x))"
by auto


ML
\<open>
val Ord_atomize =
  atomize ([(\<^const_name>\<open>oall\<close>, @{thms ospec}), (\<^const_name>\<open>rall\<close>, @{thms rspec})] @
    ZF_conn_pairs, ZF_mem_pairs);
\<close>
declaration \<open>fn _ =>
  Simplifier.map_ss (Simplifier.set_mksimps (fn ctxt =>
    map mk_eq o Ord_atomize o Variable.gen_all ctxt))
\<close>

text \<open>Setting up the one-point-rule simproc\<close>

simproc_setup defined_rex ("\<exists>x[M]. P(x) \<and> Q(x)") = \<open>
  K (Quantifier1.rearrange_Bex (fn ctxt => unfold_tac ctxt @{thms rex_def}))
\<close>

simproc_setup defined_rall ("\<forall>x[M]. P(x) \<longrightarrow> Q(x)") = \<open>
  K (Quantifier1.rearrange_Ball (fn ctxt => unfold_tac ctxt @{thms rall_def}))
\<close>

end
