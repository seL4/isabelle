(*  Title:      ZF/pair.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section\<open>Ordered Pairs\<close>

theory pair imports upair
begin

ML_file \<open>simpdata.ML\<close>

setup \<open>
  Simplifier.map_theory_simpset
    (Simplifier.set_mksimps (fn ctxt => map mk_eq o ZF_atomize o Variable.gen_all ctxt)
      #> Simplifier.add_cong @{thm if_weak_cong})
\<close>

ML \<open>val ZF_ss = simpset_of \<^context>\<close>

simproc_setup defined_Bex ("\<exists>x\<in>A. P(x) \<and> Q(x)") = \<open>
  K (Quantifier1.rearrange_Bex (fn ctxt => unfold_tac ctxt @{thms Bex_def}))
\<close>

simproc_setup defined_Ball ("\<forall>x\<in>A. P(x) \<longrightarrow> Q(x)") = \<open>
  K (Quantifier1.rearrange_Ball (fn ctxt => unfold_tac ctxt @{thms Ball_def}))
\<close>


(** Lemmas for showing that \<langle>a,b\<rangle> uniquely determines a and b **)

lemma singleton_eq_iff [iff]: "{a} = {b} \<longleftrightarrow> a=b"
by (rule extension [THEN iff_trans], blast)

lemma doubleton_eq_iff: "{a,b} = {c,d} \<longleftrightarrow> (a=c \<and> b=d) | (a=d \<and> b=c)"
by (rule extension [THEN iff_trans], blast)

lemma Pair_iff [simp]: "\<langle>a,b\<rangle> = \<langle>c,d\<rangle> \<longleftrightarrow> a=c \<and> b=d"
by (simp add: Pair_def doubleton_eq_iff, blast)

lemmas Pair_inject = Pair_iff [THEN iffD1, THEN conjE, elim!]

lemmas Pair_inject1 = Pair_iff [THEN iffD1, THEN conjunct1]
lemmas Pair_inject2 = Pair_iff [THEN iffD1, THEN conjunct2]

lemma Pair_not_0: "\<langle>a,b\<rangle> \<noteq> 0"
  unfolding Pair_def
apply (blast elim: equalityE)
done

lemmas Pair_neq_0 = Pair_not_0 [THEN notE, elim!]

declare sym [THEN Pair_neq_0, elim!]

lemma Pair_neq_fst: "\<langle>a,b\<rangle>=a \<Longrightarrow> P"
proof (unfold Pair_def)
  assume eq: "{{a, a}, {a, b}} = a"
  have  "{a, a} \<in> {{a, a}, {a, b}}" by (rule consI1)
  hence "{a, a} \<in> a" by (simp add: eq)
  moreover have "a \<in> {a, a}" by (rule consI1)
  ultimately show "P" by (rule mem_asym)
qed

lemma Pair_neq_snd: "\<langle>a,b\<rangle>=b \<Longrightarrow> P"
proof (unfold Pair_def)
  assume eq: "{{a, a}, {a, b}} = b"
  have  "{a, b} \<in> {{a, a}, {a, b}}" by blast
  hence "{a, b} \<in> b" by (simp add: eq)
  moreover have "b \<in> {a, b}" by blast
  ultimately show "P" by (rule mem_asym)
qed


subsection\<open>Sigma: Disjoint Union of a Family of Sets\<close>

text\<open>Generalizes Cartesian product\<close>

lemma Sigma_iff [simp]: "\<langle>a,b\<rangle>: Sigma(A,B) \<longleftrightarrow> a \<in> A \<and> b \<in> B(a)"
by (simp add: Sigma_def)

lemma SigmaI [TC,intro!]: "\<lbrakk>a \<in> A;  b \<in> B(a)\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle> \<in> Sigma(A,B)"
by simp

lemmas SigmaD1 = Sigma_iff [THEN iffD1, THEN conjunct1]
lemmas SigmaD2 = Sigma_iff [THEN iffD1, THEN conjunct2]

(*The general elimination rule*)
lemma SigmaE [elim!]:
    "\<lbrakk>c \<in> Sigma(A,B);
        \<And>x y.\<lbrakk>x \<in> A;  y \<in> B(x);  c=\<langle>x,y\<rangle>\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
by (unfold Sigma_def, blast)

lemma SigmaE2 [elim!]:
    "\<lbrakk>\<langle>a,b\<rangle> \<in> Sigma(A,B);
        \<lbrakk>a \<in> A;  b \<in> B(a)\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
by (unfold Sigma_def, blast)

lemma Sigma_cong:
    "\<lbrakk>A=A';  \<And>x. x \<in> A' \<Longrightarrow> B(x)=B'(x)\<rbrakk> \<Longrightarrow>
     Sigma(A,B) = Sigma(A',B')"
by (simp add: Sigma_def)

(*Sigma_cong, Pi_cong NOT given to Addcongs: they cause
  flex-flex pairs and the "Check your prover" error.  Most
  Sigmas and Pis are abbreviated as * or -> *)

lemma Sigma_empty1 [simp]: "Sigma(0,B) = 0"
by blast

lemma Sigma_empty2 [simp]: "A*0 = 0"
by blast

lemma Sigma_empty_iff: "A*B=0 \<longleftrightarrow> A=0 | B=0"
by blast


subsection\<open>Projections \<^term>\<open>fst\<close> and \<^term>\<open>snd\<close>\<close>

lemma fst_conv [simp]: "fst(\<langle>a,b\<rangle>) = a"
by (simp add: fst_def)

lemma snd_conv [simp]: "snd(\<langle>a,b\<rangle>) = b"
by (simp add: snd_def)

lemma fst_type [TC]: "p \<in> Sigma(A,B) \<Longrightarrow> fst(p) \<in> A"
by auto

lemma snd_type [TC]: "p \<in> Sigma(A,B) \<Longrightarrow> snd(p) \<in> B(fst(p))"
by auto

lemma Pair_fst_snd_eq: "a \<in> Sigma(A,B) \<Longrightarrow> <fst(a),snd(a)> = a"
by auto


subsection\<open>The Eliminator, \<^term>\<open>split\<close>\<close>

(*A META-equality, so that it applies to higher types as well...*)
lemma split [simp]: "split(\<lambda>x y. c(x,y), \<langle>a,b\<rangle>) \<equiv> c(a,b)"
by (simp add: split_def)

lemma split_type [TC]:
    "\<lbrakk>p \<in> Sigma(A,B);
         \<And>x y.\<lbrakk>x \<in> A; y \<in> B(x)\<rbrakk> \<Longrightarrow> c(x,y):C(\<langle>x,y\<rangle>)
\<rbrakk> \<Longrightarrow> split(\<lambda>x y. c(x,y), p) \<in> C(p)"
by (erule SigmaE, auto)

lemma expand_split:
  "u \<in> A*B \<Longrightarrow>
        R(split(c,u)) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. u = \<langle>x,y\<rangle> \<longrightarrow> R(c(x,y)))"
by (auto simp add: split_def)


subsection\<open>A version of \<^term>\<open>split\<close> for Formulae: Result Type \<^typ>\<open>o\<close>\<close>

lemma splitI: "R(a,b) \<Longrightarrow> split(R, \<langle>a,b\<rangle>)"
by (simp add: split_def)

lemma splitE:
    "\<lbrakk>split(R,z);  z \<in> Sigma(A,B);
        \<And>x y. \<lbrakk>z = \<langle>x,y\<rangle>;  R(x,y)\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
by (auto simp add: split_def)

lemma splitD: "split(R,\<langle>a,b\<rangle>) \<Longrightarrow> R(a,b)"
by (simp add: split_def)

text \<open>
  \bigskip Complex rules for Sigma.
\<close>

lemma split_paired_Bex_Sigma [simp]:
     "(\<exists>z \<in> Sigma(A,B). P(z)) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B(x). P(\<langle>x,y\<rangle>))"
by blast

lemma split_paired_Ball_Sigma [simp]:
     "(\<forall>z \<in> Sigma(A,B). P(z)) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B(x). P(\<langle>x,y\<rangle>))"
by blast

end


