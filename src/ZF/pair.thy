(*  Title:      ZF/pair.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header{*Ordered Pairs*}

theory pair imports upair
begin

ML_file "simpdata.ML"

setup {*
  Simplifier.map_simpset_global
    (Simplifier.set_mksimps (K (map mk_eq o ZF_atomize o gen_all))
      #> Simplifier.add_cong @{thm if_weak_cong})
*}

ML {* val ZF_ss = @{simpset} *}

simproc_setup defined_Bex ("\<exists>x\<in>A. P(x) & Q(x)") = {*
  let
    val unfold_bex_tac = unfold_tac @{thms Bex_def};
    fun prove_bex_tac ss = unfold_bex_tac ss THEN Quantifier1.prove_one_point_ex_tac;
  in fn _ => fn ss => Quantifier1.rearrange_bex (prove_bex_tac ss) ss end
*}

simproc_setup defined_Ball ("\<forall>x\<in>A. P(x) \<longrightarrow> Q(x)") = {*
  let
    val unfold_ball_tac = unfold_tac @{thms Ball_def};
    fun prove_ball_tac ss = unfold_ball_tac ss THEN Quantifier1.prove_one_point_all_tac;
  in fn _ => fn ss => Quantifier1.rearrange_ball (prove_ball_tac ss) ss end
*}


(** Lemmas for showing that <a,b> uniquely determines a and b **)

lemma singleton_eq_iff [iff]: "{a} = {b} \<longleftrightarrow> a=b"
by (rule extension [THEN iff_trans], blast)

lemma doubleton_eq_iff: "{a,b} = {c,d} \<longleftrightarrow> (a=c & b=d) | (a=d & b=c)"
by (rule extension [THEN iff_trans], blast)

lemma Pair_iff [simp]: "<a,b> = <c,d> \<longleftrightarrow> a=c & b=d"
by (simp add: Pair_def doubleton_eq_iff, blast)

lemmas Pair_inject = Pair_iff [THEN iffD1, THEN conjE, elim!]

lemmas Pair_inject1 = Pair_iff [THEN iffD1, THEN conjunct1]
lemmas Pair_inject2 = Pair_iff [THEN iffD1, THEN conjunct2]

lemma Pair_not_0: "<a,b> \<noteq> 0"
apply (unfold Pair_def)
apply (blast elim: equalityE)
done

lemmas Pair_neq_0 = Pair_not_0 [THEN notE, elim!]

declare sym [THEN Pair_neq_0, elim!]

lemma Pair_neq_fst: "<a,b>=a ==> P"
proof (unfold Pair_def)
  assume eq: "{{a, a}, {a, b}} = a"
  have  "{a, a} \<in> {{a, a}, {a, b}}" by (rule consI1)
  hence "{a, a} \<in> a" by (simp add: eq)
  moreover have "a \<in> {a, a}" by (rule consI1)
  ultimately show "P" by (rule mem_asym)
qed

lemma Pair_neq_snd: "<a,b>=b ==> P"
proof (unfold Pair_def)
  assume eq: "{{a, a}, {a, b}} = b"
  have  "{a, b} \<in> {{a, a}, {a, b}}" by blast
  hence "{a, b} \<in> b" by (simp add: eq)
  moreover have "b \<in> {a, b}" by blast
  ultimately show "P" by (rule mem_asym)
qed


subsection{*Sigma: Disjoint Union of a Family of Sets*}

text{*Generalizes Cartesian product*}

lemma Sigma_iff [simp]: "<a,b>: Sigma(A,B) \<longleftrightarrow> a \<in> A & b \<in> B(a)"
by (simp add: Sigma_def)

lemma SigmaI [TC,intro!]: "[| a \<in> A;  b \<in> B(a) |] ==> <a,b> \<in> Sigma(A,B)"
by simp

lemmas SigmaD1 = Sigma_iff [THEN iffD1, THEN conjunct1]
lemmas SigmaD2 = Sigma_iff [THEN iffD1, THEN conjunct2]

(*The general elimination rule*)
lemma SigmaE [elim!]:
    "[| c \<in> Sigma(A,B);
        !!x y.[| x \<in> A;  y \<in> B(x);  c=<x,y> |] ==> P
     |] ==> P"
by (unfold Sigma_def, blast)

lemma SigmaE2 [elim!]:
    "[| <a,b> \<in> Sigma(A,B);
        [| a \<in> A;  b \<in> B(a) |] ==> P
     |] ==> P"
by (unfold Sigma_def, blast)

lemma Sigma_cong:
    "[| A=A';  !!x. x \<in> A' ==> B(x)=B'(x) |] ==>
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


subsection{*Projections @{term fst} and @{term snd}*}

lemma fst_conv [simp]: "fst(<a,b>) = a"
by (simp add: fst_def)

lemma snd_conv [simp]: "snd(<a,b>) = b"
by (simp add: snd_def)

lemma fst_type [TC]: "p \<in> Sigma(A,B) ==> fst(p) \<in> A"
by auto

lemma snd_type [TC]: "p \<in> Sigma(A,B) ==> snd(p) \<in> B(fst(p))"
by auto

lemma Pair_fst_snd_eq: "a \<in> Sigma(A,B) ==> <fst(a),snd(a)> = a"
by auto


subsection{*The Eliminator, @{term split}*}

(*A META-equality, so that it applies to higher types as well...*)
lemma split [simp]: "split(%x y. c(x,y), <a,b>) == c(a,b)"
by (simp add: split_def)

lemma split_type [TC]:
    "[|  p \<in> Sigma(A,B);
         !!x y.[| x \<in> A; y \<in> B(x) |] ==> c(x,y):C(<x,y>)
     |] ==> split(%x y. c(x,y), p) \<in> C(p)"
by (erule SigmaE, auto)

lemma expand_split:
  "u \<in> A*B ==>
        R(split(c,u)) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. u = <x,y> \<longrightarrow> R(c(x,y)))"
by (auto simp add: split_def)


subsection{*A version of @{term split} for Formulae: Result Type @{typ o}*}

lemma splitI: "R(a,b) ==> split(R, <a,b>)"
by (simp add: split_def)

lemma splitE:
    "[| split(R,z);  z \<in> Sigma(A,B);
        !!x y. [| z = <x,y>;  R(x,y) |] ==> P
     |] ==> P"
by (auto simp add: split_def)

lemma splitD: "split(R,<a,b>) ==> R(a,b)"
by (simp add: split_def)

text {*
  \bigskip Complex rules for Sigma.
*}

lemma split_paired_Bex_Sigma [simp]:
     "(\<exists>z \<in> Sigma(A,B). P(z)) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B(x). P(<x,y>))"
by blast

lemma split_paired_Ball_Sigma [simp]:
     "(\<forall>z \<in> Sigma(A,B). P(z)) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B(x). P(<x,y>))"
by blast

end


