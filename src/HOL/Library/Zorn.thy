(*  Title       : HOL/Library/Zorn.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Description : Zorn's Lemma -- see Larry Paulson's Zorn.thy in ZF
*)

header {* Zorn's Lemma *}

theory Zorn = Main:

text{*
  The lemma and section numbers refer to an unpublished article
  \cite{Abrial-Laffitte}.
*}

constdefs
  chain     ::  "'a set set => 'a set set set"
  "chain S  == {F. F \<subseteq> S & (\<forall>x \<in> F. \<forall>y \<in> F. x \<subseteq> y | y \<subseteq> x)}"

  super     ::  "['a set set,'a set set] => 'a set set set"
  "super S c == {d. d \<in> chain S & c \<subset> d}"

  maxchain  ::  "'a set set => 'a set set set"
  "maxchain S == {c. c \<in> chain S & super S c = {}}"

  succ      ::  "['a set set,'a set set] => 'a set set"
  "succ S c ==
    if c \<notin> chain S | c \<in> maxchain S
    then c else SOME c'. c' \<in> super S c"

consts
  TFin :: "'a set set => 'a set set set"

inductive "TFin S"
  intros
    succI:        "x \<in> TFin S ==> succ S x \<in> TFin S"
    Pow_UnionI:   "Y \<in> Pow(TFin S) ==> Union(Y) \<in> TFin S"
  monos          Pow_mono


subsection{*Mathematical Preamble*}

lemma Union_lemma0: "(\<forall>x \<in> C. x \<subseteq> A | B \<subseteq> x) ==> Union(C)<=A | B \<subseteq> Union(C)"
by blast


text{*This is theorem @{text increasingD2} of ZF/Zorn.thy*}
lemma Abrial_axiom1: "x \<subseteq> succ S x"
apply (unfold succ_def)
apply (rule split_if [THEN iffD2])
apply (auto simp add: super_def maxchain_def psubset_def)
apply (rule swap, assumption)
apply (rule someI2, blast+)
done

lemmas TFin_UnionI = TFin.Pow_UnionI [OF PowI]

lemma TFin_induct:
          "[| n \<in> TFin S;
             !!x. [| x \<in> TFin S; P(x) |] ==> P(succ S x);
             !!Y. [| Y \<subseteq> TFin S; Ball Y P |] ==> P(Union Y) |]
          ==> P(n)"
apply (erule TFin.induct, blast+)
done

lemma succ_trans: "x \<subseteq> y ==> x \<subseteq> succ S y"
apply (erule subset_trans)
apply (rule Abrial_axiom1)
done

text{*Lemma 1 of section 3.1*}
lemma TFin_linear_lemma1:
     "[| n \<in> TFin S;  m \<in> TFin S;
         \<forall>x \<in> TFin S. x \<subseteq> m --> x = m | succ S x \<subseteq> m
      |] ==> n \<subseteq> m | succ S m \<subseteq> n"
apply (erule TFin_induct)
apply (erule_tac [2] Union_lemma0) (*or just blast*)
apply (blast del: subsetI intro: succ_trans)
done

text{* Lemma 2 of section 3.2 *}
lemma TFin_linear_lemma2:
     "m \<in> TFin S ==> \<forall>n \<in> TFin S. n \<subseteq> m --> n=m | succ S n \<subseteq> m"
apply (erule TFin_induct)
apply (rule impI [THEN ballI])
txt{*case split using @{text TFin_linear_lemma1}*}
apply (rule_tac n1 = n and m1 = x in TFin_linear_lemma1 [THEN disjE],
       assumption+)
apply (drule_tac x = n in bspec, assumption)
apply (blast del: subsetI intro: succ_trans, blast)
txt{*second induction step*}
apply (rule impI [THEN ballI])
apply (rule Union_lemma0 [THEN disjE])
apply (rule_tac [3] disjI2)
 prefer 2 apply blast
apply (rule ballI)
apply (rule_tac n1 = n and m1 = x in TFin_linear_lemma1 [THEN disjE],
       assumption+, auto)
apply (blast intro!: Abrial_axiom1 [THEN subsetD])
done

text{*Re-ordering the premises of Lemma 2*}
lemma TFin_subsetD:
     "[| n \<subseteq> m;  m \<in> TFin S;  n \<in> TFin S |] ==> n=m | succ S n \<subseteq> m"
apply (rule TFin_linear_lemma2 [rule_format])
apply (assumption+)
done

text{*Consequences from section 3.3 -- Property 3.2, the ordering is total*}
lemma TFin_subset_linear: "[| m \<in> TFin S;  n \<in> TFin S|] ==> n \<subseteq> m | m \<subseteq> n"
apply (rule disjE)
apply (rule TFin_linear_lemma1 [OF _ _TFin_linear_lemma2])
apply (assumption+, erule disjI2)
apply (blast del: subsetI
             intro: subsetI Abrial_axiom1 [THEN subset_trans])
done

text{*Lemma 3 of section 3.3*}
lemma eq_succ_upper: "[| n \<in> TFin S;  m \<in> TFin S;  m = succ S m |] ==> n \<subseteq> m"
apply (erule TFin_induct)
apply (drule TFin_subsetD)
apply (assumption+, force, blast)
done

text{*Property 3.3 of section 3.3*}
lemma equal_succ_Union: "m \<in> TFin S ==> (m = succ S m) = (m = Union(TFin S))"
apply (rule iffI)
apply (rule Union_upper [THEN equalityI])
apply (rule_tac [2] eq_succ_upper [THEN Union_least])
apply (assumption+)
apply (erule ssubst)
apply (rule Abrial_axiom1 [THEN equalityI])
apply (blast del: subsetI
             intro: subsetI TFin_UnionI TFin.succI)
done

subsection{*Hausdorff's Theorem: Every Set Contains a Maximal Chain.*}

text{*NB: We assume the partial ordering is @{text "\<subseteq>"},
 the subset relation!*}

lemma empty_set_mem_chain: "({} :: 'a set set) \<in> chain S"
by (unfold chain_def, auto)

lemma super_subset_chain: "super S c \<subseteq> chain S"
by (unfold super_def, fast)

lemma maxchain_subset_chain: "maxchain S \<subseteq> chain S"
by (unfold maxchain_def, fast)

lemma mem_super_Ex: "c \<in> chain S - maxchain S ==> ? d. d \<in> super S c"
by (unfold super_def maxchain_def, auto)

lemma select_super: "c \<in> chain S - maxchain S ==>
                          (@c'. c': super S c): super S c"
apply (erule mem_super_Ex [THEN exE])
apply (rule someI2, auto)
done

lemma select_not_equals: "c \<in> chain S - maxchain S ==>
                          (@c'. c': super S c) \<noteq> c"
apply (rule notI)
apply (drule select_super)
apply (simp add: super_def psubset_def)
done

lemma succI3: "c \<in> chain S - maxchain S ==> succ S c = (@c'. c': super S c)"
apply (unfold succ_def)
apply (fast intro!: if_not_P)
done

lemma succ_not_equals: "c \<in> chain S - maxchain S ==> succ S c \<noteq> c"
apply (frule succI3)
apply (simp (no_asm_simp))
apply (rule select_not_equals, assumption)
done

lemma TFin_chain_lemma4: "c \<in> TFin S ==> (c :: 'a set set): chain S"
apply (erule TFin_induct)
apply (simp add: succ_def select_super [THEN super_subset_chain[THEN subsetD]])
apply (unfold chain_def)
apply (rule CollectI, safe)
apply (drule bspec, assumption)
apply (rule_tac [2] m1 = Xa and n1 = X in TFin_subset_linear [THEN disjE],
       blast+)
done

theorem Hausdorff: "\<exists>c. (c :: 'a set set): maxchain S"
apply (rule_tac x = "Union (TFin S) " in exI)
apply (rule classical)
apply (subgoal_tac "succ S (Union (TFin S)) = Union (TFin S) ")
 prefer 2
 apply (blast intro!: TFin_UnionI equal_succ_Union [THEN iffD2, symmetric])
apply (cut_tac subset_refl [THEN TFin_UnionI, THEN TFin_chain_lemma4])
apply (drule DiffI [THEN succ_not_equals], blast+)
done


subsection{*Zorn's Lemma: If All Chains Have Upper Bounds Then
                               There Is  a Maximal Element*}

lemma chain_extend:
    "[| c \<in> chain S; z \<in> S;
        \<forall>x \<in> c. x<=(z:: 'a set) |] ==> {z} Un c \<in> chain S"
by (unfold chain_def, blast)

lemma chain_Union_upper: "[| c \<in> chain S; x \<in> c |] ==> x \<subseteq> Union(c)"
by (unfold chain_def, auto)

lemma chain_ball_Union_upper: "c \<in> chain S ==> \<forall>x \<in> c. x \<subseteq> Union(c)"
by (unfold chain_def, auto)

lemma maxchain_Zorn:
     "[| c \<in> maxchain S; u \<in> S; Union(c) \<subseteq> u |] ==> Union(c) = u"
apply (rule ccontr)
apply (simp add: maxchain_def)
apply (erule conjE)
apply (subgoal_tac " ({u} Un c) \<in> super S c")
apply simp
apply (unfold super_def psubset_def)
apply (blast intro: chain_extend dest: chain_Union_upper)
done

theorem Zorn_Lemma:
     "\<forall>c \<in> chain S. Union(c): S ==> \<exists>y \<in> S. \<forall>z \<in> S. y \<subseteq> z --> y = z"
apply (cut_tac Hausdorff maxchain_subset_chain)
apply (erule exE)
apply (drule subsetD, assumption)
apply (drule bspec, assumption)
apply (rule_tac x = "Union (c) " in bexI)
apply (rule ballI, rule impI)
apply (blast dest!: maxchain_Zorn, assumption)
done

subsection{*Alternative version of Zorn's Lemma*}

lemma Zorn_Lemma2:
     "\<forall>c \<in> chain S. \<exists>y \<in> S. \<forall>x \<in> c. x \<subseteq> y
      ==> \<exists>y \<in> S. \<forall>x \<in> S. (y :: 'a set) \<subseteq> x --> y = x"
apply (cut_tac Hausdorff maxchain_subset_chain)
apply (erule exE)
apply (drule subsetD, assumption)
apply (drule bspec, assumption, erule bexE)
apply (rule_tac x = y in bexI)
 prefer 2 apply assumption
apply clarify
apply (rule ccontr)
apply (frule_tac z = x in chain_extend)
apply (assumption, blast)
apply (unfold maxchain_def super_def psubset_def)
apply (blast elim!: equalityCE)
done

text{*Various other lemmas*}

lemma chainD: "[| c \<in> chain S; x \<in> c; y \<in> c |] ==> x \<subseteq> y | y \<subseteq> x"
by (unfold chain_def, blast)

lemma chainD2: "!!(c :: 'a set set). c \<in> chain S ==> c \<subseteq> S"
by (unfold chain_def, blast)

end
