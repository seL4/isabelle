(*  Title:      HOL/Meson.thy
    Author:     Lawrence C Paulson, Tobias Nipkow
    Copyright   2001  University of Cambridge
*)

header {* MESON Proof Procedure (Model Elimination) *}

theory Meson
imports Nat
uses ("Tools/Meson/meson.ML")
     ("Tools/Meson/meson_clausify.ML")
begin

section {* Negation Normal Form *}

text {* de Morgan laws *}

lemma meson_not_conjD: "~(P&Q) ==> ~P | ~Q"
  and meson_not_disjD: "~(P|Q) ==> ~P & ~Q"
  and meson_not_notD: "~~P ==> P"
  and meson_not_allD: "!!P. ~(\<forall>x. P(x)) ==> \<exists>x. ~P(x)"
  and meson_not_exD: "!!P. ~(\<exists>x. P(x)) ==> \<forall>x. ~P(x)"
  by fast+

text {* Removal of @{text "-->"} and @{text "<->"} (positive and
negative occurrences) *}

lemma meson_imp_to_disjD: "P-->Q ==> ~P | Q"
  and meson_not_impD: "~(P-->Q) ==> P & ~Q"
  and meson_iff_to_disjD: "P=Q ==> (~P | Q) & (~Q | P)"
  and meson_not_iffD: "~(P=Q) ==> (P | Q) & (~P | ~Q)"
    -- {* Much more efficient than @{prop "(P & ~Q) | (Q & ~P)"} for computing CNF *}
  and meson_not_refl_disj_D: "x ~= x | P ==> P"
  by fast+


section {* Pulling out the existential quantifiers *}

text {* Conjunction *}

lemma meson_conj_exD1: "!!P Q. (\<exists>x. P(x)) & Q ==> \<exists>x. P(x) & Q"
  and meson_conj_exD2: "!!P Q. P & (\<exists>x. Q(x)) ==> \<exists>x. P & Q(x)"
  by fast+


text {* Disjunction *}

lemma meson_disj_exD: "!!P Q. (\<exists>x. P(x)) | (\<exists>x. Q(x)) ==> \<exists>x. P(x) | Q(x)"
  -- {* DO NOT USE with forall-Skolemization: makes fewer schematic variables!! *}
  -- {* With ex-Skolemization, makes fewer Skolem constants *}
  and meson_disj_exD1: "!!P Q. (\<exists>x. P(x)) | Q ==> \<exists>x. P(x) | Q"
  and meson_disj_exD2: "!!P Q. P | (\<exists>x. Q(x)) ==> \<exists>x. P | Q(x)"
  by fast+

lemma meson_disj_assoc: "(P|Q)|R ==> P|(Q|R)"
  and meson_disj_comm: "P|Q ==> Q|P"
  and meson_disj_FalseD1: "False|P ==> P"
  and meson_disj_FalseD2: "P|False ==> P"
  by fast+


text{* Generation of contrapositives *}

text{*Inserts negated disjunct after removing the negation; P is a literal.
  Model elimination requires assuming the negation of every attempted subgoal,
  hence the negated disjuncts.*}
lemma make_neg_rule: "~P|Q ==> ((~P==>P) ==> Q)"
by blast

text{*Version for Plaisted's "Postive refinement" of the Meson procedure*}
lemma make_refined_neg_rule: "~P|Q ==> (P ==> Q)"
by blast

text{*@{term P} should be a literal*}
lemma make_pos_rule: "P|Q ==> ((P==>~P) ==> Q)"
by blast

text{*Versions of @{text make_neg_rule} and @{text make_pos_rule} that don't
insert new assumptions, for ordinary resolution.*}

lemmas make_neg_rule' = make_refined_neg_rule

lemma make_pos_rule': "[|P|Q; ~P|] ==> Q"
by blast

text{* Generation of a goal clause -- put away the final literal *}

lemma make_neg_goal: "~P ==> ((~P==>P) ==> False)"
by blast

lemma make_pos_goal: "P ==> ((P==>~P) ==> False)"
by blast


section {* Lemmas for Forward Proof *}

text{*There is a similarity to congruence rules*}

(*NOTE: could handle conjunctions (faster?) by
    nf(th RS conjunct2) RS (nf(th RS conjunct1) RS conjI) *)
lemma conj_forward: "[| P'&Q';  P' ==> P;  Q' ==> Q |] ==> P&Q"
by blast

lemma disj_forward: "[| P'|Q';  P' ==> P;  Q' ==> Q |] ==> P|Q"
by blast

(*Version of @{text disj_forward} for removal of duplicate literals*)
lemma disj_forward2:
    "[| P'|Q';  P' ==> P;  [| Q'; P==>False |] ==> Q |] ==> P|Q"
apply blast 
done

lemma all_forward: "[| \<forall>x. P'(x);  !!x. P'(x) ==> P(x) |] ==> \<forall>x. P(x)"
by blast

lemma ex_forward: "[| \<exists>x. P'(x);  !!x. P'(x) ==> P(x) |] ==> \<exists>x. P(x)"
by blast


section {* Clausification helper *}

lemma TruepropI: "P \<equiv> Q \<Longrightarrow> Trueprop P \<equiv> Trueprop Q"
by simp


text{* Combinator translation helpers *}

definition COMBI :: "'a \<Rightarrow> 'a" where
[no_atp]: "COMBI P = P"

definition COMBK :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
[no_atp]: "COMBK P Q = P"

definition COMBB :: "('b => 'c) \<Rightarrow> ('a => 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where [no_atp]:
"COMBB P Q R = P (Q R)"

definition COMBC :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
[no_atp]: "COMBC P Q R = P R Q"

definition COMBS :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where
[no_atp]: "COMBS P Q R = P R (Q R)"

lemma abs_S [no_atp]: "\<lambda>x. (f x) (g x) \<equiv> COMBS f g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBS_def) 
done

lemma abs_I [no_atp]: "\<lambda>x. x \<equiv> COMBI"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBI_def) 
done

lemma abs_K [no_atp]: "\<lambda>x. y \<equiv> COMBK y"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBK_def) 
done

lemma abs_B [no_atp]: "\<lambda>x. a (g x) \<equiv> COMBB a g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBB_def) 
done

lemma abs_C [no_atp]: "\<lambda>x. (f x) b \<equiv> COMBC f b"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBC_def) 
done


section {* Skolemization helpers *}

definition skolem :: "'a \<Rightarrow> 'a" where
[no_atp]: "skolem = (\<lambda>x. x)"

lemma skolem_COMBK_iff: "P \<longleftrightarrow> skolem (COMBK P (i\<Colon>nat))"
unfolding skolem_def COMBK_def by (rule refl)

lemmas skolem_COMBK_I = iffD1 [OF skolem_COMBK_iff]
lemmas skolem_COMBK_D = iffD2 [OF skolem_COMBK_iff]


section {* Meson package *}

ML {*
structure Meson_Choices = Named_Thms
(
  val name = "meson_choice"
  val description = "choice axioms for MESON's (and Metis's) skolemizer"
)
*}

use "Tools/Meson/meson.ML"
use "Tools/Meson/meson_clausify.ML"

setup {*
  Meson_Choices.setup
  #> Meson.setup
  #> Meson_Clausify.setup
*}

end
