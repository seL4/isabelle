(*  Title:      HOL/Hilbert_Choice.thy
    ID: $Id$
    Author:     Lawrence C Paulson
    Copyright   2001  University of Cambridge
*)

header {* Hilbert's Epsilon-Operator and the Axiom of Choice *}

theory Hilbert_Choice = NatArith
files ("Tools/meson.ML") ("Tools/specification_package.ML"):


subsection {* Hilbert's epsilon *}

consts
  Eps           :: "('a => bool) => 'a"

syntax (epsilon)
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3\<some>_./ _)" [0, 10] 10)
syntax (HOL)
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3@ _./ _)" [0, 10] 10)
syntax
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3SOME _./ _)" [0, 10] 10)
translations
  "SOME x. P" == "Eps (%x. P)"

print_translation {*
(* to avoid eta-contraction of body *)
[("Eps", fn [Abs abs] =>
     let val (x,t) = atomic_abs_tr' abs
     in Syntax.const "_Eps" $ x $ t end)]
*}

axioms
  someI: "P (x::'a) ==> P (SOME x. P x)"


constdefs
  inv :: "('a => 'b) => ('b => 'a)"
  "inv(f :: 'a => 'b) == %y. SOME x. f x = y"

  Inv :: "'a set => ('a => 'b) => ('b => 'a)"
  "Inv A f == %x. SOME y. y \<in> A & f y = x"


subsection {*Hilbert's Epsilon-operator*}

text{*Easier to apply than @{text someI} if the witness comes from an
existential formula*}
lemma someI_ex [elim?]: "\<exists>x. P x ==> P (SOME x. P x)"
apply (erule exE)
apply (erule someI)
done

text{*Easier to apply than @{text someI} because the conclusion has only one
occurrence of @{term P}.*}
lemma someI2: "[| P a;  !!x. P x ==> Q x |] ==> Q (SOME x. P x)"
by (blast intro: someI)

text{*Easier to apply than @{text someI2} if the witness comes from an
existential formula*}
lemma someI2_ex: "[| \<exists>a. P a; !!x. P x ==> Q x |] ==> Q (SOME x. P x)"
by (blast intro: someI2)

lemma some_equality [intro]:
     "[| P a;  !!x. P x ==> x=a |] ==> (SOME x. P x) = a"
by (blast intro: someI2)

lemma some1_equality: "[| EX!x. P x; P a |] ==> (SOME x. P x) = a"
by (blast intro: some_equality)

lemma some_eq_ex: "P (SOME x. P x) =  (\<exists>x. P x)"
by (blast intro: someI)

lemma some_eq_trivial [simp]: "(SOME y. y=x) = x"
apply (rule some_equality)
apply (rule refl, assumption)
done

lemma some_sym_eq_trivial [simp]: "(SOME y. x=y) = x"
apply (rule some_equality)
apply (rule refl)
apply (erule sym)
done


subsection{*Axiom of Choice, Proved Using the Description Operator*}

text{*Used in @{text "Tools/meson.ML"}*}
lemma choice: "\<forall>x. \<exists>y. Q x y ==> \<exists>f. \<forall>x. Q x (f x)"
by (fast elim: someI)

lemma bchoice: "\<forall>x\<in>S. \<exists>y. Q x y ==> \<exists>f. \<forall>x\<in>S. Q x (f x)"
by (fast elim: someI)


subsection {*Function Inverse*}

lemma inv_id [simp]: "inv id = id"
by (simp add: inv_def id_def)

text{*A one-to-one function has an inverse.*}
lemma inv_f_f [simp]: "inj f ==> inv f (f x) = x"
by (simp add: inv_def inj_eq)

lemma inv_f_eq: "[| inj f;  f x = y |] ==> inv f y = x"
apply (erule subst)
apply (erule inv_f_f)
done

lemma inj_imp_inv_eq: "[| inj f; \<forall>x. f(g x) = x |] ==> inv f = g"
by (blast intro: ext inv_f_eq)

text{*But is it useful?*}
lemma inj_transfer:
  assumes injf: "inj f" and minor: "!!y. y \<in> range(f) ==> P(inv f y)"
  shows "P x"
proof -
  have "f x \<in> range f" by auto
  hence "P(inv f (f x))" by (rule minor)
  thus "P x" by (simp add: inv_f_f [OF injf])
qed


lemma inj_iff: "(inj f) = (inv f o f = id)"
apply (simp add: o_def expand_fun_eq)
apply (blast intro: inj_on_inverseI inv_f_f)
done

lemma inj_imp_surj_inv: "inj f ==> surj (inv f)"
by (blast intro: surjI inv_f_f)

lemma f_inv_f: "y \<in> range(f) ==> f(inv f y) = y"
apply (simp add: inv_def)
apply (fast intro: someI)
done

lemma surj_f_inv_f: "surj f ==> f(inv f y) = y"
by (simp add: f_inv_f surj_range)

lemma inv_injective:
  assumes eq: "inv f x = inv f y"
      and x: "x: range f"
      and y: "y: range f"
  shows "x=y"
proof -
  have "f (inv f x) = f (inv f y)" using eq by simp
  thus ?thesis by (simp add: f_inv_f x y) 
qed

lemma inj_on_inv: "A <= range(f) ==> inj_on (inv f) A"
by (fast intro: inj_onI elim: inv_injective injD)

lemma surj_imp_inj_inv: "surj f ==> inj (inv f)"
by (simp add: inj_on_inv surj_range)

lemma surj_iff: "(surj f) = (f o inv f = id)"
apply (simp add: o_def expand_fun_eq)
apply (blast intro: surjI surj_f_inv_f)
done

lemma surj_imp_inv_eq: "[| surj f; \<forall>x. g(f x) = x |] ==> inv f = g"
apply (rule ext)
apply (drule_tac x = "inv f x" in spec)
apply (simp add: surj_f_inv_f)
done

lemma bij_imp_bij_inv: "bij f ==> bij (inv f)"
by (simp add: bij_def inj_imp_surj_inv surj_imp_inj_inv)

lemma inv_equality: "[| !!x. g (f x) = x;  !!y. f (g y) = y |] ==> inv f = g"
apply (rule ext)
apply (auto simp add: inv_def)
done

lemma inv_inv_eq: "bij f ==> inv (inv f) = f"
apply (rule inv_equality)
apply (auto simp add: bij_def surj_f_inv_f)
done

(** bij(inv f) implies little about f.  Consider f::bool=>bool such that
    f(True)=f(False)=True.  Then it's consistent with axiom someI that
    inv f could be any function at all, including the identity function.
    If inv f=id then inv f is a bijection, but inj f, surj(f) and
    inv(inv f)=f all fail.
**)

lemma o_inv_distrib: "[| bij f; bij g |] ==> inv (f o g) = inv g o inv f"
apply (rule inv_equality)
apply (auto simp add: bij_def surj_f_inv_f)
done


lemma image_surj_f_inv_f: "surj f ==> f ` (inv f ` A) = A"
by (simp add: image_eq_UN surj_f_inv_f)

lemma image_inv_f_f: "inj f ==> (inv f) ` (f ` A) = A"
by (simp add: image_eq_UN)

lemma inv_image_comp: "inj f ==> inv f ` (f`X) = X"
by (auto simp add: image_def)

lemma bij_image_Collect_eq: "bij f ==> f ` Collect P = {y. P (inv f y)}"
apply auto
apply (force simp add: bij_is_inj)
apply (blast intro: bij_is_surj [THEN surj_f_inv_f, symmetric])
done

lemma bij_vimage_eq_inv_image: "bij f ==> f -` A = inv f ` A" 
apply (auto simp add: bij_is_surj [THEN surj_f_inv_f])
apply (blast intro: bij_is_inj [THEN inv_f_f, symmetric])
done


subsection {*Inverse of a PI-function (restricted domain)*}

lemma Inv_f_f: "[| inj_on f A;  x \<in> A |] ==> Inv A f (f x) = x"
apply (simp add: Inv_def inj_on_def)
apply (blast intro: someI2)
done

lemma f_Inv_f: "y \<in> f`A  ==> f (Inv A f y) = y"
apply (simp add: Inv_def)
apply (fast intro: someI2)
done

lemma Inv_injective:
  assumes eq: "Inv A f x = Inv A f y"
      and x: "x: f`A"
      and y: "y: f`A"
  shows "x=y"
proof -
  have "f (Inv A f x) = f (Inv A f y)" using eq by simp
  thus ?thesis by (simp add: f_Inv_f x y) 
qed

lemma inj_on_Inv: "B <= f`A ==> inj_on (Inv A f) B"
apply (rule inj_onI)
apply (blast intro: inj_onI dest: Inv_injective injD)
done

lemma Inv_mem: "[| f ` A = B;  x \<in> B |] ==> Inv A f x \<in> A"
apply (simp add: Inv_def)
apply (fast intro: someI2)
done

lemma Inv_f_eq: "[| inj_on f A; f x = y; x \<in> A |] ==> Inv A f y = x"
  apply (erule subst)
  apply (erule Inv_f_f, assumption)
  done

lemma Inv_comp:
  "[| inj_on f (g ` A); inj_on g A; x \<in> f ` g ` A |] ==>
  Inv A (f o g) x = (Inv A g o Inv (g ` A) f) x"
  apply simp
  apply (rule Inv_f_eq)
    apply (fast intro: comp_inj_on)
   apply (simp add: f_Inv_f Inv_mem)
  apply (simp add: Inv_mem)
  done


subsection {*Other Consequences of Hilbert's Epsilon*}

text {*Hilbert's Epsilon and the @{term split} Operator*}

text{*Looping simprule*}
lemma split_paired_Eps: "(SOME x. P x) = (SOME (a,b). P(a,b))"
by (simp add: split_Pair_apply)

lemma Eps_split: "Eps (split P) = (SOME xy. P (fst xy) (snd xy))"
by (simp add: split_def)

lemma Eps_split_eq [simp]: "(@(x',y'). x = x' & y = y') = (x,y)"
by blast


text{*A relation is wellfounded iff it has no infinite descending chain*}
lemma wf_iff_no_infinite_down_chain:
  "wf r = (~(\<exists>f. \<forall>i. (f(Suc i),f i) \<in> r))"
apply (simp only: wf_eq_minimal)
apply (rule iffI)
 apply (rule notI)
 apply (erule exE)
 apply (erule_tac x = "{w. \<exists>i. w=f i}" in allE, blast)
apply (erule contrapos_np, simp, clarify)
apply (subgoal_tac "\<forall>n. nat_rec x (%i y. @z. z:Q & (z,y) :r) n \<in> Q")
 apply (rule_tac x = "nat_rec x (%i y. @z. z:Q & (z,y) :r)" in exI)
 apply (rule allI, simp)
 apply (rule someI2_ex, blast, blast)
apply (rule allI)
apply (induct_tac "n", simp_all)
apply (rule someI2_ex, blast+)
done

text{*A dynamically-scoped fact for TFL *}
lemma tfl_some: "\<forall>P x. P x --> P (Eps P)"
  by (blast intro: someI)


subsection {* Least value operator *}

constdefs
  LeastM :: "['a => 'b::ord, 'a => bool] => 'a"
  "LeastM m P == SOME x. P x & (\<forall>y. P y --> m x <= m y)"

syntax
  "_LeastM" :: "[pttrn, 'a => 'b::ord, bool] => 'a"    ("LEAST _ WRT _. _" [0, 4, 10] 10)
translations
  "LEAST x WRT m. P" == "LeastM m (%x. P)"

lemma LeastMI2:
  "P x ==> (!!y. P y ==> m x <= m y)
    ==> (!!x. P x ==> \<forall>y. P y --> m x \<le> m y ==> Q x)
    ==> Q (LeastM m P)"
  apply (simp add: LeastM_def)
  apply (rule someI2_ex, blast, blast)
  done

lemma LeastM_equality:
  "P k ==> (!!x. P x ==> m k <= m x)
    ==> m (LEAST x WRT m. P x) = (m k::'a::order)"
  apply (rule LeastMI2, assumption, blast)
  apply (blast intro!: order_antisym)
  done

lemma wf_linord_ex_has_least:
  "wf r ==> \<forall>x y. ((x,y):r^+) = ((y,x)~:r^*) ==> P k
    ==> \<exists>x. P x & (!y. P y --> (m x,m y):r^*)"
  apply (drule wf_trancl [THEN wf_eq_minimal [THEN iffD1]])
  apply (drule_tac x = "m`Collect P" in spec, force)
  done

lemma ex_has_least_nat:
    "P k ==> \<exists>x. P x & (\<forall>y. P y --> m x <= (m y::nat))"
  apply (simp only: pred_nat_trancl_eq_le [symmetric])
  apply (rule wf_pred_nat [THEN wf_linord_ex_has_least])
   apply (simp add: less_eq not_le_iff_less pred_nat_trancl_eq_le, assumption)
  done

lemma LeastM_nat_lemma:
    "P k ==> P (LeastM m P) & (\<forall>y. P y --> m (LeastM m P) <= (m y::nat))"
  apply (simp add: LeastM_def)
  apply (rule someI_ex)
  apply (erule ex_has_least_nat)
  done

lemmas LeastM_natI = LeastM_nat_lemma [THEN conjunct1, standard]

lemma LeastM_nat_le: "P x ==> m (LeastM m P) <= (m x::nat)"
by (rule LeastM_nat_lemma [THEN conjunct2, THEN spec, THEN mp], assumption, assumption)


subsection {* Greatest value operator *}

constdefs
  GreatestM :: "['a => 'b::ord, 'a => bool] => 'a"
  "GreatestM m P == SOME x. P x & (\<forall>y. P y --> m y <= m x)"

  Greatest :: "('a::ord => bool) => 'a"    (binder "GREATEST " 10)
  "Greatest == GreatestM (%x. x)"

syntax
  "_GreatestM" :: "[pttrn, 'a=>'b::ord, bool] => 'a"
      ("GREATEST _ WRT _. _" [0, 4, 10] 10)

translations
  "GREATEST x WRT m. P" == "GreatestM m (%x. P)"

lemma GreatestMI2:
  "P x ==> (!!y. P y ==> m y <= m x)
    ==> (!!x. P x ==> \<forall>y. P y --> m y \<le> m x ==> Q x)
    ==> Q (GreatestM m P)"
  apply (simp add: GreatestM_def)
  apply (rule someI2_ex, blast, blast)
  done

lemma GreatestM_equality:
 "P k ==> (!!x. P x ==> m x <= m k)
    ==> m (GREATEST x WRT m. P x) = (m k::'a::order)"
  apply (rule_tac m = m in GreatestMI2, assumption, blast)
  apply (blast intro!: order_antisym)
  done

lemma Greatest_equality:
  "P (k::'a::order) ==> (!!x. P x ==> x <= k) ==> (GREATEST x. P x) = k"
  apply (simp add: Greatest_def)
  apply (erule GreatestM_equality, blast)
  done

lemma ex_has_greatest_nat_lemma:
  "P k ==> \<forall>x. P x --> (\<exists>y. P y & ~ ((m y::nat) <= m x))
    ==> \<exists>y. P y & ~ (m y < m k + n)"
  apply (induct_tac n, force)
  apply (force simp add: le_Suc_eq)
  done

lemma ex_has_greatest_nat:
  "P k ==> \<forall>y. P y --> m y < b
    ==> \<exists>x. P x & (\<forall>y. P y --> (m y::nat) <= m x)"
  apply (rule ccontr)
  apply (cut_tac P = P and n = "b - m k" in ex_has_greatest_nat_lemma)
    apply (subgoal_tac [3] "m k <= b", auto)
  done

lemma GreatestM_nat_lemma:
  "P k ==> \<forall>y. P y --> m y < b
    ==> P (GreatestM m P) & (\<forall>y. P y --> (m y::nat) <= m (GreatestM m P))"
  apply (simp add: GreatestM_def)
  apply (rule someI_ex)
  apply (erule ex_has_greatest_nat, assumption)
  done

lemmas GreatestM_natI = GreatestM_nat_lemma [THEN conjunct1, standard]

lemma GreatestM_nat_le:
  "P x ==> \<forall>y. P y --> m y < b
    ==> (m x::nat) <= m (GreatestM m P)"
  apply (blast dest: GreatestM_nat_lemma [THEN conjunct2, THEN spec])
  done


text {* \medskip Specialization to @{text GREATEST}. *}

lemma GreatestI: "P (k::nat) ==> \<forall>y. P y --> y < b ==> P (GREATEST x. P x)"
  apply (simp add: Greatest_def)
  apply (rule GreatestM_natI, auto)
  done

lemma Greatest_le:
    "P x ==> \<forall>y. P y --> y < b ==> (x::nat) <= (GREATEST x. P x)"
  apply (simp add: Greatest_def)
  apply (rule GreatestM_nat_le, auto)
  done


subsection {* The Meson proof procedure *}

subsubsection {* Negation Normal Form *}

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
  by fast+


subsubsection {* Pulling out the existential quantifiers *}

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


subsubsection {* Generating clauses for the Meson Proof Procedure *}

text {* Disjunctions *}

lemma meson_disj_assoc: "(P|Q)|R ==> P|(Q|R)"
  and meson_disj_comm: "P|Q ==> Q|P"
  and meson_disj_FalseD1: "False|P ==> P"
  and meson_disj_FalseD2: "P|False ==> P"
  by fast+


subsection{*Lemmas for Meson, the Model Elimination Procedure*}


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


subsubsection{* Lemmas for Forward Proof*}

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

ML
{*
val inv_def = thm "inv_def";
val Inv_def = thm "Inv_def";

val someI = thm "someI";
val someI_ex = thm "someI_ex";
val someI2 = thm "someI2";
val someI2_ex = thm "someI2_ex";
val some_equality = thm "some_equality";
val some1_equality = thm "some1_equality";
val some_eq_ex = thm "some_eq_ex";
val some_eq_trivial = thm "some_eq_trivial";
val some_sym_eq_trivial = thm "some_sym_eq_trivial";
val choice = thm "choice";
val bchoice = thm "bchoice";
val inv_id = thm "inv_id";
val inv_f_f = thm "inv_f_f";
val inv_f_eq = thm "inv_f_eq";
val inj_imp_inv_eq = thm "inj_imp_inv_eq";
val inj_transfer = thm "inj_transfer";
val inj_iff = thm "inj_iff";
val inj_imp_surj_inv = thm "inj_imp_surj_inv";
val f_inv_f = thm "f_inv_f";
val surj_f_inv_f = thm "surj_f_inv_f";
val inv_injective = thm "inv_injective";
val inj_on_inv = thm "inj_on_inv";
val surj_imp_inj_inv = thm "surj_imp_inj_inv";
val surj_iff = thm "surj_iff";
val surj_imp_inv_eq = thm "surj_imp_inv_eq";
val bij_imp_bij_inv = thm "bij_imp_bij_inv";
val inv_equality = thm "inv_equality";
val inv_inv_eq = thm "inv_inv_eq";
val o_inv_distrib = thm "o_inv_distrib";
val image_surj_f_inv_f = thm "image_surj_f_inv_f";
val image_inv_f_f = thm "image_inv_f_f";
val inv_image_comp = thm "inv_image_comp";
val bij_image_Collect_eq = thm "bij_image_Collect_eq";
val bij_vimage_eq_inv_image = thm "bij_vimage_eq_inv_image";
val Inv_f_f = thm "Inv_f_f";
val f_Inv_f = thm "f_Inv_f";
val Inv_injective = thm "Inv_injective";
val inj_on_Inv = thm "inj_on_Inv";
val split_paired_Eps = thm "split_paired_Eps";
val Eps_split = thm "Eps_split";
val Eps_split_eq = thm "Eps_split_eq";
val wf_iff_no_infinite_down_chain = thm "wf_iff_no_infinite_down_chain";
val Inv_mem = thm "Inv_mem";
val Inv_f_eq = thm "Inv_f_eq";
val Inv_comp = thm "Inv_comp";
val tfl_some = thm "tfl_some";
val make_neg_rule = thm "make_neg_rule";
val make_refined_neg_rule = thm "make_refined_neg_rule";
val make_pos_rule = thm "make_pos_rule";
val make_neg_rule' = thm "make_neg_rule'";
val make_pos_rule' = thm "make_pos_rule'";
val make_neg_goal = thm "make_neg_goal";
val make_pos_goal = thm "make_pos_goal";
val conj_forward = thm "conj_forward";
val disj_forward = thm "disj_forward";
val disj_forward2 = thm "disj_forward2";
val all_forward = thm "all_forward";
val ex_forward = thm "ex_forward";
*}


use "Tools/meson.ML"
setup meson_setup

use "Tools/specification_package.ML"

end
