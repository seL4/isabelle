(*  Title:      HOL/Codatatype/More_BNFs.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Andreas Lochbihler, Karlsruhe Institute of Technology
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Registration of various types as bounded natural functors.
*)

header {* Registration of Various Types as Bounded Natural Functors *}

theory More_BNFs
imports
  BNF_LFP
  BNF_GFP
  "~~/src/HOL/Quotient_Examples/FSet"
  "~~/src/HOL/Library/Multiset"
  Countable_Set
begin

lemma option_rec_conv_option_case: "option_rec = option_case"
by (simp add: fun_eq_iff split: option.split)

bnf_def option = Option.map [Option.set] "\<lambda>_::'a option. natLeq" ["None"]
proof -
  show "Option.map id = id" by (simp add: fun_eq_iff Option.map_def split: option.split)
next
  fix f g
  show "Option.map (g \<circ> f) = Option.map g \<circ> Option.map f"
    by (auto simp add: fun_eq_iff Option.map_def split: option.split)
next
  fix f g x
  assume "\<And>z. z \<in> Option.set x \<Longrightarrow> f z = g z"
  thus "Option.map f x = Option.map g x"
    by (simp cong: Option.map_cong)
next
  fix f
  show "Option.set \<circ> Option.map f = op ` f \<circ> Option.set"
    by fastforce
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix x
  show "|Option.set x| \<le>o natLeq"
    by (cases x) (simp_all add: ordLess_imp_ordLeq finite_iff_ordLess_natLeq[symmetric])
next
  fix A
  have unfold: "{x. Option.set x \<subseteq> A} = Some ` A \<union> {None}"
    by (auto simp add: option_rec_conv_option_case Option.set_def split: option.split_asm)
  show "|{x. Option.set x \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq"
    apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst[OF unfold])
    apply (rule ordLeq_transitive)
    apply (rule Un_csum)
    apply (rule ordLeq_transitive)
    apply (rule csum_mono)
    apply (rule card_of_image)
    apply (rule ordIso_ordLeq_trans)
    apply (rule single_cone)
    apply (rule cone_ordLeq_ctwo)
    apply (rule ordLeq_cexp1)
    apply (simp_all add: natLeq_cinfinite natLeq_Card_order cinfinite_not_czero Card_order_csum)
    done
next
  fix A B1 B2 f1 f2 p1 p2
  assume wpull: "wpull A B1 B2 f1 f2 p1 p2"
  show "wpull {x. Option.set x \<subseteq> A} {x. Option.set x \<subseteq> B1} {x. Option.set x \<subseteq> B2}
    (Option.map f1) (Option.map f2) (Option.map p1) (Option.map p2)"
    (is "wpull ?A ?B1 ?B2 ?f1 ?f2 ?p1 ?p2")
    unfolding wpull_def
  proof (intro strip, elim conjE)
    fix b1 b2
    assume "b1 \<in> ?B1" "b2 \<in> ?B2" "?f1 b1 = ?f2 b2"
    thus "\<exists>a \<in> ?A. ?p1 a = b1 \<and> ?p2 a = b2" using wpull
      unfolding wpull_def by (cases b2) (auto 4 5)
  qed
next
  fix z
  assume "z \<in> Option.set None"
  thus False by simp
qed

lemma card_of_list_in:
  "|{xs. set xs \<subseteq> A}| \<le>o |Pfunc (UNIV :: nat set) A|" (is "|?LHS| \<le>o |?RHS|")
proof -
  let ?f = "%xs. %i. if i < length xs \<and> set xs \<subseteq> A then Some (nth xs i) else None"
  have "inj_on ?f ?LHS" unfolding inj_on_def fun_eq_iff
  proof safe
    fix xs :: "'a list" and ys :: "'a list"
    assume su: "set xs \<subseteq> A" "set ys \<subseteq> A" and eq: "\<forall>i. ?f xs i = ?f ys i"
    hence *: "length xs = length ys"
    by (metis linorder_cases option.simps(2) order_less_irrefl)
    thus "xs = ys" by (rule nth_equalityI) (metis * eq su option.inject)
  qed
  moreover have "?f ` ?LHS \<subseteq> ?RHS" unfolding Pfunc_def by fastforce
  ultimately show ?thesis using card_of_ordLeq by blast
qed

lemma list_in_empty: "A = {} \<Longrightarrow> {x. set x \<subseteq> A} = {[]}"
by simp

lemma card_of_Func: "|Func A B| =o |B| ^c |A|"
unfolding cexp_def Field_card_of by (rule card_of_refl)

lemma not_emp_czero_notIn_ordIso_Card_order:
"A \<noteq> {} \<Longrightarrow> ( |A|, czero) \<notin> ordIso \<and> Card_order |A|"
  apply (rule conjI)
  apply (metis Field_card_of czeroE)
  by (rule card_of_Card_order)

lemma list_in_bd: "|{x. set x \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq"
proof -
  fix A :: "'a set"
  show "|{x. set x \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq"
  proof (cases "A = {}")
    case False thus ?thesis
      apply -
      apply (rule ordLeq_transitive)
      apply (rule card_of_list_in)
      apply (rule ordLeq_transitive)
      apply (erule card_of_Pfunc_Pow_Func)
      apply (rule ordIso_ordLeq_trans)
      apply (rule Times_cprod)
      apply (rule cprod_cinfinite_bound)
      apply (rule ordIso_ordLeq_trans)
      apply (rule Pow_cexp_ctwo)
      apply (rule ordIso_ordLeq_trans)
      apply (rule cexp_cong2)
      apply (rule card_of_nat)
      apply (rule Card_order_ctwo)
      apply (rule card_of_Card_order)
      apply (rule natLeq_Card_order)
      apply (rule disjI1)
      apply (rule ctwo_Cnotzero)
      apply (rule cexp_mono1)
      apply (rule ordLeq_csum2)
      apply (rule Card_order_ctwo)
      apply (rule disjI1)
      apply (rule ctwo_Cnotzero)
      apply (rule natLeq_Card_order)
      apply (rule ordIso_ordLeq_trans)
      apply (rule card_of_Func)
      apply (rule ordIso_ordLeq_trans)
      apply (rule cexp_cong2)
      apply (rule card_of_nat)
      apply (rule card_of_Card_order)
      apply (rule card_of_Card_order)
      apply (rule natLeq_Card_order)
      apply (rule disjI1)
      apply (erule not_emp_czero_notIn_ordIso_Card_order)
      apply (rule cexp_mono1)
      apply (rule ordLeq_csum1)
      apply (rule card_of_Card_order)
      apply (rule disjI1)
      apply (erule not_emp_czero_notIn_ordIso_Card_order)
      apply (rule natLeq_Card_order)
      apply (rule card_of_Card_order)
      apply (rule card_of_Card_order)
      apply (rule Cinfinite_cexp)
      apply (rule ordLeq_csum2)
      apply (rule Card_order_ctwo)
      apply (rule conjI)
      apply (rule natLeq_cinfinite)
      by (rule natLeq_Card_order)
  next
    case True thus ?thesis
      apply -
      apply (rule ordIso_ordLeq_trans)
      apply (rule card_of_ordIso_subst)
      apply (erule list_in_empty)
      apply (rule ordIso_ordLeq_trans)
      apply (rule single_cone)
      apply (rule cone_ordLeq_cexp)
      apply (rule ordLeq_transitive)
      apply (rule cone_ordLeq_ctwo)
      apply (rule ordLeq_csum2)
      by (rule Card_order_ctwo)
  qed
qed

bnf_def list = map [set] "\<lambda>_::'a list. natLeq" ["[]"]
proof -
  show "map id = id" by (rule List.map.id)
next
  fix f g
  show "map (g o f) = map g o map f" by (rule List.map.comp[symmetric])
next
  fix x f g
  assume "\<And>z. z \<in> set x \<Longrightarrow> f z = g z"
  thus "map f x = map g x" by simp
next
  fix f
  show "set o map f = image f o set" by (rule ext, unfold o_apply, rule set_map)
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix x
  show "|set x| \<le>o natLeq"
    apply (rule ordLess_imp_ordLeq)
    apply (rule finite_ordLess_infinite[OF _ natLeq_Well_order])
    unfolding Field_natLeq Field_card_of by (auto simp: card_of_well_order_on)
next
  fix A :: "'a set"
  show "|{x. set x \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq" by (rule list_in_bd)
next
  fix A B1 B2 f1 f2 p1 p2
  assume "wpull A B1 B2 f1 f2 p1 p2"
  hence pull: "\<And>b1 b2. b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2 \<Longrightarrow> \<exists>a \<in> A. p1 a = b1 \<and> p2 a = b2"
    unfolding wpull_def by auto
  show "wpull {x. set x \<subseteq> A} {x. set x \<subseteq> B1} {x. set x \<subseteq> B2} (map f1) (map f2) (map p1) (map p2)"
    (is "wpull ?A ?B1 ?B2 _ _ _ _")
  proof (unfold wpull_def)
    { fix as bs assume *: "as \<in> ?B1" "bs \<in> ?B2" "map f1 as = map f2 bs"
      hence "length as = length bs" by (metis length_map)
      hence "\<exists>zs \<in> ?A. map p1 zs = as \<and> map p2 zs = bs" using *
      proof (induct as bs rule: list_induct2)
        case (Cons a as b bs)
        hence "a \<in> B1" "b \<in> B2" "f1 a = f2 b" by auto
        with pull obtain z where "z \<in> A" "p1 z = a" "p2 z = b" by blast
        moreover
        from Cons obtain zs where "zs \<in> ?A" "map p1 zs = as" "map p2 zs = bs" by auto
        ultimately have "z # zs \<in> ?A" "map p1 (z # zs) = a # as \<and> map p2 (z # zs) = b # bs" by auto
        thus ?case by (rule_tac x = "z # zs" in bexI)
      qed simp
    }
    thus "\<forall>as bs. as \<in> ?B1 \<and> bs \<in> ?B2 \<and> map f1 as = map f2 bs \<longrightarrow>
      (\<exists>zs \<in> ?A. map p1 zs = as \<and> map p2 zs = bs)" by blast
  qed
qed auto

(* Finite sets *)
abbreviation afset where "afset \<equiv> abs_fset"
abbreviation rfset where "rfset \<equiv> rep_fset"

lemma fset_fset_member:
"fset A = {a. a |\<in>| A}"
unfolding fset_def fset_member_def by auto

lemma afset_rfset:
"afset (rfset x) = x"
by (rule Quotient_fset[unfolded Quotient_def, THEN conjunct1, rule_format])

lemma afset_rfset_id:
"afset o rfset = id"
unfolding comp_def afset_rfset id_def ..

lemma rfset:
"rfset A = rfset B \<longleftrightarrow> A = B"
by (metis afset_rfset)

lemma afset_set:
"afset as = afset bs \<longleftrightarrow> set as = set bs"
using Quotient_fset unfolding Quotient_def list_eq_def by auto

lemma surj_afset:
"\<exists> as. A = afset as"
by (metis afset_rfset)

lemma fset_def2:
"fset = set o rfset"
unfolding fset_def map_fun_def[abs_def] by simp

lemma fset_def2_raw:
"fset A = set (rfset A)"
unfolding fset_def2 by simp

lemma fset_comp_afset:
"fset o afset = set"
unfolding fset_def2 comp_def apply(rule ext)
unfolding afset_set[symmetric] afset_rfset ..

lemma fset_afset:
"fset (afset as) = set as"
unfolding fset_comp_afset[symmetric] by simp

lemma set_rfset_afset:
"set (rfset (afset as)) = set as"
unfolding afset_set[symmetric] afset_rfset ..

lemma map_fset_comp_afset:
"(map_fset f) o afset = afset o (map f)"
unfolding map_fset_def map_fun_def[abs_def] comp_def apply(rule ext)
unfolding afset_set set_map set_rfset_afset id_apply ..

lemma map_fset_afset:
"(map_fset f) (afset as) = afset (map f as)"
using map_fset_comp_afset unfolding comp_def fun_eq_iff by auto

lemma fset_map_fset:
"fset (map_fset f A) = (image f) (fset A)"
apply(subst afset_rfset[symmetric, of A])
unfolding map_fset_afset fset_afset set_map
unfolding fset_def2_raw ..

lemma map_fset_def2:
"map_fset f = afset o (map f) o rfset"
unfolding map_fset_def map_fun_def[abs_def] by simp

lemma map_fset_def2_raw:
"map_fset f A = afset (map f (rfset A))"
unfolding map_fset_def2 by simp

lemma finite_ex_fset:
assumes "finite A"
shows "\<exists> B. fset B = A"
by (metis assms finite_list fset_afset)

lemma wpull_image:
assumes "wpull A B1 B2 f1 f2 p1 p2"
shows "wpull (Pow A) (Pow B1) (Pow B2) (image f1) (image f2) (image p1) (image p2)"
unfolding wpull_def Pow_def Bex_def mem_Collect_eq proof clarify
  fix Y1 Y2 assume Y1: "Y1 \<subseteq> B1" and Y2: "Y2 \<subseteq> B2" and EQ: "f1 ` Y1 = f2 ` Y2"
  def X \<equiv> "{a \<in> A. p1 a \<in> Y1 \<and> p2 a \<in> Y2}"
  show "\<exists>X\<subseteq>A. p1 ` X = Y1 \<and> p2 ` X = Y2"
  proof (rule exI[of _ X], intro conjI)
    show "p1 ` X = Y1"
    proof
      show "Y1 \<subseteq> p1 ` X"
      proof safe
        fix y1 assume y1: "y1 \<in> Y1"
        then obtain y2 where y2: "y2 \<in> Y2" and eq: "f1 y1 = f2 y2" using EQ by auto
        then obtain x where "x \<in> A" and "p1 x = y1" and "p2 x = y2"
        using assms y1 Y1 Y2 unfolding wpull_def by blast
        thus "y1 \<in> p1 ` X" unfolding X_def using y1 y2 by auto
      qed
    qed(unfold X_def, auto)
    show "p2 ` X = Y2"
    proof
      show "Y2 \<subseteq> p2 ` X"
      proof safe
        fix y2 assume y2: "y2 \<in> Y2"
        then obtain y1 where y1: "y1 \<in> Y1" and eq: "f1 y1 = f2 y2" using EQ by force
        then obtain x where "x \<in> A" and "p1 x = y1" and "p2 x = y2"
        using assms y2 Y1 Y2 unfolding wpull_def by blast
        thus "y2 \<in> p2 ` X" unfolding X_def using y1 y2 by auto
      qed
    qed(unfold X_def, auto)
  qed(unfold X_def, auto)
qed

lemma fset_to_fset: "finite A \<Longrightarrow> fset (the_inv fset A) = A"
by (rule f_the_inv_into_f) (auto simp: inj_on_def fset_cong dest!: finite_ex_fset)

bnf_def fset = map_fset [fset] "\<lambda>_::'a fset. natLeq" ["{||}"]
proof -
  show "map_fset id = id"
  unfolding map_fset_def2 map_id o_id afset_rfset_id ..
next
  fix f g
  show "map_fset (g o f) = map_fset g o map_fset f"
  unfolding map_fset_def2 map.comp[symmetric] comp_def apply(rule ext)
  unfolding afset_set set_map fset_def2_raw[symmetric] image_image[symmetric]
  unfolding map_fset_afset[symmetric] map_fset_image afset_rfset
  by (rule refl)
next
  fix x f g
  assume "\<And>z. z \<in> fset x \<Longrightarrow> f z = g z"
  hence "map f (rfset x) = map g (rfset x)"
  apply(intro map_cong) unfolding fset_def2_raw by auto
  thus "map_fset f x = map_fset g x" unfolding map_fset_def2_raw
  by (rule arg_cong)
next
  fix f
  show "fset o map_fset f = image f o fset"
  unfolding comp_def fset_map_fset ..
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix x
  show "|fset x| \<le>o natLeq"
  unfolding fset_def2_raw
  apply (rule ordLess_imp_ordLeq)
  apply (rule finite_iff_ordLess_natLeq[THEN iffD1])
  by (rule finite_set)
next
  fix A :: "'a set"
  have "|{x. fset x \<subseteq> A}| \<le>o |afset ` {as. set as \<subseteq> A}|"
  apply(rule card_of_mono1) unfolding fset_def2_raw apply auto
  apply (rule image_eqI)
  by (auto simp: afset_rfset)
  also have "|afset ` {as. set as \<subseteq> A}| \<le>o |{as. set as \<subseteq> A}|" using card_of_image .
  also have "|{as. set as \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq" by (rule list_in_bd)
  finally show "|{x. fset x \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq" .
next
  fix A B1 B2 f1 f2 p1 p2
  assume wp: "wpull A B1 B2 f1 f2 p1 p2"
  hence "wpull (Pow A) (Pow B1) (Pow B2) (image f1) (image f2) (image p1) (image p2)"
  by (rule wpull_image)
  show "wpull {x. fset x \<subseteq> A} {x. fset x \<subseteq> B1} {x. fset x \<subseteq> B2}
              (map_fset f1) (map_fset f2) (map_fset p1) (map_fset p2)"
  unfolding wpull_def Pow_def Bex_def mem_Collect_eq proof clarify
    fix y1 y2
    assume Y1: "fset y1 \<subseteq> B1" and Y2: "fset y2 \<subseteq> B2"
    assume "map_fset f1 y1 = map_fset f2 y2"
    hence EQ: "f1 ` (fset y1) = f2 ` (fset y2)" unfolding map_fset_def2_raw
    unfolding afset_set set_map fset_def2_raw .
    with Y1 Y2 obtain X where X: "X \<subseteq> A"
    and Y1: "p1 ` X = fset y1" and Y2: "p2 ` X = fset y2"
    using wpull_image[OF wp] unfolding wpull_def Pow_def
    unfolding Bex_def mem_Collect_eq apply -
    apply(erule allE[of _ "fset y1"], erule allE[of _ "fset y2"]) by auto
    have "\<forall> y1' \<in> fset y1. \<exists> x. x \<in> X \<and> y1' = p1 x" using Y1 by auto
    then obtain q1 where q1: "\<forall> y1' \<in> fset y1. q1 y1' \<in> X \<and> y1' = p1 (q1 y1')" by metis
    have "\<forall> y2' \<in> fset y2. \<exists> x. x \<in> X \<and> y2' = p2 x" using Y2 by auto
    then obtain q2 where q2: "\<forall> y2' \<in> fset y2. q2 y2' \<in> X \<and> y2' = p2 (q2 y2')" by metis
    def X' \<equiv> "q1 ` (fset y1) \<union> q2 ` (fset y2)"
    have X': "X' \<subseteq> A" and Y1: "p1 ` X' = fset y1" and Y2: "p2 ` X' = fset y2"
    using X Y1 Y2 q1 q2 unfolding X'_def by auto
    have fX': "finite X'" unfolding X'_def by simp
    then obtain x where X'eq: "X' = fset x" by (auto dest: finite_ex_fset)
    show "\<exists>x. fset x \<subseteq> A \<and> map_fset p1 x = y1 \<and> map_fset p2 x = y2"
    apply(intro exI[of _ "x"]) using X' Y1 Y2
    unfolding X'eq map_fset_def2_raw fset_def2_raw set_map[symmetric]
    afset_set[symmetric] afset_rfset by simp
  qed
qed auto

lemma fset_pred[simp]: "fset_pred R a b \<longleftrightarrow>
  ((\<forall>t \<in> fset a. (\<exists>u \<in> fset b. R t u)) \<and>
   (\<forall>t \<in> fset b. (\<exists>u \<in> fset a. R u t)))" (is "?L = ?R")
proof
  assume ?L thus ?R unfolding fset_rel_def fset_pred_def
    Gr_def relcomp_unfold converse_unfold
  apply (simp add: subset_eq Ball_def)
  apply (rule conjI)
  apply (clarsimp, metis snd_conv)
  by (clarsimp, metis fst_conv)
next
  assume ?R
  def R' \<equiv> "the_inv fset (Collect (split R) \<inter> (fset a \<times> fset b))" (is "the_inv fset ?R'")
  have "finite ?R'" by (intro finite_Int[OF disjI2] finite_cartesian_product) auto
  hence *: "fset R' = ?R'" unfolding R'_def by (intro fset_to_fset)
  show ?L unfolding fset_rel_def fset_pred_def Gr_def relcomp_unfold converse_unfold
  proof (intro CollectI prod_caseI exI conjI)
    from * show "(R', a) = (R', map_fset fst R')" using conjunct1[OF `?R`]
      by (auto simp add: fset_cong[symmetric] image_def Int_def split: prod.splits)
    from * show "(R', b) = (R', map_fset snd R')" using conjunct2[OF `?R`]
      by (auto simp add: fset_cong[symmetric] image_def Int_def split: prod.splits)
  qed (auto simp add: *)
qed

(* Countable sets *)

lemma card_of_countable_sets_range:
fixes A :: "'a set"
shows "|{X. X \<subseteq> A \<and> countable X \<and> X \<noteq> {}}| \<le>o |{f::nat \<Rightarrow> 'a. range f \<subseteq> A}|"
apply(rule card_of_ordLeqI[of fromNat]) using inj_on_fromNat
unfolding inj_on_def by auto

lemma card_of_countable_sets_Func:
"|{X. X \<subseteq> A \<and> countable X \<and> X \<noteq> {}}| \<le>o |A| ^c natLeq"
using card_of_countable_sets_range card_of_Func_UNIV[THEN ordIso_symmetric]
unfolding cexp_def Field_natLeq Field_card_of
by (rule ordLeq_ordIso_trans)

lemma ordLeq_countable_subsets:
"|A| \<le>o |{X. X \<subseteq> A \<and> countable X}|"
apply (rule card_of_ordLeqI[of "\<lambda> a. {a}"]) unfolding inj_on_def by auto

lemma finite_countable_subset:
"finite {X. X \<subseteq> A \<and> countable X} \<longleftrightarrow> finite A"
apply default
 apply (erule contrapos_pp)
 apply (rule card_of_ordLeq_infinite)
 apply (rule ordLeq_countable_subsets)
 apply assumption
apply (rule finite_Collect_conjI)
apply (rule disjI1)
by (erule finite_Collect_subsets)

lemma card_of_countable_sets:
"|{X. X \<subseteq> A \<and> countable X}| \<le>o ( |A| +c ctwo) ^c natLeq"
(is "|?L| \<le>o _")
proof(cases "finite A")
  let ?R = "Func (UNIV::nat set) (A <+> (UNIV::bool set))"
  case True hence "finite ?L" by simp
  moreover have "infinite ?R"
  apply(rule infinite_Func[of _ "Inr True" "Inr False"]) by auto
  ultimately show ?thesis unfolding cexp_def csum_def ctwo_def Field_natLeq Field_card_of
  apply(intro ordLess_imp_ordLeq) by (rule finite_ordLess_infinite2)
next
  case False
  hence "|{X. X \<subseteq> A \<and> countable X}| =o |{X. X \<subseteq> A \<and> countable X} - {{}}|"
  by (intro card_of_infinite_diff_finitte finite.emptyI finite.insertI ordIso_symmetric)
     (unfold finite_countable_subset)
  also have "|{X. X \<subseteq> A \<and> countable X} - {{}}| \<le>o |A| ^c natLeq"
  using card_of_countable_sets_Func[of A] unfolding set_diff_eq by auto
  also have "|A| ^c natLeq \<le>o ( |A| +c ctwo) ^c natLeq"
  apply(rule cexp_mono1_cone_ordLeq)
    apply(rule ordLeq_csum1, rule card_of_Card_order)
    apply (rule cone_ordLeq_cexp)
    apply (rule cone_ordLeq_Cnotzero)
    using csum_Cnotzero2 ctwo_Cnotzero apply blast
    by (rule natLeq_Card_order)
  finally show ?thesis .
qed

bnf_def cset = cIm [rcset] "\<lambda>_::'a cset. natLeq" ["cEmp"]
proof -
  show "cIm id = id" unfolding cIm_def[abs_def] id_def by auto
next
  fix f g show "cIm (g \<circ> f) = cIm g \<circ> cIm f"
  unfolding cIm_def[abs_def] apply(rule ext) unfolding comp_def by auto
next
  fix C f g assume eq: "\<And>a. a \<in> rcset C \<Longrightarrow> f a = g a"
  thus "cIm f C = cIm g C"
  unfolding cIm_def[abs_def] unfolding image_def by auto
next
  fix f show "rcset \<circ> cIm f = op ` f \<circ> rcset" unfolding cIm_def[abs_def] by auto
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix C show "|rcset C| \<le>o natLeq" using rcset unfolding countable_def .
next
  fix A :: "'a set"
  have "|{Z. rcset Z \<subseteq> A}| \<le>o |acset ` {X. X \<subseteq> A \<and> countable X}|"
  apply(rule card_of_mono1) unfolding Pow_def image_def
  proof (rule Collect_mono, clarsimp)
    fix x
    assume "rcset x \<subseteq> A"
    hence "rcset x \<subseteq> A \<and> countable (rcset x) \<and> x = acset (rcset x)"
    using acset_rcset[of x] rcset[of x] by force
    thus "\<exists>y \<subseteq> A. countable y \<and> x = acset y" by blast
  qed
  also have "|acset ` {X. X \<subseteq> A \<and> countable X}| \<le>o |{X. X \<subseteq> A \<and> countable X}|"
  using card_of_image .
  also have "|{X. X \<subseteq> A \<and> countable X}| \<le>o ( |A| +c ctwo) ^c natLeq"
  using card_of_countable_sets .
  finally show "|{Z. rcset Z \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq" .
next
  fix A B1 B2 f1 f2 p1 p2
  assume wp: "wpull A B1 B2 f1 f2 p1 p2"
  show "wpull {x. rcset x \<subseteq> A} {x. rcset x \<subseteq> B1} {x. rcset x \<subseteq> B2}
              (cIm f1) (cIm f2) (cIm p1) (cIm p2)"
  unfolding wpull_def proof safe
    fix y1 y2
    assume Y1: "rcset y1 \<subseteq> B1" and Y2: "rcset y2 \<subseteq> B2"
    assume "cIm f1 y1 = cIm f2 y2"
    hence EQ: "f1 ` (rcset y1) = f2 ` (rcset y2)"
    unfolding cIm_def by auto
    with Y1 Y2 obtain X where X: "X \<subseteq> A"
    and Y1: "p1 ` X = rcset y1" and Y2: "p2 ` X = rcset y2"
    using wpull_image[OF wp] unfolding wpull_def Pow_def
    unfolding Bex_def mem_Collect_eq apply -
    apply(erule allE[of _ "rcset y1"], erule allE[of _ "rcset y2"]) by auto
    have "\<forall> y1' \<in> rcset y1. \<exists> x. x \<in> X \<and> y1' = p1 x" using Y1 by auto
    then obtain q1 where q1: "\<forall> y1' \<in> rcset y1. q1 y1' \<in> X \<and> y1' = p1 (q1 y1')" by metis
    have "\<forall> y2' \<in> rcset y2. \<exists> x. x \<in> X \<and> y2' = p2 x" using Y2 by auto
    then obtain q2 where q2: "\<forall> y2' \<in> rcset y2. q2 y2' \<in> X \<and> y2' = p2 (q2 y2')" by metis
    def X' \<equiv> "q1 ` (rcset y1) \<union> q2 ` (rcset y2)"
    have X': "X' \<subseteq> A" and Y1: "p1 ` X' = rcset y1" and Y2: "p2 ` X' = rcset y2"
    using X Y1 Y2 q1 q2 unfolding X'_def by fast+
    have fX': "countable X'" unfolding X'_def by simp
    then obtain x where X'eq: "X' = rcset x" by (metis rcset_acset)
    show "\<exists>x\<in>{x. rcset x \<subseteq> A}. cIm p1 x = y1 \<and> cIm p2 x = y2"
    apply(intro bexI[of _ "x"]) using X' Y1 Y2 unfolding X'eq cIm_def by auto
  qed
qed (unfold cEmp_def, auto)


(* Multisets *)

lemma setsum_gt_0_iff:
fixes f :: "'a \<Rightarrow> nat" assumes "finite A"
shows "setsum f A > 0 \<longleftrightarrow> (\<exists> a \<in> A. f a > 0)"
(is "?L \<longleftrightarrow> ?R")
proof-
  have "?L \<longleftrightarrow> \<not> setsum f A = 0" by fast
  also have "... \<longleftrightarrow> (\<exists> a \<in> A. f a \<noteq> 0)" using assms by simp
  also have "... \<longleftrightarrow> ?R" by simp
  finally show ?thesis .
qed

(*   *)
definition mmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'b \<Rightarrow> nat" where
"mmap h f b = setsum f {a. h a = b \<and> f a > 0}"

lemma mmap_id: "mmap id = id"
proof (rule ext)+
  fix f a show "mmap id f a = id f a"
  proof(cases "f a = 0")
    case False
    hence 1: "{aa. aa = a \<and> 0 < f aa} = {a}" by auto
    show ?thesis by (simp add: mmap_def id_apply 1)
  qed(unfold mmap_def, auto)
qed

lemma inj_on_setsum_inv:
assumes f: "f \<in> multiset"
and 1: "(0::nat) < setsum f {a. h a = b' \<and> 0 < f a}" (is "0 < setsum f ?A'")
and 2: "{a. h a = b \<and> 0 < f a} = {a. h a = b' \<and> 0 < f a}" (is "?A = ?A'")
shows "b = b'"
proof-
  have "finite ?A'" using f unfolding multiset_def by auto
  hence "?A' \<noteq> {}" using 1 setsum_gt_0_iff by auto
  thus ?thesis using 2 by auto
qed

lemma mmap_comp:
fixes h1 :: "'a \<Rightarrow> 'b" and h2 :: "'b \<Rightarrow> 'c"
assumes f: "f \<in> multiset"
shows "mmap (h2 o h1) f = (mmap h2 o mmap h1) f"
unfolding mmap_def[abs_def] comp_def proof(rule ext)+
  fix c :: 'c
  let ?A = "{a. h2 (h1 a) = c \<and> 0 < f a}"
  let ?As = "\<lambda> b. {a. h1 a = b \<and> 0 < f a}"
  let ?B = "{b. h2 b = c \<and> 0 < setsum f (?As b)}"
  have 0: "{?As b | b.  b \<in> ?B} = ?As ` ?B" by auto
  have "\<And> b. finite (?As b)" using f unfolding multiset_def by simp
  hence "?B = {b. h2 b = c \<and> ?As b \<noteq> {}}" using setsum_gt_0_iff by auto
  hence A: "?A = \<Union> {?As b | b.  b \<in> ?B}" by auto
  have "setsum f ?A = setsum (setsum f) {?As b | b.  b \<in> ?B}"
  unfolding A apply(rule setsum_Union_disjoint)
  using f unfolding multiset_def by auto
  also have "... = setsum (setsum f) (?As ` ?B)" unfolding 0 ..
  also have "... = setsum (setsum f o ?As) ?B" apply(rule setsum_reindex)
  unfolding inj_on_def apply auto using inj_on_setsum_inv[OF f, of h1] by blast
  also have "... = setsum (\<lambda> b. setsum f (?As b)) ?B" unfolding comp_def ..
  finally show "setsum f ?A = setsum (\<lambda> b. setsum f (?As b)) ?B" .
qed

lemma mmap_comp1:
fixes h1 :: "'a \<Rightarrow> 'b" and h2 :: "'b \<Rightarrow> 'c"
assumes "f \<in> multiset"
shows "mmap (\<lambda> a. h2 (h1 a)) f = mmap h2 (mmap h1 f)"
using mmap_comp[OF assms] unfolding comp_def by auto

lemma mmap:
assumes "f \<in> multiset"
shows "mmap h f \<in> multiset"
using assms unfolding mmap_def[abs_def] multiset_def proof safe
  assume fin: "finite {a. 0 < f a}"  (is "finite ?A")
  show "finite {b. 0 < setsum f {a. h a = b \<and> 0 < f a}}"
  (is "finite {b. 0 < setsum f (?As b)}")
  proof- let ?B = "{b. 0 < setsum f (?As b)}"
    have "\<And> b. finite (?As b)" using assms unfolding multiset_def by simp
    hence B: "?B = {b. ?As b \<noteq> {}}" using setsum_gt_0_iff by auto
    hence "?B \<subseteq> h ` ?A" by auto
    thus ?thesis using finite_surj[OF fin] by auto
  qed
qed

lemma mmap_cong:
assumes "\<And>a. a \<in># M \<Longrightarrow> f a = g a"
shows "mmap f (count M) = mmap g (count M)"
using assms unfolding mmap_def[abs_def] by (intro ext, intro setsum_cong) auto

abbreviation supp where "supp f \<equiv> {a. f a > 0}"

lemma mmap_image_comp:
assumes f: "f \<in> multiset"
shows "(supp o mmap h) f = (image h o supp) f"
unfolding mmap_def[abs_def] comp_def proof-
  have "\<And> b. finite {a. h a = b \<and> 0 < f a}" (is "\<And> b. finite (?As b)")
  using f unfolding multiset_def by auto
  thus "{b. 0 < setsum f (?As b)} = h ` {a. 0 < f a}"
  using setsum_gt_0_iff by auto
qed

lemma mmap_image:
assumes f: "f \<in> multiset"
shows "supp (mmap h f) = h ` (supp f)"
using mmap_image_comp[OF assms] unfolding comp_def .

lemma set_of_Abs_multiset:
assumes f: "f \<in> multiset"
shows "set_of (Abs_multiset f) = supp f"
using assms unfolding set_of_def by (auto simp: Abs_multiset_inverse)

lemma supp_count:
"supp (count M) = set_of M"
using assms unfolding set_of_def by auto

lemma multiset_of_surj:
"multiset_of ` {as. set as \<subseteq> A} = {M. set_of M \<subseteq> A}"
proof safe
  fix M assume M: "set_of M \<subseteq> A"
  obtain as where eq: "M = multiset_of as" using surj_multiset_of unfolding surj_def by auto
  hence "set as \<subseteq> A" using M by auto
  thus "M \<in> multiset_of ` {as. set as \<subseteq> A}" using eq by auto
next
  show "\<And>x xa xb. \<lbrakk>set xa \<subseteq> A; xb \<in> set_of (multiset_of xa)\<rbrakk> \<Longrightarrow> xb \<in> A"
  by (erule set_mp) (unfold set_of_multiset_of)
qed

lemma card_of_set_of:
"|{M. set_of M \<subseteq> A}| \<le>o |{as. set as \<subseteq> A}|"
apply(rule card_of_ordLeqI2[of _ multiset_of]) using multiset_of_surj by auto

lemma nat_sum_induct:
assumes "\<And>n1 n2. (\<And> m1 m2. m1 + m2 < n1 + n2 \<Longrightarrow> phi m1 m2) \<Longrightarrow> phi n1 n2"
shows "phi (n1::nat) (n2::nat)"
proof-
  let ?chi = "\<lambda> n1n2 :: nat * nat. phi (fst n1n2) (snd n1n2)"
  have "?chi (n1,n2)"
  apply(induct rule: measure_induct[of "\<lambda> n1n2. fst n1n2 + snd n1n2" ?chi])
  using assms by (metis fstI sndI)
  thus ?thesis by simp
qed

lemma matrix_count:
fixes ct1 ct2 :: "nat \<Rightarrow> nat"
assumes "setsum ct1 {..<Suc n1} = setsum ct2 {..<Suc n2}"
shows
"\<exists> ct. (\<forall> i1 \<le> n1. setsum (\<lambda> i2. ct i1 i2) {..<Suc n2} = ct1 i1) \<and>
       (\<forall> i2 \<le> n2. setsum (\<lambda> i1. ct i1 i2) {..<Suc n1} = ct2 i2)"
(is "?phi ct1 ct2 n1 n2")
proof-
  have "\<forall> ct1 ct2 :: nat \<Rightarrow> nat.
        setsum ct1 {..<Suc n1} = setsum ct2 {..<Suc n2} \<longrightarrow> ?phi ct1 ct2 n1 n2"
  proof(induct rule: nat_sum_induct[of
"\<lambda> n1 n2. \<forall> ct1 ct2 :: nat \<Rightarrow> nat.
     setsum ct1 {..<Suc n1} = setsum ct2 {..<Suc n2} \<longrightarrow> ?phi ct1 ct2 n1 n2"],
      clarify)
  fix n1 n2 :: nat and ct1 ct2 :: "nat \<Rightarrow> nat"
  assume IH: "\<And> m1 m2. m1 + m2 < n1 + n2 \<Longrightarrow>
                \<forall> dt1 dt2 :: nat \<Rightarrow> nat.
                setsum dt1 {..<Suc m1} = setsum dt2 {..<Suc m2} \<longrightarrow> ?phi dt1 dt2 m1 m2"
  and ss: "setsum ct1 {..<Suc n1} = setsum ct2 {..<Suc n2}"
  show "?phi ct1 ct2 n1 n2"
  proof(cases n1)
    case 0 note n1 = 0
    show ?thesis
    proof(cases n2)
      case 0 note n2 = 0
      let ?ct = "\<lambda> i1 i2. ct2 0"
      show ?thesis apply(rule exI[of _ ?ct]) using n1 n2 ss by simp
    next
      case (Suc m2) note n2 = Suc
      let ?ct = "\<lambda> i1 i2. ct2 i2"
      show ?thesis apply(rule exI[of _ ?ct]) using n1 n2 ss by auto
    qed
  next
    case (Suc m1) note n1 = Suc
    show ?thesis
    proof(cases n2)
      case 0 note n2 = 0
      let ?ct = "\<lambda> i1 i2. ct1 i1"
      show ?thesis apply(rule exI[of _ ?ct]) using n1 n2 ss by auto
    next
      case (Suc m2) note n2 = Suc
      show ?thesis
      proof(cases "ct1 n1 \<le> ct2 n2")
        case True
        def dt2 \<equiv> "\<lambda> i2. if i2 = n2 then ct2 i2 - ct1 n1 else ct2 i2"
        have "setsum ct1 {..<Suc m1} = setsum dt2 {..<Suc n2}"
        unfolding dt2_def using ss n1 True by auto
        hence "?phi ct1 dt2 m1 n2" using IH[of m1 n2] n1 by simp
        then obtain dt where
        1: "\<And> i1. i1 \<le> m1 \<Longrightarrow> setsum (\<lambda> i2. dt i1 i2) {..<Suc n2} = ct1 i1" and
        2: "\<And> i2. i2 \<le> n2 \<Longrightarrow> setsum (\<lambda> i1. dt i1 i2) {..<Suc m1} = dt2 i2" by auto
        let ?ct = "\<lambda> i1 i2. if i1 = n1 then (if i2 = n2 then ct1 n1 else 0)
                                       else dt i1 i2"
        show ?thesis apply(rule exI[of _ ?ct])
        using n1 n2 1 2 True unfolding dt2_def by simp
      next
        case False
        hence False: "ct2 n2 < ct1 n1" by simp
        def dt1 \<equiv> "\<lambda> i1. if i1 = n1 then ct1 i1 - ct2 n2 else ct1 i1"
        have "setsum dt1 {..<Suc n1} = setsum ct2 {..<Suc m2}"
        unfolding dt1_def using ss n2 False by auto
        hence "?phi dt1 ct2 n1 m2" using IH[of n1 m2] n2 by simp
        then obtain dt where
        1: "\<And> i1. i1 \<le> n1 \<Longrightarrow> setsum (\<lambda> i2. dt i1 i2) {..<Suc m2} = dt1 i1" and
        2: "\<And> i2. i2 \<le> m2 \<Longrightarrow> setsum (\<lambda> i1. dt i1 i2) {..<Suc n1} = ct2 i2" by force
        let ?ct = "\<lambda> i1 i2. if i2 = n2 then (if i1 = n1 then ct2 n2 else 0)
                                       else dt i1 i2"
        show ?thesis apply(rule exI[of _ ?ct])
        using n1 n2 1 2 False unfolding dt1_def by simp
      qed
    qed
  qed
  qed
  thus ?thesis using assms by auto
qed

definition
"inj2 u B1 B2 \<equiv>
 \<forall> b1 b1' b2 b2'. {b1,b1'} \<subseteq> B1 \<and> {b2,b2'} \<subseteq> B2 \<and> u b1 b2 = u b1' b2'
                  \<longrightarrow> b1 = b1' \<and> b2 = b2'"

lemma matrix_count_finite:
assumes B1: "B1 \<noteq> {}" "finite B1" and B2: "B2 \<noteq> {}" "finite B2" and u: "inj2 u B1 B2"
and ss: "setsum N1 B1 = setsum N2 B2"
shows "\<exists> M :: 'a \<Rightarrow> nat.
            (\<forall> b1 \<in> B1. setsum (\<lambda> b2. M (u b1 b2)) B2 = N1 b1) \<and>
            (\<forall> b2 \<in> B2. setsum (\<lambda> b1. M (u b1 b2)) B1 = N2 b2)"
proof-
  obtain n1 where "card B1 = Suc n1" using B1 by (metis card_insert finite.simps)
  then obtain e1 where e1: "bij_betw e1 {..<Suc n1} B1"
  using ex_bij_betw_finite_nat[OF B1(2)] by (metis atLeast0LessThan bij_betw_the_inv_into)
  hence e1_inj: "inj_on e1 {..<Suc n1}" and e1_surj: "e1 ` {..<Suc n1} = B1"
  unfolding bij_betw_def by auto
  def f1 \<equiv> "inv_into {..<Suc n1} e1"
  have f1: "bij_betw f1 B1 {..<Suc n1}"
  and f1e1[simp]: "\<And> i1. i1 < Suc n1 \<Longrightarrow> f1 (e1 i1) = i1"
  and e1f1[simp]: "\<And> b1. b1 \<in> B1 \<Longrightarrow> e1 (f1 b1) = b1" unfolding f1_def
  apply (metis bij_betw_inv_into e1, metis bij_betw_inv_into_left e1 lessThan_iff)
  by (metis e1_surj f_inv_into_f)
  (*  *)
  obtain n2 where "card B2 = Suc n2" using B2 by (metis card_insert finite.simps)
  then obtain e2 where e2: "bij_betw e2 {..<Suc n2} B2"
  using ex_bij_betw_finite_nat[OF B2(2)] by (metis atLeast0LessThan bij_betw_the_inv_into)
  hence e2_inj: "inj_on e2 {..<Suc n2}" and e2_surj: "e2 ` {..<Suc n2} = B2"
  unfolding bij_betw_def by auto
  def f2 \<equiv> "inv_into {..<Suc n2} e2"
  have f2: "bij_betw f2 B2 {..<Suc n2}"
  and f2e2[simp]: "\<And> i2. i2 < Suc n2 \<Longrightarrow> f2 (e2 i2) = i2"
  and e2f2[simp]: "\<And> b2. b2 \<in> B2 \<Longrightarrow> e2 (f2 b2) = b2" unfolding f2_def
  apply (metis bij_betw_inv_into e2, metis bij_betw_inv_into_left e2 lessThan_iff)
  by (metis e2_surj f_inv_into_f)
  (*  *)
  let ?ct1 = "N1 o e1"  let ?ct2 = "N2 o e2"
  have ss: "setsum ?ct1 {..<Suc n1} = setsum ?ct2 {..<Suc n2}"
  unfolding setsum_reindex[OF e1_inj, symmetric] setsum_reindex[OF e2_inj, symmetric]
  e1_surj e2_surj using ss .
  obtain ct where
  ct1: "\<And> i1. i1 \<le> n1 \<Longrightarrow> setsum (\<lambda> i2. ct i1 i2) {..<Suc n2} = ?ct1 i1" and
  ct2: "\<And> i2. i2 \<le> n2 \<Longrightarrow> setsum (\<lambda> i1. ct i1 i2) {..<Suc n1} = ?ct2 i2"
  using matrix_count[OF ss] by blast
  (*  *)
  def A \<equiv> "{u b1 b2 | b1 b2. b1 \<in> B1 \<and> b2 \<in> B2}"
  have "\<forall> a \<in> A. \<exists> b1b2 \<in> B1 <*> B2. u (fst b1b2) (snd b1b2) = a"
  unfolding A_def Ball_def mem_Collect_eq by auto
  then obtain h1h2 where h12:
  "\<And>a. a \<in> A \<Longrightarrow> u (fst (h1h2 a)) (snd (h1h2 a)) = a \<and> h1h2 a \<in> B1 <*> B2" by metis
  def h1 \<equiv> "fst o h1h2"  def h2 \<equiv> "snd o h1h2"
  have h12[simp]: "\<And>a. a \<in> A \<Longrightarrow> u (h1 a) (h2 a) = a"
                  "\<And> a. a \<in> A \<Longrightarrow> h1 a \<in> B1"  "\<And> a. a \<in> A \<Longrightarrow> h2 a \<in> B2"
  using h12 unfolding h1_def h2_def by force+
  {fix b1 b2 assume b1: "b1 \<in> B1" and b2: "b2 \<in> B2"
   hence inA: "u b1 b2 \<in> A" unfolding A_def by auto
   hence "u b1 b2 = u (h1 (u b1 b2)) (h2 (u b1 b2))" by auto
   moreover have "h1 (u b1 b2) \<in> B1" "h2 (u b1 b2) \<in> B2" using inA by auto
   ultimately have "h1 (u b1 b2) = b1 \<and> h2 (u b1 b2) = b2"
   using u b1 b2 unfolding inj2_def by fastforce
  }
  hence h1[simp]: "\<And> b1 b2. \<lbrakk>b1 \<in> B1; b2 \<in> B2\<rbrakk> \<Longrightarrow> h1 (u b1 b2) = b1" and
        h2[simp]: "\<And> b1 b2. \<lbrakk>b1 \<in> B1; b2 \<in> B2\<rbrakk> \<Longrightarrow> h2 (u b1 b2) = b2" by auto
  def M \<equiv> "\<lambda> a. ct (f1 (h1 a)) (f2 (h2 a))"
  show ?thesis
  apply(rule exI[of _ M]) proof safe
    fix b1 assume b1: "b1 \<in> B1"
    hence f1b1: "f1 b1 \<le> n1" using f1 unfolding bij_betw_def
    by (metis bij_betwE f1 lessThan_iff less_Suc_eq_le)
    have "(\<Sum>b2\<in>B2. M (u b1 b2)) = (\<Sum>i2<Suc n2. ct (f1 b1) (f2 (e2 i2)))"
    unfolding e2_surj[symmetric] setsum_reindex[OF e2_inj]
    unfolding M_def comp_def apply(intro setsum_cong) apply force
    by (metis e2_surj b1 h1 h2 imageI)
    also have "... = N1 b1" using b1 ct1[OF f1b1] by simp
    finally show "(\<Sum>b2\<in>B2. M (u b1 b2)) = N1 b1" .
  next
    fix b2 assume b2: "b2 \<in> B2"
    hence f2b2: "f2 b2 \<le> n2" using f2 unfolding bij_betw_def
    by (metis bij_betwE f2 lessThan_iff less_Suc_eq_le)
    have "(\<Sum>b1\<in>B1. M (u b1 b2)) = (\<Sum>i1<Suc n1. ct (f1 (e1 i1)) (f2 b2))"
    unfolding e1_surj[symmetric] setsum_reindex[OF e1_inj]
    unfolding M_def comp_def apply(intro setsum_cong) apply force
    by (metis e1_surj b2 h1 h2 imageI)
    also have "... = N2 b2" using b2 ct2[OF f2b2] by simp
    finally show "(\<Sum>b1\<in>B1. M (u b1 b2)) = N2 b2" .
  qed
qed

lemma supp_vimage_mmap:
assumes "M \<in> multiset"
shows "supp M \<subseteq> f -` (supp (mmap f M))"
using assms by (auto simp: mmap_image)

lemma mmap_ge_0:
assumes "M \<in> multiset"
shows "0 < mmap f M b \<longleftrightarrow> (\<exists>a. 0 < M a \<and> f a = b)"
proof-
  have f: "finite {a. f a = b \<and> 0 < M a}" using assms unfolding multiset_def by auto
  show ?thesis unfolding mmap_def setsum_gt_0_iff[OF f] by auto
qed

lemma finite_twosets:
assumes "finite B1" and "finite B2"
shows "finite {u b1 b2 |b1 b2. b1 \<in> B1 \<and> b2 \<in> B2}"  (is "finite ?A")
proof-
  have A: "?A = (\<lambda> b1b2. u (fst b1b2) (snd b1b2)) ` (B1 <*> B2)" by force
  show ?thesis unfolding A using finite_cartesian_product[OF assms] by auto
qed

lemma wp_mmap:
fixes A :: "'a set" and B1 :: "'b1 set" and B2 :: "'b2 set"
assumes wp: "wpull A B1 B2 f1 f2 p1 p2"
shows
"wpull {M. M \<in> multiset \<and> supp M \<subseteq> A}
       {N1. N1 \<in> multiset \<and> supp N1 \<subseteq> B1} {N2. N2 \<in> multiset \<and> supp N2 \<subseteq> B2}
       (mmap f1) (mmap f2) (mmap p1) (mmap p2)"
unfolding wpull_def proof (safe, unfold Bex_def mem_Collect_eq)
  fix N1 :: "'b1 \<Rightarrow> nat" and N2 :: "'b2 \<Rightarrow> nat"
  assume mmap': "mmap f1 N1 = mmap f2 N2"
  and N1[simp]: "N1 \<in> multiset" "supp N1 \<subseteq> B1"
  and N2[simp]: "N2 \<in> multiset" "supp N2 \<subseteq> B2"
  have mN1[simp]: "mmap f1 N1 \<in> multiset" using N1 by (auto simp: mmap)
  have mN2[simp]: "mmap f2 N2 \<in> multiset" using N2 by (auto simp: mmap)
  def P \<equiv> "mmap f1 N1"
  have P1: "P = mmap f1 N1" and P2: "P = mmap f2 N2" unfolding P_def using mmap' by auto
  note P = P1 P2
  have P_mult[simp]: "P \<in> multiset" unfolding P_def using N1 by auto
  have fin_N1[simp]: "finite (supp N1)" using N1(1) unfolding multiset_def by auto
  have fin_N2[simp]: "finite (supp N2)" using N2(1) unfolding multiset_def by auto
  have fin_P[simp]: "finite (supp P)" using P_mult unfolding multiset_def by auto
  (*  *)
  def set1 \<equiv> "\<lambda> c. {b1 \<in> supp N1. f1 b1 = c}"
  have set1[simp]: "\<And> c b1. b1 \<in> set1 c \<Longrightarrow> f1 b1 = c" unfolding set1_def by auto
  have fin_set1: "\<And> c. c \<in> supp P \<Longrightarrow> finite (set1 c)"
  using N1(1) unfolding set1_def multiset_def by auto
  have set1_NE: "\<And> c. c \<in> supp P \<Longrightarrow> set1 c \<noteq> {}"
  unfolding set1_def P1 mmap_ge_0[OF N1(1)] by auto
  have supp_N1_set1: "supp N1 = (\<Union> c \<in> supp P. set1 c)"
  using supp_vimage_mmap[OF N1(1), of f1] unfolding set1_def P1 by auto
  hence set1_inclN1: "\<And>c. c \<in> supp P \<Longrightarrow> set1 c \<subseteq> supp N1" by auto
  hence set1_incl: "\<And> c. c \<in> supp P \<Longrightarrow> set1 c \<subseteq> B1" using N1(2) by blast
  have set1_disj: "\<And> c c'. c \<noteq> c' \<Longrightarrow> set1 c \<inter> set1 c' = {}"
  unfolding set1_def by auto
  have setsum_set1: "\<And> c. setsum N1 (set1 c) = P c"
  unfolding P1 set1_def mmap_def apply(rule setsum_cong) by auto
  (*  *)
  def set2 \<equiv> "\<lambda> c. {b2 \<in> supp N2. f2 b2 = c}"
  have set2[simp]: "\<And> c b2. b2 \<in> set2 c \<Longrightarrow> f2 b2 = c" unfolding set2_def by auto
  have fin_set2: "\<And> c. c \<in> supp P \<Longrightarrow> finite (set2 c)"
  using N2(1) unfolding set2_def multiset_def by auto
  have set2_NE: "\<And> c. c \<in> supp P \<Longrightarrow> set2 c \<noteq> {}"
  unfolding set2_def P2 mmap_ge_0[OF N2(1)] by auto
  have supp_N2_set2: "supp N2 = (\<Union> c \<in> supp P. set2 c)"
  using supp_vimage_mmap[OF N2(1), of f2] unfolding set2_def P2 by auto
  hence set2_inclN2: "\<And>c. c \<in> supp P \<Longrightarrow> set2 c \<subseteq> supp N2" by auto
  hence set2_incl: "\<And> c. c \<in> supp P \<Longrightarrow> set2 c \<subseteq> B2" using N2(2) by blast
  have set2_disj: "\<And> c c'. c \<noteq> c' \<Longrightarrow> set2 c \<inter> set2 c' = {}"
  unfolding set2_def by auto
  have setsum_set2: "\<And> c. setsum N2 (set2 c) = P c"
  unfolding P2 set2_def mmap_def apply(rule setsum_cong) by auto
  (*  *)
  have ss: "\<And> c. c \<in> supp P \<Longrightarrow> setsum N1 (set1 c) = setsum N2 (set2 c)"
  unfolding setsum_set1 setsum_set2 ..
  have "\<forall> c \<in> supp P. \<forall> b1b2 \<in> (set1 c) \<times> (set2 c).
          \<exists> a \<in> A. p1 a = fst b1b2 \<and> p2 a = snd b1b2"
  using wp set1_incl set2_incl unfolding wpull_def Ball_def mem_Collect_eq
  by simp (metis set1 set2 set_rev_mp)
  then obtain uu where uu:
  "\<forall> c \<in> supp P. \<forall> b1b2 \<in> (set1 c) \<times> (set2 c).
     uu c b1b2 \<in> A \<and> p1 (uu c b1b2) = fst b1b2 \<and> p2 (uu c b1b2) = snd b1b2" by metis
  def u \<equiv> "\<lambda> c b1 b2. uu c (b1,b2)"
  have u[simp]:
  "\<And> c b1 b2. \<lbrakk>c \<in> supp P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk> \<Longrightarrow> u c b1 b2 \<in> A"
  "\<And> c b1 b2. \<lbrakk>c \<in> supp P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk> \<Longrightarrow> p1 (u c b1 b2) = b1"
  "\<And> c b1 b2. \<lbrakk>c \<in> supp P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk> \<Longrightarrow> p2 (u c b1 b2) = b2"
  using uu unfolding u_def by auto
  {fix c assume c: "c \<in> supp P"
   have "inj2 (u c) (set1 c) (set2 c)" unfolding inj2_def proof clarify
     fix b1 b1' b2 b2'
     assume "{b1, b1'} \<subseteq> set1 c" "{b2, b2'} \<subseteq> set2 c" and 0: "u c b1 b2 = u c b1' b2'"
     hence "p1 (u c b1 b2) = b1 \<and> p2 (u c b1 b2) = b2 \<and>
            p1 (u c b1' b2') = b1' \<and> p2 (u c b1' b2') = b2'"
     using u(2)[OF c] u(3)[OF c] by simp metis
     thus "b1 = b1' \<and> b2 = b2'" using 0 by auto
   qed
  } note inj = this
  def sset \<equiv> "\<lambda> c. {u c b1 b2 | b1 b2. b1 \<in> set1 c \<and> b2 \<in> set2 c}"
  have fin_sset[simp]: "\<And> c. c \<in> supp P \<Longrightarrow> finite (sset c)" unfolding sset_def
  using fin_set1 fin_set2 finite_twosets by blast
  have sset_A: "\<And> c. c \<in> supp P \<Longrightarrow> sset c \<subseteq> A" unfolding sset_def by auto
  {fix c a assume c: "c \<in> supp P" and ac: "a \<in> sset c"
   then obtain b1 b2 where b1: "b1 \<in> set1 c" and b2: "b2 \<in> set2 c"
   and a: "a = u c b1 b2" unfolding sset_def by auto
   have "p1 a \<in> set1 c" and p2a: "p2 a \<in> set2 c"
   using ac a b1 b2 c u(2) u(3) by simp+
   hence "u c (p1 a) (p2 a) = a" unfolding a using b1 b2 inj[OF c]
   unfolding inj2_def by (metis c u(2) u(3))
  } note u_p12[simp] = this
  {fix c a assume c: "c \<in> supp P" and ac: "a \<in> sset c"
   hence "p1 a \<in> set1 c" unfolding sset_def by auto
  }note p1[simp] = this
  {fix c a assume c: "c \<in> supp P" and ac: "a \<in> sset c"
   hence "p2 a \<in> set2 c" unfolding sset_def by auto
  }note p2[simp] = this
  (*  *)
  {fix c assume c: "c \<in> supp P"
   hence "\<exists> M. (\<forall> b1 \<in> set1 c. setsum (\<lambda> b2. M (u c b1 b2)) (set2 c) = N1 b1) \<and>
               (\<forall> b2 \<in> set2 c. setsum (\<lambda> b1. M (u c b1 b2)) (set1 c) = N2 b2)"
   unfolding sset_def
   using matrix_count_finite[OF set1_NE[OF c] fin_set1[OF c]
                                set2_NE[OF c] fin_set2[OF c] inj[OF c] ss[OF c]] by auto
  }
  then obtain Ms where
  ss1: "\<And> c b1. \<lbrakk>c \<in> supp P; b1 \<in> set1 c\<rbrakk> \<Longrightarrow>
                   setsum (\<lambda> b2. Ms c (u c b1 b2)) (set2 c) = N1 b1" and
  ss2: "\<And> c b2. \<lbrakk>c \<in> supp P; b2 \<in> set2 c\<rbrakk> \<Longrightarrow>
                   setsum (\<lambda> b1. Ms c (u c b1 b2)) (set1 c) = N2 b2"
  by metis
  def SET \<equiv> "\<Union> c \<in> supp P. sset c"
  have fin_SET[simp]: "finite SET" unfolding SET_def apply(rule finite_UN_I) by auto
  have SET_A: "SET \<subseteq> A" unfolding SET_def using sset_A by auto
  have u_SET[simp]: "\<And> c b1 b2. \<lbrakk>c \<in> supp P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk> \<Longrightarrow> u c b1 b2 \<in> SET"
  unfolding SET_def sset_def by blast
  {fix c a assume c: "c \<in> supp P" and a: "a \<in> SET" and p1a: "p1 a \<in> set1 c"
   then obtain c' where c': "c' \<in> supp P" and ac': "a \<in> sset c'"
   unfolding SET_def by auto
   hence "p1 a \<in> set1 c'" unfolding sset_def by auto
   hence eq: "c = c'" using p1a c c' set1_disj by auto
   hence "a \<in> sset c" using ac' by simp
  } note p1_rev = this
  {fix c a assume c: "c \<in> supp P" and a: "a \<in> SET" and p2a: "p2 a \<in> set2 c"
   then obtain c' where c': "c' \<in> supp P" and ac': "a \<in> sset c'"
   unfolding SET_def by auto
   hence "p2 a \<in> set2 c'" unfolding sset_def by auto
   hence eq: "c = c'" using p2a c c' set2_disj by auto
   hence "a \<in> sset c" using ac' by simp
  } note p2_rev = this
  (*  *)
  have "\<forall> a \<in> SET. \<exists> c \<in> supp P. a \<in> sset c" unfolding SET_def by auto
  then obtain h where h: "\<forall> a \<in> SET. h a \<in> supp P \<and> a \<in> sset (h a)" by metis
  have h_u[simp]: "\<And> c b1 b2. \<lbrakk>c \<in> supp P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk>
                      \<Longrightarrow> h (u c b1 b2) = c"
  by (metis h p2 set2 u(3) u_SET)
  have h_u1: "\<And> c b1 b2. \<lbrakk>c \<in> supp P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk>
                      \<Longrightarrow> h (u c b1 b2) = f1 b1"
  using h unfolding sset_def by auto
  have h_u2: "\<And> c b1 b2. \<lbrakk>c \<in> supp P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk>
                      \<Longrightarrow> h (u c b1 b2) = f2 b2"
  using h unfolding sset_def by auto
  def M \<equiv> "\<lambda> a. if a \<in> SET \<and> p1 a \<in> supp N1 \<and> p2 a \<in> supp N2 then Ms (h a) a else 0"
  have sM: "supp M \<subseteq> SET" "supp M \<subseteq> p1 -` (supp N1)" "supp M \<subseteq> p2 -` (supp N2)"
  unfolding M_def by auto
  show "\<exists>M. (M \<in> multiset \<and> supp M \<subseteq> A) \<and> mmap p1 M = N1 \<and> mmap p2 M = N2"
  proof(rule exI[of _ M], safe)
    show "M \<in> multiset"
    unfolding multiset_def using finite_subset[OF sM(1) fin_SET] by simp
  next
    fix a assume "0 < M a"
    thus "a \<in> A" unfolding M_def using SET_A by (cases "a \<in> SET") auto
  next
    show "mmap p1 M = N1"
    unfolding mmap_def[abs_def] proof(rule ext)
      fix b1
      let ?K = "{a. p1 a = b1 \<and> 0 < M a}"
      show "setsum M ?K = N1 b1"
      proof(cases "b1 \<in> supp N1")
        case False
        hence "?K = {}" using sM(2) by auto
        thus ?thesis using False by auto
      next
        case True
        def c \<equiv> "f1 b1"
        have c: "c \<in> supp P" and b1: "b1 \<in> set1 c"
        unfolding set1_def c_def P1 using True by (auto simp: mmap_image)
        have "setsum M ?K = setsum M {a. p1 a = b1 \<and> a \<in> SET}"
        apply(rule setsum_mono_zero_cong_left) unfolding M_def by auto
        also have "... = setsum M ((\<lambda> b2. u c b1 b2) ` (set2 c))"
        apply(rule setsum_cong) using c b1 proof safe
          fix a assume p1a: "p1 a \<in> set1 c" and "0 < P c" and "a \<in> SET"
          hence ac: "a \<in> sset c" using p1_rev by auto
          hence "a = u c (p1 a) (p2 a)" using c by auto
          moreover have "p2 a \<in> set2 c" using ac c by auto
          ultimately show "a \<in> u c (p1 a) ` set2 c" by auto
        next
          fix b2 assume b1: "b1 \<in> set1 c" and b2: "b2 \<in> set2 c"
          hence "u c b1 b2 \<in> SET" using c by auto
        qed auto
        also have "... = setsum (\<lambda> b2. M (u c b1 b2)) (set2 c)"
        unfolding comp_def[symmetric] apply(rule setsum_reindex)
        using inj unfolding inj_on_def inj2_def using b1 c u(3) by blast
        also have "... = N1 b1" unfolding ss1[OF c b1, symmetric]
          apply(rule setsum_cong[OF refl]) unfolding M_def
          using True h_u[OF c b1] set2_def u(2,3)[OF c b1] u_SET[OF c b1] by fastforce
        finally show ?thesis .
      qed
    qed
  next
    show "mmap p2 M = N2"
    unfolding mmap_def[abs_def] proof(rule ext)
      fix b2
      let ?K = "{a. p2 a = b2 \<and> 0 < M a}"
      show "setsum M ?K = N2 b2"
      proof(cases "b2 \<in> supp N2")
        case False
        hence "?K = {}" using sM(3) by auto
        thus ?thesis using False by auto
      next
        case True
        def c \<equiv> "f2 b2"
        have c: "c \<in> supp P" and b2: "b2 \<in> set2 c"
        unfolding set2_def c_def P2 using True by (auto simp: mmap_image)
        have "setsum M ?K = setsum M {a. p2 a = b2 \<and> a \<in> SET}"
        apply(rule setsum_mono_zero_cong_left) unfolding M_def by auto
        also have "... = setsum M ((\<lambda> b1. u c b1 b2) ` (set1 c))"
        apply(rule setsum_cong) using c b2 proof safe
          fix a assume p2a: "p2 a \<in> set2 c" and "0 < P c" and "a \<in> SET"
          hence ac: "a \<in> sset c" using p2_rev by auto
          hence "a = u c (p1 a) (p2 a)" using c by auto
          moreover have "p1 a \<in> set1 c" using ac c by auto
          ultimately show "a \<in> (\<lambda>b1. u c b1 (p2 a)) ` set1 c" by auto
        next
          fix b2 assume b1: "b1 \<in> set1 c" and b2: "b2 \<in> set2 c"
          hence "u c b1 b2 \<in> SET" using c by auto
        qed auto
        also have "... = setsum (M o (\<lambda> b1. u c b1 b2)) (set1 c)"
        apply(rule setsum_reindex)
        using inj unfolding inj_on_def inj2_def using b2 c u(2) by blast
        also have "... = setsum (\<lambda> b1. M (u c b1 b2)) (set1 c)"
        unfolding comp_def[symmetric] by simp
        also have "... = N2 b2" unfolding ss2[OF c b2, symmetric]
          apply(rule setsum_cong[OF refl]) unfolding M_def set2_def
          using True h_u1[OF c _ b2] u(2,3)[OF c _ b2] u_SET[OF c _ b2]
          unfolding set1_def by fastforce
        finally show ?thesis .
      qed
    qed
  qed
qed

definition mset_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a multiset \<Rightarrow> 'b multiset" where
"mset_map h = Abs_multiset \<circ> mmap h \<circ> count"

bnf_def mset = mset_map [set_of] "\<lambda>_::'a multiset. natLeq" ["{#}"]
unfolding mset_map_def
proof -
  show "Abs_multiset \<circ> mmap id \<circ> count = id" unfolding mmap_id by (auto simp: count_inverse)
next
  fix f g
  show "Abs_multiset \<circ> mmap (g \<circ> f) \<circ> count =
        Abs_multiset \<circ> mmap g \<circ> count \<circ> (Abs_multiset \<circ> mmap f \<circ> count)"
  unfolding comp_def apply(rule ext)
  by (auto simp: Abs_multiset_inverse count mmap_comp1 mmap)
next
  fix M f g assume eq: "\<And>a. a \<in> set_of M \<Longrightarrow> f a = g a"
  thus "(Abs_multiset \<circ> mmap f \<circ> count) M = (Abs_multiset \<circ> mmap g \<circ> count) M" apply auto
  unfolding cIm_def[abs_def] image_def
  by (auto intro!: mmap_cong simp: Abs_multiset_inject count mmap)
next
  fix f show "set_of \<circ> (Abs_multiset \<circ> mmap f \<circ> count) = op ` f \<circ> set_of"
  by (auto simp: count mmap mmap_image set_of_Abs_multiset supp_count)
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix M show "|set_of M| \<le>o natLeq"
  apply(rule ordLess_imp_ordLeq)
  unfolding finite_iff_ordLess_natLeq[symmetric] using finite_set_of .
next
  fix A :: "'a set"
  have "|{M. set_of M \<subseteq> A}| \<le>o |{as. set as \<subseteq> A}|" using card_of_set_of .
  also have "|{as. set as \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq"
  by (rule list_in_bd)
  finally show "|{M. set_of M \<subseteq> A}| \<le>o ( |A| +c ctwo) ^c natLeq" .
next
  fix A B1 B2 f1 f2 p1 p2
  let ?map = "\<lambda> f. Abs_multiset \<circ> mmap f \<circ> count"
  assume wp: "wpull A B1 B2 f1 f2 p1 p2"
  show "wpull {x. set_of x \<subseteq> A} {x. set_of x \<subseteq> B1} {x. set_of x \<subseteq> B2}
              (?map f1) (?map f2) (?map p1) (?map p2)"
  unfolding wpull_def proof safe
    fix y1 y2
    assume y1: "set_of y1 \<subseteq> B1" and y2: "set_of y2 \<subseteq> B2"
    and m: "?map f1 y1 = ?map f2 y2"
    def N1 \<equiv> "count y1"  def N2 \<equiv> "count y2"
    have "N1 \<in> multiset \<and> supp N1 \<subseteq> B1" and "N2 \<in> multiset \<and> supp N2 \<subseteq> B2"
    and "mmap f1 N1 = mmap f2 N2"
    using y1 y2 m unfolding N1_def N2_def
    by (auto simp: Abs_multiset_inject count mmap)
    then obtain M where M: "M \<in> multiset \<and> supp M \<subseteq> A"
    and N1: "mmap p1 M = N1" and N2: "mmap p2 M = N2"
    using wp_mmap[OF wp] unfolding wpull_def by auto
    def x \<equiv> "Abs_multiset M"
    show "\<exists>x\<in>{x. set_of x \<subseteq> A}. ?map p1 x = y1 \<and> ?map p2 x = y2"
    apply(intro bexI[of _ x]) using M N1 N2 unfolding N1_def N2_def x_def
    by (auto simp: count_inverse Abs_multiset_inverse)
  qed
qed (unfold set_of_empty, auto)

end
