(*  Title:      HOL/Cardinals/Bounded_Set.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2015

Bounded powerset type.
*)

section \<open>Sets Strictly Bounded by an Infinite Cardinal\<close>

theory Bounded_Set
imports Cardinals
begin

typedef ('a, 'k) bset (\<open>_ set[_]\<close> [22, 21] 21) =
  "{A :: 'a set. |A| <o natLeq +c |UNIV :: 'k set|}"
  morphisms set_bset Abs_bset
  by (rule exI[of _ "{}"]) (auto simp: card_of_empty4 csum_def)

setup_lifting type_definition_bset

lift_definition map_bset ::
  "('a \<Rightarrow> 'b) \<Rightarrow> 'a set['k] \<Rightarrow> 'b set['k]" is image
  using card_of_image ordLeq_ordLess_trans by blast

lift_definition rel_bset ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set['k] \<Rightarrow> 'b set['k] \<Rightarrow> bool" is rel_set
  .

lift_definition bempty :: "'a set['k]" is "{}"
  by (auto simp: card_of_empty4 csum_def)

lift_definition binsert :: "'a \<Rightarrow> 'a set['k] \<Rightarrow> 'a set['k]" is "insert"
  using infinite_card_of_insert ordIso_ordLess_trans Field_card_of Field_natLeq UNIV_Plus_UNIV
   csum_def finite_Plus_UNIV_iff finite_insert finite_ordLess_infinite2 infinite_UNIV_nat by metis

definition bsingleton where
  "bsingleton x = binsert x bempty"

lemma set_bset_to_set_bset: "|A| <o natLeq +c |UNIV :: 'k set| \<Longrightarrow>
  set_bset (the_inv set_bset A :: 'a set['k]) = A"
  apply (rule f_the_inv_into_f[unfolded inj_on_def])
  apply (simp add: set_bset_inject range_eqI Abs_bset_inverse[symmetric])
  apply (rule range_eqI Abs_bset_inverse[symmetric] CollectI)+
  .

lemma rel_bset_aux_infinite:
  fixes a :: "'a set['k]" and b :: "'b set['k]"
  shows "(\<forall>t \<in> set_bset a. \<exists>u \<in> set_bset b. R t u) \<and> (\<forall>u \<in> set_bset b. \<exists>t \<in> set_bset a. R t u) \<longleftrightarrow>
   ((BNF_Def.Grp {a. set_bset a \<subseteq> {(a, b). R a b}} (map_bset fst))\<inverse>\<inverse> OO
    BNF_Def.Grp {a. set_bset a \<subseteq> {(a, b). R a b}} (map_bset snd)) a b" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  define R' :: "('a \<times> 'b) set['k]"
    where "R' = the_inv set_bset (Collect (case_prod R) \<inter> (set_bset a \<times> set_bset b))"
      (is "_ = the_inv set_bset ?L'")
  have "|?L'| <o natLeq +c |UNIV :: 'k set|"
    unfolding csum_def Field_natLeq
    by (intro ordLeq_ordLess_trans[OF card_of_mono1[OF Int_lower2]]
      card_of_Times_ordLess_infinite)
      (simp, (transfer, simp add: csum_def Field_natLeq)+)
  hence *: "set_bset R' = ?L'" unfolding R'_def by (intro set_bset_to_set_bset)
  show ?R unfolding Grp_def relcompp.simps conversep.simps
  proof (intro CollectI case_prodI exI[of _ a] exI[of _ b] exI[of _ R'] conjI refl)
    from * show "a = map_bset fst R'" using conjunct1[OF \<open>?L\<close>]
      by (transfer, auto simp add: image_def Int_def split: prod.splits)
    from * show "b = map_bset snd R'" using conjunct2[OF \<open>?L\<close>]
      by (transfer, auto simp add: image_def Int_def split: prod.splits)
  qed (auto simp add: *)
next
  assume ?R thus ?L unfolding Grp_def relcompp.simps conversep.simps
    by transfer force
qed

bnf "'a set['k]"
  map: map_bset
  sets: set_bset
  bd: "natLeq +c card_suc |UNIV :: 'k set|"
  wits: bempty
  rel: rel_bset
proof -
  show "map_bset id = id" by (rule ext, transfer) simp
next
  fix f g
  show "map_bset (f o g) = map_bset f o map_bset g" by (rule ext, transfer) auto
next
  fix X f g
  assume "\<And>z. z \<in> set_bset X \<Longrightarrow> f z = g z"
  then show "map_bset f X = map_bset g X" by transfer force
next
  fix f
  show "set_bset \<circ> map_bset f = (`) f \<circ> set_bset" by (rule ext, transfer) auto
next
  fix X :: "'a set['k]"
  have "|set_bset X| <o natLeq +c |UNIV :: 'k set|" by transfer blast
  then show "|set_bset X| <o natLeq +c card_suc |UNIV :: 'k set|"
    by (rule ordLess_ordLeq_trans[OF _ csum_mono2[OF ordLess_imp_ordLeq[OF card_suc_greater[OF card_of_card_order_on]]]])
next
  fix R S
  show "rel_bset R OO rel_bset S \<le> rel_bset (R OO S)"
    by (rule predicate2I, transfer) (auto simp: rel_set_OO[symmetric])
next
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  show "rel_bset R = ((\<lambda>x y. \<exists>z. set_bset z \<subseteq> {(x, y). R x y} \<and>
    map_bset fst z = x \<and> map_bset snd z = y) :: 'a set['k] \<Rightarrow> 'b set['k] \<Rightarrow> bool)"
    by (simp add: rel_bset_def map_fun_def o_def rel_set_def
      rel_bset_aux_infinite[unfolded OO_Grp_alt])
next
  fix x
  assume "x \<in> set_bset bempty"
  then show False by transfer simp
qed (simp_all add: card_order_bd_fun Cinfinite_bd_fun regularCard_bd_fun)


lemma map_bset_bempty[simp]: "map_bset f bempty = bempty"
  by transfer auto

lemma map_bset_binsert[simp]: "map_bset f (binsert x X) = binsert (f x) (map_bset f X)"
  by transfer auto

lemma map_bset_bsingleton: "map_bset f (bsingleton x) = bsingleton (f x)"
  unfolding bsingleton_def by simp

lemma bempty_not_binsert: "bempty \<noteq> binsert x X" "binsert x X \<noteq> bempty"
  by (transfer, auto)+

lemma bempty_not_bsingleton[simp]: "bempty \<noteq> bsingleton x" "bsingleton x \<noteq> bempty"
  unfolding bsingleton_def by (simp_all add: bempty_not_binsert)

lemma bsingleton_inj[simp]: "bsingleton x = bsingleton y \<longleftrightarrow> x = y"
  unfolding bsingleton_def by transfer auto

lemma rel_bsingleton[simp]:
  "rel_bset R (bsingleton x1) (bsingleton x2) = R x1 x2"
  unfolding bsingleton_def
  by transfer (auto simp: rel_set_def)

lemma rel_bset_bsingleton[simp]:
  "rel_bset R (bsingleton x1) = (\<lambda>X. X \<noteq> bempty \<and> (\<forall>x2\<in>set_bset X. R x1 x2))"
  "rel_bset R X (bsingleton x2) = (X \<noteq> bempty \<and> (\<forall>x1\<in>set_bset X. R x1 x2))"
  unfolding bsingleton_def fun_eq_iff
  by (transfer, force simp add: rel_set_def)+

lemma rel_bset_bempty[simp]:
  "rel_bset R bempty X = (X = bempty)"
  "rel_bset R Y bempty = (Y = bempty)"
  by (transfer, simp add: rel_set_def)+

definition bset_of_option where
  "bset_of_option = case_option bempty bsingleton"

lift_definition bgraph :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<times> 'b) set['a set]" is
  "\<lambda>f. {(a, b). f a = Some b}"
proof -
  fix f :: "'a \<Rightarrow> 'b option"
  have "|{(a, b). f a = Some b}| \<le>o |UNIV :: 'a set|"
    by (rule surj_imp_ordLeq[of _ "\<lambda>x. (x, the (f x))"]) auto
  also have "|UNIV :: 'a set| <o |UNIV :: 'a set set|"
    by simp
  also have "|UNIV :: 'a set set| \<le>o natLeq +c |UNIV :: 'a set set|"
    by (rule ordLeq_csum2) simp
  finally show "|{(a, b). f a = Some b}| <o natLeq +c |UNIV :: 'a set set|" .
qed

lemma rel_bset_False[simp]: "rel_bset (\<lambda>x y. False) x y = (x = bempty \<and> y = bempty)"
  by transfer (auto simp: rel_set_def)

lemma rel_bset_of_option[simp]:
  "rel_bset R (bset_of_option x1) (bset_of_option x2) = rel_option R x1 x2"
  unfolding bset_of_option_def bsingleton_def[abs_def]
  by transfer (auto simp: rel_set_def split: option.splits)

lemma rel_bgraph[simp]:
  "rel_bset (rel_prod (=) R) (bgraph f1) (bgraph f2) = rel_fun (=) (rel_option R) f1 f2"
  apply transfer
  apply (auto simp: rel_fun_def rel_option_iff rel_set_def split: option.splits)
  using option.collapse apply fastforce+
  done

lemma set_bset_bsingleton[simp]:
  "set_bset (bsingleton x) = {x}"
  unfolding bsingleton_def by transfer auto

lemma binsert_absorb[simp]: "binsert a (binsert a x) = binsert a x"
  by transfer simp

lemma map_bset_eq_bempty_iff[simp]: "map_bset f X = bempty \<longleftrightarrow> X = bempty"
  by transfer auto

lemma map_bset_eq_bsingleton_iff[simp]:
  "map_bset f X = bsingleton x \<longleftrightarrow> (set_bset X \<noteq> {} \<and> (\<forall>y \<in> set_bset X. f y = x))"
  unfolding bsingleton_def by transfer auto

lift_definition bCollect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set['a set]" is Collect
  apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF subset_UNIV]])
  apply (rule ordLess_ordLeq_trans[OF card_of_set_type])
  apply (rule ordLeq_csum2[OF card_of_Card_order])
  done

lift_definition bmember :: "'a \<Rightarrow> 'a set['k] \<Rightarrow> bool" is "(\<in>)" .

lemma bmember_bCollect[simp]: "bmember a (bCollect P) = P a"
  by transfer simp

lemma bset_eq_iff: "A = B \<longleftrightarrow> (\<forall>a. bmember a A = bmember a B)"
  by transfer auto

(* FIXME: Lifting does not work with dead variables,
   that is why we are hiding the below setup in a locale*)
locale bset_lifting
begin

declare bset.rel_eq[relator_eq]
declare bset.rel_mono[relator_mono]
declare bset.rel_compp[symmetric, relator_distr]
declare bset.rel_transfer[transfer_rule]

lemma bset_quot_map[quot_map]: "Quotient R Abs Rep T \<Longrightarrow>
  Quotient (rel_bset R) (map_bset Abs) (map_bset Rep) (rel_bset T)"
  unfolding Quotient_alt_def5 bset.rel_Grp[of UNIV, simplified, symmetric]
    bset.rel_conversep[symmetric] bset.rel_compp[symmetric]
    by (auto elim: bset.rel_mono_strong)

lemma set_relator_eq_onp [relator_eq_onp]:
  "rel_bset (eq_onp P) = eq_onp (\<lambda>A. Ball (set_bset A) P)"
  unfolding fun_eq_iff eq_onp_def by transfer (auto simp: rel_set_def)

end

end
