(*  Title:      HOL/HOLCF/Library/Option_Cpo.thy
    Author:     Brian Huffman
*)

header {* Cpo class instance for HOL option type *}

theory Option_Cpo
imports HOLCF Sum_Cpo
begin

subsection {* Ordering on option type *}

instantiation option :: (below) below
begin

definition below_option_def:
  "x \<sqsubseteq> y \<equiv> case x of
         None \<Rightarrow> (case y of None \<Rightarrow> True | Some b \<Rightarrow> False) |
         Some a \<Rightarrow> (case y of None \<Rightarrow> False | Some b \<Rightarrow> a \<sqsubseteq> b)"

instance ..
end

lemma None_below_None [simp]: "None \<sqsubseteq> None"
unfolding below_option_def by simp

lemma Some_below_Some [simp]: "Some x \<sqsubseteq> Some y \<longleftrightarrow> x \<sqsubseteq> y"
unfolding below_option_def by simp

lemma Some_below_None [simp]: "\<not> Some x \<sqsubseteq> None"
unfolding below_option_def by simp

lemma None_below_Some [simp]: "\<not> None \<sqsubseteq> Some y"
unfolding below_option_def by simp

lemma Some_mono: "x \<sqsubseteq> y \<Longrightarrow> Some x \<sqsubseteq> Some y"
by simp

lemma None_below_iff [simp]: "None \<sqsubseteq> x \<longleftrightarrow> x = None"
by (cases x, simp_all)

lemma below_None_iff [simp]: "x \<sqsubseteq> None \<longleftrightarrow> x = None"
by (cases x, simp_all)

lemma option_below_cases:
  assumes "x \<sqsubseteq> y"
  obtains "x = None" and "y = None"
  | a b where "x = Some a" and "y = Some b" and "a \<sqsubseteq> b"
using assms unfolding below_option_def
by (simp split: option.split_asm)

subsection {* Option type is a complete partial order *}

instance option :: (po) po
proof
  fix x :: "'a option"
  show "x \<sqsubseteq> x"
    unfolding below_option_def
    by (simp split: option.split)
next
  fix x y :: "'a option"
  assume "x \<sqsubseteq> y" and "y \<sqsubseteq> x" thus "x = y"
    unfolding below_option_def
    by (auto split: option.split_asm intro: below_antisym)
next
  fix x y z :: "'a option"
  assume "x \<sqsubseteq> y" and "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    unfolding below_option_def
    by (auto split: option.split_asm intro: below_trans)
qed

lemma monofun_the: "monofun the"
by (rule monofunI, erule option_below_cases, simp_all)

lemma option_chain_cases:
  assumes Y: "chain Y"
  obtains "Y = (\<lambda>i. None)" | A where "chain A" and "Y = (\<lambda>i. Some (A i))"
 apply (cases "Y 0")
  apply (rule that(1))
  apply (rule ext)
  apply (cut_tac j=i in chain_mono [OF Y le0], simp)
 apply (rule that(2))
  apply (rule ch2ch_monofun [OF monofun_the Y])
 apply (rule ext)
 apply (cut_tac j=i in chain_mono [OF Y le0], simp)
 apply (case_tac "Y i", simp_all)
done

lemma is_lub_Some: "range S <<| x \<Longrightarrow> range (\<lambda>i. Some (S i)) <<| Some x"
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (simp add: is_lub_rangeD1)
 apply (frule ub_rangeD [where i=arbitrary])
 apply (case_tac u, simp_all)
 apply (erule is_lubD2)
 apply (rule ub_rangeI)
 apply (drule ub_rangeD, simp)
done

instance option :: (cpo) cpo
 apply intro_classes
 apply (erule option_chain_cases, safe)
  apply (rule exI, rule is_lub_const)
 apply (rule exI)
 apply (rule is_lub_Some)
 apply (erule cpo_lubI)
done

subsection {* Continuity of Some and case function *}

lemma cont_Some: "cont Some"
by (intro contI is_lub_Some cpo_lubI)

lemmas cont2cont_Some [simp, cont2cont] = cont_compose [OF cont_Some]

lemmas ch2ch_Some [simp] = ch2ch_cont [OF cont_Some]

lemmas lub_Some = cont2contlubE [OF cont_Some, symmetric]

lemma cont2cont_case_option:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h1: "\<And>a. cont (\<lambda>x. h x a)"
  assumes h2: "\<And>x. cont (\<lambda>a. h x a)"
  shows "cont (\<lambda>x. case f x of None \<Rightarrow> g x | Some a \<Rightarrow> h x a)"
apply (rule cont_apply [OF f])
apply (rule contI)
apply (erule option_chain_cases)
apply (simp add: is_lub_const)
apply (simp add: lub_Some)
apply (simp add: cont2contlubE [OF h2])
apply (rule cpo_lubI, rule chainI)
apply (erule cont2monofunE [OF h2 chainE])
apply (case_tac y, simp_all add: g h1)
done

lemma cont2cont_case_option' [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h: "cont (\<lambda>p. h (fst p) (snd p))"
  shows "cont (\<lambda>x. case f x of None \<Rightarrow> g x | Some a \<Rightarrow> h x a)"
using assms by (simp add: cont2cont_case_option prod_cont_iff)

text {* Simple version for when the element type is not a cpo. *}

lemma cont2cont_case_option_simple [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)"
  assumes "\<And>a. cont (\<lambda>x. g x a)"
  shows "cont (\<lambda>x. case z of None \<Rightarrow> f x | Some a \<Rightarrow> g x a)"
using assms by (cases z) auto

text {* Continuity rule for map. *}

lemma cont2cont_map_option [simp, cont2cont]:
  assumes f: "cont (\<lambda>(x, y). f x y)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. map_option (\<lambda>y. f x y) (g x))"
using assms by (simp add: prod_cont_iff map_option_case)

subsection {* Compactness and chain-finiteness *}

lemma compact_None [simp]: "compact None"
apply (rule compactI2)
apply (erule option_chain_cases, safe)
apply simp
apply (simp add: lub_Some)
done

lemma compact_Some: "compact a \<Longrightarrow> compact (Some a)"
apply (rule compactI2)
apply (erule option_chain_cases, safe)
apply simp
apply (simp add: lub_Some)
apply (erule (2) compactD2)
done

lemma compact_Some_rev: "compact (Some a) \<Longrightarrow> compact a"
unfolding compact_def
by (drule adm_subst [OF cont_Some], simp)

lemma compact_Some_iff [simp]: "compact (Some a) = compact a"
by (safe elim!: compact_Some compact_Some_rev)

instance option :: (chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (case_tac "\<Squnion>i. Y i", simp_all)
done

instance option :: (discrete_cpo) discrete_cpo
by intro_classes (simp add: below_option_def split: option.split)

subsection {* Using option types with Fixrec *}

definition
  "match_None = (\<Lambda> x k. case x of None \<Rightarrow> k | Some a \<Rightarrow> Fixrec.fail)"

definition
  "match_Some = (\<Lambda> x k. case x of None \<Rightarrow> Fixrec.fail | Some a \<Rightarrow> k\<cdot>a)"

lemma match_None_simps [simp]:
  "match_None\<cdot>None\<cdot>k = k"
  "match_None\<cdot>(Some a)\<cdot>k = Fixrec.fail"
unfolding match_None_def by simp_all

lemma match_Some_simps [simp]:
  "match_Some\<cdot>None\<cdot>k = Fixrec.fail"
  "match_Some\<cdot>(Some a)\<cdot>k = k\<cdot>a"
unfolding match_Some_def by simp_all

setup {*
  Fixrec.add_matchers
    [ (@{const_name None}, @{const_name match_None}),
      (@{const_name Some}, @{const_name match_Some}) ]
*}

subsection {* Option type is a predomain *}

definition
  "encode_option = (\<Lambda> x. case x of None \<Rightarrow> Inl () | Some a \<Rightarrow> Inr a)"

definition
  "decode_option = (\<Lambda> x. case x of Inl (u::unit) \<Rightarrow> None | Inr a \<Rightarrow> Some a)"

lemma decode_encode_option [simp]: "decode_option\<cdot>(encode_option\<cdot>x) = x"
unfolding decode_option_def encode_option_def
by (cases x, simp_all)

lemma encode_decode_option [simp]: "encode_option\<cdot>(decode_option\<cdot>x) = x"
unfolding decode_option_def encode_option_def
by (cases x, simp_all)

instantiation option :: (predomain) predomain
begin

definition
  "liftemb = liftemb oo u_map\<cdot>encode_option"

definition
  "liftprj = u_map\<cdot>decode_option oo liftprj"

definition
  "liftdefl (t::('a option) itself) = LIFTDEFL(unit + 'a)"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> ('a option) u)"
    unfolding liftemb_option_def liftprj_option_def
    apply (intro ep_pair_comp ep_pair_u_map predomain_ep)
    apply (rule ep_pair.intro, simp, simp)
    done
  show "cast\<cdot>LIFTDEFL('a option) = liftemb oo (liftprj :: udom u \<rightarrow> ('a option) u)"
    unfolding liftemb_option_def liftprj_option_def liftdefl_option_def
    by (simp add: cast_liftdefl cfcomp1 u_map_map ID_def [symmetric] u_map_ID)
qed

end

subsection {* Configuring domain package to work with option type *}

lemma liftdefl_option [domain_defl_simps]:
  "LIFTDEFL('a::predomain option) = LIFTDEFL(unit + 'a)"
by (rule liftdefl_option_def)

abbreviation option_map
  where "option_map f \<equiv> Abs_cfun (map_option (Rep_cfun f))"

lemma option_map_ID [domain_map_ID]: "option_map ID = ID"
by (simp add: ID_def cfun_eq_iff option.map_id[unfolded id_def] id_def)

lemma deflation_option_map [domain_deflation]:
  "deflation d \<Longrightarrow> deflation (option_map d)"
apply default
apply (induct_tac x, simp_all add: deflation.idem)
apply (induct_tac x, simp_all add: deflation.below)
done

lemma encode_option_option_map:
  "encode_option\<cdot>(map_option (\<lambda>x. f\<cdot>x) (decode_option\<cdot>x)) = map_sum' ID f\<cdot>x"
by (induct x, simp_all add: decode_option_def encode_option_def)

lemma isodefl_option [domain_isodefl]:
  assumes "isodefl' d t"
  shows "isodefl' (option_map d) (sum_liftdefl\<cdot>(liftdefl_of\<cdot>DEFL(unit))\<cdot>t)"
using isodefl_sum [OF isodefl_LIFTDEFL [where 'a=unit] assms]
unfolding isodefl'_def liftemb_option_def liftprj_option_def liftdefl_eq
by (simp add: cfcomp1 u_map_map encode_option_option_map)

setup {*
  Domain_Take_Proofs.add_rec_type (@{type_name "option"}, [true])
*}

end
