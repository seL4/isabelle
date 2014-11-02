(*  Title:      HOL/HOLCF/Library/Sum_Cpo.thy
    Author:     Brian Huffman
*)

section {* The cpo of disjoint sums *}

theory Sum_Cpo
imports HOLCF
begin

subsection {* Ordering on sum type *}

instantiation sum :: (below, below) below
begin

definition below_sum_def:
  "x \<sqsubseteq> y \<equiv> case x of
         Inl a \<Rightarrow> (case y of Inl b \<Rightarrow> a \<sqsubseteq> b | Inr b \<Rightarrow> False) |
         Inr a \<Rightarrow> (case y of Inl b \<Rightarrow> False | Inr b \<Rightarrow> a \<sqsubseteq> b)"

instance ..
end

lemma Inl_below_Inl [simp]: "Inl x \<sqsubseteq> Inl y \<longleftrightarrow> x \<sqsubseteq> y"
unfolding below_sum_def by simp

lemma Inr_below_Inr [simp]: "Inr x \<sqsubseteq> Inr y \<longleftrightarrow> x \<sqsubseteq> y"
unfolding below_sum_def by simp

lemma Inl_below_Inr [simp]: "\<not> Inl x \<sqsubseteq> Inr y"
unfolding below_sum_def by simp

lemma Inr_below_Inl [simp]: "\<not> Inr x \<sqsubseteq> Inl y"
unfolding below_sum_def by simp

lemma Inl_mono: "x \<sqsubseteq> y \<Longrightarrow> Inl x \<sqsubseteq> Inl y"
by simp

lemma Inr_mono: "x \<sqsubseteq> y \<Longrightarrow> Inr x \<sqsubseteq> Inr y"
by simp

lemma Inl_belowE: "\<lbrakk>Inl a \<sqsubseteq> x; \<And>b. \<lbrakk>x = Inl b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (cases x, simp_all)

lemma Inr_belowE: "\<lbrakk>Inr a \<sqsubseteq> x; \<And>b. \<lbrakk>x = Inr b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (cases x, simp_all)

lemmas sum_below_elims = Inl_belowE Inr_belowE

lemma sum_below_cases:
  "\<lbrakk>x \<sqsubseteq> y;
    \<And>a b. \<lbrakk>x = Inl a; y = Inl b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow> R;
    \<And>a b. \<lbrakk>x = Inr a; y = Inr b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow> R\<rbrakk>
      \<Longrightarrow> R"
by (cases x, safe elim!: sum_below_elims, auto)

subsection {* Sum type is a complete partial order *}

instance sum :: (po, po) po
proof
  fix x :: "'a + 'b"
  show "x \<sqsubseteq> x"
    by (induct x, simp_all)
next
  fix x y :: "'a + 'b"
  assume "x \<sqsubseteq> y" and "y \<sqsubseteq> x" thus "x = y"
    by (induct x, auto elim!: sum_below_elims intro: below_antisym)
next
  fix x y z :: "'a + 'b"
  assume "x \<sqsubseteq> y" and "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    by (induct x, auto elim!: sum_below_elims intro: below_trans)
qed

lemma monofun_inv_Inl: "monofun (\<lambda>p. THE a. p = Inl a)"
by (rule monofunI, erule sum_below_cases, simp_all)

lemma monofun_inv_Inr: "monofun (\<lambda>p. THE b. p = Inr b)"
by (rule monofunI, erule sum_below_cases, simp_all)

lemma sum_chain_cases:
  assumes Y: "chain Y"
  assumes A: "\<And>A. \<lbrakk>chain A; Y = (\<lambda>i. Inl (A i))\<rbrakk> \<Longrightarrow> R"
  assumes B: "\<And>B. \<lbrakk>chain B; Y = (\<lambda>i. Inr (B i))\<rbrakk> \<Longrightarrow> R"
  shows "R"
 apply (cases "Y 0")
  apply (rule A)
   apply (rule ch2ch_monofun [OF monofun_inv_Inl Y])
  apply (rule ext)
  apply (cut_tac j=i in chain_mono [OF Y le0], simp)
  apply (erule Inl_belowE, simp)
 apply (rule B)
  apply (rule ch2ch_monofun [OF monofun_inv_Inr Y])
 apply (rule ext)
 apply (cut_tac j=i in chain_mono [OF Y le0], simp)
 apply (erule Inr_belowE, simp)
done

lemma is_lub_Inl: "range S <<| x \<Longrightarrow> range (\<lambda>i. Inl (S i)) <<| Inl x"
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (simp add: is_lub_rangeD1)
 apply (frule ub_rangeD [where i=arbitrary])
 apply (erule Inl_belowE, simp)
 apply (erule is_lubD2)
 apply (rule ub_rangeI)
 apply (drule ub_rangeD, simp)
done

lemma is_lub_Inr: "range S <<| x \<Longrightarrow> range (\<lambda>i. Inr (S i)) <<| Inr x"
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (simp add: is_lub_rangeD1)
 apply (frule ub_rangeD [where i=arbitrary])
 apply (erule Inr_belowE, simp)
 apply (erule is_lubD2)
 apply (rule ub_rangeI)
 apply (drule ub_rangeD, simp)
done

instance sum :: (cpo, cpo) cpo
 apply intro_classes
 apply (erule sum_chain_cases, safe)
  apply (rule exI)
  apply (rule is_lub_Inl)
  apply (erule cpo_lubI)
 apply (rule exI)
 apply (rule is_lub_Inr)
 apply (erule cpo_lubI)
done

subsection {* Continuity of \emph{Inl}, \emph{Inr}, and case function *}

lemma cont_Inl: "cont Inl"
by (intro contI is_lub_Inl cpo_lubI)

lemma cont_Inr: "cont Inr"
by (intro contI is_lub_Inr cpo_lubI)

lemmas cont2cont_Inl [simp, cont2cont] = cont_compose [OF cont_Inl]
lemmas cont2cont_Inr [simp, cont2cont] = cont_compose [OF cont_Inr]

lemmas ch2ch_Inl [simp] = ch2ch_cont [OF cont_Inl]
lemmas ch2ch_Inr [simp] = ch2ch_cont [OF cont_Inr]

lemmas lub_Inl = cont2contlubE [OF cont_Inl, symmetric]
lemmas lub_Inr = cont2contlubE [OF cont_Inr, symmetric]

lemma cont_case_sum1:
  assumes f: "\<And>a. cont (\<lambda>x. f x a)"
  assumes g: "\<And>b. cont (\<lambda>x. g x b)"
  shows "cont (\<lambda>x. case y of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b)"
by (induct y, simp add: f, simp add: g)

lemma cont_case_sum2: "\<lbrakk>cont f; cont g\<rbrakk> \<Longrightarrow> cont (case_sum f g)"
apply (rule contI)
apply (erule sum_chain_cases)
apply (simp add: cont2contlubE [OF cont_Inl, symmetric] contE)
apply (simp add: cont2contlubE [OF cont_Inr, symmetric] contE)
done

lemma cont2cont_case_sum:
  assumes f1: "\<And>a. cont (\<lambda>x. f x a)" and f2: "\<And>x. cont (\<lambda>a. f x a)"
  assumes g1: "\<And>b. cont (\<lambda>x. g x b)" and g2: "\<And>x. cont (\<lambda>b. g x b)"
  assumes h: "cont (\<lambda>x. h x)"
  shows "cont (\<lambda>x. case h x of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b)"
apply (rule cont_apply [OF h])
apply (rule cont_case_sum2 [OF f2 g2])
apply (rule cont_case_sum1 [OF f1 g1])
done

lemma cont2cont_case_sum' [simp, cont2cont]:
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  assumes g: "cont (\<lambda>p. g (fst p) (snd p))"
  assumes h: "cont (\<lambda>x. h x)"
  shows "cont (\<lambda>x. case h x of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b)"
using assms by (simp add: cont2cont_case_sum prod_cont_iff)

text {* Continuity of map function. *}

lemma map_sum_eq: "map_sum f g = case_sum (\<lambda>a. Inl (f a)) (\<lambda>b. Inr (g b))"
by (rule ext, case_tac x, simp_all)

lemma cont2cont_map_sum [simp, cont2cont]:
  assumes f: "cont (\<lambda>(x, y). f x y)"
  assumes g: "cont (\<lambda>(x, y). g x y)"
  assumes h: "cont (\<lambda>x. h x)"
  shows "cont (\<lambda>x. map_sum (\<lambda>y. f x y) (\<lambda>y. g x y) (h x))"
using assms by (simp add: map_sum_eq prod_cont_iff)

subsection {* Compactness and chain-finiteness *}

lemma compact_Inl: "compact a \<Longrightarrow> compact (Inl a)"
apply (rule compactI2)
apply (erule sum_chain_cases, safe)
apply (simp add: lub_Inl)
apply (erule (2) compactD2)
apply (simp add: lub_Inr)
done

lemma compact_Inr: "compact a \<Longrightarrow> compact (Inr a)"
apply (rule compactI2)
apply (erule sum_chain_cases, safe)
apply (simp add: lub_Inl)
apply (simp add: lub_Inr)
apply (erule (2) compactD2)
done

lemma compact_Inl_rev: "compact (Inl a) \<Longrightarrow> compact a"
unfolding compact_def
by (drule adm_subst [OF cont_Inl], simp)

lemma compact_Inr_rev: "compact (Inr a) \<Longrightarrow> compact a"
unfolding compact_def
by (drule adm_subst [OF cont_Inr], simp)

lemma compact_Inl_iff [simp]: "compact (Inl a) = compact a"
by (safe elim!: compact_Inl compact_Inl_rev)

lemma compact_Inr_iff [simp]: "compact (Inr a) = compact a"
by (safe elim!: compact_Inr compact_Inr_rev)

instance sum :: (chfin, chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (case_tac "\<Squnion>i. Y i", simp_all)
done

instance sum :: (discrete_cpo, discrete_cpo) discrete_cpo
by intro_classes (simp add: below_sum_def split: sum.split)

subsection {* Using sum types with fixrec *}

definition
  "match_Inl = (\<Lambda> x k. case x of Inl a \<Rightarrow> k\<cdot>a | Inr b \<Rightarrow> Fixrec.fail)"

definition
  "match_Inr = (\<Lambda> x k. case x of Inl a \<Rightarrow> Fixrec.fail | Inr b \<Rightarrow> k\<cdot>b)"

lemma match_Inl_simps [simp]:
  "match_Inl\<cdot>(Inl a)\<cdot>k = k\<cdot>a"
  "match_Inl\<cdot>(Inr b)\<cdot>k = Fixrec.fail"
unfolding match_Inl_def by simp_all

lemma match_Inr_simps [simp]:
  "match_Inr\<cdot>(Inl a)\<cdot>k = Fixrec.fail"
  "match_Inr\<cdot>(Inr b)\<cdot>k = k\<cdot>b"
unfolding match_Inr_def by simp_all

setup {*
  Fixrec.add_matchers
    [ (@{const_name Inl}, @{const_name match_Inl}),
      (@{const_name Inr}, @{const_name match_Inr}) ]
*}

subsection {* Disjoint sum is a predomain *}

definition
  "encode_sum_u =
    (\<Lambda>(up\<cdot>x). case x of Inl a \<Rightarrow> sinl\<cdot>(up\<cdot>a) | Inr b \<Rightarrow> sinr\<cdot>(up\<cdot>b))"

definition
  "decode_sum_u = sscase\<cdot>(\<Lambda>(up\<cdot>a). up\<cdot>(Inl a))\<cdot>(\<Lambda>(up\<cdot>b). up\<cdot>(Inr b))"

lemma decode_encode_sum_u [simp]: "decode_sum_u\<cdot>(encode_sum_u\<cdot>x) = x"
unfolding decode_sum_u_def encode_sum_u_def
by (case_tac x, simp, rename_tac y, case_tac y, simp_all)

lemma encode_decode_sum_u [simp]: "encode_sum_u\<cdot>(decode_sum_u\<cdot>x) = x"
unfolding decode_sum_u_def encode_sum_u_def
apply (case_tac x, simp)
apply (rename_tac a, case_tac a, simp, simp)
apply (rename_tac b, case_tac b, simp, simp)
done

text {* A deflation combinator for making unpointed types *}

definition udefl :: "udom defl \<rightarrow> udom u defl"
  where "udefl = defl_fun1 (strictify\<cdot>up) (fup\<cdot>ID) ID"

lemma ep_pair_strictify_up:
  "ep_pair (strictify\<cdot>up) (fup\<cdot>ID)"
apply (rule ep_pair.intro)
apply (simp add: strictify_conv_if)
apply (case_tac y, simp, simp add: strictify_conv_if)
done

lemma cast_udefl:
  "cast\<cdot>(udefl\<cdot>t) = strictify\<cdot>up oo cast\<cdot>t oo fup\<cdot>ID"
unfolding udefl_def by (simp add: cast_defl_fun1 ep_pair_strictify_up)

definition sum_liftdefl :: "udom u defl \<rightarrow> udom u defl \<rightarrow> udom u defl"
  where "sum_liftdefl = (\<Lambda> a b. udefl\<cdot>(ssum_defl\<cdot>(u_liftdefl\<cdot>a)\<cdot>(u_liftdefl\<cdot>b)))"

lemma u_emb_bottom: "u_emb\<cdot>\<bottom> = \<bottom>"
by (rule pcpo_ep_pair.e_strict [unfolded pcpo_ep_pair_def, OF ep_pair_u])

(*
definition sum_liftdefl :: "udom u defl \<rightarrow> udom u defl \<rightarrow> udom u defl"
  where "sum_liftdefl = defl_fun2 (u_map\<cdot>emb oo strictify\<cdot>up)
    (fup\<cdot>ID oo u_map\<cdot>prj) ssum_map"
*)

instantiation sum :: (predomain, predomain) predomain
begin

definition
  "liftemb = (strictify\<cdot>up oo ssum_emb) oo
    (ssum_map\<cdot>(u_emb oo liftemb)\<cdot>(u_emb oo liftemb) oo encode_sum_u)"

definition
  "liftprj = (decode_sum_u oo ssum_map\<cdot>(liftprj oo u_prj)\<cdot>(liftprj oo u_prj))
    oo (ssum_prj oo fup\<cdot>ID)"

definition
  "liftdefl (t::('a + 'b) itself) = sum_liftdefl\<cdot>LIFTDEFL('a)\<cdot>LIFTDEFL('b)"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> ('a + 'b) u)"
    unfolding liftemb_sum_def liftprj_sum_def
    by (intro ep_pair_comp ep_pair_ssum_map ep_pair_u predomain_ep
      ep_pair_ssum ep_pair_strictify_up, simp add: ep_pair.intro)
  show "cast\<cdot>LIFTDEFL('a + 'b) = liftemb oo (liftprj :: udom u \<rightarrow> ('a + 'b) u)"
    unfolding liftemb_sum_def liftprj_sum_def liftdefl_sum_def
    by (simp add: sum_liftdefl_def cast_udefl cast_ssum_defl cast_u_liftdefl
      cast_liftdefl cfcomp1 ssum_map_map u_emb_bottom)
qed

end

subsection {* Configuring domain package to work with sum type *}

lemma liftdefl_sum [domain_defl_simps]:
  "LIFTDEFL('a::predomain + 'b::predomain) =
    sum_liftdefl\<cdot>LIFTDEFL('a)\<cdot>LIFTDEFL('b)"
by (rule liftdefl_sum_def)

abbreviation map_sum'
  where "map_sum' f g \<equiv> Abs_cfun (map_sum (Rep_cfun f) (Rep_cfun g))"

lemma map_sum_ID [domain_map_ID]: "map_sum' ID ID = ID"
by (simp add: ID_def cfun_eq_iff map_sum.identity id_def)

lemma deflation_map_sum [domain_deflation]:
  "\<lbrakk>deflation d1; deflation d2\<rbrakk> \<Longrightarrow> deflation (map_sum' d1 d2)"
apply default
apply (induct_tac x, simp_all add: deflation.idem)
apply (induct_tac x, simp_all add: deflation.below)
done

lemma encode_sum_u_map_sum:
  "encode_sum_u\<cdot>(u_map\<cdot>(map_sum' f g)\<cdot>(decode_sum_u\<cdot>x))
    = ssum_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>g)\<cdot>x"
apply (induct x, simp add: decode_sum_u_def encode_sum_u_def)
apply (case_tac x, simp, simp add: decode_sum_u_def encode_sum_u_def)
apply (case_tac y, simp, simp add: decode_sum_u_def encode_sum_u_def)
done

lemma isodefl_sum [domain_isodefl]:
  fixes d :: "'a::predomain \<rightarrow> 'a"
  assumes "isodefl' d1 t1" and "isodefl' d2 t2"
  shows "isodefl' (map_sum' d1 d2) (sum_liftdefl\<cdot>t1\<cdot>t2)"
using assms unfolding isodefl'_def liftemb_sum_def liftprj_sum_def
apply (simp add: sum_liftdefl_def cast_udefl cast_ssum_defl cast_u_liftdefl)
apply (simp add: cfcomp1 encode_sum_u_map_sum)
apply (simp add: ssum_map_map u_emb_bottom)
done

setup {*
  Domain_Take_Proofs.add_rec_type (@{type_name "sum"}, [true, true])
*}

end
