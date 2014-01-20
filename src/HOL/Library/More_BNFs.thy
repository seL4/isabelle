(*  Title:      HOL/Library/More_BNFs.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Andreas Lochbihler, Karlsruhe Institute of Technology
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Registration of various types as bounded natural functors.
*)

header {* Registration of Various Types as Bounded Natural Functors *}

theory More_BNFs
imports FSet Multiset Cardinal_Notations
begin

abbreviation "Grp \<equiv> BNF_Util.Grp"
abbreviation "fstOp \<equiv> BNF_Def.fstOp"
abbreviation "sndOp \<equiv> BNF_Def.sndOp"

lemma option_rec_conv_option_case: "option_rec = option_case"
by (simp add: fun_eq_iff split: option.split)

bnf "'a option"
  map: Option.map
  sets: Option.set
  bd: natLeq 
  wits: None
  rel: option_rel
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
  fix R S
  show "option_rel R OO option_rel S \<le> option_rel (R OO S)"
    by (auto simp: option_rel_def split: option.splits)
next
  fix z
  assume "z \<in> Option.set None"
  thus False by simp
next
  fix R
  show "option_rel R =
        (Grp {x. Option.set x \<subseteq> Collect (split R)} (Option.map fst))\<inverse>\<inverse> OO
         Grp {x. Option.set x \<subseteq> Collect (split R)} (Option.map snd)"
  unfolding option_rel_def Grp_def relcompp.simps conversep.simps fun_eq_iff prod.cases
  by (auto simp: trans[OF eq_commute option_map_is_None] trans[OF eq_commute option_map_eq_Some]
           split: option.splits)
qed

bnf "'a list"
  map: map
  sets: set
  bd: natLeq
  wits: Nil
  rel: list_all2
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
  show "set o map f = image f o set" by (rule ext, unfold comp_apply, rule set_map)
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix x
  show "|set x| \<le>o natLeq"
    by (metis List.finite_set finite_iff_ordLess_natLeq ordLess_imp_ordLeq)
next
  fix R S
  show "list_all2 R OO list_all2 S \<le> list_all2 (R OO S)"
    by (metis list_all2_OO order_refl)
next
  fix R
  show "list_all2 R =
         (Grp {x. set x \<subseteq> {(x, y). R x y}} (map fst))\<inverse>\<inverse> OO
         Grp {x. set x \<subseteq> {(x, y). R x y}} (map snd)"
    unfolding list_all2_def[abs_def] Grp_def fun_eq_iff relcompp.simps conversep.simps
    by (force simp: zip_map_fst_snd)
qed simp_all


(* Finite sets *)

context
includes fset.lifting
begin

lemma fset_rel_alt: "fset_rel R a b \<longleftrightarrow> (\<forall>t \<in> fset a. \<exists>u \<in> fset b. R t u) \<and>
                                        (\<forall>t \<in> fset b. \<exists>u \<in> fset a. R u t)"
  by transfer (simp add: set_rel_def)

lemma fset_to_fset: "finite A \<Longrightarrow> fset (the_inv fset A) = A"
  apply (rule f_the_inv_into_f[unfolded inj_on_def])
  apply (simp add: fset_inject) apply (rule range_eqI Abs_fset_inverse[symmetric] CollectI)+
  .

lemma fset_rel_aux:
"(\<forall>t \<in> fset a. \<exists>u \<in> fset b. R t u) \<and> (\<forall>u \<in> fset b. \<exists>t \<in> fset a. R t u) \<longleftrightarrow>
 ((Grp {a. fset a \<subseteq> {(a, b). R a b}} (fimage fst))\<inverse>\<inverse> OO
  Grp {a. fset a \<subseteq> {(a, b). R a b}} (fimage snd)) a b" (is "?L = ?R")
proof
  assume ?L
  def R' \<equiv> "the_inv fset (Collect (split R) \<inter> (fset a \<times> fset b))" (is "the_inv fset ?L'")
  have "finite ?L'" by (intro finite_Int[OF disjI2] finite_cartesian_product) (transfer, simp)+
  hence *: "fset R' = ?L'" unfolding R'_def by (intro fset_to_fset)
  show ?R unfolding Grp_def relcompp.simps conversep.simps
  proof (intro CollectI prod_caseI exI[of _ a] exI[of _ b] exI[of _ R'] conjI refl)
    from * show "a = fimage fst R'" using conjunct1[OF `?L`]
      by (transfer, auto simp add: image_def Int_def split: prod.splits)
    from * show "b = fimage snd R'" using conjunct2[OF `?L`]
      by (transfer, auto simp add: image_def Int_def split: prod.splits)
  qed (auto simp add: *)
next
  assume ?R thus ?L unfolding Grp_def relcompp.simps conversep.simps
  apply (simp add: subset_eq Ball_def)
  apply (rule conjI)
  apply (transfer, clarsimp, metis snd_conv)
  by (transfer, clarsimp, metis fst_conv)
qed

bnf "'a fset"
  map: fimage
  sets: fset 
  bd: natLeq
  wits: "{||}"
  rel: fset_rel
apply -
          apply transfer' apply simp
         apply transfer' apply force
        apply transfer apply force
       apply transfer' apply force
      apply (rule natLeq_card_order)
     apply (rule natLeq_cinfinite)
    apply transfer apply (metis ordLess_imp_ordLeq finite_iff_ordLess_natLeq)
   apply (fastforce simp: fset_rel_alt)
 apply (simp add: Grp_def relcompp.simps conversep.simps fun_eq_iff fset_rel_alt fset_rel_aux) 
apply transfer apply simp
done

lemma fset_rel_fset: "set_rel \<chi> (fset A1) (fset A2) = fset_rel \<chi> A1 A2"
  by transfer (rule refl)

end

lemmas [simp] = fset.map_comp fset.map_id fset.set_map


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

lift_definition mmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a multiset \<Rightarrow> 'b multiset" is
  "\<lambda>h f b. setsum f {a. h a = b \<and> f a > 0} :: nat"
unfolding multiset_def proof safe
  fix h :: "'a \<Rightarrow> 'b" and f :: "'a \<Rightarrow> nat"
  assume fin: "finite {a. 0 < f a}"  (is "finite ?A")
  show "finite {b. 0 < setsum f {a. h a = b \<and> 0 < f a}}"
  (is "finite {b. 0 < setsum f (?As b)}")
  proof- let ?B = "{b. 0 < setsum f (?As b)}"
    have "\<And> b. finite (?As b)" using fin by simp
    hence B: "?B = {b. ?As b \<noteq> {}}" by (auto simp add: setsum_gt_0_iff)
    hence "?B \<subseteq> h ` ?A" by auto
    thus ?thesis using finite_surj[OF fin] by auto
  qed
qed

lemma mmap_id0: "mmap id = id"
proof (intro ext multiset_eqI)
  fix f a show "count (mmap id f) a = count (id f) a"
  proof (cases "count f a = 0")
    case False
    hence 1: "{aa. aa = a \<and> aa \<in># f} = {a}" by auto
    thus ?thesis by transfer auto
  qed (transfer, simp)
qed

lemma inj_on_setsum_inv:
assumes 1: "(0::nat) < setsum (count f) {a. h a = b' \<and> a \<in># f}" (is "0 < setsum (count f) ?A'")
and     2: "{a. h a = b \<and> a \<in># f} = {a. h a = b' \<and> a \<in># f}" (is "?A = ?A'")
shows "b = b'"
using assms by (auto simp add: setsum_gt_0_iff)

lemma mmap_comp:
fixes h1 :: "'a \<Rightarrow> 'b" and h2 :: "'b \<Rightarrow> 'c"
shows "mmap (h2 o h1) = mmap h2 o mmap h1"
proof (intro ext multiset_eqI)
  fix f :: "'a multiset" fix c :: 'c
  let ?A = "{a. h2 (h1 a) = c \<and> a \<in># f}"
  let ?As = "\<lambda> b. {a. h1 a = b \<and> a \<in># f}"
  let ?B = "{b. h2 b = c \<and> 0 < setsum (count f) (?As b)}"
  have 0: "{?As b | b.  b \<in> ?B} = ?As ` ?B" by auto
  have "\<And> b. finite (?As b)" by transfer (simp add: multiset_def)
  hence "?B = {b. h2 b = c \<and> ?As b \<noteq> {}}" by (auto simp add: setsum_gt_0_iff)
  hence A: "?A = \<Union> {?As b | b.  b \<in> ?B}" by auto
  have "setsum (count f) ?A = setsum (setsum (count f)) {?As b | b.  b \<in> ?B}"
    unfolding A by transfer (intro setsum_Union_disjoint, auto simp: multiset_def)
  also have "... = setsum (setsum (count f)) (?As ` ?B)" unfolding 0 ..
  also have "... = setsum (setsum (count f) o ?As) ?B"
    by(intro setsum_reindex) (auto simp add: setsum_gt_0_iff inj_on_def)
  also have "... = setsum (\<lambda> b. setsum (count f) (?As b)) ?B" unfolding comp_def ..
  finally have "setsum (count f) ?A = setsum (\<lambda> b. setsum (count f) (?As b)) ?B" .
  thus "count (mmap (h2 \<circ> h1) f) c = count ((mmap h2 \<circ> mmap h1) f) c"
    by transfer (unfold comp_apply, blast)
qed

lemma mmap_cong:
assumes "\<And>a. a \<in># M \<Longrightarrow> f a = g a"
shows "mmap f M = mmap g M"
using assms by transfer (auto intro!: setsum_cong)

context
begin
interpretation lifting_syntax .

lemma set_of_transfer[transfer_rule]: "(pcr_multiset op = ===> op =) (\<lambda>f. {a. 0 < f a}) set_of"
  unfolding set_of_def pcr_multiset_def cr_multiset_def fun_rel_def by auto

end

lemma set_of_mmap: "set_of o mmap h = image h o set_of"
proof (rule ext, unfold comp_apply)
  fix M show "set_of (mmap h M) = h ` set_of M"
    by transfer (auto simp add: multiset_def setsum_gt_0_iff)
qed

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

lemma matrix_setsum_finite:
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
    by (metis image_eqI lessThan_iff less_Suc_eq_le)
    have "(\<Sum>b2\<in>B2. M (u b1 b2)) = (\<Sum>i2<Suc n2. ct (f1 b1) (f2 (e2 i2)))"
    unfolding e2_surj[symmetric] setsum_reindex[OF e2_inj]
    unfolding M_def comp_def apply(intro setsum_cong) apply force
    by (metis e2_surj b1 h1 h2 imageI)
    also have "... = N1 b1" using b1 ct1[OF f1b1] by simp
    finally show "(\<Sum>b2\<in>B2. M (u b1 b2)) = N1 b1" .
  next
    fix b2 assume b2: "b2 \<in> B2"
    hence f2b2: "f2 b2 \<le> n2" using f2 unfolding bij_betw_def
    by (metis image_eqI lessThan_iff less_Suc_eq_le)
    have "(\<Sum>b1\<in>B1. M (u b1 b2)) = (\<Sum>i1<Suc n1. ct (f1 (e1 i1)) (f2 b2))"
    unfolding e1_surj[symmetric] setsum_reindex[OF e1_inj]
    unfolding M_def comp_def apply(intro setsum_cong) apply force
    by (metis e1_surj b2 h1 h2 imageI)
    also have "... = N2 b2" using b2 ct2[OF f2b2] by simp
    finally show "(\<Sum>b1\<in>B1. M (u b1 b2)) = N2 b2" .
  qed
qed

lemma supp_vimage_mmap: "set_of M \<subseteq> f -` (set_of (mmap f M))"
  by transfer (auto simp: multiset_def setsum_gt_0_iff)

lemma mmap_ge_0: "b \<in># mmap f M \<longleftrightarrow> (\<exists>a. a \<in># M \<and> f a = b)"
  by transfer (auto simp: multiset_def setsum_gt_0_iff)

lemma finite_twosets:
assumes "finite B1" and "finite B2"
shows "finite {u b1 b2 |b1 b2. b1 \<in> B1 \<and> b2 \<in> B2}"  (is "finite ?A")
proof-
  have A: "?A = (\<lambda> b1b2. u (fst b1b2) (snd b1b2)) ` (B1 <*> B2)" by force
  show ?thesis unfolding A using finite_cartesian_product[OF assms] by auto
qed

(* Weak pullbacks: *)
definition wpull where
"wpull A B1 B2 f1 f2 p1 p2 \<longleftrightarrow>
 (\<forall> b1 b2. b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2 \<longrightarrow> (\<exists> a \<in> A. p1 a = b1 \<and> p2 a = b2))"

(* Weak pseudo-pullbacks *)
definition wppull where
"wppull A B1 B2 f1 f2 e1 e2 p1 p2 \<longleftrightarrow>
 (\<forall> b1 b2. b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2 \<longrightarrow>
           (\<exists> a \<in> A. e1 (p1 a) = e1 b1 \<and> e2 (p2 a) = e2 b2))"


(* The pullback of sets *)
definition thePull where
"thePull B1 B2 f1 f2 = {(b1,b2). b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2}"

lemma wpull_thePull:
"wpull (thePull B1 B2 f1 f2) B1 B2 f1 f2 fst snd"
unfolding wpull_def thePull_def by auto

lemma wppull_thePull:
assumes "wppull A B1 B2 f1 f2 e1 e2 p1 p2"
shows
"\<exists> j. \<forall> a' \<in> thePull B1 B2 f1 f2.
   j a' \<in> A \<and>
   e1 (p1 (j a')) = e1 (fst a') \<and> e2 (p2 (j a')) = e2 (snd a')"
(is "\<exists> j. \<forall> a' \<in> ?A'. ?phi a' (j a')")
proof(rule bchoice[of ?A' ?phi], default)
  fix a' assume a': "a' \<in> ?A'"
  hence "fst a' \<in> B1" unfolding thePull_def by auto
  moreover
  from a' have "snd a' \<in> B2" unfolding thePull_def by auto
  moreover have "f1 (fst a') = f2 (snd a')"
  using a' unfolding csquare_def thePull_def by auto
  ultimately show "\<exists> ja'. ?phi a' ja'"
  using assms unfolding wppull_def by blast
qed

lemma wpull_wppull:
assumes wp: "wpull A' B1 B2 f1 f2 p1' p2'" and
1: "\<forall> a' \<in> A'. j a' \<in> A \<and> e1 (p1 (j a')) = e1 (p1' a') \<and> e2 (p2 (j a')) = e2 (p2' a')"
shows "wppull A B1 B2 f1 f2 e1 e2 p1 p2"
unfolding wppull_def proof safe
  fix b1 b2
  assume b1: "b1 \<in> B1" and b2: "b2 \<in> B2" and f: "f1 b1 = f2 b2"
  then obtain a' where a': "a' \<in> A'" and b1: "b1 = p1' a'" and b2: "b2 = p2' a'"
  using wp unfolding wpull_def by blast
  show "\<exists>a\<in>A. e1 (p1 a) = e1 b1 \<and> e2 (p2 a) = e2 b2"
  apply (rule bexI[of _ "j a'"]) unfolding b1 b2 using a' 1 by auto
qed

lemma wppull_fstOp_sndOp:
shows "wppull (Collect (split (P OO Q))) (Collect (split P)) (Collect (split Q))
  snd fst fst snd (fstOp P Q) (sndOp P Q)"
using pick_middlep unfolding wppull_def fstOp_def sndOp_def relcompp.simps by auto

lemma wpull_mmap:
fixes A :: "'a set" and B1 :: "'b1 set" and B2 :: "'b2 set"
assumes wp: "wpull A B1 B2 f1 f2 p1 p2"
shows
"wpull {M. set_of M \<subseteq> A}
       {N1. set_of N1 \<subseteq> B1} {N2. set_of N2 \<subseteq> B2}
       (mmap f1) (mmap f2) (mmap p1) (mmap p2)"
unfolding wpull_def proof (safe, unfold Bex_def mem_Collect_eq)
  fix N1 :: "'b1 multiset" and N2 :: "'b2 multiset"
  assume mmap': "mmap f1 N1 = mmap f2 N2"
  and N1[simp]: "set_of N1 \<subseteq> B1"
  and N2[simp]: "set_of N2 \<subseteq> B2"
  def P \<equiv> "mmap f1 N1"
  have P1: "P = mmap f1 N1" and P2: "P = mmap f2 N2" unfolding P_def using mmap' by auto
  note P = P1 P2
  have fin_N1[simp]: "finite (set_of N1)"
   and fin_N2[simp]: "finite (set_of N2)"
   and fin_P[simp]: "finite (set_of P)" by auto
  (*  *)
  def set1 \<equiv> "\<lambda> c. {b1 \<in> set_of N1. f1 b1 = c}"
  have set1[simp]: "\<And> c b1. b1 \<in> set1 c \<Longrightarrow> f1 b1 = c" unfolding set1_def by auto
  have fin_set1: "\<And> c. c \<in> set_of P \<Longrightarrow> finite (set1 c)"
    using N1(1) unfolding set1_def multiset_def by auto
  have set1_NE: "\<And> c. c \<in> set_of P \<Longrightarrow> set1 c \<noteq> {}"
   unfolding set1_def set_of_def P mmap_ge_0 by auto
  have supp_N1_set1: "set_of N1 = (\<Union> c \<in> set_of P. set1 c)"
    using supp_vimage_mmap[of N1 f1] unfolding set1_def P1 by auto
  hence set1_inclN1: "\<And>c. c \<in> set_of P \<Longrightarrow> set1 c \<subseteq> set_of N1" by auto
  hence set1_incl: "\<And> c. c \<in> set_of P \<Longrightarrow> set1 c \<subseteq> B1" using N1 by blast
  have set1_disj: "\<And> c c'. c \<noteq> c' \<Longrightarrow> set1 c \<inter> set1 c' = {}"
    unfolding set1_def by auto
  have setsum_set1: "\<And> c. setsum (count N1) (set1 c) = count P c"
    unfolding P1 set1_def by transfer (auto intro: setsum_cong)
  (*  *)
  def set2 \<equiv> "\<lambda> c. {b2 \<in> set_of N2. f2 b2 = c}"
  have set2[simp]: "\<And> c b2. b2 \<in> set2 c \<Longrightarrow> f2 b2 = c" unfolding set2_def by auto
  have fin_set2: "\<And> c. c \<in> set_of P \<Longrightarrow> finite (set2 c)"
  using N2(1) unfolding set2_def multiset_def by auto
  have set2_NE: "\<And> c. c \<in> set_of P \<Longrightarrow> set2 c \<noteq> {}"
    unfolding set2_def P2 mmap_ge_0 set_of_def by auto
  have supp_N2_set2: "set_of N2 = (\<Union> c \<in> set_of P. set2 c)"
    using supp_vimage_mmap[of N2 f2] unfolding set2_def P2 by auto
  hence set2_inclN2: "\<And>c. c \<in> set_of P \<Longrightarrow> set2 c \<subseteq> set_of N2" by auto
  hence set2_incl: "\<And> c. c \<in> set_of P \<Longrightarrow> set2 c \<subseteq> B2" using N2 by blast
  have set2_disj: "\<And> c c'. c \<noteq> c' \<Longrightarrow> set2 c \<inter> set2 c' = {}"
    unfolding set2_def by auto
  have setsum_set2: "\<And> c. setsum (count N2) (set2 c) = count P c"
    unfolding P2 set2_def by transfer (auto intro: setsum_cong)
  (*  *)
  have ss: "\<And> c. c \<in> set_of P \<Longrightarrow> setsum (count N1) (set1 c) = setsum (count N2) (set2 c)"
    unfolding setsum_set1 setsum_set2 ..
  have "\<forall> c \<in> set_of P. \<forall> b1b2 \<in> (set1 c) \<times> (set2 c).
          \<exists> a \<in> A. p1 a = fst b1b2 \<and> p2 a = snd b1b2"
    using wp set1_incl set2_incl unfolding wpull_def Ball_def mem_Collect_eq
    by simp (metis set1 set2 set_rev_mp)
  then obtain uu where uu:
  "\<forall> c \<in> set_of P. \<forall> b1b2 \<in> (set1 c) \<times> (set2 c).
     uu c b1b2 \<in> A \<and> p1 (uu c b1b2) = fst b1b2 \<and> p2 (uu c b1b2) = snd b1b2" by metis
  def u \<equiv> "\<lambda> c b1 b2. uu c (b1,b2)"
  have u[simp]:
  "\<And> c b1 b2. \<lbrakk>c \<in> set_of P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk> \<Longrightarrow> u c b1 b2 \<in> A"
  "\<And> c b1 b2. \<lbrakk>c \<in> set_of P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk> \<Longrightarrow> p1 (u c b1 b2) = b1"
  "\<And> c b1 b2. \<lbrakk>c \<in> set_of P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk> \<Longrightarrow> p2 (u c b1 b2) = b2"
    using uu unfolding u_def by auto
  {fix c assume c: "c \<in> set_of P"
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
  have fin_sset[simp]: "\<And> c. c \<in> set_of P \<Longrightarrow> finite (sset c)" unfolding sset_def
    using fin_set1 fin_set2 finite_twosets by blast
  have sset_A: "\<And> c. c \<in> set_of P \<Longrightarrow> sset c \<subseteq> A" unfolding sset_def by auto
  {fix c a assume c: "c \<in> set_of P" and ac: "a \<in> sset c"
   then obtain b1 b2 where b1: "b1 \<in> set1 c" and b2: "b2 \<in> set2 c"
   and a: "a = u c b1 b2" unfolding sset_def by auto
   have "p1 a \<in> set1 c" and p2a: "p2 a \<in> set2 c"
   using ac a b1 b2 c u(2) u(3) by simp+
   hence "u c (p1 a) (p2 a) = a" unfolding a using b1 b2 inj[OF c]
   unfolding inj2_def by (metis c u(2) u(3))
  } note u_p12[simp] = this
  {fix c a assume c: "c \<in> set_of P" and ac: "a \<in> sset c"
   hence "p1 a \<in> set1 c" unfolding sset_def by auto
  }note p1[simp] = this
  {fix c a assume c: "c \<in> set_of P" and ac: "a \<in> sset c"
   hence "p2 a \<in> set2 c" unfolding sset_def by auto
  }note p2[simp] = this
  (*  *)
  {fix c assume c: "c \<in> set_of P"
   hence "\<exists> M. (\<forall> b1 \<in> set1 c. setsum (\<lambda> b2. M (u c b1 b2)) (set2 c) = count N1 b1) \<and>
               (\<forall> b2 \<in> set2 c. setsum (\<lambda> b1. M (u c b1 b2)) (set1 c) = count N2 b2)"
   unfolding sset_def
   using matrix_setsum_finite[OF set1_NE[OF c] fin_set1[OF c]
                                 set2_NE[OF c] fin_set2[OF c] inj[OF c] ss[OF c]] by auto
  }
  then obtain Ms where
  ss1: "\<And> c b1. \<lbrakk>c \<in> set_of P; b1 \<in> set1 c\<rbrakk> \<Longrightarrow>
                   setsum (\<lambda> b2. Ms c (u c b1 b2)) (set2 c) = count N1 b1" and
  ss2: "\<And> c b2. \<lbrakk>c \<in> set_of P; b2 \<in> set2 c\<rbrakk> \<Longrightarrow>
                   setsum (\<lambda> b1. Ms c (u c b1 b2)) (set1 c) = count N2 b2"
  by metis
  def SET \<equiv> "\<Union> c \<in> set_of P. sset c"
  have fin_SET[simp]: "finite SET" unfolding SET_def apply(rule finite_UN_I) by auto
  have SET_A: "SET \<subseteq> A" unfolding SET_def using sset_A by blast
  have u_SET[simp]: "\<And> c b1 b2. \<lbrakk>c \<in> set_of P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk> \<Longrightarrow> u c b1 b2 \<in> SET"
    unfolding SET_def sset_def by blast
  {fix c a assume c: "c \<in> set_of P" and a: "a \<in> SET" and p1a: "p1 a \<in> set1 c"
   then obtain c' where c': "c' \<in> set_of P" and ac': "a \<in> sset c'"
    unfolding SET_def by auto
   hence "p1 a \<in> set1 c'" unfolding sset_def by auto
   hence eq: "c = c'" using p1a c c' set1_disj by auto
   hence "a \<in> sset c" using ac' by simp
  } note p1_rev = this
  {fix c a assume c: "c \<in> set_of P" and a: "a \<in> SET" and p2a: "p2 a \<in> set2 c"
   then obtain c' where c': "c' \<in> set_of P" and ac': "a \<in> sset c'"
   unfolding SET_def by auto
   hence "p2 a \<in> set2 c'" unfolding sset_def by auto
   hence eq: "c = c'" using p2a c c' set2_disj by auto
   hence "a \<in> sset c" using ac' by simp
  } note p2_rev = this
  (*  *)
  have "\<forall> a \<in> SET. \<exists> c \<in> set_of P. a \<in> sset c" unfolding SET_def by auto
  then obtain h where h: "\<forall> a \<in> SET. h a \<in> set_of P \<and> a \<in> sset (h a)" by metis
  have h_u[simp]: "\<And> c b1 b2. \<lbrakk>c \<in> set_of P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk>
                      \<Longrightarrow> h (u c b1 b2) = c"
  by (metis h p2 set2 u(3) u_SET)
  have h_u1: "\<And> c b1 b2. \<lbrakk>c \<in> set_of P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk>
                      \<Longrightarrow> h (u c b1 b2) = f1 b1"
  using h unfolding sset_def by auto
  have h_u2: "\<And> c b1 b2. \<lbrakk>c \<in> set_of P; b1 \<in> set1 c; b2 \<in> set2 c\<rbrakk>
                      \<Longrightarrow> h (u c b1 b2) = f2 b2"
  using h unfolding sset_def by auto
  def M \<equiv>
    "Abs_multiset (\<lambda> a. if a \<in> SET \<and> p1 a \<in> set_of N1 \<and> p2 a \<in> set_of N2 then Ms (h a) a else 0)"
  have "(\<lambda> a. if a \<in> SET \<and> p1 a \<in> set_of N1 \<and> p2 a \<in> set_of N2 then Ms (h a) a else 0) \<in> multiset"
    unfolding multiset_def by auto
  hence [transfer_rule]: "pcr_multiset op = (\<lambda> a. if a \<in> SET \<and> p1 a \<in> set_of N1 \<and> p2 a \<in> set_of N2 then Ms (h a) a else 0) M"
    unfolding M_def pcr_multiset_def cr_multiset_def by (auto simp: Abs_multiset_inverse)
  have sM: "set_of M \<subseteq> SET" "set_of M \<subseteq> p1 -` (set_of N1)" "set_of M \<subseteq> p2 -` set_of N2"
    by (transfer, auto split: split_if_asm)+
  show "\<exists>M. set_of M \<subseteq> A \<and> mmap p1 M = N1 \<and> mmap p2 M = N2"
  proof(rule exI[of _ M], safe)
    fix a assume *: "a \<in> set_of M"
    from SET_A show "a \<in> A"
    proof (cases "a \<in> SET")
      case False thus ?thesis using * by transfer' auto
    qed blast
  next
    show "mmap p1 M = N1"
    proof(intro multiset_eqI)
      fix b1
      let ?K = "{a. p1 a = b1 \<and> a \<in># M}"
      have "setsum (count M) ?K = count N1 b1"
      proof(cases "b1 \<in> set_of N1")
        case False
        hence "?K = {}" using sM(2) by auto
        thus ?thesis using False by auto
      next
        case True
        def c \<equiv> "f1 b1"
        have c: "c \<in> set_of P" and b1: "b1 \<in> set1 c"
          unfolding set1_def c_def P1 using True by (auto simp: comp_eq_dest[OF set_of_mmap])
        with sM(1) have "setsum (count M) ?K = setsum (count M) {a. p1 a = b1 \<and> a \<in> SET}"
          by transfer (force intro: setsum_mono_zero_cong_left split: split_if_asm)
        also have "... = setsum (count M) ((\<lambda> b2. u c b1 b2) ` (set2 c))"
          apply(rule setsum_cong) using c b1 proof safe
          fix a assume p1a: "p1 a \<in> set1 c" and "c \<in> set_of P" and "a \<in> SET"
          hence ac: "a \<in> sset c" using p1_rev by auto
          hence "a = u c (p1 a) (p2 a)" using c by auto
          moreover have "p2 a \<in> set2 c" using ac c by auto
          ultimately show "a \<in> u c (p1 a) ` set2 c" by auto
        qed auto
        also have "... = setsum (\<lambda> b2. count M (u c b1 b2)) (set2 c)"
          unfolding comp_def[symmetric] apply(rule setsum_reindex)
          using inj unfolding inj_on_def inj2_def using b1 c u(3) by blast
        also have "... = count N1 b1" unfolding ss1[OF c b1, symmetric]
          apply(rule setsum_cong[OF refl]) apply (transfer fixing: Ms u c b1 set2)
          using True h_u[OF c b1] set2_def u(2,3)[OF c b1] u_SET[OF c b1] by fastforce
        finally show ?thesis .
      qed
      thus "count (mmap p1 M) b1 = count N1 b1" by transfer
    qed
  next
next
    show "mmap p2 M = N2"
    proof(intro multiset_eqI)
      fix b2
      let ?K = "{a. p2 a = b2 \<and> a \<in># M}"
      have "setsum (count M) ?K = count N2 b2"
      proof(cases "b2 \<in> set_of N2")
        case False
        hence "?K = {}" using sM(3) by auto
        thus ?thesis using False by auto
      next
        case True
        def c \<equiv> "f2 b2"
        have c: "c \<in> set_of P" and b2: "b2 \<in> set2 c"
          unfolding set2_def c_def P2 using True by (auto simp: comp_eq_dest[OF set_of_mmap])
        with sM(1) have "setsum (count M) ?K = setsum (count M) {a. p2 a = b2 \<and> a \<in> SET}"
          by transfer (force intro: setsum_mono_zero_cong_left split: split_if_asm)
        also have "... = setsum (count M) ((\<lambda> b1. u c b1 b2) ` (set1 c))"
          apply(rule setsum_cong) using c b2 proof safe
          fix a assume p2a: "p2 a \<in> set2 c" and "c \<in> set_of P" and "a \<in> SET"
          hence ac: "a \<in> sset c" using p2_rev by auto
          hence "a = u c (p1 a) (p2 a)" using c by auto
          moreover have "p1 a \<in> set1 c" using ac c by auto
          ultimately show "a \<in> (\<lambda>x. u c x (p2 a)) ` set1 c" by auto
        qed auto
        also have "... = setsum (count M o (\<lambda> b1. u c b1 b2)) (set1 c)"
          apply(rule setsum_reindex)
          using inj unfolding inj_on_def inj2_def using b2 c u(2) by blast
        also have "... = setsum (\<lambda> b1. count M (u c b1 b2)) (set1 c)" by simp
        also have "... = count N2 b2" unfolding ss2[OF c b2, symmetric] comp_def
          apply(rule setsum_cong[OF refl]) apply (transfer fixing: Ms u c b2 set1)
          using True h_u1[OF c _ b2] u(2,3)[OF c _ b2] u_SET[OF c _ b2] set1_def by fastforce
        finally show ?thesis .
      qed
      thus "count (mmap p2 M) b2 = count N2 b2" by transfer
    qed
  qed
qed

lemma set_of_bd: "|set_of x| \<le>o natLeq"
  by transfer
    (auto intro!: ordLess_imp_ordLeq simp: finite_iff_ordLess_natLeq[symmetric] multiset_def)

lemma wppull_mmap:
  assumes "wppull A B1 B2 f1 f2 e1 e2 p1 p2"
  shows "wppull {M. set_of M \<subseteq> A} {N1. set_of N1 \<subseteq> B1} {N2. set_of N2 \<subseteq> B2}
    (mmap f1) (mmap f2) (mmap e1) (mmap e2) (mmap p1) (mmap p2)"
proof -
  from assms obtain j where j: "\<forall>a'\<in>thePull B1 B2 f1 f2.
    j a' \<in> A \<and> e1 (p1 (j a')) = e1 (fst a') \<and> e2 (p2 (j a')) = e2 (snd a')" 
    by (blast dest: wppull_thePull)
  then show ?thesis
    by (intro wpull_wppull[OF wpull_mmap[OF wpull_thePull], of _ _ _ _ "mmap j"])
      (auto simp: comp_eq_dest_lhs[OF mmap_comp[symmetric]] comp_eq_dest[OF set_of_mmap]
        intro!: mmap_cong simp del: mem_set_of_iff simp: mem_set_of_iff[symmetric])
qed

bnf "'a multiset"
  map: mmap
  sets: set_of 
  bd: natLeq
  wits: "{#}"
by (auto simp add: mmap_id0 mmap_comp set_of_mmap natLeq_card_order natLeq_cinfinite set_of_bd
  Grp_def relcompp.simps intro: mmap_cong)
  (metis wppull_mmap[OF wppull_fstOp_sndOp, unfolded wppull_def
    o_eq_dest_lhs[OF mmap_comp[symmetric]] fstOp_def sndOp_def comp_def, simplified])

inductive rel_multiset' where
  Zero[intro]: "rel_multiset' R {#} {#}"
| Plus[intro]: "\<lbrakk>R a b; rel_multiset' R M N\<rbrakk> \<Longrightarrow> rel_multiset' R (M + {#a#}) (N + {#b#})"

lemma map_multiset_Zero_iff[simp]: "mmap f M = {#} \<longleftrightarrow> M = {#}"
by (metis image_is_empty multiset.set_map set_of_eq_empty_iff)

lemma map_multiset_Zero[simp]: "mmap f {#} = {#}" by simp

lemma rel_multiset_Zero: "rel_multiset R {#} {#}"
unfolding rel_multiset_def Grp_def by auto

declare multiset.count[simp]
declare Abs_multiset_inverse[simp]
declare multiset.count_inverse[simp]
declare union_preserves_multiset[simp]


lemma map_multiset_Plus[simp]: "mmap f (M1 + M2) = mmap f M1 + mmap f M2"
proof (intro multiset_eqI, transfer fixing: f)
  fix x :: 'a and M1 M2 :: "'b \<Rightarrow> nat"
  assume "M1 \<in> multiset" "M2 \<in> multiset"
  hence "setsum M1 {a. f a = x \<and> 0 < M1 a} = setsum M1 {a. f a = x \<and> 0 < M1 a + M2 a}"
        "setsum M2 {a. f a = x \<and> 0 < M2 a} = setsum M2 {a. f a = x \<and> 0 < M1 a + M2 a}"
    by (auto simp: multiset_def intro!: setsum_mono_zero_cong_left)
  then show "(\<Sum>a | f a = x \<and> 0 < M1 a + M2 a. M1 a + M2 a) =
       setsum M1 {a. f a = x \<and> 0 < M1 a} +
       setsum M2 {a. f a = x \<and> 0 < M2 a}"
    by (auto simp: setsum.distrib[symmetric])
qed

lemma map_multiset_singl[simp]: "mmap f {#a#} = {#f a#}"
  by transfer auto

lemma rel_multiset_Plus:
assumes ab: "R a b" and MN: "rel_multiset R M N"
shows "rel_multiset R (M + {#a#}) (N + {#b#})"
proof-
  {fix y assume "R a b" and "set_of y \<subseteq> {(x, y). R x y}"
   hence "\<exists>ya. mmap fst y + {#a#} = mmap fst ya \<and>
               mmap snd y + {#b#} = mmap snd ya \<and>
               set_of ya \<subseteq> {(x, y). R x y}"
   apply(intro exI[of _ "y + {#(a,b)#}"]) by auto
  }
  thus ?thesis
  using assms
  unfolding rel_multiset_def Grp_def by force
qed

lemma rel_multiset'_imp_rel_multiset:
"rel_multiset' R M N \<Longrightarrow> rel_multiset R M N"
apply(induct rule: rel_multiset'.induct)
using rel_multiset_Zero rel_multiset_Plus by auto

lemma mcard_mmap[simp]: "mcard (mmap f M) = mcard M"
proof -
  def A \<equiv> "\<lambda> b. {a. f a = b \<and> a \<in># M}"
  let ?B = "{b. 0 < setsum (count M) (A b)}"
  have "{b. \<exists>a. f a = b \<and> a \<in># M} \<subseteq> f ` {a. a \<in># M}" by auto
  moreover have "finite (f ` {a. a \<in># M})" apply(rule finite_imageI)
  using finite_Collect_mem .
  ultimately have fin: "finite {b. \<exists>a. f a = b \<and> a \<in># M}" by(rule finite_subset)
  have i: "inj_on A ?B" unfolding inj_on_def A_def apply clarsimp
    by (metis (lifting, full_types) mem_Collect_eq neq0_conv setsum.neutral)
  have 0: "\<And> b. 0 < setsum (count M) (A b) \<longleftrightarrow> (\<exists> a \<in> A b. count M a > 0)"
  apply safe
    apply (metis less_not_refl setsum_gt_0_iff setsum_infinite)
    by (metis A_def finite_Collect_conjI finite_Collect_mem setsum_gt_0_iff)
  hence AB: "A ` ?B = {A b | b. \<exists> a \<in> A b. count M a > 0}" by auto

  have "setsum (\<lambda> x. setsum (count M) (A x)) ?B = setsum (setsum (count M) o A) ?B"
  unfolding comp_def ..
  also have "... = (\<Sum>x\<in> A ` ?B. setsum (count M) x)"
  unfolding setsum.reindex [OF i, symmetric] ..
  also have "... = setsum (count M) (\<Union>x\<in>A ` {b. 0 < setsum (count M) (A b)}. x)"
  (is "_ = setsum (count M) ?J")
  apply(rule setsum.UNION_disjoint[symmetric])
  using 0 fin unfolding A_def by auto
  also have "?J = {a. a \<in># M}" unfolding AB unfolding A_def by auto
  finally have "setsum (\<lambda> x. setsum (count M) (A x)) ?B =
                setsum (count M) {a. a \<in># M}" .
  then show ?thesis unfolding mcard_unfold_setsum A_def by transfer
qed

lemma rel_multiset_mcard:
assumes "rel_multiset R M N"
shows "mcard M = mcard N"
using assms unfolding rel_multiset_def Grp_def by auto

lemma multiset_induct2[case_names empty addL addR]:
assumes empty: "P {#} {#}"
and addL: "\<And>M N a. P M N \<Longrightarrow> P (M + {#a#}) N"
and addR: "\<And>M N a. P M N \<Longrightarrow> P M (N + {#a#})"
shows "P M N"
apply(induct N rule: multiset_induct)
  apply(induct M rule: multiset_induct, rule empty, erule addL)
  apply(induct M rule: multiset_induct, erule addR, erule addR)
done

lemma multiset_induct2_mcard[consumes 1, case_names empty add]:
assumes c: "mcard M = mcard N"
and empty: "P {#} {#}"
and add: "\<And>M N a b. P M N \<Longrightarrow> P (M + {#a#}) (N + {#b#})"
shows "P M N"
using c proof(induct M arbitrary: N rule: measure_induct_rule[of mcard])
  case (less M)  show ?case
  proof(cases "M = {#}")
    case True hence "N = {#}" using less.prems by auto
    thus ?thesis using True empty by auto
  next
    case False then obtain M1 a where M: "M = M1 + {#a#}" by (metis multi_nonempty_split)
    have "N \<noteq> {#}" using False less.prems by auto
    then obtain N1 b where N: "N = N1 + {#b#}" by (metis multi_nonempty_split)
    have "mcard M1 = mcard N1" using less.prems unfolding M N by auto
    thus ?thesis using M N less.hyps add by auto
  qed
qed

lemma msed_map_invL:
assumes "mmap f (M + {#a#}) = N"
shows "\<exists> N1. N = N1 + {#f a#} \<and> mmap f M = N1"
proof-
  have "f a \<in># N"
  using assms multiset.set_map[of f "M + {#a#}"] by auto
  then obtain N1 where N: "N = N1 + {#f a#}" using multi_member_split by metis
  have "mmap f M = N1" using assms unfolding N by simp
  thus ?thesis using N by blast
qed

lemma msed_map_invR:
assumes "mmap f M = N + {#b#}"
shows "\<exists> M1 a. M = M1 + {#a#} \<and> f a = b \<and> mmap f M1 = N"
proof-
  obtain a where a: "a \<in># M" and fa: "f a = b"
  using multiset.set_map[of f M] unfolding assms
  by (metis image_iff mem_set_of_iff union_single_eq_member)
  then obtain M1 where M: "M = M1 + {#a#}" using multi_member_split by metis
  have "mmap f M1 = N" using assms unfolding M fa[symmetric] by simp
  thus ?thesis using M fa by blast
qed

lemma msed_rel_invL:
assumes "rel_multiset R (M + {#a#}) N"
shows "\<exists> N1 b. N = N1 + {#b#} \<and> R a b \<and> rel_multiset R M N1"
proof-
  obtain K where KM: "mmap fst K = M + {#a#}"
  and KN: "mmap snd K = N" and sK: "set_of K \<subseteq> {(a, b). R a b}"
  using assms
  unfolding rel_multiset_def Grp_def by auto
  obtain K1 ab where K: "K = K1 + {#ab#}" and a: "fst ab = a"
  and K1M: "mmap fst K1 = M" using msed_map_invR[OF KM] by auto
  obtain N1 where N: "N = N1 + {#snd ab#}" and K1N1: "mmap snd K1 = N1"
  using msed_map_invL[OF KN[unfolded K]] by auto
  have Rab: "R a (snd ab)" using sK a unfolding K by auto
  have "rel_multiset R M N1" using sK K1M K1N1
  unfolding K rel_multiset_def Grp_def by auto
  thus ?thesis using N Rab by auto
qed

lemma msed_rel_invR:
assumes "rel_multiset R M (N + {#b#})"
shows "\<exists> M1 a. M = M1 + {#a#} \<and> R a b \<and> rel_multiset R M1 N"
proof-
  obtain K where KN: "mmap snd K = N + {#b#}"
  and KM: "mmap fst K = M" and sK: "set_of K \<subseteq> {(a, b). R a b}"
  using assms
  unfolding rel_multiset_def Grp_def by auto
  obtain K1 ab where K: "K = K1 + {#ab#}" and b: "snd ab = b"
  and K1N: "mmap snd K1 = N" using msed_map_invR[OF KN] by auto
  obtain M1 where M: "M = M1 + {#fst ab#}" and K1M1: "mmap fst K1 = M1"
  using msed_map_invL[OF KM[unfolded K]] by auto
  have Rab: "R (fst ab) b" using sK b unfolding K by auto
  have "rel_multiset R M1 N" using sK K1N K1M1
  unfolding K rel_multiset_def Grp_def by auto
  thus ?thesis using M Rab by auto
qed

lemma rel_multiset_imp_rel_multiset':
assumes "rel_multiset R M N"
shows "rel_multiset' R M N"
using assms proof(induct M arbitrary: N rule: measure_induct_rule[of mcard])
  case (less M)
  have c: "mcard M = mcard N" using rel_multiset_mcard[OF less.prems] .
  show ?case
  proof(cases "M = {#}")
    case True hence "N = {#}" using c by simp
    thus ?thesis using True rel_multiset'.Zero by auto
  next
    case False then obtain M1 a where M: "M = M1 + {#a#}" by (metis multi_nonempty_split)
    obtain N1 b where N: "N = N1 + {#b#}" and R: "R a b" and ms: "rel_multiset R M1 N1"
    using msed_rel_invL[OF less.prems[unfolded M]] by auto
    have "rel_multiset' R M1 N1" using less.hyps[of M1 N1] ms unfolding M by simp
    thus ?thesis using rel_multiset'.Plus[of R a b, OF R] unfolding M N by simp
  qed
qed

lemma rel_multiset_rel_multiset':
"rel_multiset R M N = rel_multiset' R M N"
using  rel_multiset_imp_rel_multiset' rel_multiset'_imp_rel_multiset by auto

(* The main end product for rel_multiset: inductive characterization *)
theorems rel_multiset_induct[case_names empty add, induct pred: rel_multiset] =
         rel_multiset'.induct[unfolded rel_multiset_rel_multiset'[symmetric]]


(* Advanced relator customization *)

(* Set vs. sum relators: *)

lemma set_rel_sum_rel[simp]: 
"set_rel (sum_rel \<chi> \<phi>) A1 A2 \<longleftrightarrow> 
 set_rel \<chi> (Inl -` A1) (Inl -` A2) \<and> set_rel \<phi> (Inr -` A1) (Inr -` A2)"
(is "?L \<longleftrightarrow> ?Rl \<and> ?Rr")
proof safe
  assume L: "?L"
  show ?Rl unfolding set_rel_def Bex_def vimage_eq proof safe
    fix l1 assume "Inl l1 \<in> A1"
    then obtain a2 where a2: "a2 \<in> A2" and "sum_rel \<chi> \<phi> (Inl l1) a2"
    using L unfolding set_rel_def by auto
    then obtain l2 where "a2 = Inl l2 \<and> \<chi> l1 l2" by (cases a2, auto)
    thus "\<exists> l2. Inl l2 \<in> A2 \<and> \<chi> l1 l2" using a2 by auto
  next
    fix l2 assume "Inl l2 \<in> A2"
    then obtain a1 where a1: "a1 \<in> A1" and "sum_rel \<chi> \<phi> a1 (Inl l2)"
    using L unfolding set_rel_def by auto
    then obtain l1 where "a1 = Inl l1 \<and> \<chi> l1 l2" by (cases a1, auto)
    thus "\<exists> l1. Inl l1 \<in> A1 \<and> \<chi> l1 l2" using a1 by auto
  qed
  show ?Rr unfolding set_rel_def Bex_def vimage_eq proof safe
    fix r1 assume "Inr r1 \<in> A1"
    then obtain a2 where a2: "a2 \<in> A2" and "sum_rel \<chi> \<phi> (Inr r1) a2"
    using L unfolding set_rel_def by auto
    then obtain r2 where "a2 = Inr r2 \<and> \<phi> r1 r2" by (cases a2, auto)
    thus "\<exists> r2. Inr r2 \<in> A2 \<and> \<phi> r1 r2" using a2 by auto
  next
    fix r2 assume "Inr r2 \<in> A2"
    then obtain a1 where a1: "a1 \<in> A1" and "sum_rel \<chi> \<phi> a1 (Inr r2)"
    using L unfolding set_rel_def by auto
    then obtain r1 where "a1 = Inr r1 \<and> \<phi> r1 r2" by (cases a1, auto)
    thus "\<exists> r1. Inr r1 \<in> A1 \<and> \<phi> r1 r2" using a1 by auto
  qed
next
  assume Rl: "?Rl" and Rr: "?Rr"
  show ?L unfolding set_rel_def Bex_def vimage_eq proof safe
    fix a1 assume a1: "a1 \<in> A1"
    show "\<exists> a2. a2 \<in> A2 \<and> sum_rel \<chi> \<phi> a1 a2"
    proof(cases a1)
      case (Inl l1) then obtain l2 where "Inl l2 \<in> A2 \<and> \<chi> l1 l2"
      using Rl a1 unfolding set_rel_def by blast
      thus ?thesis unfolding Inl by auto
    next
      case (Inr r1) then obtain r2 where "Inr r2 \<in> A2 \<and> \<phi> r1 r2"
      using Rr a1 unfolding set_rel_def by blast
      thus ?thesis unfolding Inr by auto
    qed
  next
    fix a2 assume a2: "a2 \<in> A2"
    show "\<exists> a1. a1 \<in> A1 \<and> sum_rel \<chi> \<phi> a1 a2"
    proof(cases a2)
      case (Inl l2) then obtain l1 where "Inl l1 \<in> A1 \<and> \<chi> l1 l2"
      using Rl a2 unfolding set_rel_def by blast
      thus ?thesis unfolding Inl by auto
    next
      case (Inr r2) then obtain r1 where "Inr r1 \<in> A1 \<and> \<phi> r1 r2"
      using Rr a2 unfolding set_rel_def by blast
      thus ?thesis unfolding Inr by auto
    qed
  qed
qed

end
