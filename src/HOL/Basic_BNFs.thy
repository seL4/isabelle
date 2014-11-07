(*  Title:      HOL/Basic_BNFs.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Registration of basic types as bounded natural functors.
*)

section {* Registration of Basic Types as Bounded Natural Functors *}

theory Basic_BNFs
imports BNF_Def
begin

inductive_set setl :: "'a + 'b \<Rightarrow> 'a set" for s :: "'a + 'b" where
  "s = Inl x \<Longrightarrow> x \<in> setl s"
inductive_set setr :: "'a + 'b \<Rightarrow> 'b set" for s :: "'a + 'b" where
  "s = Inr x \<Longrightarrow> x \<in> setr s"

lemma sum_set_defs[code]:
  "setl = (\<lambda>x. case x of Inl z => {z} | _ => {})"
  "setr = (\<lambda>x. case x of Inr z => {z} | _ => {})"
  by (auto simp: fun_eq_iff intro: setl.intros setr.intros elim: setl.cases setr.cases split: sum.splits)

lemma rel_sum_simps[code, simp]:
  "rel_sum R1 R2 (Inl a1) (Inl b1) = R1 a1 b1"
  "rel_sum R1 R2 (Inl a1) (Inr b2) = False"
  "rel_sum R1 R2 (Inr a2) (Inl b1) = False"
  "rel_sum R1 R2 (Inr a2) (Inr b2) = R2 a2 b2"
  by (auto intro: rel_sum.intros elim: rel_sum.cases)

bnf "'a + 'b"
  map: map_sum
  sets: setl setr
  bd: natLeq
  wits: Inl Inr
  rel: rel_sum
proof -
  show "map_sum id id = id" by (rule map_sum.id)
next
  fix f1 :: "'o \<Rightarrow> 's" and f2 :: "'p \<Rightarrow> 't" and g1 :: "'s \<Rightarrow> 'q" and g2 :: "'t \<Rightarrow> 'r"
  show "map_sum (g1 o f1) (g2 o f2) = map_sum g1 g2 o map_sum f1 f2"
    by (rule map_sum.comp[symmetric])
next
  fix x and f1 :: "'o \<Rightarrow> 'q" and f2 :: "'p \<Rightarrow> 'r" and g1 g2
  assume a1: "\<And>z. z \<in> setl x \<Longrightarrow> f1 z = g1 z" and
         a2: "\<And>z. z \<in> setr x \<Longrightarrow> f2 z = g2 z"
  thus "map_sum f1 f2 x = map_sum g1 g2 x"
  proof (cases x)
    case Inl thus ?thesis using a1 by (clarsimp simp: sum_set_defs(1))
  next
    case Inr thus ?thesis using a2 by (clarsimp simp: sum_set_defs(2))
  qed
next
  fix f1 :: "'o \<Rightarrow> 'q" and f2 :: "'p \<Rightarrow> 'r"
  show "setl o map_sum f1 f2 = image f1 o setl"
    by (rule ext, unfold o_apply) (simp add: sum_set_defs(1) split: sum.split)
next
  fix f1 :: "'o \<Rightarrow> 'q" and f2 :: "'p \<Rightarrow> 'r"
  show "setr o map_sum f1 f2 = image f2 o setr"
    by (rule ext, unfold o_apply) (simp add: sum_set_defs(2) split: sum.split)
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix x :: "'o + 'p"
  show "|setl x| \<le>o natLeq"
    apply (rule ordLess_imp_ordLeq)
    apply (rule finite_iff_ordLess_natLeq[THEN iffD1])
    by (simp add: sum_set_defs(1) split: sum.split)
next
  fix x :: "'o + 'p"
  show "|setr x| \<le>o natLeq"
    apply (rule ordLess_imp_ordLeq)
    apply (rule finite_iff_ordLess_natLeq[THEN iffD1])
    by (simp add: sum_set_defs(2) split: sum.split)
next
  fix R1 R2 S1 S2
  show "rel_sum R1 R2 OO rel_sum S1 S2 \<le> rel_sum (R1 OO S1) (R2 OO S2)"
    by (force elim: rel_sum.cases)
next
  fix R S
  show "rel_sum R S =
        (Grp {x. setl x \<subseteq> Collect (split R) \<and> setr x \<subseteq> Collect (split S)} (map_sum fst fst))\<inverse>\<inverse> OO
        Grp {x. setl x \<subseteq> Collect (split R) \<and> setr x \<subseteq> Collect (split S)} (map_sum snd snd)"
  unfolding sum_set_defs Grp_def relcompp.simps conversep.simps fun_eq_iff
  by (fastforce elim: rel_sum.cases split: sum.splits)
qed (auto simp: sum_set_defs)

inductive_set fsts :: "'a \<times> 'b \<Rightarrow> 'a set" for p :: "'a \<times> 'b" where
  "fst p \<in> fsts p"
inductive_set snds :: "'a \<times> 'b \<Rightarrow> 'b set" for p :: "'a \<times> 'b" where
  "snd p \<in> snds p"

lemma prod_set_defs[code]: "fsts = (\<lambda>p. {fst p})" "snds = (\<lambda>p. {snd p})"
  by (auto intro: fsts.intros snds.intros elim: fsts.cases snds.cases)

inductive
  rel_prod :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'c \<Rightarrow> 'b \<times> 'd \<Rightarrow> bool" for R1 R2
where
  "\<lbrakk>R1 a b; R2 c d\<rbrakk> \<Longrightarrow> rel_prod R1 R2 (a, c) (b, d)"

hide_fact rel_prod_def

lemma rel_prod_apply [code, simp]:
  "rel_prod R1 R2 (a, b) (c, d) \<longleftrightarrow> R1 a c \<and> R2 b d"
  by (auto intro: rel_prod.intros elim: rel_prod.cases)

lemma rel_prod_conv:
  "rel_prod R1 R2 = (\<lambda>(a, b) (c, d). R1 a c \<and> R2 b d)"
  by (rule ext, rule ext) auto

bnf "'a \<times> 'b"
  map: map_prod
  sets: fsts snds
  bd: natLeq
  rel: rel_prod
proof (unfold prod_set_defs)
  show "map_prod id id = id" by (rule map_prod.id)
next
  fix f1 f2 g1 g2
  show "map_prod (g1 o f1) (g2 o f2) = map_prod g1 g2 o map_prod f1 f2"
    by (rule map_prod.comp[symmetric])
next
  fix x f1 f2 g1 g2
  assume "\<And>z. z \<in> {fst x} \<Longrightarrow> f1 z = g1 z" "\<And>z. z \<in> {snd x} \<Longrightarrow> f2 z = g2 z"
  thus "map_prod f1 f2 x = map_prod g1 g2 x" by (cases x) simp
next
  fix f1 f2
  show "(\<lambda>x. {fst x}) o map_prod f1 f2 = image f1 o (\<lambda>x. {fst x})"
    by (rule ext, unfold o_apply) simp
next
  fix f1 f2
  show "(\<lambda>x. {snd x}) o map_prod f1 f2 = image f2 o (\<lambda>x. {snd x})"
    by (rule ext, unfold o_apply) simp
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix x
  show "|{fst x}| \<le>o natLeq"
    by (rule ordLess_imp_ordLeq) (simp add: finite_iff_ordLess_natLeq[symmetric])
next
  fix x
  show "|{snd x}| \<le>o natLeq"
    by (rule ordLess_imp_ordLeq) (simp add: finite_iff_ordLess_natLeq[symmetric])
next
  fix R1 R2 S1 S2
  show "rel_prod R1 R2 OO rel_prod S1 S2 \<le> rel_prod (R1 OO S1) (R2 OO S2)" by auto
next
  fix R S
  show "rel_prod R S =
        (Grp {x. {fst x} \<subseteq> Collect (split R) \<and> {snd x} \<subseteq> Collect (split S)} (map_prod fst fst))\<inverse>\<inverse> OO
        Grp {x. {fst x} \<subseteq> Collect (split R) \<and> {snd x} \<subseteq> Collect (split S)} (map_prod snd snd)"
  unfolding prod_set_defs rel_prod_apply Grp_def relcompp.simps conversep.simps fun_eq_iff
  by auto
qed

bnf "'a \<Rightarrow> 'b"
  map: "op \<circ>"
  sets: range
  bd: "natLeq +c |UNIV :: 'a set|"
  rel: "rel_fun op ="
proof
  fix f show "id \<circ> f = id f" by simp
next
  fix f g show "op \<circ> (g \<circ> f) = op \<circ> g \<circ> op \<circ> f"
  unfolding comp_def[abs_def] ..
next
  fix x f g
  assume "\<And>z. z \<in> range x \<Longrightarrow> f z = g z"
  thus "f \<circ> x = g \<circ> x" by auto
next
  fix f show "range \<circ> op \<circ> f = op ` f \<circ> range"
    by (auto simp add: fun_eq_iff)
next
  show "card_order (natLeq +c |UNIV| )" (is "_ (_ +c ?U)")
  apply (rule card_order_csum)
  apply (rule natLeq_card_order)
  by (rule card_of_card_order_on)
(*  *)
  show "cinfinite (natLeq +c ?U)"
    apply (rule cinfinite_csum)
    apply (rule disjI1)
    by (rule natLeq_cinfinite)
next
  fix f :: "'d => 'a"
  have "|range f| \<le>o | (UNIV::'d set) |" (is "_ \<le>o ?U") by (rule card_of_image)
  also have "?U \<le>o natLeq +c ?U" by (rule ordLeq_csum2) (rule card_of_Card_order)
  finally show "|range f| \<le>o natLeq +c ?U" .
next
  fix R S
  show "rel_fun op = R OO rel_fun op = S \<le> rel_fun op = (R OO S)" by (auto simp: rel_fun_def)
next
  fix R
  show "rel_fun op = R =
        (Grp {x. range x \<subseteq> Collect (split R)} (op \<circ> fst))\<inverse>\<inverse> OO
         Grp {x. range x \<subseteq> Collect (split R)} (op \<circ> snd)"
  unfolding rel_fun_def Grp_def fun_eq_iff relcompp.simps conversep.simps subset_iff image_iff
    comp_apply mem_Collect_eq split_beta bex_UNIV
  proof (safe, unfold fun_eq_iff[symmetric])
    fix x xa a b c xb y aa ba
    assume *: "x = a" "xa = c" "a = ba" "b = aa" "c = (\<lambda>x. snd (b x))" "ba = (\<lambda>x. fst (aa x))" and
       **: "\<forall>t. (\<exists>x. t = aa x) \<longrightarrow> R (fst t) (snd t)"
    show "R (x y) (xa y)" unfolding * by (rule mp[OF spec[OF **]]) blast
  qed force
qed

end
