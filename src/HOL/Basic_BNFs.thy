(*  Title:      HOL/Basic_BNFs.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Jan van Brügge, TU Muenchen
    Copyright   2012, 2022

Registration of basic types as bounded natural functors.
*)

section \<open>Registration of Basic Types as Bounded Natural Functors\<close>

theory Basic_BNFs
imports BNF_Def
begin

inductive_set setl :: "'a + 'b \<Rightarrow> 'a set" for s :: "'a + 'b" where
  "s = Inl x \<Longrightarrow> x \<in> setl s"
inductive_set setr :: "'a + 'b \<Rightarrow> 'b set" for s :: "'a + 'b" where
  "s = Inr x \<Longrightarrow> x \<in> setr s"

lemma sum_set_defs [code]:
  "setl = (\<lambda>x. case x of Inl z \<Rightarrow> {z} | _ \<Rightarrow> {})"
  "setr = (\<lambda>x. case x of Inr z \<Rightarrow> {z} | _ \<Rightarrow> {})"
  by (auto simp: fun_eq_iff intro: setl.intros setr.intros elim: setl.cases setr.cases split: sum.splits)

lemma rel_sum_simps [code, simp]:
  "rel_sum R1 R2 (Inl a1) (Inl b1) = R1 a1 b1"
  "rel_sum R1 R2 (Inl a1) (Inr b2) = False"
  "rel_sum R1 R2 (Inr a2) (Inl b1) = False"
  "rel_sum R1 R2 (Inr a2) (Inr b2) = R2 a2 b2"
  by (auto intro: rel_sum.intros elim: rel_sum.cases)

inductive
   pred_sum :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> bool" for P1 P2
where
  "P1 a \<Longrightarrow> pred_sum P1 P2 (Inl a)"
| "P2 b \<Longrightarrow> pred_sum P1 P2 (Inr b)"

lemma pred_sum_inject [code, simp]:
  "pred_sum P1 P2 (Inl a) \<longleftrightarrow> P1 a"
  "pred_sum P1 P2 (Inr b) \<longleftrightarrow> P2 b"
  by (simp add: pred_sum.simps)+

bnf "'a + 'b"
  map: map_sum
  sets: setl setr
  bd: natLeq
  wits: Inl Inr
  rel: rel_sum
  pred: pred_sum
proof -
  show "map_sum id id = id" by (rule map_sum.id)
next
  fix f1 :: "'o \<Rightarrow> 's" and f2 :: "'p \<Rightarrow> 't" and g1 :: "'s \<Rightarrow> 'q" and g2 :: "'t \<Rightarrow> 'r"
  show "map_sum (g1 \<circ> f1) (g2 \<circ> f2) = map_sum g1 g2 \<circ> map_sum f1 f2"
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
  show "setl \<circ> map_sum f1 f2 = image f1 \<circ> setl"
    by (rule ext, unfold o_apply) (simp add: sum_set_defs(1) split: sum.split)
next
  fix f1 :: "'o \<Rightarrow> 'q" and f2 :: "'p \<Rightarrow> 'r"
  show "setr \<circ> map_sum f1 f2 = image f2 \<circ> setr"
    by (rule ext, unfold o_apply) (simp add: sum_set_defs(2) split: sum.split)
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  show "regularCard natLeq" by (rule regularCard_natLeq)
next
  fix x :: "'o + 'p"
  show "|setl x| <o natLeq"
    apply (rule finite_iff_ordLess_natLeq[THEN iffD1])
    by (simp add: sum_set_defs(1) split: sum.split)
next
  fix x :: "'o + 'p"
  show "|setr x| <o natLeq"
    apply (rule finite_iff_ordLess_natLeq[THEN iffD1])
    by (simp add: sum_set_defs(2) split: sum.split)
next
  fix R1 R2 S1 S2
  show "rel_sum R1 R2 OO rel_sum S1 S2 \<le> rel_sum (R1 OO S1) (R2 OO S2)"
    by (force elim: rel_sum.cases)
next
  fix R S
  show "rel_sum R S = (\<lambda>x y.
    \<exists>z. (setl z \<subseteq> {(x, y). R x y} \<and> setr z \<subseteq> {(x, y). S x y}) \<and>
    map_sum fst fst z = x \<and> map_sum snd snd z = y)"
  unfolding sum_set_defs relcompp.simps conversep.simps fun_eq_iff
  by (fastforce elim: rel_sum.cases split: sum.splits)
qed (auto simp: sum_set_defs fun_eq_iff pred_sum.simps split: sum.splits)

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

inductive
  pred_prod :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" for P1 P2
where
  "\<lbrakk>P1 a; P2 b\<rbrakk> \<Longrightarrow> pred_prod P1 P2 (a, b)"

lemma rel_prod_inject [code, simp]:
  "rel_prod R1 R2 (a, b) (c, d) \<longleftrightarrow> R1 a c \<and> R2 b d"
  by (auto intro: rel_prod.intros elim: rel_prod.cases)

lemma pred_prod_inject [code, simp]:
  "pred_prod P1 P2 (a, b) \<longleftrightarrow> P1 a \<and> P2 b"
  by (auto intro: pred_prod.intros elim: pred_prod.cases)

lemma rel_prod_conv:
  "rel_prod R1 R2 = (\<lambda>(a, b) (c, d). R1 a c \<and> R2 b d)"
  by force

definition
  pred_fun :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "pred_fun A B = (\<lambda>f. \<forall>x. A x \<longrightarrow> B (f x))"

lemma pred_funI: "(\<And>x. A x \<Longrightarrow> B (f x)) \<Longrightarrow> pred_fun A B f"
  unfolding pred_fun_def by simp

bnf "'a \<times> 'b"
  map: map_prod
  sets: fsts snds
  bd: natLeq
  rel: rel_prod
  pred: pred_prod
proof (unfold prod_set_defs)
  show "map_prod id id = id" by (rule map_prod.id)
next
  fix f1 f2 g1 g2
  show "map_prod (g1 \<circ> f1) (g2 \<circ> f2) = map_prod g1 g2 \<circ> map_prod f1 f2"
    by (rule map_prod.comp[symmetric])
next
  fix x f1 f2 g1 g2
  assume "\<And>z. z \<in> {fst x} \<Longrightarrow> f1 z = g1 z" "\<And>z. z \<in> {snd x} \<Longrightarrow> f2 z = g2 z"
  thus "map_prod f1 f2 x = map_prod g1 g2 x" by (cases x) simp
next
  fix f1 f2
  show "(\<lambda>x. {fst x}) \<circ> map_prod f1 f2 = image f1 \<circ> (\<lambda>x. {fst x})"
    by (rule ext, unfold o_apply) simp
next
  fix f1 f2
  show "(\<lambda>x. {snd x}) \<circ> map_prod f1 f2 = image f2 \<circ> (\<lambda>x. {snd x})"
    by (rule ext, unfold o_apply) simp
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  show "regularCard natLeq" by (rule regularCard_natLeq)
next
  fix x
  show "|{fst x}| <o natLeq"
    by (simp add: finite_iff_ordLess_natLeq[symmetric])
next
  fix x
  show "|{snd x}| <o natLeq"
    by (simp add: finite_iff_ordLess_natLeq[symmetric])
next
  fix R1 R2 S1 S2
  show "rel_prod R1 R2 OO rel_prod S1 S2 \<le> rel_prod (R1 OO S1) (R2 OO S2)" by auto
next
  fix R S
  show "rel_prod R S = (\<lambda>x y.
    \<exists>z. ({fst z} \<subseteq> {(x, y). R x y} \<and> {snd z} \<subseteq> {(x, y). S x y}) \<and>
      map_prod fst fst z = x \<and> map_prod snd snd z = y)"
  unfolding prod_set_defs rel_prod_inject relcompp.simps conversep.simps fun_eq_iff
  by auto
qed auto

lemma card_order_bd_fun: "card_order (natLeq +c card_suc ( |UNIV| ))"
  by (auto simp: card_order_csum natLeq_card_order card_order_card_suc card_of_card_order_on)

lemma Cinfinite_bd_fun: "Cinfinite (natLeq +c card_suc ( |UNIV| ))"
  by (auto simp: Cinfinite_csum natLeq_Cinfinite)

lemma regularCard_bd_fun: "regularCard (natLeq +c card_suc ( |UNIV| ))"
  (is "regularCard (_ +c card_suc ?U)")
proof (cases "Cinfinite ?U")
  case True
  then show ?thesis 
    by (intro regularCard_csum natLeq_Cinfinite Cinfinite_card_suc 
              card_of_card_order_on regularCard_natLeq regularCard_card_suc)
next
  case False
  then have "card_suc ?U \<le>o natLeq"
    unfolding cinfinite_def Field_card_of
    by (intro card_suc_least; 
        simp add: natLeq_Card_order card_of_card_order_on flip: finite_iff_ordLess_natLeq)
  then have "natLeq =o natLeq +c card_suc ?U"
    using natLeq_Cinfinite csum_absorb1 ordIso_symmetric by blast
  then show ?thesis 
    by (intro regularCard_ordIso[OF _ natLeq_Cinfinite regularCard_natLeq])
qed

lemma ordLess_bd_fun: "|UNIV::'a set| <o natLeq +c card_suc ( |UNIV::'a set| )"
  (is "_ <o (_ +c card_suc (?U :: 'a rel))")
proof (cases "Cinfinite ?U")
  case True
  have "?U <o card_suc ?U" using card_of_card_order_on natLeq_card_order card_suc_greater by blast
  also have "card_suc ?U =o natLeq +c card_suc ?U" by (rule csum_absorb2[THEN ordIso_symmetric])
    (auto simp: True card_of_card_order_on intro!: Cinfinite_card_suc natLeq_ordLeq_cinfinite)
  finally show ?thesis .
next
  case False
  then have "?U <o natLeq"
    by (auto simp: cinfinite_def Field_card_of card_of_card_order_on finite_iff_ordLess_natLeq[symmetric])
  then show ?thesis
    by (rule ordLess_ordLeq_trans[OF _ ordLeq_csum1[OF natLeq_Card_order]])
qed

bnf "'a \<Rightarrow> 'b"
  map: "(\<circ>)"
  sets: range
  bd: "natLeq +c card_suc ( |UNIV::'a set| )"
  rel: "rel_fun (=)"
  pred: "pred_fun (\<lambda>_. True)"
proof
  fix f show "id \<circ> f = id f" by simp
next
  fix f g show "(\<circ>) (g \<circ> f) = (\<circ>) g \<circ> (\<circ>) f"
  unfolding comp_def[abs_def] ..
next
  fix x f g
  assume "\<And>z. z \<in> range x \<Longrightarrow> f z = g z"
  thus "f \<circ> x = g \<circ> x" by auto
next
  fix f show "range \<circ> (\<circ>) f = (`) f \<circ> range"
    by (auto simp add: fun_eq_iff)
next
  show "card_order (natLeq +c card_suc ( |UNIV| ))"
    by (rule card_order_bd_fun)
next
  show "cinfinite (natLeq +c card_suc ( |UNIV| ))"
    by (rule Cinfinite_bd_fun[THEN conjunct1])
next
  show "regularCard (natLeq +c card_suc ( |UNIV| ))"
    by (rule regularCard_bd_fun)
next
  fix f :: "'d \<Rightarrow> 'a"
  show "|range f| <o natLeq +c card_suc |UNIV :: 'd set|"
    by (rule ordLeq_ordLess_trans[OF card_of_image ordLess_bd_fun])
next
  fix R S
  show "rel_fun (=) R OO rel_fun (=) S \<le> rel_fun (=) (R OO S)" by (auto simp: rel_fun_def)
next
  fix R
  show "rel_fun (=) R = (\<lambda>x y.
    \<exists>z. range z \<subseteq> {(x, y). R x y} \<and> fst \<circ> z = x \<and> snd \<circ> z = y)"
  unfolding rel_fun_def subset_iff by (force simp: fun_eq_iff[symmetric])
qed (auto simp: pred_fun_def)

end
