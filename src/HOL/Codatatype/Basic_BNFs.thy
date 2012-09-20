(*  Title:      HOL/Codatatype/Basic_BNFs.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Registration of basic types as bounded natural functors.
*)

header {* Registration of Basic Types as Bounded Natural Functors *}

theory Basic_BNFs
imports BNF_Def
begin

lemma wpull_id: "wpull UNIV B1 B2 id id id id"
unfolding wpull_def by simp

lemmas natLeq_card_order = natLeq_Card_order[unfolded Field_natLeq]

lemma ctwo_card_order: "card_order ctwo"
using Card_order_ctwo by (unfold ctwo_def Field_card_of)

lemma natLeq_cinfinite: "cinfinite natLeq"
unfolding cinfinite_def Field_natLeq by (rule nat_infinite)

bnf_def ID: "id :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ["\<lambda>x. {x}"] "\<lambda>_:: 'a. natLeq" ["id :: 'a \<Rightarrow> 'a"]
  "\<lambda>x :: ('a \<times> 'b) set. x"
apply auto
apply (rule natLeq_card_order)
apply (rule natLeq_cinfinite)
apply (rule ordLess_imp_ordLeq[OF finite_ordLess_infinite[OF _ natLeq_Well_order]])
apply (auto simp add: Field_card_of Field_natLeq card_of_well_order_on)[3]
apply (rule ordLeq_transitive)
apply (rule ordLeq_cexp1[of natLeq])
apply (rule Cinfinite_Cnotzero)
apply (rule conjI)
apply (rule natLeq_cinfinite)
apply (rule natLeq_Card_order)
apply (rule card_of_Card_order)
apply (rule cexp_mono1)
apply (rule ordLeq_csum1)
apply (rule card_of_Card_order)
apply (rule disjI2)
apply (rule cone_ordLeq_cexp)
apply (rule ordLeq_transitive)
apply (rule cone_ordLeq_ctwo)
apply (rule ordLeq_csum2)
apply (rule Card_order_ctwo)
apply (rule natLeq_Card_order)
apply (auto simp: Gr_def fun_eq_iff)
done

bnf_def DEADID: "id :: 'a \<Rightarrow> 'a" [] "\<lambda>_:: 'a. natLeq +c |UNIV :: 'a set|" ["SOME x :: 'a. True"] Id
apply (auto simp add: wpull_id)
apply (rule card_order_csum)
apply (rule natLeq_card_order)
apply (rule card_of_card_order_on)
apply (rule cinfinite_csum)
apply (rule disjI1)
apply (rule natLeq_cinfinite)
apply (rule ordLess_imp_ordLeq)
apply (rule ordLess_ordLeq_trans)
apply (rule ordLess_ctwo_cexp)
apply (rule card_of_Card_order)
apply (rule cexp_mono2'')
apply (rule ordLeq_csum2)
apply (rule card_of_Card_order)
apply (rule ctwo_Cnotzero)
apply (rule card_of_Card_order)
apply (auto simp: Id_def Gr_def fun_eq_iff)
done

definition setl :: "'a + 'b \<Rightarrow> 'a set" where
"setl x = (case x of Inl z => {z} | _ => {})"

definition setr :: "'a + 'b \<Rightarrow> 'b set" where
"setr x = (case x of Inr z => {z} | _ => {})"

lemmas sum_set_defs = setl_def[abs_def] setr_def[abs_def]

(*### RENAME TODO *)
definition sum_rel0 :: "('a \<times> 'b) set \<Rightarrow> ('c \<times> 'd) set \<Rightarrow> (('a + 'c) \<times> ('b + 'd)) set" where
"sum_rel0 R S =
   {x. case x of (Inl a, Inl c) \<Rightarrow> (a, c) \<in> R
       | (Inr b, Inr d) \<Rightarrow> (b, d) \<in> S
       | _ \<Rightarrow> False}"

bnf_def sum_map [setl, setr] "\<lambda>_::'a + 'b. natLeq" [Inl, Inr] sum_rel0
proof -
  show "sum_map id id = id" by (rule sum_map.id)
next
  fix f1 f2 g1 g2
  show "sum_map (g1 o f1) (g2 o f2) = sum_map g1 g2 o sum_map f1 f2"
    by (rule sum_map.comp[symmetric])
next
  fix x f1 f2 g1 g2
  assume a1: "\<And>z. z \<in> setl x \<Longrightarrow> f1 z = g1 z" and
         a2: "\<And>z. z \<in> setr x \<Longrightarrow> f2 z = g2 z"
  thus "sum_map f1 f2 x = sum_map g1 g2 x"
  proof (cases x)
    case Inl thus ?thesis using a1 by (clarsimp simp: setl_def)
  next
    case Inr thus ?thesis using a2 by (clarsimp simp: setr_def)
  qed
next
  fix f1 f2
  show "setl o sum_map f1 f2 = image f1 o setl"
    by (rule ext, unfold o_apply) (simp add: setl_def split: sum.split)
next
  fix f1 f2
  show "setr o sum_map f1 f2 = image f2 o setr"
    by (rule ext, unfold o_apply) (simp add: setr_def split: sum.split)
next
  show "card_order natLeq" by (rule natLeq_card_order)
next
  show "cinfinite natLeq" by (rule natLeq_cinfinite)
next
  fix x
  show "|setl x| \<le>o natLeq"
    apply (rule ordLess_imp_ordLeq)
    apply (rule finite_iff_ordLess_natLeq[THEN iffD1])
    by (simp add: setl_def split: sum.split)
next
  fix x
  show "|setr x| \<le>o natLeq"
    apply (rule ordLess_imp_ordLeq)
    apply (rule finite_iff_ordLess_natLeq[THEN iffD1])
    by (simp add: setr_def split: sum.split)
next
  fix A1 :: "'a set" and A2 :: "'b set"
  have in_alt: "{x. (case x of Inl z => {z} | _ => {}) \<subseteq> A1 \<and>
    (case x of Inr z => {z} | _ => {}) \<subseteq> A2} = A1 <+> A2" (is "?L = ?R")
  proof safe
    fix x :: "'a + 'b"
    assume "(case x of Inl z \<Rightarrow> {z} | _ \<Rightarrow> {}) \<subseteq> A1" "(case x of Inr z \<Rightarrow> {z} | _ \<Rightarrow> {}) \<subseteq> A2"
    hence "x \<in> Inl ` A1 \<or> x \<in> Inr ` A2" by (cases x) simp+
    thus "x \<in> A1 <+> A2" by blast
  qed (auto split: sum.split)
  show "|{x. setl x \<subseteq> A1 \<and> setr x \<subseteq> A2}| \<le>o
    (( |A1| +c |A2| ) +c ctwo) ^c natLeq"
    apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (unfold sum_set_defs)
    apply (rule in_alt)
    apply (rule ordIso_ordLeq_trans)
    apply (rule Plus_csum)
    apply (rule ordLeq_transitive)
    apply (rule ordLeq_csum1)
    apply (rule Card_order_csum)
    apply (rule ordLeq_cexp1)
    apply (rule conjI)
    using Field_natLeq UNIV_not_empty czeroE apply fast
    apply (rule natLeq_Card_order)
    by (rule Card_order_csum)
next
  fix A1 A2 B11 B12 B21 B22 f11 f12 f21 f22 p11 p12 p21 p22
  assume "wpull A1 B11 B21 f11 f21 p11 p21" "wpull A2 B12 B22 f12 f22 p12 p22"
  hence
    pull1: "\<And>b1 b2. \<lbrakk>b1 \<in> B11; b2 \<in> B21; f11 b1 = f21 b2\<rbrakk> \<Longrightarrow> \<exists>a \<in> A1. p11 a = b1 \<and> p21 a = b2"
    and pull2: "\<And>b1 b2. \<lbrakk>b1 \<in> B12; b2 \<in> B22; f12 b1 = f22 b2\<rbrakk> \<Longrightarrow> \<exists>a \<in> A2. p12 a = b1 \<and> p22 a = b2"
    unfolding wpull_def by blast+
  show "wpull {x. setl x \<subseteq> A1 \<and> setr x \<subseteq> A2}
  {x. setl x \<subseteq> B11 \<and> setr x \<subseteq> B12} {x. setl x \<subseteq> B21 \<and> setr x \<subseteq> B22}
  (sum_map f11 f12) (sum_map f21 f22) (sum_map p11 p12) (sum_map p21 p22)"
    (is "wpull ?in ?in1 ?in2 ?mapf1 ?mapf2 ?mapp1 ?mapp2")
  proof (unfold wpull_def)
    { fix B1 B2
      assume *: "B1 \<in> ?in1" "B2 \<in> ?in2" "?mapf1 B1 = ?mapf2 B2"
      have "\<exists>A \<in> ?in. ?mapp1 A = B1 \<and> ?mapp2 A = B2"
      proof (cases B1)
        case (Inl b1)
        { fix b2 assume "B2 = Inr b2"
          with Inl *(3) have False by simp
        } then obtain b2 where Inl': "B2 = Inl b2" by (cases B2) (simp, blast)
        with Inl * have "b1 \<in> B11" "b2 \<in> B21" "f11 b1 = f21 b2"
        by (simp add: setl_def)+
        with pull1 obtain a where "a \<in> A1" "p11 a = b1" "p21 a = b2" by blast+
        with Inl Inl' have "Inl a \<in> ?in" "?mapp1 (Inl a) = B1 \<and> ?mapp2 (Inl a) = B2"
        by (simp add: sum_set_defs)+
        thus ?thesis by blast
      next
        case (Inr b1)
        { fix b2 assume "B2 = Inl b2"
          with Inr *(3) have False by simp
        } then obtain b2 where Inr': "B2 = Inr b2" by (cases B2) (simp, blast)
        with Inr * have "b1 \<in> B12" "b2 \<in> B22" "f12 b1 = f22 b2"
        by (simp add: sum_set_defs)+
        with pull2 obtain a where "a \<in> A2" "p12 a = b1" "p22 a = b2" by blast+
        with Inr Inr' have "Inr a \<in> ?in" "?mapp1 (Inr a) = B1 \<and> ?mapp2 (Inr a) = B2"
        by (simp add: sum_set_defs)+
        thus ?thesis by blast
      qed
    }
    thus "\<forall>B1 B2. B1 \<in> ?in1 \<and> B2 \<in> ?in2 \<and> ?mapf1 B1 = ?mapf2 B2 \<longrightarrow>
      (\<exists>A \<in> ?in. ?mapp1 A = B1 \<and> ?mapp2 A = B2)" by fastforce
  qed
next
  fix R S
  show "sum_rel0 R S =
          (Gr {x. setl x \<subseteq> R \<and> setr x \<subseteq> S} (sum_map fst fst))\<inverse> O
          Gr {x. setl x \<subseteq> R \<and> setr x \<subseteq> S} (sum_map snd snd)"
  unfolding setl_def setr_def sum_rel0_def Gr_def relcomp_unfold converse_unfold
  by (fastforce split: sum.splits)
qed (auto simp: sum_set_defs)

lemma singleton_ordLeq_ctwo_natLeq: "|{x}| \<le>o ctwo *c natLeq"
  apply (rule ordLeq_transitive)
  apply (rule ordLeq_cprod2)
  apply (rule ctwo_Cnotzero)
  apply (auto simp: Field_card_of intro: card_of_card_order_on)
  apply (rule cprod_mono2)
  apply (rule ordLess_imp_ordLeq)
  apply (unfold finite_iff_ordLess_natLeq[symmetric])
  by simp

definition fsts :: "'a \<times> 'b \<Rightarrow> 'a set" where
"fsts x = {fst x}"

definition snds :: "'a \<times> 'b \<Rightarrow> 'b set" where
"snds x = {snd x}"

lemmas prod_set_defs = fsts_def[abs_def] snds_def[abs_def]

definition prod_rel0 :: "('a \<times> 'b) set \<Rightarrow> ('c \<times> 'd) set \<Rightarrow> (('a \<times> 'c) \<times> 'b \<times> 'd) set" where
"prod_rel0 R S = {((a, c), b, d) | a b c d. (a, b) \<in> R \<and> (c, d) \<in> S}"

bnf_def map_pair [fsts, snds] "\<lambda>_::'a \<times> 'b. ctwo *c natLeq" [Pair] prod_rel0
proof (unfold prod_set_defs)
  show "map_pair id id = id" by (rule map_pair.id)
next
  fix f1 f2 g1 g2
  show "map_pair (g1 o f1) (g2 o f2) = map_pair g1 g2 o map_pair f1 f2"
    by (rule map_pair.comp[symmetric])
next
  fix x f1 f2 g1 g2
  assume "\<And>z. z \<in> {fst x} \<Longrightarrow> f1 z = g1 z" "\<And>z. z \<in> {snd x} \<Longrightarrow> f2 z = g2 z"
  thus "map_pair f1 f2 x = map_pair g1 g2 x" by (cases x) simp
next
  fix f1 f2
  show "(\<lambda>x. {fst x}) o map_pair f1 f2 = image f1 o (\<lambda>x. {fst x})"
    by (rule ext, unfold o_apply) simp
next
  fix f1 f2
  show "(\<lambda>x. {snd x}) o map_pair f1 f2 = image f2 o (\<lambda>x. {snd x})"
    by (rule ext, unfold o_apply) simp
next
  show "card_order (ctwo *c natLeq)"
    apply (rule card_order_cprod)
    apply (rule ctwo_card_order)
    by (rule natLeq_card_order)
next
  show "cinfinite (ctwo *c natLeq)"
    apply (rule cinfinite_cprod2)
    apply (rule ctwo_Cnotzero)
    apply (rule conjI[OF _ natLeq_Card_order])
    by (rule natLeq_cinfinite)
next
  fix x
  show "|{fst x}| \<le>o ctwo *c natLeq"
    by (rule singleton_ordLeq_ctwo_natLeq)
next
  fix x
  show "|{snd x}| \<le>o ctwo *c natLeq"
    by (rule singleton_ordLeq_ctwo_natLeq)
next
  fix A1 :: "'a set" and A2 :: "'b set"
  have in_alt: "{x. {fst x} \<subseteq> A1 \<and> {snd x} \<subseteq> A2} = A1 \<times> A2" by auto
  show "|{x. {fst x} \<subseteq> A1 \<and> {snd x} \<subseteq> A2}| \<le>o
    ( ( |A1| +c |A2| ) +c ctwo) ^c (ctwo *c natLeq)"
    apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (rule in_alt)
    apply (rule ordIso_ordLeq_trans)
    apply (rule Times_cprod)
    apply (rule ordLeq_transitive)
    apply (rule cprod_csum_cexp)
    apply (rule cexp_mono)
    apply (rule ordLeq_csum1)
    apply (rule Card_order_csum)
    apply (rule ordLeq_cprod1)
    apply (rule Card_order_ctwo)
    apply (rule Cinfinite_Cnotzero)
    apply (rule conjI[OF _ natLeq_Card_order])
    apply (rule natLeq_cinfinite)
    apply (rule disjI2)
    apply (rule cone_ordLeq_cexp)
    apply (rule ordLeq_transitive)
    apply (rule cone_ordLeq_ctwo)
    apply (rule ordLeq_csum2)
    apply (rule Card_order_ctwo)
    apply (rule notE)
    apply (rule ctwo_not_czero)
    apply assumption
    by (rule Card_order_ctwo)
next
  fix A1 A2 B11 B12 B21 B22 f11 f12 f21 f22 p11 p12 p21 p22
  assume "wpull A1 B11 B21 f11 f21 p11 p21" "wpull A2 B12 B22 f12 f22 p12 p22"
  thus "wpull {x. {fst x} \<subseteq> A1 \<and> {snd x} \<subseteq> A2}
    {x. {fst x} \<subseteq> B11 \<and> {snd x} \<subseteq> B12} {x. {fst x} \<subseteq> B21 \<and> {snd x} \<subseteq> B22}
   (map_pair f11 f12) (map_pair f21 f22) (map_pair p11 p12) (map_pair p21 p22)"
    unfolding wpull_def by simp fast
next
  fix R S
  show "prod_rel0 R S =
          (Gr {x. {fst x} \<subseteq> R \<and> {snd x} \<subseteq> S} (map_pair fst fst))\<inverse> O
          Gr {x. {fst x} \<subseteq> R \<and> {snd x} \<subseteq> S} (map_pair snd snd)"
  unfolding prod_set_defs prod_rel0_def Gr_def relcomp_unfold converse_unfold
  by auto
qed simp+

(* Categorical version of pullback: *)
lemma wpull_cat:
assumes p: "wpull A B1 B2 f1 f2 p1 p2"
and c: "f1 o q1 = f2 o q2"
and r: "range q1 \<subseteq> B1" "range q2 \<subseteq> B2"
obtains h where "range h \<subseteq> A \<and> q1 = p1 o h \<and> q2 = p2 o h"
proof-
  have *: "\<forall>d. \<exists>a \<in> A. p1 a = q1 d & p2 a = q2 d"
  proof safe
    fix d
    have "f1 (q1 d) = f2 (q2 d)" using c unfolding comp_def[abs_def] by (rule fun_cong)
    moreover
    have "q1 d : B1" "q2 d : B2" using r unfolding image_def by auto
    ultimately show "\<exists>a \<in> A. p1 a = q1 d \<and> p2 a = q2 d"
      using p unfolding wpull_def by auto
  qed
  then obtain h where "!! d. h d \<in> A & p1 (h d) = q1 d & p2 (h d) = q2 d" by metis
  thus ?thesis using that by fastforce
qed

lemma card_of_bounded_range:
  "|{f :: 'd \<Rightarrow> 'a. range f \<subseteq> B}| \<le>o |Func (UNIV :: 'd set) B|" (is "|?LHS| \<le>o |?RHS|")
proof -
  let ?f = "\<lambda>f. %x. if f x \<in> B then Some (f x) else None"
  have "inj_on ?f ?LHS" unfolding inj_on_def
  proof (unfold fun_eq_iff, safe)
    fix g :: "'d \<Rightarrow> 'a" and f :: "'d \<Rightarrow> 'a" and x
    assume "range f \<subseteq> B" "range g \<subseteq> B" and eq: "\<forall>x. ?f f x = ?f g x"
    hence "f x \<in> B" "g x \<in> B" by auto
    with eq have "Some (f x) = Some (g x)" by metis
    thus "f x = g x" by simp
  qed
  moreover have "?f ` ?LHS \<subseteq> ?RHS" unfolding Func_def by fastforce
  ultimately show ?thesis using card_of_ordLeq by fast
qed

definition fun_rel0 :: "('a \<times> 'b) set \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'b)) set" where
"fun_rel0 R = {(f, g) | f g. \<forall>x. (f x, g x) \<in> R}"

bnf_def "op \<circ>" [range] "\<lambda>_:: 'a \<Rightarrow> 'b. natLeq +c |UNIV :: 'a set|" ["%c x::'b::type. c::'a::type"]
  fun_rel0
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
  unfolding image_def comp_def[abs_def] by auto
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
  also have "?U \<le>o natLeq +c ?U"  by (rule ordLeq_csum2) (rule card_of_Card_order)
  finally show "|range f| \<le>o natLeq +c ?U" .
next
  fix B :: "'a set"
  have "|{f::'d => 'a. range f \<subseteq> B}| \<le>o |Func (UNIV :: 'd set) B|" by (rule card_of_bounded_range)
  also have "|Func (UNIV :: 'd set) B| =o |B| ^c |UNIV :: 'd set|"
    unfolding cexp_def Field_card_of by (rule card_of_refl)
  also have "|B| ^c |UNIV :: 'd set| \<le>o
             ( |B| +c ctwo) ^c (natLeq +c |UNIV :: 'd set| )"
    apply (rule cexp_mono)
     apply (rule ordLeq_csum1) apply (rule card_of_Card_order)
     apply (rule ordLeq_csum2) apply (rule card_of_Card_order)
     apply (rule disjI2) apply (rule cone_ordLeq_cexp)
      apply (rule ordLeq_transitive) apply (rule cone_ordLeq_ctwo) apply (rule ordLeq_csum2)
      apply (rule Card_order_ctwo)
     apply (rule notE) apply (rule conjunct1) apply (rule Cnotzero_UNIV) apply blast
     apply (rule card_of_Card_order)
  done
  finally
  show "|{f::'d => 'a. range f \<subseteq> B}| \<le>o
        ( |B| +c ctwo) ^c (natLeq +c |UNIV :: 'd set| )" .
next
  fix A B1 B2 f1 f2 p1 p2 assume p: "wpull A B1 B2 f1 f2 p1 p2"
  show "wpull {h. range h \<subseteq> A} {g1. range g1 \<subseteq> B1} {g2. range g2 \<subseteq> B2}
    (op \<circ> f1) (op \<circ> f2) (op \<circ> p1) (op \<circ> p2)"
  unfolding wpull_def
  proof safe
    fix g1 g2 assume r: "range g1 \<subseteq> B1" "range g2 \<subseteq> B2"
    and c: "f1 \<circ> g1 = f2 \<circ> g2"
    show "\<exists>h \<in> {h. range h \<subseteq> A}. p1 \<circ> h = g1 \<and> p2 \<circ> h = g2"
    using wpull_cat[OF p c r] by simp metis
  qed
next
  fix R
  show "fun_rel0 R = (Gr {x. range x \<subseteq> R} (op \<circ> fst))\<inverse> O Gr {x. range x \<subseteq> R} (op \<circ> snd)"
  unfolding fun_rel0_def Gr_def relcomp_unfold converse_unfold
  by (auto intro!: exI dest!: in_mono)
qed auto

end
