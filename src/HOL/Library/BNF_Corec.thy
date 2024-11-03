(*  Title:      HOL/Library/BNF_Corec.thy
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Dmitriy Traytel, ETH Zurich
    Copyright   2015, 2016

Generalized corecursor sugar ("corec" and friends).
*)

section \<open>Generalized Corecursor Sugar (corec and friends)\<close>

theory BNF_Corec
imports Main
keywords
  "corec" :: thy_defn and
  "corecursive" :: thy_goal_defn and
  "friend_of_corec" :: thy_goal_defn and
  "coinduction_upto" :: thy_decl
begin

lemma obj_distinct_prems: "P \<longrightarrow> P \<longrightarrow> Q \<Longrightarrow> P \<Longrightarrow> Q"
  by auto

lemma inject_refine: "g (f x) = x \<Longrightarrow> g (f y) = y \<Longrightarrow> f x = f y \<longleftrightarrow> x = y"
  by (metis (no_types))

lemma convol_apply: "BNF_Def.convol f g x = (f x, g x)"
  unfolding convol_def ..

lemma Grp_UNIV_id: "BNF_Def.Grp UNIV id = (=)"
  unfolding BNF_Def.Grp_def by auto

lemma sum_comp_cases:
  assumes "f \<circ> Inl = g \<circ> Inl" and "f \<circ> Inr = g \<circ> Inr"
  shows "f = g"
proof (rule ext)
  fix a show "f a = g a"
    using assms unfolding comp_def fun_eq_iff by (cases a) auto
qed

lemma case_sum_Inl_Inr_L: "case_sum (f \<circ> Inl) (f \<circ> Inr) = f"
  by (metis case_sum_expand_Inr')

lemma eq_o_InrI: "\<lbrakk>g \<circ> Inl = h; case_sum h f = g\<rbrakk> \<Longrightarrow> f = g \<circ> Inr"
  by (auto simp: fun_eq_iff split: sum.splits)

lemma id_bnf_o: "BNF_Composition.id_bnf \<circ> f = f"
  unfolding BNF_Composition.id_bnf_def by (rule o_def)

lemma o_id_bnf: "f \<circ> BNF_Composition.id_bnf = f"
  unfolding BNF_Composition.id_bnf_def by (rule o_def)

lemma if_True_False:
  "(if P then True else Q) \<longleftrightarrow> P \<or> Q"
  "(if P then False else Q) \<longleftrightarrow> \<not> P \<and> Q"
  "(if P then Q else True) \<longleftrightarrow> \<not> P \<or> Q"
  "(if P then Q else False) \<longleftrightarrow> P \<and> Q"
  by auto

lemma if_distrib_fun: "(if c then f else g) x = (if c then f x else g x)"
  by simp


subsection \<open>Coinduction\<close>

lemma eq_comp_compI: "a \<circ> b = f \<circ> x \<Longrightarrow> x \<circ> c = id \<Longrightarrow> f = a \<circ> (b \<circ> c)"
  unfolding fun_eq_iff by simp

lemma self_bounded_weaken_left: "(a :: 'a :: semilattice_inf) \<le> inf a b \<Longrightarrow> a \<le> b"
  by (erule le_infE)

lemma self_bounded_weaken_right: "(a :: 'a :: semilattice_inf) \<le> inf b a \<Longrightarrow> a \<le> b"
  by (erule le_infE)

lemma symp_iff: "symp R \<longleftrightarrow> R = R\<inverse>\<inverse>"
  by (metis antisym conversep.cases conversep_le_swap predicate2I symp_def)

lemma equivp_inf: "\<lbrakk>equivp R; equivp S\<rbrakk> \<Longrightarrow> equivp (inf R S)"
  unfolding equivp_def inf_fun_def inf_bool_def by metis

lemma vimage2p_rel_prod:
  "(\<lambda>x y. rel_prod R S (BNF_Def.convol f1 g1 x) (BNF_Def.convol f2 g2 y)) =
   (inf (BNF_Def.vimage2p f1 f2 R) (BNF_Def.vimage2p g1 g2 S))"
  unfolding vimage2p_def rel_prod.simps convol_def by auto

lemma predicate2I_obj: "(\<forall>x y. P x y \<longrightarrow> Q x y) \<Longrightarrow> P \<le> Q"
  by auto

lemma predicate2D_obj: "P \<le> Q \<Longrightarrow> P x y \<longrightarrow> Q x y"
  by auto

locale cong =
  fixes rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool)"
    and eval :: "'b \<Rightarrow> 'a"
    and retr :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  assumes rel_mono: "\<And>R S. R \<le> S \<Longrightarrow> rel R \<le> rel S"
    and equivp_retr: "\<And>R. equivp R \<Longrightarrow> equivp (retr R)"
    and retr_eval: "\<And>R x y. \<lbrakk>(rel_fun (rel R) R) eval eval; rel (inf R (retr R)) x y\<rbrakk> \<Longrightarrow>
      retr R (eval x) (eval y)"
begin

definition cong :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "cong R \<equiv> equivp R \<and> (rel_fun (rel R) R) eval eval"

lemma cong_retr: "cong R \<Longrightarrow> cong (inf R (retr R))"
  unfolding cong_def
  by (auto simp: rel_fun_def dest: predicate2D[OF rel_mono, rotated]
    intro: equivp_inf equivp_retr retr_eval)

lemma cong_equivp: "cong R \<Longrightarrow> equivp R"
  unfolding cong_def by simp

definition gen_cong :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "gen_cong R j1 j2 \<equiv> \<forall>R'. R \<le> R' \<and> cong R' \<longrightarrow> R' j1 j2"

lemma gen_cong_reflp[intro, simp]: "x = y \<Longrightarrow> gen_cong R x y"
  unfolding gen_cong_def by (auto dest: cong_equivp equivp_reflp)

lemma gen_cong_symp[intro]: "gen_cong R x y \<Longrightarrow> gen_cong R y x"
  unfolding gen_cong_def by (auto dest: cong_equivp equivp_symp)

lemma gen_cong_transp[intro]: "gen_cong R x y \<Longrightarrow> gen_cong R y z \<Longrightarrow> gen_cong R x z"
  unfolding gen_cong_def by (auto dest: cong_equivp equivp_transp)

lemma equivp_gen_cong: "equivp (gen_cong R)"
  by (intro equivpI reflpI sympI transpI) auto

lemma leq_gen_cong: "R \<le> gen_cong R"
  unfolding gen_cong_def[abs_def] by auto

lemmas imp_gen_cong[intro] = predicate2D[OF leq_gen_cong]

lemma gen_cong_minimal: "\<lbrakk>R \<le> R'; cong R'\<rbrakk> \<Longrightarrow> gen_cong R \<le> R'"
  unfolding gen_cong_def[abs_def] by (rule predicate2I) metis

lemma congdd_base_gen_congdd_base_aux:
  "rel (gen_cong R) x y \<Longrightarrow> R \<le> R' \<Longrightarrow> cong R' \<Longrightarrow> R' (eval x) (eval y)"
   by (force simp: rel_fun_def gen_cong_def cong_def dest: spec[of _ R'] predicate2D[OF rel_mono, rotated -1, of _ _ _ R'])

lemma cong_gen_cong: "cong (gen_cong R)"
proof -
  have "rel (gen_cong R) x y \<Longrightarrow> R \<le> R' \<Longrightarrow> cong R' \<Longrightarrow> R' (eval x) (eval y)" for R' x y
    by (force simp: rel_fun_def gen_cong_def cong_def dest: spec[of _ R']
        predicate2D[OF rel_mono, rotated -1, of _ _ _ R'])
  then show "cong (gen_cong R)" by (auto simp: equivp_gen_cong rel_fun_def gen_cong_def cong_def)
qed

lemma gen_cong_eval_rel_fun:
  "(rel_fun (rel (gen_cong R)) (gen_cong R)) eval eval"
  using cong_gen_cong[of R] unfolding cong_def by simp

lemma gen_cong_eval:
  "rel (gen_cong R) x y \<Longrightarrow> gen_cong R (eval x) (eval y)"
  by (erule rel_funD[OF gen_cong_eval_rel_fun])

lemma gen_cong_idem: "gen_cong (gen_cong R) = gen_cong R"
  by (simp add: antisym cong_gen_cong gen_cong_minimal leq_gen_cong)

lemma gen_cong_rho:
  "\<rho> = eval \<circ> f \<Longrightarrow> rel (gen_cong R) (f x) (f y) \<Longrightarrow> gen_cong R (\<rho> x) (\<rho> y)"
  by (simp add: gen_cong_eval)
lemma coinduction:
  assumes coind: "\<forall>R. R \<le> retr R \<longrightarrow> R \<le> (=)"
  assumes cih: "R \<le> retr (gen_cong R)"
  shows "R \<le> (=)"
  apply (rule order_trans[OF leq_gen_cong mp[OF spec[OF coind]]])
  apply (rule self_bounded_weaken_left[OF gen_cong_minimal])
   apply (rule inf_greatest[OF leq_gen_cong cih])
  apply (rule cong_retr[OF cong_gen_cong])
  done

end

lemma rel_sum_case_sum:
  "rel_fun (rel_sum R S) T (case_sum f1 g1) (case_sum f2 g2) = (rel_fun R T f1 f2 \<and> rel_fun S T g1 g2)"
  by (auto simp: rel_fun_def rel_sum.simps split: sum.splits)

context
  fixes rel eval rel' eval' retr emb
  assumes base: "cong rel eval retr"
  and step: "cong rel' eval' retr"
  and emb: "eval' \<circ> emb = eval"
  and emb_transfer: "rel_fun (rel R) (rel' R) emb emb"
begin

interpretation base: cong rel eval retr by (rule base)
interpretation step: cong rel' eval' retr by (rule step)

lemma gen_cong_emb: "base.gen_cong R \<le> step.gen_cong R"
proof (rule base.gen_cong_minimal[OF step.leq_gen_cong])
  note step.gen_cong_eval_rel_fun[transfer_rule] emb_transfer[transfer_rule]
  have "(rel_fun (rel (step.gen_cong R)) (step.gen_cong R)) eval eval"
    unfolding emb[symmetric] by transfer_prover
  then show "base.cong (step.gen_cong R)"
    by (auto simp: base.cong_def step.equivp_gen_cong)
qed

end

named_theorems friend_of_corec_simps

ML_file \<open>../Tools/BNF/bnf_gfp_grec_tactics.ML\<close>
ML_file \<open>../Tools/BNF/bnf_gfp_grec.ML\<close>
ML_file \<open>../Tools/BNF/bnf_gfp_grec_sugar_util.ML\<close>
ML_file \<open>../Tools/BNF/bnf_gfp_grec_sugar_tactics.ML\<close>
ML_file \<open>../Tools/BNF/bnf_gfp_grec_sugar.ML\<close>
ML_file \<open>../Tools/BNF/bnf_gfp_grec_unique_sugar.ML\<close>

method_setup transfer_prover_eq = \<open>
  Scan.succeed (SIMPLE_METHOD' o BNF_GFP_Grec_Tactics.transfer_prover_eq_tac)
\<close> "apply transfer_prover after folding relator_eq"

method_setup corec_unique = \<open>
  Scan.succeed (SIMPLE_METHOD' o BNF_GFP_Grec_Unique_Sugar.corec_unique_tac)
\<close> "prove uniqueness of corecursive equation"

end
