(*  Title:      HOL/BNF_LFP.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Least fixed point operation on bounded natural functors.
*)

header {* Least Fixed Point Operation on Bounded Natural Functors *}

theory BNF_LFP
imports BNF_FP_Base
keywords
  "datatype_new" :: thy_decl and
  "datatype_compat" :: thy_decl
begin

lemma subset_emptyI: "(\<And>x. x \<in> A \<Longrightarrow> False) \<Longrightarrow> A \<subseteq> {}"
by blast

lemma image_Collect_subsetI: "(\<And>x. P x \<Longrightarrow> f x \<in> B) \<Longrightarrow> f ` {x. P x} \<subseteq> B"
by blast

lemma Collect_restrict: "{x. x \<in> X \<and> P x} \<subseteq> X"
by auto

lemma prop_restrict: "\<lbrakk>x \<in> Z; Z \<subseteq> {x. x \<in> X \<and> P x}\<rbrakk> \<Longrightarrow> P x"
by auto

lemma underS_I: "\<lbrakk>i \<noteq> j; (i, j) \<in> R\<rbrakk> \<Longrightarrow> i \<in> underS R j"
unfolding underS_def by simp

lemma underS_E: "i \<in> underS R j \<Longrightarrow> i \<noteq> j \<and> (i, j) \<in> R"
unfolding underS_def by simp

lemma underS_Field: "i \<in> underS R j \<Longrightarrow> i \<in> Field R"
unfolding underS_def Field_def by auto

lemma FieldI2: "(i, j) \<in> R \<Longrightarrow> j \<in> Field R"
unfolding Field_def by auto

lemma fst_convol': "fst (<f, g> x) = f x"
using fst_convol unfolding convol_def by simp

lemma snd_convol': "snd (<f, g> x) = g x"
using snd_convol unfolding convol_def by simp

lemma convol_expand_snd: "fst o f = g \<Longrightarrow>  <g, snd o f> = f"
unfolding convol_def by auto

lemma convol_expand_snd':
  assumes "(fst o f = g)"
  shows "h = snd o f \<longleftrightarrow> <g, h> = f"
proof -
  from assms have *: "<g, snd o f> = f" by (rule convol_expand_snd)
  then have "h = snd o f \<longleftrightarrow> h = snd o <g, snd o f>" by simp
  moreover have "\<dots> \<longleftrightarrow> h = snd o f" by (simp add: snd_convol)
  moreover have "\<dots> \<longleftrightarrow> <g, h> = f" by (subst (2) *[symmetric]) (auto simp: convol_def fun_eq_iff)
  ultimately show ?thesis by simp
qed
lemma bij_betwE: "bij_betw f A B \<Longrightarrow> \<forall>a\<in>A. f a \<in> B"
unfolding bij_betw_def by auto

lemma bij_betw_imageE: "bij_betw f A B \<Longrightarrow> f ` A = B"
unfolding bij_betw_def by auto

lemma f_the_inv_into_f_bij_betw: "bij_betw f A B \<Longrightarrow>
  (bij_betw f A B \<Longrightarrow> x \<in> B) \<Longrightarrow> f (the_inv_into A f x) = x"
  unfolding bij_betw_def by (blast intro: f_the_inv_into_f)

lemma ex_bij_betw: "|A| \<le>o (r :: 'b rel) \<Longrightarrow> \<exists>f B :: 'b set. bij_betw f B A"
  by (subst (asm) internalize_card_of_ordLeq)
    (auto dest!: iffD2[OF card_of_ordIso ordIso_symmetric])

lemma bij_betwI':
  "\<lbrakk>\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (f x = f y) = (x = y);
    \<And>x. x \<in> X \<Longrightarrow> f x \<in> Y;
    \<And>y. y \<in> Y \<Longrightarrow> \<exists>x \<in> X. y = f x\<rbrakk> \<Longrightarrow> bij_betw f X Y"
unfolding bij_betw_def inj_on_def by blast

lemma surj_fun_eq:
  assumes surj_on: "f ` X = UNIV" and eq_on: "\<forall>x \<in> X. (g1 o f) x = (g2 o f) x"
  shows "g1 = g2"
proof (rule ext)
  fix y
  from surj_on obtain x where "x \<in> X" and "y = f x" by blast
  thus "g1 y = g2 y" using eq_on by simp
qed

lemma Card_order_wo_rel: "Card_order r \<Longrightarrow> wo_rel r"
unfolding wo_rel_def card_order_on_def by blast

lemma Cinfinite_limit: "\<lbrakk>x \<in> Field r; Cinfinite r\<rbrakk> \<Longrightarrow>
  \<exists>y \<in> Field r. x \<noteq> y \<and> (x, y) \<in> r"
unfolding cinfinite_def by (auto simp add: infinite_Card_order_limit)

lemma Card_order_trans:
  "\<lbrakk>Card_order r; x \<noteq> y; (x, y) \<in> r; y \<noteq> z; (y, z) \<in> r\<rbrakk> \<Longrightarrow> x \<noteq> z \<and> (x, z) \<in> r"
unfolding card_order_on_def well_order_on_def linear_order_on_def
  partial_order_on_def preorder_on_def trans_def antisym_def by blast

lemma Cinfinite_limit2:
 assumes x1: "x1 \<in> Field r" and x2: "x2 \<in> Field r" and r: "Cinfinite r"
 shows "\<exists>y \<in> Field r. (x1 \<noteq> y \<and> (x1, y) \<in> r) \<and> (x2 \<noteq> y \<and> (x2, y) \<in> r)"
proof -
  from r have trans: "trans r" and total: "Total r" and antisym: "antisym r"
    unfolding card_order_on_def well_order_on_def linear_order_on_def
      partial_order_on_def preorder_on_def by auto
  obtain y1 where y1: "y1 \<in> Field r" "x1 \<noteq> y1" "(x1, y1) \<in> r"
    using Cinfinite_limit[OF x1 r] by blast
  obtain y2 where y2: "y2 \<in> Field r" "x2 \<noteq> y2" "(x2, y2) \<in> r"
    using Cinfinite_limit[OF x2 r] by blast
  show ?thesis
  proof (cases "y1 = y2")
    case True with y1 y2 show ?thesis by blast
  next
    case False
    with y1(1) y2(1) total have "(y1, y2) \<in> r \<or> (y2, y1) \<in> r"
      unfolding total_on_def by auto
    thus ?thesis
    proof
      assume *: "(y1, y2) \<in> r"
      with trans y1(3) have "(x1, y2) \<in> r" unfolding trans_def by blast
      with False y1 y2 * antisym show ?thesis by (cases "x1 = y2") (auto simp: antisym_def)
    next
      assume *: "(y2, y1) \<in> r"
      with trans y2(3) have "(x2, y1) \<in> r" unfolding trans_def by blast
      with False y1 y2 * antisym show ?thesis by (cases "x2 = y1") (auto simp: antisym_def)
    qed
  qed
qed

lemma Cinfinite_limit_finite: "\<lbrakk>finite X; X \<subseteq> Field r; Cinfinite r\<rbrakk>
 \<Longrightarrow> \<exists>y \<in> Field r. \<forall>x \<in> X. (x \<noteq> y \<and> (x, y) \<in> r)"
proof (induct X rule: finite_induct)
  case empty thus ?case unfolding cinfinite_def using ex_in_conv[of "Field r"] finite.emptyI by auto
next
  case (insert x X)
  then obtain y where y: "y \<in> Field r" "\<forall>x \<in> X. (x \<noteq> y \<and> (x, y) \<in> r)" by blast
  then obtain z where z: "z \<in> Field r" "x \<noteq> z \<and> (x, z) \<in> r" "y \<noteq> z \<and> (y, z) \<in> r"
    using Cinfinite_limit2[OF _ y(1) insert(5), of x] insert(4) by blast
  show ?case
    apply (intro bexI ballI)
    apply (erule insertE)
    apply hypsubst
    apply (rule z(2))
    using Card_order_trans[OF insert(5)[THEN conjunct2]] y(2) z(3)
    apply blast
    apply (rule z(1))
    done
qed

lemma insert_subsetI: "\<lbrakk>x \<in> A; X \<subseteq> A\<rbrakk> \<Longrightarrow> insert x X \<subseteq> A"
by auto

(*helps resolution*)
lemma well_order_induct_imp:
  "wo_rel r \<Longrightarrow> (\<And>x. \<forall>y. y \<noteq> x \<and> (y, x) \<in> r \<longrightarrow> y \<in> Field r \<longrightarrow> P y \<Longrightarrow> x \<in> Field r \<longrightarrow> P x) \<Longrightarrow>
     x \<in> Field r \<longrightarrow> P x"
by (erule wo_rel.well_order_induct)

lemma meta_spec2:
  assumes "(\<And>x y. PROP P x y)"
  shows "PROP P x y"
by (rule assms)

lemma nchotomy_relcomppE:
  assumes "\<And>y. \<exists>x. y = f x" "(r OO s) a c" "\<And>b. r a (f b) \<Longrightarrow> s (f b) c \<Longrightarrow> P"
  shows P
proof (rule relcompp.cases[OF assms(2)], hypsubst)
  fix b assume "r a b" "s b c"
  moreover from assms(1) obtain b' where "b = f b'" by blast
  ultimately show P by (blast intro: assms(3))
qed

lemma vimage2p_rel_fun: "rel_fun (vimage2p f g R) R f g"
  unfolding rel_fun_def vimage2p_def by auto

lemma predicate2D_vimage2p: "\<lbrakk>R \<le> vimage2p f g S; R x y\<rbrakk> \<Longrightarrow> S (f x) (g y)"
  unfolding vimage2p_def by auto

lemma id_transfer: "rel_fun A A id id"
  unfolding rel_fun_def by simp

lemma ssubst_Pair_rhs: "\<lbrakk>(r, s) \<in> R; s' = s\<rbrakk> \<Longrightarrow> (r, s') \<in> R"
  by (rule ssubst)

lemma fun_cong_unused_0: "f = (\<lambda>x. g) \<Longrightarrow> f (\<lambda>x. 0) = g"
  by (erule arg_cong)

lemma snd_o_convol: "(snd \<circ> (\<lambda>x. (f x, g x))) = g"
  by (rule ext) simp

lemma inj_on_convol_id: "inj_on (\<lambda>x. (x, f x)) X"
  unfolding inj_on_def by simp

lemma case_prod_app: "case_prod f x y = case_prod (\<lambda>l r. f l r y) x"
  by (case_tac x) simp

lemma case_sum_o_map_sum: "case_sum l r (map_sum f g x) = case_sum (l \<circ> f) (r \<circ> g) x"
  by (case_tac x) simp+

lemma case_prod_o_map_prod: "case_prod h (map_prod f g x) = case_prod (\<lambda>l r. h (f l) (g r)) x"
  by (case_tac x) simp+

lemma prod_inj_map: "inj f \<Longrightarrow> inj g \<Longrightarrow> inj (map_prod f g)"
  by (simp add: inj_on_def)

declare [[ML_print_depth = 10000]] (*###*)

ML_file "Tools/BNF/bnf_lfp_util.ML"
ML_file "Tools/BNF/bnf_lfp_tactics.ML"
ML_file "Tools/BNF/bnf_lfp.ML"
ML_file "Tools/BNF/bnf_lfp_compat.ML"
ML_file "Tools/BNF/bnf_lfp_rec_sugar_more.ML"
ML_file "Tools/BNF/bnf_lfp_size.ML"

hide_fact (open) id_transfer

datatype_new 'a i = I 'a
thm i.size i.rec_o_map i.size_o_map

datatype_new ('a, 'b) j = J0 | J 'a "('a, 'b) j"
thm j.size j.rec_o_map j.size_o_map

datatype_new 'a l = N nat nat | C 'a "'a l"
thm l.size l.rec_o_map l.size_o_map

datatype_new ('a, 'b) x = XN 'b | XC 'a "('a, 'b) x"
thm x.size x.rec_o_map x.size_o_map

datatype_new
  'a tl = TN | TC "'a mt" "'a tl" and
  'a mt = MT 'a "'a tl"
thm tl.size tl.rec_o_map tl.size_o_map
thm mt.size mt.rec_o_map mt.size_o_map

datatype_new 'a t = T nat 'a "'a t l"
thm t.size t.rec_o_map t.size_o_map

datatype_new 'a fset = FSet0 | FSet 'a "'a fset"
thm fset.size fset.rec_o_map fset.size_o_map

datatype_new 'a u = U 'a "'a u fset"
thm u.size u.rec_o_map u.size_o_map

datatype_new
  ('a, 'b) v = V "nat l" | V' 'a "('a, 'b) w" and
  ('a, 'b) w = W 'b "('a, 'b) v fset l"
thm v.size v.rec_o_map v.size_o_map
thm w.size w.rec_o_map w.size_o_map

(*TODO:
* what happens if recursion through arbitrary bnf, like 'fsize'?
  * by default
  * offer possibility to register size function and theorems
* compat with old size?
  * recursion of old through new (e.g. through list)?
  * recursion of new through old?
  * should they share theory data?
* code generator setup?
*)


end
datatype_new 'a x = X0 | X 'a (*###*)
thm x.size
thm x.size_o_map
datatype_new 'a x = X0 | X 'a "'a x" (*###*)
thm x.size
thm x.size_o_map
datatype_new 'a l = N | C 'a "'a l"
datatype_new ('a, 'b) tl = TN 'b | TC 'a "'a l"

end
