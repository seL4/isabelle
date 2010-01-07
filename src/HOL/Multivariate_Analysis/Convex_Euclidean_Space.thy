(*  Title:      HOL/Library/Convex_Euclidean_Space.thy
    Author:     Robert Himmelmann, TU Muenchen
*)

header {* Convex sets, functions and related things. *}

theory Convex_Euclidean_Space
imports Topology_Euclidean_Space
begin


(* ------------------------------------------------------------------------- *)
(* To be moved elsewhere                                                     *)
(* ------------------------------------------------------------------------- *)

declare vector_add_ldistrib[simp] vector_ssub_ldistrib[simp] vector_smult_assoc[simp] vector_smult_rneg[simp]
declare vector_sadd_rdistrib[simp] vector_sub_rdistrib[simp]
declare dot_ladd[simp] dot_radd[simp] dot_lsub[simp] dot_rsub[simp]
declare dot_lmult[simp] dot_rmult[simp] dot_lneg[simp] dot_rneg[simp]
declare UNIV_1[simp]

lemma dim1in[intro]:"Suc 0 \<in> {1::nat .. CARD(1)}" by auto

lemmas vector_component_simps = vector_minus_component vector_smult_component vector_add_component vector_le_def Cart_lambda_beta dest_vec1_def basis_component vector_uminus_component

lemmas continuous_intros = continuous_add continuous_vmul continuous_cmul continuous_const continuous_sub continuous_at_id continuous_within_id

lemmas continuous_on_intros = continuous_on_add continuous_on_const continuous_on_id continuous_on_compose continuous_on_cmul continuous_on_neg continuous_on_sub
  uniformly_continuous_on_add uniformly_continuous_on_const uniformly_continuous_on_id uniformly_continuous_on_compose uniformly_continuous_on_cmul uniformly_continuous_on_neg uniformly_continuous_on_sub

lemma dest_vec1_simps[simp]: fixes a::"real^1"
  shows "a$1 = 0 \<longleftrightarrow> a = 0" (*"a \<le> 1 \<longleftrightarrow> dest_vec1 a \<le> 1" "0 \<le> a \<longleftrightarrow> 0 \<le> dest_vec1 a"*)
  "a \<le> b \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 b" "dest_vec1 (1::real^1) = 1"
  by(auto simp add:vector_component_simps all_1 Cart_eq)

lemma nequals0I:"x\<in>A \<Longrightarrow> A \<noteq> {}" by auto

lemma norm_not_0:"(x::real^'n)\<noteq>0 \<Longrightarrow> norm x \<noteq> 0" by auto

lemma setsum_delta_notmem: assumes "x\<notin>s"
  shows "setsum (\<lambda>y. if (y = x) then P x else Q y) s = setsum Q s"
        "setsum (\<lambda>y. if (x = y) then P x else Q y) s = setsum Q s"
        "setsum (\<lambda>y. if (y = x) then P y else Q y) s = setsum Q s"
        "setsum (\<lambda>y. if (x = y) then P y else Q y) s = setsum Q s"
  apply(rule_tac [!] setsum_cong2) using assms by auto

lemma setsum_delta'':
  fixes s::"'a::real_vector set" assumes "finite s"
  shows "(\<Sum>x\<in>s. (if y = x then f x else 0) *\<^sub>R x) = (if y\<in>s then (f y) *\<^sub>R y else 0)"
proof-
  have *:"\<And>x y. (if y = x then f x else (0::real)) *\<^sub>R x = (if x=y then (f x) *\<^sub>R x else 0)" by auto
  show ?thesis unfolding * using setsum_delta[OF assms, of y "\<lambda>x. f x *\<^sub>R x"] by auto
qed

lemma not_disjointI:"x\<in>A \<Longrightarrow> x\<in>B \<Longrightarrow> A \<inter> B \<noteq> {}" by blast

lemma if_smult:"(if P then x else (y::real)) *\<^sub>R v = (if P then x *\<^sub>R v else y *\<^sub>R v)" by auto

lemma mem_interval_1: fixes x :: "real^1" shows
 "(x \<in> {a .. b} \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b)"
 "(x \<in> {a<..<b} \<longleftrightarrow> dest_vec1 a < dest_vec1 x \<and> dest_vec1 x < dest_vec1 b)"
by(simp_all add: Cart_eq vector_less_def vector_le_def dest_vec1_def all_1)

lemma image_smult_interval:"(\<lambda>x. m *\<^sub>R (x::real^'n)) ` {a..b} =
  (if {a..b} = {} then {} else if 0 \<le> m then {m *\<^sub>R a..m *\<^sub>R b} else {m *\<^sub>R b..m *\<^sub>R a})"
  using image_affinity_interval[of m 0 a b] by auto

lemma dest_vec1_inverval:
  "dest_vec1 ` {a .. b} = {dest_vec1 a .. dest_vec1 b}"
  "dest_vec1 ` {a<.. b} = {dest_vec1 a<.. dest_vec1 b}"
  "dest_vec1 ` {a ..<b} = {dest_vec1 a ..<dest_vec1 b}"
  "dest_vec1 ` {a<..<b} = {dest_vec1 a<..<dest_vec1 b}"
  apply(rule_tac [!] equalityI)
  unfolding subset_eq Ball_def Bex_def mem_interval_1 image_iff
  apply(rule_tac [!] allI)apply(rule_tac [!] impI)
  apply(rule_tac[2] x="vec1 x" in exI)apply(rule_tac[4] x="vec1 x" in exI)
  apply(rule_tac[6] x="vec1 x" in exI)apply(rule_tac[8] x="vec1 x" in exI)
  by (auto simp add: vector_less_def vector_le_def all_1 dest_vec1_def
    vec1_dest_vec1[unfolded dest_vec1_def One_nat_def])

lemma dest_vec1_setsum: assumes "finite S"
  shows " dest_vec1 (setsum f S) = setsum (\<lambda>x. dest_vec1 (f x)) S"
  using dest_vec1_sum[OF assms] by auto

lemma dist_triangle_eq:
  fixes x y z :: "real ^ _"
  shows "dist x z = dist x y + dist y z \<longleftrightarrow> norm (x - y) *\<^sub>R (y - z) = norm (y - z) *\<^sub>R (x - y)"
proof- have *:"x - y + (y - z) = x - z" by auto
  show ?thesis unfolding dist_norm norm_triangle_eq[of "x - y" "y - z", unfolded smult_conv_scaleR *]
    by(auto simp add:norm_minus_commute) qed

lemma norm_eqI:"x = y \<Longrightarrow> norm x = norm y" by auto 
lemma norm_minus_eqI:"(x::real^'n) = - y \<Longrightarrow> norm x = norm y" by auto

lemma Min_grI: assumes "finite A" "A \<noteq> {}" "\<forall>a\<in>A. x < a" shows "x < Min A"
  unfolding Min_gr_iff[OF assms(1,2)] using assms(3) by auto

lemma dimindex_ge_1:"CARD(_::finite) \<ge> 1"
  using one_le_card_finite by auto

lemma real_dimindex_ge_1:"real (CARD('n::finite)) \<ge> 1" 
  by(metis dimindex_ge_1 linorder_not_less real_eq_of_nat real_le_trans real_of_nat_1 real_of_nat_le_iff) 

lemma real_dimindex_gt_0:"real (CARD('n::finite)) > 0" apply(rule less_le_trans[OF _ real_dimindex_ge_1]) by auto

subsection {* Affine set and affine hull.*}

definition
  affine :: "'a::real_vector set \<Rightarrow> bool" where
  "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma affine_alt: "affine s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u::real. (1 - u) *\<^sub>R x + u *\<^sub>R y \<in> s)"
proof- have *:"\<And>u v ::real. u + v = 1 \<longleftrightarrow> v = 1 - u" by auto
  { fix x y assume "x\<in>s" "y\<in>s"
    hence "(\<forall>u v::real. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s) \<longleftrightarrow> (\<forall>u::real. (1 - u) *\<^sub>R x + u *\<^sub>R y \<in> s)" apply auto 
      apply(erule_tac[!] x="1 - u" in allE) unfolding * by auto  }
  thus ?thesis unfolding affine_def by auto qed

lemma affine_empty[intro]: "affine {}"
  unfolding affine_def by auto

lemma affine_sing[intro]: "affine {x}"
  unfolding affine_alt by (auto simp add: scaleR_left_distrib [symmetric])

lemma affine_UNIV[intro]: "affine UNIV"
  unfolding affine_def by auto

lemma affine_Inter: "(\<forall>s\<in>f. affine s) \<Longrightarrow> affine (\<Inter> f)"
  unfolding affine_def by auto 

lemma affine_Int: "affine s \<Longrightarrow> affine t \<Longrightarrow> affine (s \<inter> t)"
  unfolding affine_def by auto

lemma affine_affine_hull: "affine(affine hull s)"
  unfolding hull_def using affine_Inter[of "{t \<in> affine. s \<subseteq> t}"]
  unfolding mem_def by auto

lemma affine_hull_eq[simp]: "(affine hull s = s) \<longleftrightarrow> affine s"
proof-
  { fix f assume "f \<subseteq> affine"
    hence "affine (\<Inter>f)" using affine_Inter[of f] unfolding subset_eq mem_def by auto  }
  thus ?thesis using hull_eq[unfolded mem_def, of affine s] by auto
qed

lemma setsum_restrict_set'': assumes "finite A"
  shows "setsum f {x \<in> A. P x} = (\<Sum>x\<in>A. if P x  then f x else 0)"
  unfolding mem_def[of _ P, symmetric] unfolding setsum_restrict_set'[OF assms] ..

subsection {* Some explicit formulations (from Lars Schewe). *}

lemma affine: fixes V::"'a::real_vector set"
  shows "affine V \<longleftrightarrow> (\<forall>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> V \<and> setsum u s = 1 \<longrightarrow> (setsum (\<lambda>x. (u x) *\<^sub>R x)) s \<in> V)"
unfolding affine_def apply rule apply(rule, rule, rule) apply(erule conjE)+ 
defer apply(rule, rule, rule, rule, rule) proof-
  fix x y u v assume as:"x \<in> V" "y \<in> V" "u + v = (1::real)"
    "\<forall>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> V \<and> setsum u s = 1 \<longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V"
  thus "u *\<^sub>R x + v *\<^sub>R y \<in> V" apply(cases "x=y")
    using as(4)[THEN spec[where x="{x,y}"], THEN spec[where x="\<lambda>w. if w = x then u else v"]] and as(1-3) 
    by(auto simp add: scaleR_left_distrib[THEN sym])
next
  fix s u assume as:"\<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V"
    "finite s" "s \<noteq> {}" "s \<subseteq> V" "setsum u s = (1::real)"
  def n \<equiv> "card s"
  have "card s = 0 \<or> card s = 1 \<or> card s = 2 \<or> card s > 2" by auto
  thus "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V" proof(auto simp only: disjE)
    assume "card s = 2" hence "card s = Suc (Suc 0)" by auto
    then obtain a b where "s = {a, b}" unfolding card_Suc_eq by auto
    thus ?thesis using as(1)[THEN bspec[where x=a], THEN bspec[where x=b]] using as(4,5)
      by(auto simp add: setsum_clauses(2))
  next assume "card s > 2" thus ?thesis using as and n_def proof(induct n arbitrary: u s)
      case (Suc n) fix s::"'a set" and u::"'a \<Rightarrow> real"
      assume IA:"\<And>u s.  \<lbrakk>2 < card s; \<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V; finite s;
               s \<noteq> {}; s \<subseteq> V; setsum u s = 1; n \<equiv> card s \<rbrakk> \<Longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V" and
        as:"Suc n \<equiv> card s" "2 < card s" "\<forall>x\<in>V. \<forall>y\<in>V. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> V"
           "finite s" "s \<noteq> {}" "s \<subseteq> V" "setsum u s = 1"
      have "\<exists>x\<in>s. u x \<noteq> 1" proof(rule_tac ccontr)
        assume " \<not> (\<exists>x\<in>s. u x \<noteq> 1)" hence "setsum u s = real_of_nat (card s)" unfolding card_eq_setsum by auto
        thus False using as(7) and `card s > 2` by (metis Numeral1_eq1_nat less_0_number_of less_int_code(15)
          less_nat_number_of not_less_iff_gr_or_eq of_nat_1 of_nat_eq_iff pos2 rel_simps(4)) qed
      then obtain x where x:"x\<in>s" "u x \<noteq> 1" by auto

      have c:"card (s - {x}) = card s - 1" apply(rule card_Diff_singleton) using `x\<in>s` as(4) by auto
      have *:"s = insert x (s - {x})" "finite (s - {x})" using `x\<in>s` and as(4) by auto
      have **:"setsum u (s - {x}) = 1 - u x"
        using setsum_clauses(2)[OF *(2), of u x, unfolded *(1)[THEN sym] as(7)] by auto
      have ***:"inverse (1 - u x) * setsum u (s - {x}) = 1" unfolding ** using `u x \<noteq> 1` by auto
      have "(\<Sum>xa\<in>s - {x}. (inverse (1 - u x) * u xa) *\<^sub>R xa) \<in> V" proof(cases "card (s - {x}) > 2")
        case True hence "s - {x} \<noteq> {}" "card (s - {x}) = n" unfolding c and as(1)[symmetric] proof(rule_tac ccontr) 
          assume "\<not> s - {x} \<noteq> {}" hence "card (s - {x}) = 0" unfolding card_0_eq[OF *(2)] by simp 
          thus False using True by auto qed auto
        thus ?thesis apply(rule_tac IA[of "s - {x}" "\<lambda>y. (inverse (1 - u x) * u y)"])
        unfolding setsum_right_distrib[THEN sym] using as and *** and True by auto
      next case False hence "card (s - {x}) = Suc (Suc 0)" using as(2) and c by auto
        then obtain a b where "(s - {x}) = {a, b}" "a\<noteq>b" unfolding card_Suc_eq by auto
        thus ?thesis using as(3)[THEN bspec[where x=a], THEN bspec[where x=b]]
          using *** *(2) and `s \<subseteq> V` unfolding setsum_right_distrib by(auto simp add: setsum_clauses(2)) qed
      thus "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> V" unfolding scaleR_scaleR[THEN sym] and scaleR_right.setsum [symmetric]
         apply(subst *) unfolding setsum_clauses(2)[OF *(2)]
         using as(3)[THEN bspec[where x=x], THEN bspec[where x="(inverse (1 - u x)) *\<^sub>R (\<Sum>xa\<in>s - {x}. u xa *\<^sub>R xa)"], 
         THEN spec[where x="u x"], THEN spec[where x="1 - u x"]] and rev_subsetD[OF `x\<in>s` `s\<subseteq>V`] and `u x \<noteq> 1` by auto
    qed auto
  next assume "card s = 1" then obtain a where "s={a}" by(auto simp add: card_Suc_eq)
    thus ?thesis using as(4,5) by simp
  qed(insert `s\<noteq>{}` `finite s`, auto)
qed

lemma affine_hull_explicit:
  "affine hull p = {y. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> setsum (\<lambda>v. (u v) *\<^sub>R v) s = y}"
  apply(rule hull_unique) apply(subst subset_eq) prefer 3 apply rule unfolding mem_Collect_eq and mem_def[of _ affine]
  apply (erule exE)+ apply(erule conjE)+ prefer 2 apply rule proof-
  fix x assume "x\<in>p" thus "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    apply(rule_tac x="{x}" in exI, rule_tac x="\<lambda>x. 1" in exI) by auto
next
  fix t x s u assume as:"p \<subseteq> t" "affine t" "finite s" "s \<noteq> {}" "s \<subseteq> p" "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x" 
  thus "x \<in> t" using as(2)[unfolded affine, THEN spec[where x=s], THEN spec[where x=u]] by auto
next
  show "affine {y. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y}" unfolding affine_def
    apply(rule,rule,rule,rule,rule) unfolding mem_Collect_eq proof-
    fix u v ::real assume uv:"u + v = 1"
    fix x assume "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
    then obtain sx ux where x:"finite sx" "sx \<noteq> {}" "sx \<subseteq> p" "setsum ux sx = 1" "(\<Sum>v\<in>sx. ux v *\<^sub>R v) = x" by auto
    fix y assume "\<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
    then obtain sy uy where y:"finite sy" "sy \<noteq> {}" "sy \<subseteq> p" "setsum uy sy = 1" "(\<Sum>v\<in>sy. uy v *\<^sub>R v) = y" by auto
    have xy:"finite (sx \<union> sy)" using x(1) y(1) by auto
    have **:"(sx \<union> sy) \<inter> sx = sx" "(sx \<union> sy) \<inter> sy = sy" by auto
    show "\<exists>s ua. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p \<and> setsum ua s = 1 \<and> (\<Sum>v\<in>s. ua v *\<^sub>R v) = u *\<^sub>R x + v *\<^sub>R y"
      apply(rule_tac x="sx \<union> sy" in exI)
      apply(rule_tac x="\<lambda>a. (if a\<in>sx then u * ux a else 0) + (if a\<in>sy then v * uy a else 0)" in exI)
      unfolding scaleR_left_distrib setsum_addf if_smult scaleR_zero_left  ** setsum_restrict_set[OF xy, THEN sym]
      unfolding scaleR_scaleR[THEN sym] scaleR_right.setsum [symmetric] and setsum_right_distrib[THEN sym]
      unfolding x y using x(1-3) y(1-3) uv by simp qed qed

lemma affine_hull_finite:
  assumes "finite s"
  shows "affine hull s = {y. \<exists>u. setsum u s = 1 \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = y}"
  unfolding affine_hull_explicit and expand_set_eq and mem_Collect_eq apply (rule,rule)
  apply(erule exE)+ apply(erule conjE)+ defer apply(erule exE) apply(erule conjE) proof-
  fix x u assume "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
  thus "\<exists>sa u. finite sa \<and> \<not> (\<forall>x. (x \<in> sa) = (x \<in> {})) \<and> sa \<subseteq> s \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = x"
    apply(rule_tac x=s in exI, rule_tac x=u in exI) using assms by auto
next
  fix x t u assume "t \<subseteq> s" hence *:"s \<inter> t = t" by auto
  assume "finite t" "\<not> (\<forall>x. (x \<in> t) = (x \<in> {}))" "setsum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = x"
  thus "\<exists>u. setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x" apply(rule_tac x="\<lambda>x. if x\<in>t then u x else 0" in exI)
    unfolding if_smult scaleR_zero_left and setsum_restrict_set[OF assms, THEN sym] and * by auto qed

subsection {* Stepping theorems and hence small special cases. *}

lemma affine_hull_empty[simp]: "affine hull {} = {}"
  apply(rule hull_unique) unfolding mem_def by auto

lemma affine_hull_finite_step:
  fixes y :: "'a::real_vector"
  shows "(\<exists>u. setsum u {} = w \<and> setsum (\<lambda>x. u x *\<^sub>R x) {} = y) \<longleftrightarrow> w = 0 \<and> y = 0" (is ?th1)
  "finite s \<Longrightarrow> (\<exists>u. setsum u (insert a s) = w \<and> setsum (\<lambda>x. u x *\<^sub>R x) (insert a s) = y) \<longleftrightarrow>
                (\<exists>v u. setsum u s = w - v \<and> setsum (\<lambda>x. u x *\<^sub>R x) s = y - v *\<^sub>R a)" (is "?as \<Longrightarrow> (?lhs = ?rhs)")
proof-
  show ?th1 by simp
  assume ?as 
  { assume ?lhs
    then obtain u where u:"setsum u (insert a s) = w \<and> (\<Sum>x\<in>insert a s. u x *\<^sub>R x) = y" by auto
    have ?rhs proof(cases "a\<in>s")
      case True hence *:"insert a s = s" by auto
      show ?thesis using u[unfolded *] apply(rule_tac x=0 in exI) by auto
    next
      case False thus ?thesis apply(rule_tac x="u a" in exI) using u and `?as` by auto 
    qed  } moreover
  { assume ?rhs
    then obtain v u where vu:"setsum u s = w - v"  "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a" by auto
    have *:"\<And>x M. (if x = a then v else M) *\<^sub>R x = (if x = a then v *\<^sub>R x else M *\<^sub>R x)" by auto
    have ?lhs proof(cases "a\<in>s")
      case True thus ?thesis
        apply(rule_tac x="\<lambda>x. (if x=a then v else 0) + u x" in exI)
        unfolding setsum_clauses(2)[OF `?as`]  apply simp
        unfolding scaleR_left_distrib and setsum_addf 
        unfolding vu and * and scaleR_zero_left
        by (auto simp add: setsum_delta[OF `?as`])
    next
      case False 
      hence **:"\<And>x. x \<in> s \<Longrightarrow> u x = (if x = a then v else u x)"
               "\<And>x. x \<in> s \<Longrightarrow> u x *\<^sub>R x = (if x = a then v *\<^sub>R x else u x *\<^sub>R x)" by auto
      from False show ?thesis
        apply(rule_tac x="\<lambda>x. if x=a then v else u x" in exI)
        unfolding setsum_clauses(2)[OF `?as`] and * using vu
        using setsum_cong2[of s "\<lambda>x. u x *\<^sub>R x" "\<lambda>x. if x = a then v *\<^sub>R x else u x *\<^sub>R x", OF **(2)]
        using setsum_cong2[of s u "\<lambda>x. if x = a then v else u x", OF **(1)] by auto  
    qed }
  ultimately show "?lhs = ?rhs" by blast
qed

lemma affine_hull_2:
  fixes a b :: "'a::real_vector"
  shows "affine hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b| u v. (u + v = 1)}" (is "?lhs = ?rhs")
proof-
  have *:"\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::real)" 
         "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::'a)" by auto
  have "?lhs = {y. \<exists>u. setsum u {a, b} = 1 \<and> (\<Sum>v\<in>{a, b}. u v *\<^sub>R v) = y}"
    using affine_hull_finite[of "{a,b}"] by auto
  also have "\<dots> = {y. \<exists>v u. u b = 1 - v \<and> u b *\<^sub>R b = y - v *\<^sub>R a}"
    by(simp add: affine_hull_finite_step(2)[of "{b}" a]) 
  also have "\<dots> = ?rhs" unfolding * by auto
  finally show ?thesis by auto
qed

lemma affine_hull_3:
  fixes a b c :: "'a::real_vector"
  shows "affine hull {a,b,c} = { u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c| u v w. u + v + w = 1}" (is "?lhs = ?rhs")
proof-
  have *:"\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::real)" 
         "\<And>x y z. z = x - y \<longleftrightarrow> y + z = (x::'a)" by auto
  show ?thesis apply(simp add: affine_hull_finite affine_hull_finite_step)
    unfolding * apply auto
    apply(rule_tac x=v in exI) apply(rule_tac x=va in exI) apply auto
    apply(rule_tac x=u in exI) by(auto intro!: exI)
qed

subsection {* Some relations between affine hull and subspaces. *}

lemma affine_hull_insert_subset_span:
  fixes a :: "real ^ _"
  shows "affine hull (insert a s) \<subseteq> {a + v| v . v \<in> span {x - a | x . x \<in> s}}"
  unfolding subset_eq Ball_def unfolding affine_hull_explicit span_explicit mem_Collect_eq smult_conv_scaleR
  apply(rule,rule) apply(erule exE)+ apply(erule conjE)+ proof-
  fix x t u assume as:"finite t" "t \<noteq> {}" "t \<subseteq> insert a s" "setsum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = x"
  have "(\<lambda>x. x - a) ` (t - {a}) \<subseteq> {x - a |x. x \<in> s}" using as(3) by auto
  thus "\<exists>v. x = a + v \<and> (\<exists>S u. finite S \<and> S \<subseteq> {x - a |x. x \<in> s} \<and> (\<Sum>v\<in>S. u v *\<^sub>R v) = v)"
    apply(rule_tac x="x - a" in exI)
    apply (rule conjI, simp)
    apply(rule_tac x="(\<lambda>x. x - a) ` (t - {a})" in exI)
    apply(rule_tac x="\<lambda>x. u (x + a)" in exI)
    apply (rule conjI) using as(1) apply simp
    apply (erule conjI)
    using as(1)
    apply (simp add: setsum_reindex[unfolded inj_on_def] scaleR_right_diff_distrib setsum_subtractf scaleR_left.setsum[THEN sym] setsum_diff1 scaleR_left_diff_distrib)
    unfolding as by simp qed

lemma affine_hull_insert_span:
  fixes a :: "real ^ _"
  assumes "a \<notin> s"
  shows "affine hull (insert a s) =
            {a + v | v . v \<in> span {x - a | x.  x \<in> s}}"
  apply(rule, rule affine_hull_insert_subset_span) unfolding subset_eq Ball_def
  unfolding affine_hull_explicit and mem_Collect_eq proof(rule,rule,erule exE,erule conjE)
  fix y v assume "y = a + v" "v \<in> span {x - a |x. x \<in> s}"
  then obtain t u where obt:"finite t" "t \<subseteq> {x - a |x. x \<in> s}" "a + (\<Sum>v\<in>t. u v *\<^sub>R v) = y" unfolding span_explicit smult_conv_scaleR by auto
  def f \<equiv> "(\<lambda>x. x + a) ` t"
  have f:"finite f" "f \<subseteq> s" "(\<Sum>v\<in>f. u (v - a) *\<^sub>R (v - a)) = y - a" unfolding f_def using obt 
    by(auto simp add: setsum_reindex[unfolded inj_on_def])
  have *:"f \<inter> {a} = {}" "f \<inter> - {a} = f" using f(2) assms by auto
  show "\<exists>sa u. finite sa \<and> sa \<noteq> {} \<and> sa \<subseteq> insert a s \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y"
    apply(rule_tac x="insert a f" in exI)
    apply(rule_tac x="\<lambda>x. if x=a then 1 - setsum (\<lambda>x. u (x - a)) f else u (x - a)" in exI)
    using assms and f unfolding setsum_clauses(2)[OF f(1)] and if_smult
    unfolding setsum_cases[OF f(1), of "{a}", unfolded singleton_iff] and *
    by (auto simp add: setsum_subtractf scaleR_left.setsum algebra_simps) qed

lemma affine_hull_span:
  fixes a :: "real ^ _"
  assumes "a \<in> s"
  shows "affine hull s = {a + v | v. v \<in> span {x - a | x. x \<in> s - {a}}}"
  using affine_hull_insert_span[of a "s - {a}", unfolded insert_Diff[OF assms]] by auto

subsection {* Convexity. *}

definition
  convex :: "'a::real_vector set \<Rightarrow> bool" where
  "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s)"

lemma convex_alt: "convex s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> ((1 - u) *\<^sub>R x + u *\<^sub>R y) \<in> s)"
proof- have *:"\<And>u v::real. u + v = 1 \<longleftrightarrow> u = 1 - v" by auto
  show ?thesis unfolding convex_def apply auto
    apply(erule_tac x=x in ballE) apply(erule_tac x=y in ballE) apply(erule_tac x="1 - u" in allE)
    by (auto simp add: *) qed

lemma mem_convex:
  assumes "convex s" "a \<in> s" "b \<in> s" "0 \<le> u" "u \<le> 1"
  shows "((1 - u) *\<^sub>R a + u *\<^sub>R b) \<in> s"
  using assms unfolding convex_alt by auto

lemma convex_vec1:"convex (vec1 ` s) = convex (s::real set)"
  unfolding convex_def Ball_def forall_vec1 unfolding vec1_dest_vec1_simps image_iff by auto

lemma convex_empty[intro]: "convex {}"
  unfolding convex_def by simp

lemma convex_singleton[intro]: "convex {a}"
  unfolding convex_def by (auto simp add:scaleR_left_distrib[THEN sym])

lemma convex_UNIV[intro]: "convex UNIV"
  unfolding convex_def by auto

lemma convex_Inter: "(\<forall>s\<in>f. convex s) ==> convex(\<Inter> f)"
  unfolding convex_def by auto

lemma convex_Int: "convex s \<Longrightarrow> convex t \<Longrightarrow> convex (s \<inter> t)"
  unfolding convex_def by auto

lemma convex_halfspace_le: "convex {x. inner a x \<le> b}"
  unfolding convex_def apply auto
  unfolding inner_add inner_scaleR
  by (metis real_convex_bound_le)

lemma convex_halfspace_ge: "convex {x. inner a x \<ge> b}"
proof- have *:"{x. inner a x \<ge> b} = {x. inner (-a) x \<le> -b}" by auto
  show ?thesis apply(unfold *) using convex_halfspace_le[of "-a" "-b"] by auto qed

lemma convex_hyperplane: "convex {x. inner a x = b}"
proof-
  have *:"{x. inner a x = b} = {x. inner a x \<le> b} \<inter> {x. inner a x \<ge> b}" by auto
  show ?thesis unfolding * apply(rule convex_Int)
    using convex_halfspace_le convex_halfspace_ge by auto
qed

lemma convex_halfspace_lt: "convex {x. inner a x < b}"
  unfolding convex_def
  by(auto simp add: real_convex_bound_lt inner_add)

lemma convex_halfspace_gt: "convex {x. inner a x > b}"
   using convex_halfspace_lt[of "-a" "-b"] by auto

lemma convex_positive_orthant: "convex {x::real^'n. (\<forall>i. 0 \<le> x$i)}"
  unfolding convex_def apply auto apply(erule_tac x=i in allE)+
  apply(rule add_nonneg_nonneg) by(auto simp add: mult_nonneg_nonneg)

subsection {* Explicit expressions for convexity in terms of arbitrary sums. *}

lemma convex: "convex s \<longleftrightarrow>
  (\<forall>(k::nat) u x. (\<forall>i. 1\<le>i \<and> i\<le>k \<longrightarrow> 0 \<le> u i \<and> x i \<in>s) \<and> (setsum u {1..k} = 1)
           \<longrightarrow> setsum (\<lambda>i. u i *\<^sub>R x i) {1..k} \<in> s)"
  unfolding convex_def apply rule apply(rule allI)+ defer apply(rule ballI)+ apply(rule allI)+ proof(rule,rule,rule,rule)
  fix x y u v assume as:"\<forall>(k::nat) u x. (\<forall>i. 1 \<le> i \<and> i \<le> k \<longrightarrow> 0 \<le> u i \<and> x i \<in> s) \<and> setsum u {1..k} = 1 \<longrightarrow> (\<Sum>i = 1..k. u i *\<^sub>R x i) \<in> s"
    "x \<in> s" "y \<in> s" "0 \<le> u" "0 \<le> v" "u + v = (1::real)"
  show "u *\<^sub>R x + v *\<^sub>R y \<in> s" using as(1)[THEN spec[where x=2], THEN spec[where x="\<lambda>n. if n=1 then u else v"], THEN spec[where x="\<lambda>n. if n=1 then x else y"]] and as(2-)
    by (auto simp add: setsum_head_Suc) 
next
  fix k u x assume as:"\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s" 
  show "(\<forall>i::nat. 1 \<le> i \<and> i \<le> k \<longrightarrow> 0 \<le> u i \<and> x i \<in> s) \<and> setsum u {1..k} = 1 \<longrightarrow> (\<Sum>i = 1..k. u i *\<^sub>R x i) \<in> s" apply(rule,erule conjE) proof(induct k arbitrary: u)
  case (Suc k) show ?case proof(cases "u (Suc k) = 1")
    case True hence "(\<Sum>i = Suc 0..k. u i *\<^sub>R x i) = 0" apply(rule_tac setsum_0') apply(rule ccontr) unfolding ball_simps apply(erule bexE) proof-
      fix i assume i:"i \<in> {Suc 0..k}" "u i *\<^sub>R x i \<noteq> 0"
      hence ui:"u i \<noteq> 0" by auto
      hence "setsum (\<lambda>k. if k=i then u i else 0) {1 .. k} \<le> setsum u {1 .. k}" apply(rule_tac setsum_mono) using Suc(2) by auto
      hence "setsum u {1 .. k} \<ge> u i" using i(1) by(auto simp add: setsum_delta) 
      hence "setsum u {1 .. k} > 0"  using ui apply(rule_tac less_le_trans[of _ "u i"]) using Suc(2)[THEN spec[where x=i]] and i(1) by auto
      thus False using Suc(3) unfolding setsum_cl_ivl_Suc and True by simp qed
    thus ?thesis unfolding setsum_cl_ivl_Suc using True and Suc(2) by auto
  next
    have *:"setsum u {1..k} = 1 - u (Suc k)" using Suc(3)[unfolded setsum_cl_ivl_Suc] by auto
    have **:"u (Suc k) \<le> 1" apply(rule ccontr) unfolding not_le using Suc(3) using setsum_nonneg[of "{1..k}" u] using Suc(2) by auto
    have ***:"\<And>i k. (u i / (1 - u (Suc k))) *\<^sub>R x i = (inverse (1 - u (Suc k))) *\<^sub>R (u i *\<^sub>R x i)" unfolding real_divide_def by (auto simp add: algebra_simps)
    case False hence nn:"1 - u (Suc k) \<noteq> 0" by auto
    have "(\<Sum>i = 1..k. (u i / (1 - u (Suc k))) *\<^sub>R x i) \<in> s" apply(rule Suc(1)) unfolding setsum_divide_distrib[THEN sym] and *
      apply(rule_tac allI) apply(rule,rule) apply(rule divide_nonneg_pos) using nn Suc(2) ** by auto
    hence "(1 - u (Suc k)) *\<^sub>R (\<Sum>i = 1..k. (u i / (1 - u (Suc k))) *\<^sub>R x i) + u (Suc k) *\<^sub>R x (Suc k) \<in> s"
      apply(rule as[THEN bspec, THEN bspec, THEN spec, THEN mp, THEN spec, THEN mp, THEN mp]) using Suc(2)[THEN spec[where x="Suc k"]] and ** by auto
    thus ?thesis unfolding setsum_cl_ivl_Suc and *** and scaleR_right.setsum [symmetric] using nn by auto qed qed auto qed


lemma convex_explicit:
  fixes s :: "'a::real_vector set"
  shows "convex s \<longleftrightarrow>
  (\<forall>t u. finite t \<and> t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and> setsum u t = 1 \<longrightarrow> setsum (\<lambda>x. u x *\<^sub>R x) t \<in> s)"
  unfolding convex_def apply(rule,rule,rule) apply(subst imp_conjL,rule) defer apply(rule,rule,rule,rule,rule,rule,rule) proof-
  fix x y u v assume as:"\<forall>t u. finite t \<and> t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and> setsum u t = 1 \<longrightarrow> (\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s" "x \<in> s" "y \<in> s" "0 \<le> u" "0 \<le> v" "u + v = (1::real)"
  show "u *\<^sub>R x + v *\<^sub>R y \<in> s" proof(cases "x=y")
    case True show ?thesis unfolding True and scaleR_left_distrib[THEN sym] using as(3,6) by auto next
    case False thus ?thesis using as(1)[THEN spec[where x="{x,y}"], THEN spec[where x="\<lambda>z. if z=x then u else v"]] and as(2-) by auto qed
next 
  fix t u assume asm:"\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> s" "finite (t::'a set)"
  (*"finite t" "t \<subseteq> s" "\<forall>x\<in>t. (0::real) \<le> u x" "setsum u t = 1"*)
  from this(2) have "\<forall>u. t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and> setsum u t = 1 \<longrightarrow> (\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s" apply(induct_tac t rule:finite_induct)
    prefer 3 apply (rule,rule) apply(erule conjE)+ proof-
    fix x f u assume ind:"\<forall>u. f \<subseteq> s \<and> (\<forall>x\<in>f. 0 \<le> u x) \<and> setsum u f = 1 \<longrightarrow> (\<Sum>x\<in>f. u x *\<^sub>R x) \<in> s"
    assume as:"finite f" "x \<notin> f" "insert x f \<subseteq> s" "\<forall>x\<in>insert x f. 0 \<le> u x" "setsum u (insert x f) = (1::real)"
    show "(\<Sum>x\<in>insert x f. u x *\<^sub>R x) \<in> s" proof(cases "u x = 1")
      case True hence "setsum (\<lambda>x. u x *\<^sub>R x) f = 0" apply(rule_tac setsum_0') apply(rule ccontr) unfolding ball_simps apply(erule bexE) proof-
        fix y assume y:"y \<in> f" "u y *\<^sub>R y \<noteq> 0"
        hence uy:"u y \<noteq> 0" by auto
        hence "setsum (\<lambda>k. if k=y then u y else 0) f \<le> setsum u f" apply(rule_tac setsum_mono) using as(4) by auto
        hence "setsum u f \<ge> u y" using y(1) and as(1) by(auto simp add: setsum_delta) 
        hence "setsum u f > 0" using uy apply(rule_tac less_le_trans[of _ "u y"]) using as(4) and y(1) by auto
        thus False using as(2,5) unfolding setsum_clauses(2)[OF as(1)] and True by auto qed
      thus ?thesis unfolding setsum_clauses(2)[OF as(1)] using as(2,3) unfolding True by auto
    next
      have *:"setsum u f = setsum u (insert x f) - u x" using as(2) unfolding setsum_clauses(2)[OF as(1)] by auto
      have **:"u x \<le> 1" apply(rule ccontr) unfolding not_le using as(5)[unfolded setsum_clauses(2)[OF as(1)]] and as(2)
        using setsum_nonneg[of f u] and as(4) by auto
      case False hence "inverse (1 - u x) *\<^sub>R (\<Sum>x\<in>f. u x *\<^sub>R x) \<in> s" unfolding scaleR_right.setsum and scaleR_scaleR
        apply(rule_tac ind[THEN spec, THEN mp]) apply rule defer apply rule apply rule apply(rule mult_nonneg_nonneg)
        unfolding setsum_right_distrib[THEN sym] and * using as and ** by auto
      hence "u x *\<^sub>R x + (1 - u x) *\<^sub>R ((inverse (1 - u x)) *\<^sub>R setsum (\<lambda>x. u x *\<^sub>R x) f) \<in>s" 
        apply(rule_tac asm(1)[THEN bspec, THEN bspec, THEN spec, THEN mp, THEN spec, THEN mp, THEN mp]) using as and ** False by auto 
      thus ?thesis unfolding setsum_clauses(2)[OF as(1)] using as(2) and False by auto qed
  qed auto thus "t \<subseteq> s \<and> (\<forall>x\<in>t. 0 \<le> u x) \<and> setsum u t = 1 \<longrightarrow> (\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s" by auto
qed

lemma convex_finite: assumes "finite s"
  shows "convex s \<longleftrightarrow> (\<forall>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1
                      \<longrightarrow> setsum (\<lambda>x. u x *\<^sub>R x) s \<in> s)"
  unfolding convex_explicit apply(rule, rule, rule) defer apply(rule,rule,rule)apply(erule conjE)+ proof-
  fix t u assume as:"\<forall>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<longrightarrow> (\<Sum>x\<in>s. u x *\<^sub>R x) \<in> s" " finite t" "t \<subseteq> s" "\<forall>x\<in>t. 0 \<le> u x" "setsum u t = (1::real)"
  have *:"s \<inter> t = t" using as(3) by auto
  show "(\<Sum>x\<in>t. u x *\<^sub>R x) \<in> s" using as(1)[THEN spec[where x="\<lambda>x. if x\<in>t then u x else 0"]]
    unfolding if_smult and setsum_cases[OF assms] and * using as(2-) by auto
qed (erule_tac x=s in allE, erule_tac x=u in allE, auto)

subsection {* Cones. *}

definition
  cone :: "'a::real_vector set \<Rightarrow> bool" where
  "cone s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>c\<ge>0. (c *\<^sub>R x) \<in> s)"

lemma cone_empty[intro, simp]: "cone {}"
  unfolding cone_def by auto

lemma cone_univ[intro, simp]: "cone UNIV"
  unfolding cone_def by auto

lemma cone_Inter[intro]: "(\<forall>s\<in>f. cone s) \<Longrightarrow> cone(\<Inter> f)"
  unfolding cone_def by auto

subsection {* Conic hull. *}

lemma cone_cone_hull: "cone (cone hull s)"
  unfolding hull_def using cone_Inter[of "{t \<in> conic. s \<subseteq> t}"] 
  by (auto simp add: mem_def)

lemma cone_hull_eq: "(cone hull s = s) \<longleftrightarrow> cone s"
  apply(rule hull_eq[unfolded mem_def])
  using cone_Inter unfolding subset_eq by (auto simp add: mem_def)

subsection {* Affine dependence and consequential theorems (from Lars Schewe). *}

definition
  affine_dependent :: "'a::real_vector set \<Rightarrow> bool" where
  "affine_dependent s \<longleftrightarrow> (\<exists>x\<in>s. x \<in> (affine hull (s - {x})))"

lemma affine_dependent_explicit:
  "affine_dependent p \<longleftrightarrow>
    (\<exists>s u. finite s \<and> s \<subseteq> p \<and> setsum u s = 0 \<and>
    (\<exists>v\<in>s. u v \<noteq> 0) \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = 0)"
  unfolding affine_dependent_def affine_hull_explicit mem_Collect_eq apply(rule)
  apply(erule bexE,erule exE,erule exE) apply(erule conjE)+ defer apply(erule exE,erule exE) apply(erule conjE)+ apply(erule bexE)
proof-
  fix x s u assume as:"x \<in> p" "finite s" "s \<noteq> {}" "s \<subseteq> p - {x}" "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"
  have "x\<notin>s" using as(1,4) by auto
  show "\<exists>s u. finite s \<and> s \<subseteq> p \<and> setsum u s = 0 \<and> (\<exists>v\<in>s. u v \<noteq> 0) \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = 0"
    apply(rule_tac x="insert x s" in exI, rule_tac x="\<lambda>v. if v = x then - 1 else u v" in exI)
    unfolding if_smult and setsum_clauses(2)[OF as(2)] and setsum_delta_notmem[OF `x\<notin>s`] and as using as by auto 
next
  fix s u v assume as:"finite s" "s \<subseteq> p" "setsum u s = 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0" "v \<in> s" "u v \<noteq> 0"
  have "s \<noteq> {v}" using as(3,6) by auto
  thus "\<exists>x\<in>p. \<exists>s u. finite s \<and> s \<noteq> {} \<and> s \<subseteq> p - {x} \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x" 
    apply(rule_tac x=v in bexI, rule_tac x="s - {v}" in exI, rule_tac x="\<lambda>x. - (1 / u v) * u x" in exI)
    unfolding scaleR_scaleR[THEN sym] and scaleR_right.setsum [symmetric] unfolding setsum_right_distrib[THEN sym] and setsum_diff1[OF as(1)] using as by auto
qed

lemma affine_dependent_explicit_finite:
  fixes s :: "'a::real_vector set" assumes "finite s"
  shows "affine_dependent s \<longleftrightarrow> (\<exists>u. setsum u s = 0 \<and> (\<exists>v\<in>s. u v \<noteq> 0) \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = 0)"
  (is "?lhs = ?rhs")
proof
  have *:"\<And>vt u v. (if vt then u v else 0) *\<^sub>R v = (if vt then (u v) *\<^sub>R v else (0::'a))" by auto
  assume ?lhs
  then obtain t u v where "finite t" "t \<subseteq> s" "setsum u t = 0" "v\<in>t" "u v \<noteq> 0"  "(\<Sum>v\<in>t. u v *\<^sub>R v) = 0"
    unfolding affine_dependent_explicit by auto
  thus ?rhs apply(rule_tac x="\<lambda>x. if x\<in>t then u x else 0" in exI)
    apply auto unfolding * and setsum_restrict_set[OF assms, THEN sym]
    unfolding Int_absorb1[OF `t\<subseteq>s`] by auto
next
  assume ?rhs
  then obtain u v where "setsum u s = 0"  "v\<in>s" "u v \<noteq> 0" "(\<Sum>v\<in>s. u v *\<^sub>R v) = 0" by auto
  thus ?lhs unfolding affine_dependent_explicit using assms by auto
qed

subsection {* A general lemma. *}

lemma convex_connected:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s" shows "connected s"
proof-
  { fix e1 e2 assume as:"open e1" "open e2" "e1 \<inter> e2 \<inter> s = {}" "s \<subseteq> e1 \<union> e2" 
    assume "e1 \<inter> s \<noteq> {}" "e2 \<inter> s \<noteq> {}"
    then obtain x1 x2 where x1:"x1\<in>e1" "x1\<in>s" and x2:"x2\<in>e2" "x2\<in>s" by auto
    hence n:"norm (x1 - x2) > 0" unfolding zero_less_norm_iff using as(3) by auto

    { fix x e::real assume as:"0 \<le> x" "x \<le> 1" "0 < e"
      { fix y have *:"(1 - x) *\<^sub>R x1 + x *\<^sub>R x2 - ((1 - y) *\<^sub>R x1 + y *\<^sub>R x2) = (y - x) *\<^sub>R x1 - (y - x) *\<^sub>R x2"
          by (simp add: algebra_simps)
        assume "\<bar>y - x\<bar> < e / norm (x1 - x2)"
        hence "norm ((1 - x) *\<^sub>R x1 + x *\<^sub>R x2 - ((1 - y) *\<^sub>R x1 + y *\<^sub>R x2)) < e"
          unfolding * and scaleR_right_diff_distrib[THEN sym]
          unfolding less_divide_eq using n by auto  }
      hence "\<exists>d>0. \<forall>y. \<bar>y - x\<bar> < d \<longrightarrow> norm ((1 - x) *\<^sub>R x1 + x *\<^sub>R x2 - ((1 - y) *\<^sub>R x1 + y *\<^sub>R x2)) < e"
        apply(rule_tac x="e / norm (x1 - x2)" in exI) using as
        apply auto unfolding zero_less_divide_iff using n by simp  }  note * = this

    have "\<exists>x\<ge>0. x \<le> 1 \<and> (1 - x) *\<^sub>R x1 + x *\<^sub>R x2 \<notin> e1 \<and> (1 - x) *\<^sub>R x1 + x *\<^sub>R x2 \<notin> e2"
      apply(rule connected_real_lemma) apply (simp add: `x1\<in>e1` `x2\<in>e2` dist_commute)+
      using * apply(simp add: dist_norm)
      using as(1,2)[unfolded open_dist] apply simp
      using as(1,2)[unfolded open_dist] apply simp
      using assms[unfolded convex_alt, THEN bspec[where x=x1], THEN bspec[where x=x2]] using x1 x2
      using as(3) by auto
    then obtain x where "x\<ge>0" "x\<le>1" "(1 - x) *\<^sub>R x1 + x *\<^sub>R x2 \<notin> e1"  "(1 - x) *\<^sub>R x1 + x *\<^sub>R x2 \<notin> e2" by auto
    hence False using as(4) 
      using assms[unfolded convex_alt, THEN bspec[where x=x1], THEN bspec[where x=x2]]
      using x1(2) x2(2) by auto  }
  thus ?thesis unfolding connected_def by auto
qed

subsection {* One rather trivial consequence. *}

lemma connected_UNIV: "connected (UNIV :: 'a::real_normed_vector set)"
  by(simp add: convex_connected convex_UNIV)

subsection {* Convex functions into the reals. *}

definition
  convex_on :: "'a::real_vector set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "convex_on s f \<longleftrightarrow>
  (\<forall>x\<in>s. \<forall>y\<in>s. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> f (u *\<^sub>R x + v *\<^sub>R y) \<le> u * f x + v * f y)"

lemma convex_on_subset: "convex_on t f \<Longrightarrow> s \<subseteq> t \<Longrightarrow> convex_on s f"
  unfolding convex_on_def by auto

lemma convex_add:
  assumes "convex_on s f" "convex_on s g"
  shows "convex_on s (\<lambda>x. f x + g x)"
proof-
  { fix x y assume "x\<in>s" "y\<in>s" moreover
    fix u v ::real assume "0 \<le> u" "0 \<le> v" "u + v = 1"
    ultimately have "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y) \<le> (u * f x + v * f y) + (u * g x + v * g y)"
      using assms(1)[unfolded convex_on_def, THEN bspec[where x=x], THEN bspec[where x=y], THEN spec[where x=u]]
      using assms(2)[unfolded convex_on_def, THEN bspec[where x=x], THEN bspec[where x=y], THEN spec[where x=u]]
      apply - apply(rule add_mono) by auto
    hence "f (u *\<^sub>R x + v *\<^sub>R y) + g (u *\<^sub>R x + v *\<^sub>R y) \<le> u * (f x + g x) + v * (f y + g y)" by (simp add: ring_simps)  }
  thus ?thesis unfolding convex_on_def by auto 
qed

lemma convex_cmul: 
  assumes "0 \<le> (c::real)" "convex_on s f"
  shows "convex_on s (\<lambda>x. c * f x)"
proof-
  have *:"\<And>u c fx v fy ::real. u * (c * fx) + v * (c * fy) = c * (u * fx + v * fy)" by (simp add: ring_simps)
  show ?thesis using assms(2) and mult_mono1[OF _ assms(1)] unfolding convex_on_def and * by auto
qed

lemma convex_lower:
  assumes "convex_on s f"  "x\<in>s"  "y \<in> s"  "0 \<le> u"  "0 \<le> v"  "u + v = 1"
  shows "f (u *\<^sub>R x + v *\<^sub>R y) \<le> max (f x) (f y)"
proof-
  let ?m = "max (f x) (f y)"
  have "u * f x + v * f y \<le> u * max (f x) (f y) + v * max (f x) (f y)" apply(rule add_mono) 
    using assms(4,5) by(auto simp add: mult_mono1)
  also have "\<dots> = max (f x) (f y)" using assms(6) unfolding distrib[THEN sym] by auto
  finally show ?thesis using assms(1)[unfolded convex_on_def, THEN bspec[where x=x], THEN bspec[where x=y], THEN spec[where x=u]]
    using assms(2-6) by auto 
qed

lemma convex_local_global_minimum:
  fixes s :: "'a::real_normed_vector set"
  assumes "0<e" "convex_on s f" "ball x e \<subseteq> s" "\<forall>y\<in>ball x e. f x \<le> f y"
  shows "\<forall>y\<in>s. f x \<le> f y"
proof(rule ccontr)
  have "x\<in>s" using assms(1,3) by auto
  assume "\<not> (\<forall>y\<in>s. f x \<le> f y)"
  then obtain y where "y\<in>s" and y:"f x > f y" by auto
  hence xy:"0 < dist x y" by (auto simp add: dist_nz[THEN sym])

  then obtain u where "0 < u" "u \<le> 1" and u:"u < e / dist x y"
    using real_lbound_gt_zero[of 1 "e / dist x y"] using xy `e>0` and divide_pos_pos[of e "dist x y"] by auto
  hence "f ((1-u) *\<^sub>R x + u *\<^sub>R y) \<le> (1-u) * f x + u * f y" using `x\<in>s` `y\<in>s`
    using assms(2)[unfolded convex_on_def, THEN bspec[where x=x], THEN bspec[where x=y], THEN spec[where x="1-u"]] by auto
  moreover
  have *:"x - ((1 - u) *\<^sub>R x + u *\<^sub>R y) = u *\<^sub>R (x - y)" by (simp add: algebra_simps)
  have "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> ball x e" unfolding mem_ball dist_norm unfolding * and norm_scaleR and abs_of_pos[OF `0<u`] unfolding dist_norm[THEN sym]
    using u unfolding pos_less_divide_eq[OF xy] by auto
  hence "f x \<le> f ((1 - u) *\<^sub>R x + u *\<^sub>R y)" using assms(4) by auto
  ultimately show False using mult_strict_left_mono[OF y `u>0`] unfolding left_diff_distrib by auto
qed

lemma convex_distance:
  fixes s :: "'a::real_normed_vector set"
  shows "convex_on s (\<lambda>x. dist a x)"
proof(auto simp add: convex_on_def dist_norm)
  fix x y assume "x\<in>s" "y\<in>s"
  fix u v ::real assume "0 \<le> u" "0 \<le> v" "u + v = 1"
  have "a = u *\<^sub>R a + v *\<^sub>R a" unfolding scaleR_left_distrib[THEN sym] and `u+v=1` by simp
  hence *:"a - (u *\<^sub>R x + v *\<^sub>R y) = (u *\<^sub>R (a - x)) + (v *\<^sub>R (a - y))"
    by (auto simp add: algebra_simps)
  show "norm (a - (u *\<^sub>R x + v *\<^sub>R y)) \<le> u * norm (a - x) + v * norm (a - y)"
    unfolding * using norm_triangle_ineq[of "u *\<^sub>R (a - x)" "v *\<^sub>R (a - y)"]
    using `0 \<le> u` `0 \<le> v` by auto
qed

subsection {* Arithmetic operations on sets preserve convexity. *}

lemma convex_scaling: "convex s \<Longrightarrow> convex ((\<lambda>x. c *\<^sub>R x) ` s)"
  unfolding convex_def and image_iff apply auto
  apply (rule_tac x="u *\<^sub>R x+v *\<^sub>R y" in bexI) by (auto simp add: algebra_simps)

lemma convex_negations: "convex s \<Longrightarrow> convex ((\<lambda>x. -x)` s)"
  unfolding convex_def and image_iff apply auto
  apply (rule_tac x="u *\<^sub>R x+v *\<^sub>R y" in bexI) by auto

lemma convex_sums:
  assumes "convex s" "convex t"
  shows "convex {x + y| x y. x \<in> s \<and> y \<in> t}"
proof(auto simp add: convex_def image_iff scaleR_right_distrib)
  fix xa xb ya yb assume xy:"xa\<in>s" "xb\<in>s" "ya\<in>t" "yb\<in>t"
  fix u v ::real assume uv:"0 \<le> u" "0 \<le> v" "u + v = 1"
  show "\<exists>x y. u *\<^sub>R xa + u *\<^sub>R ya + (v *\<^sub>R xb + v *\<^sub>R yb) = x + y \<and> x \<in> s \<and> y \<in> t"
    apply(rule_tac x="u *\<^sub>R xa + v *\<^sub>R xb" in exI) apply(rule_tac x="u *\<^sub>R ya + v *\<^sub>R yb" in exI)
    using assms(1)[unfolded convex_def, THEN bspec[where x=xa], THEN bspec[where x=xb]]
    using assms(2)[unfolded convex_def, THEN bspec[where x=ya], THEN bspec[where x=yb]]
    using uv xy by auto
qed

lemma convex_differences: 
  assumes "convex s" "convex t"
  shows "convex {x - y| x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x - y| x y. x \<in> s \<and> y \<in> t} = {x + y |x y. x \<in> s \<and> y \<in> uminus ` t}" unfolding image_iff apply auto
    apply(rule_tac x=xa in exI) apply(rule_tac x="-y" in exI) apply simp
    apply(rule_tac x=xa in exI) apply(rule_tac x=xb in exI) by simp
  thus ?thesis using convex_sums[OF assms(1)  convex_negations[OF assms(2)]] by auto
qed

lemma convex_translation: assumes "convex s" shows "convex ((\<lambda>x. a + x) ` s)"
proof- have "{a + y |y. y \<in> s} = (\<lambda>x. a + x) ` s" by auto
  thus ?thesis using convex_sums[OF convex_singleton[of a] assms] by auto qed

lemma convex_affinity: assumes "convex s" shows "convex ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof- have "(\<lambda>x. a + c *\<^sub>R x) ` s = op + a ` op *\<^sub>R c ` s" by auto
  thus ?thesis using convex_translation[OF convex_scaling[OF assms], of a c] by auto qed

lemma convex_linear_image:
  assumes c:"convex s" and l:"bounded_linear f"
  shows "convex(f ` s)"
proof(auto simp add: convex_def)
  interpret f: bounded_linear f by fact
  fix x y assume xy:"x \<in> s" "y \<in> s"
  fix u v ::real assume uv:"0 \<le> u" "0 \<le> v" "u + v = 1"
  show "u *\<^sub>R f x + v *\<^sub>R f y \<in> f ` s" unfolding image_iff
    apply(rule_tac x="u *\<^sub>R x + v *\<^sub>R y" in bexI)
    unfolding f.add f.scaleR
    using c[unfolded convex_def] xy uv by auto
qed

subsection {* Balls, being convex, are connected. *}

lemma convex_ball:
  fixes x :: "'a::real_normed_vector"
  shows "convex (ball x e)" 
proof(auto simp add: convex_def)
  fix y z assume yz:"dist x y < e" "dist x z < e"
  fix u v ::real assume uv:"0 \<le> u" "0 \<le> v" "u + v = 1"
  have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> u * dist x y + v * dist x z" using uv yz
    using convex_distance[of "ball x e" x, unfolded convex_on_def, THEN bspec[where x=y], THEN bspec[where x=z]] by auto
  thus "dist x (u *\<^sub>R y + v *\<^sub>R z) < e" using real_convex_bound_lt[OF yz uv] by auto 
qed

lemma convex_cball:
  fixes x :: "'a::real_normed_vector"
  shows "convex(cball x e)"
proof(auto simp add: convex_def Ball_def mem_cball)
  fix y z assume yz:"dist x y \<le> e" "dist x z \<le> e"
  fix u v ::real assume uv:" 0 \<le> u" "0 \<le> v" "u + v = 1"
  have "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> u * dist x y + v * dist x z" using uv yz
    using convex_distance[of "cball x e" x, unfolded convex_on_def, THEN bspec[where x=y], THEN bspec[where x=z]] by auto
  thus "dist x (u *\<^sub>R y + v *\<^sub>R z) \<le> e" using real_convex_bound_le[OF yz uv] by auto 
qed

lemma connected_ball:
  fixes x :: "'a::real_normed_vector"
  shows "connected (ball x e)"
  using convex_connected convex_ball by auto

lemma connected_cball:
  fixes x :: "'a::real_normed_vector"
  shows "connected(cball x e)"
  using convex_connected convex_cball by auto

subsection {* Convex hull. *}

lemma convex_convex_hull: "convex(convex hull s)"
  unfolding hull_def using convex_Inter[of "{t\<in>convex. s\<subseteq>t}"]
  unfolding mem_def by auto

lemma convex_hull_eq: "convex hull s = s \<longleftrightarrow> convex s"
  apply (rule hull_eq [unfolded mem_def])
  apply (rule convex_Inter [unfolded Ball_def mem_def])
  apply (simp add: le_fun_def le_bool_def)
  done

lemma bounded_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  assumes "bounded s" shows "bounded(convex hull s)"
proof- from assms obtain B where B:"\<forall>x\<in>s. norm x \<le> B" unfolding bounded_iff by auto
  show ?thesis apply(rule bounded_subset[OF bounded_cball, of _ 0 B])
    unfolding subset_hull[unfolded mem_def, of convex, OF convex_cball]
    unfolding subset_eq mem_cball dist_norm using B by auto qed

lemma finite_imp_bounded_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  shows "finite s \<Longrightarrow> bounded(convex hull s)"
  using bounded_convex_hull finite_imp_bounded by auto

subsection {* Stepping theorems for convex hulls of finite sets. *}

lemma convex_hull_empty[simp]: "convex hull {} = {}"
  apply(rule hull_unique) unfolding mem_def by auto

lemma convex_hull_singleton[simp]: "convex hull {a} = {a}"
  apply(rule hull_unique) unfolding mem_def by auto

lemma convex_hull_insert:
  fixes s :: "'a::real_vector set"
  assumes "s \<noteq> {}"
  shows "convex hull (insert a s) = {x. \<exists>u\<ge>0. \<exists>v\<ge>0. \<exists>b. (u + v = 1) \<and>
                                    b \<in> (convex hull s) \<and> (x = u *\<^sub>R a + v *\<^sub>R b)}" (is "?xyz = ?hull")
 apply(rule,rule hull_minimal,rule) unfolding mem_def[of _ convex] and insert_iff prefer 3 apply rule proof-
 fix x assume x:"x = a \<or> x \<in> s"
 thus "x\<in>?hull" apply rule unfolding mem_Collect_eq apply(rule_tac x=1 in exI) defer 
   apply(rule_tac x=0 in exI) using assms hull_subset[of s convex] by auto
next
  fix x assume "x\<in>?hull"
  then obtain u v b where obt:"u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull s" "x = u *\<^sub>R a + v *\<^sub>R b" by auto
  have "a\<in>convex hull insert a s" "b\<in>convex hull insert a s"
    using hull_mono[of s "insert a s" convex] hull_mono[of "{a}" "insert a s" convex] and obt(4) by auto
  thus "x\<in> convex hull insert a s" unfolding obt(5) using convex_convex_hull[of "insert a s", unfolded convex_def]
    apply(erule_tac x=a in ballE) apply(erule_tac x=b in ballE) apply(erule_tac x=u in allE) using obt by auto
next
  show "convex ?hull" unfolding convex_def apply(rule,rule,rule,rule,rule,rule,rule) proof-
    fix x y u v assume as:"(0::real) \<le> u" "0 \<le> v" "u + v = 1" "x\<in>?hull" "y\<in>?hull"
    from as(4) obtain u1 v1 b1 where obt1:"u1\<ge>0" "v1\<ge>0" "u1 + v1 = 1" "b1 \<in> convex hull s" "x = u1 *\<^sub>R a + v1 *\<^sub>R b1" by auto
    from as(5) obtain u2 v2 b2 where obt2:"u2\<ge>0" "v2\<ge>0" "u2 + v2 = 1" "b2 \<in> convex hull s" "y = u2 *\<^sub>R a + v2 *\<^sub>R b2" by auto
    have *:"\<And>(x::'a) s1 s2. x - s1 *\<^sub>R x - s2 *\<^sub>R x = ((1::real) - (s1 + s2)) *\<^sub>R x" by (auto simp add: algebra_simps)
    have "\<exists>b \<in> convex hull s. u *\<^sub>R x + v *\<^sub>R y = (u * u1) *\<^sub>R a + (v * u2) *\<^sub>R a + (b - (u * u1) *\<^sub>R b - (v * u2) *\<^sub>R b)"
    proof(cases "u * v1 + v * v2 = 0")
      have *:"\<And>(x::'a) s1 s2. x - s1 *\<^sub>R x - s2 *\<^sub>R x = ((1::real) - (s1 + s2)) *\<^sub>R x" by (auto simp add: algebra_simps)
      case True hence **:"u * v1 = 0" "v * v2 = 0" apply- apply(rule_tac [!] ccontr)
        using mult_nonneg_nonneg[OF `u\<ge>0` `v1\<ge>0`] mult_nonneg_nonneg[OF `v\<ge>0` `v2\<ge>0`] by auto
      hence "u * u1 + v * u2 = 1" using as(3) obt1(3) obt2(3) by auto
      thus ?thesis unfolding obt1(5) obt2(5) * using assms hull_subset[of s convex] by(auto simp add: ** scaleR_right_distrib)
    next
      have "1 - (u * u1 + v * u2) = (u + v) - (u * u1 + v * u2)" using as(3) obt1(3) obt2(3) by (auto simp add: field_simps)
      also have "\<dots> = u * (v1 + u1 - u1) + v * (v2 + u2 - u2)" using as(3) obt1(3) obt2(3) by (auto simp add: field_simps) 
      also have "\<dots> = u * v1 + v * v2" by simp finally have **:"1 - (u * u1 + v * u2) = u * v1 + v * v2" by auto
      case False have "0 \<le> u * v1 + v * v2" "0 \<le> u * v1" "0 \<le> u * v1 + v * v2" "0 \<le> v * v2" apply -
        apply(rule add_nonneg_nonneg) prefer 4 apply(rule add_nonneg_nonneg) apply(rule_tac [!] mult_nonneg_nonneg)
        using as(1,2) obt1(1,2) obt2(1,2) by auto 
      thus ?thesis unfolding obt1(5) obt2(5) unfolding * and ** using False
        apply(rule_tac x="((u * v1) / (u * v1 + v * v2)) *\<^sub>R b1 + ((v * v2) / (u * v1 + v * v2)) *\<^sub>R b2" in bexI) defer
        apply(rule convex_convex_hull[of s, unfolded convex_def, rule_format]) using obt1(4) obt2(4)
        unfolding add_divide_distrib[THEN sym] and real_0_le_divide_iff
        by (auto simp add: scaleR_left_distrib scaleR_right_distrib)
    qed note * = this
    have u1:"u1 \<le> 1" apply(rule ccontr) unfolding obt1(3)[THEN sym] and not_le using obt1(2) by auto
    have u2:"u2 \<le> 1" apply(rule ccontr) unfolding obt2(3)[THEN sym] and not_le using obt2(2) by auto
    have "u1 * u + u2 * v \<le> (max u1 u2) * u + (max u1 u2) * v" apply(rule add_mono)
      apply(rule_tac [!] mult_right_mono) using as(1,2) obt1(1,2) obt2(1,2) by auto
    also have "\<dots> \<le> 1" unfolding mult.add_right[THEN sym] and as(3) using u1 u2 by auto
    finally 
    show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull" unfolding mem_Collect_eq apply(rule_tac x="u * u1 + v * u2" in exI)
      apply(rule conjI) defer apply(rule_tac x="1 - u * u1 - v * u2" in exI) unfolding Bex_def
      using as(1,2) obt1(1,2) obt2(1,2) * by(auto intro!: mult_nonneg_nonneg add_nonneg_nonneg simp add: algebra_simps)
  qed
qed


subsection {* Explicit expression for convex hull. *}

lemma convex_hull_indexed:
  fixes s :: "'a::real_vector set"
  shows "convex hull s = {y. \<exists>k u x. (\<forall>i\<in>{1::nat .. k}. 0 \<le> u i \<and> x i \<in> s) \<and>
                            (setsum u {1..k} = 1) \<and>
                            (setsum (\<lambda>i. u i *\<^sub>R x i) {1..k} = y)}" (is "?xyz = ?hull")
  apply(rule hull_unique) unfolding mem_def[of _ convex] apply(rule) defer
  apply(subst convex_def) apply(rule,rule,rule,rule,rule,rule,rule)
proof-
  fix x assume "x\<in>s"
  thus "x \<in> ?hull" unfolding mem_Collect_eq apply(rule_tac x=1 in exI, rule_tac x="\<lambda>x. 1" in exI) by auto
next
  fix t assume as:"s \<subseteq> t" "convex t"
  show "?hull \<subseteq> t" apply(rule) unfolding mem_Collect_eq apply(erule exE | erule conjE)+ proof-
    fix x k u y assume assm:"\<forall>i\<in>{1::nat..k}. 0 \<le> u i \<and> y i \<in> s" "setsum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R y i) = x"
    show "x\<in>t" unfolding assm(3)[THEN sym] apply(rule as(2)[unfolded convex, rule_format])
      using assm(1,2) as(1) by auto qed
next
  fix x y u v assume uv:"0\<le>u" "0\<le>v" "u+v=(1::real)" and xy:"x\<in>?hull" "y\<in>?hull"
  from xy obtain k1 u1 x1 where x:"\<forall>i\<in>{1::nat..k1}. 0\<le>u1 i \<and> x1 i \<in> s" "setsum u1 {Suc 0..k1} = 1" "(\<Sum>i = Suc 0..k1. u1 i *\<^sub>R x1 i) = x" by auto
  from xy obtain k2 u2 x2 where y:"\<forall>i\<in>{1::nat..k2}. 0\<le>u2 i \<and> x2 i \<in> s" "setsum u2 {Suc 0..k2} = 1" "(\<Sum>i = Suc 0..k2. u2 i *\<^sub>R x2 i) = y" by auto
  have *:"\<And>P (x1::'a) x2 s1 s2 i.(if P i then s1 else s2) *\<^sub>R (if P i then x1 else x2) = (if P i then s1 *\<^sub>R x1 else s2 *\<^sub>R x2)"
    "{1..k1 + k2} \<inter> {1..k1} = {1..k1}" "{1..k1 + k2} \<inter> - {1..k1} = (\<lambda>i. i + k1) ` {1..k2}"
    prefer 3 apply(rule,rule) unfolding image_iff apply(rule_tac x="x - k1" in bexI) by(auto simp add: not_le)
  have inj:"inj_on (\<lambda>i. i + k1) {1..k2}" unfolding inj_on_def by auto  
  show "u *\<^sub>R x + v *\<^sub>R y \<in> ?hull" apply(rule)
    apply(rule_tac x="k1 + k2" in exI, rule_tac x="\<lambda>i. if i \<in> {1..k1} then u * u1 i else v * u2 (i - k1)" in exI)
    apply(rule_tac x="\<lambda>i. if i \<in> {1..k1} then x1 i else x2 (i - k1)" in exI) apply(rule,rule) defer apply(rule)
    unfolding * and setsum_cases[OF finite_atLeastAtMost[of 1 "k1 + k2"]] and setsum_reindex[OF inj] and o_def
    unfolding scaleR_scaleR[THEN sym] scaleR_right.setsum [symmetric] setsum_right_distrib[THEN sym] proof-
    fix i assume i:"i \<in> {1..k1+k2}"
    show "0 \<le> (if i \<in> {1..k1} then u * u1 i else v * u2 (i - k1)) \<and> (if i \<in> {1..k1} then x1 i else x2 (i - k1)) \<in> s"
    proof(cases "i\<in>{1..k1}")
      case True thus ?thesis using mult_nonneg_nonneg[of u "u1 i"] and uv(1) x(1)[THEN bspec[where x=i]] by auto
    next def j \<equiv> "i - k1"
      case False with i have "j \<in> {1..k2}" unfolding j_def by auto
      thus ?thesis unfolding j_def[symmetric] using False
        using mult_nonneg_nonneg[of v "u2 j"] and uv(2) y(1)[THEN bspec[where x=j]] by auto qed
  qed(auto simp add: not_le x(2,3) y(2,3) uv(3))
qed

lemma convex_hull_finite:
  fixes s :: "'a::real_vector set"
  assumes "finite s"
  shows "convex hull s = {y. \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and>
         setsum u s = 1 \<and> setsum (\<lambda>x. u x *\<^sub>R x) s = y}" (is "?HULL = ?set")
proof(rule hull_unique, auto simp add: mem_def[of _ convex] convex_def[of ?set])
  fix x assume "x\<in>s" thus " \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>x\<in>s. u x *\<^sub>R x) = x" 
    apply(rule_tac x="\<lambda>y. if x=y then 1 else 0" in exI) apply auto
    unfolding setsum_delta'[OF assms] and setsum_delta''[OF assms] by auto 
next
  fix u v ::real assume uv:"0 \<le> u" "0 \<le> v" "u + v = 1"
  fix ux assume ux:"\<forall>x\<in>s. 0 \<le> ux x" "setsum ux s = (1::real)"
  fix uy assume uy:"\<forall>x\<in>s. 0 \<le> uy x" "setsum uy s = (1::real)"
  { fix x assume "x\<in>s"
    hence "0 \<le> u * ux x + v * uy x" using ux(1)[THEN bspec[where x=x]] uy(1)[THEN bspec[where x=x]] and uv(1,2)
      by (auto, metis add_nonneg_nonneg mult_nonneg_nonneg uv(1) uv(2))  }
  moreover have "(\<Sum>x\<in>s. u * ux x + v * uy x) = 1"
    unfolding setsum_addf and setsum_right_distrib[THEN sym] and ux(2) uy(2) using uv(3) by auto
  moreover have "(\<Sum>x\<in>s. (u * ux x + v * uy x) *\<^sub>R x) = u *\<^sub>R (\<Sum>x\<in>s. ux x *\<^sub>R x) + v *\<^sub>R (\<Sum>x\<in>s. uy x *\<^sub>R x)"
    unfolding scaleR_left_distrib and setsum_addf and scaleR_scaleR[THEN sym] and scaleR_right.setsum [symmetric] by auto
  ultimately show "\<exists>uc. (\<forall>x\<in>s. 0 \<le> uc x) \<and> setsum uc s = 1 \<and> (\<Sum>x\<in>s. uc x *\<^sub>R x) = u *\<^sub>R (\<Sum>x\<in>s. ux x *\<^sub>R x) + v *\<^sub>R (\<Sum>x\<in>s. uy x *\<^sub>R x)"
    apply(rule_tac x="\<lambda>x. u * ux x + v * uy x" in exI) by auto 
next
  fix t assume t:"s \<subseteq> t" "convex t" 
  fix u assume u:"\<forall>x\<in>s. 0 \<le> u x" "setsum u s = (1::real)"
  thus "(\<Sum>x\<in>s. u x *\<^sub>R x) \<in> t" using t(2)[unfolded convex_explicit, THEN spec[where x=s], THEN spec[where x=u]]
    using assms and t(1) by auto
qed

subsection {* Another formulation from Lars Schewe. *}

lemma setsum_constant_scaleR:
  fixes y :: "'a::real_vector"
  shows "(\<Sum>x\<in>A. y) = of_nat (card A) *\<^sub>R y"
apply (cases "finite A")
apply (induct set: finite)
apply (simp_all add: algebra_simps)
done

lemma convex_hull_explicit:
  fixes p :: "'a::real_vector set"
  shows "convex hull p = {y. \<exists>s u. finite s \<and> s \<subseteq> p \<and>
             (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = y}" (is "?lhs = ?rhs")
proof-
  { fix x assume "x\<in>?lhs"
    then obtain k u y where obt:"\<forall>i\<in>{1::nat..k}. 0 \<le> u i \<and> y i \<in> p" "setsum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R y i) = x"
      unfolding convex_hull_indexed by auto

    have fin:"finite {1..k}" by auto
    have fin':"\<And>v. finite {i \<in> {1..k}. y i = v}" by auto
    { fix j assume "j\<in>{1..k}"
      hence "y j \<in> p" "0 \<le> setsum u {i. Suc 0 \<le> i \<and> i \<le> k \<and> y i = y j}"
        using obt(1)[THEN bspec[where x=j]] and obt(2) apply simp
        apply(rule setsum_nonneg) using obt(1) by auto } 
    moreover
    have "(\<Sum>v\<in>y ` {1..k}. setsum u {i \<in> {1..k}. y i = v}) = 1"  
      unfolding setsum_image_gen[OF fin, THEN sym] using obt(2) by auto
    moreover have "(\<Sum>v\<in>y ` {1..k}. setsum u {i \<in> {1..k}. y i = v} *\<^sub>R v) = x"
      using setsum_image_gen[OF fin, of "\<lambda>i. u i *\<^sub>R y i" y, THEN sym]
      unfolding scaleR_left.setsum using obt(3) by auto
    ultimately have "\<exists>s u. finite s \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = x"
      apply(rule_tac x="y ` {1..k}" in exI)
      apply(rule_tac x="\<lambda>v. setsum u {i\<in>{1..k}. y i = v}" in exI) by auto
    hence "x\<in>?rhs" by auto  }
  moreover
  { fix y assume "y\<in>?rhs"
    then obtain s u where obt:"finite s" "s \<subseteq> p" "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = y" by auto

    obtain f where f:"inj_on f {1..card s}" "f ` {1..card s} = s" using ex_bij_betw_nat_finite_1[OF obt(1)] unfolding bij_betw_def by auto
    
    { fix i::nat assume "i\<in>{1..card s}"
      hence "f i \<in> s"  apply(subst f(2)[THEN sym]) by auto
      hence "0 \<le> u (f i)" "f i \<in> p" using obt(2,3) by auto  }
    moreover have *:"finite {1..card s}" by auto
    { fix y assume "y\<in>s"
      then obtain i where "i\<in>{1..card s}" "f i = y" using f using image_iff[of y f "{1..card s}"] by auto
      hence "{x. Suc 0 \<le> x \<and> x \<le> card s \<and> f x = y} = {i}" apply auto using f(1)[unfolded inj_on_def] apply(erule_tac x=x in ballE) by auto
      hence "card {x. Suc 0 \<le> x \<and> x \<le> card s \<and> f x = y} = 1" by auto
      hence "(\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x)) = u y"
            "(\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x) *\<^sub>R f x) = u y *\<^sub>R y"
        by (auto simp add: setsum_constant_scaleR)   }

    hence "(\<Sum>x = 1..card s. u (f x)) = 1" "(\<Sum>i = 1..card s. u (f i) *\<^sub>R f i) = y"
      unfolding setsum_image_gen[OF *(1), of "\<lambda>x. u (f x) *\<^sub>R f x" f] and setsum_image_gen[OF *(1), of "\<lambda>x. u (f x)" f] 
      unfolding f using setsum_cong2[of s "\<lambda>y. (\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x) *\<^sub>R f x)" "\<lambda>v. u v *\<^sub>R v"]
      using setsum_cong2 [of s "\<lambda>y. (\<Sum>x\<in>{x \<in> {1..card s}. f x = y}. u (f x))" u] unfolding obt(4,5) by auto
    
    ultimately have "\<exists>k u x. (\<forall>i\<in>{1..k}. 0 \<le> u i \<and> x i \<in> p) \<and> setsum u {1..k} = 1 \<and> (\<Sum>i::nat = 1..k. u i *\<^sub>R x i) = y"
      apply(rule_tac x="card s" in exI) apply(rule_tac x="u \<circ> f" in exI) apply(rule_tac x=f in exI) by fastsimp
    hence "y \<in> ?lhs" unfolding convex_hull_indexed by auto  }
  ultimately show ?thesis unfolding expand_set_eq by blast
qed

subsection {* A stepping theorem for that expansion. *}

lemma convex_hull_finite_step:
  fixes s :: "'a::real_vector set" assumes "finite s"
  shows "(\<exists>u. (\<forall>x\<in>insert a s. 0 \<le> u x) \<and> setsum u (insert a s) = w \<and> setsum (\<lambda>x. u x *\<^sub>R x) (insert a s) = y)
     \<longleftrightarrow> (\<exists>v\<ge>0. \<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = w - v \<and> setsum (\<lambda>x. u x *\<^sub>R x) s = y - v *\<^sub>R a)" (is "?lhs = ?rhs")
proof(rule, case_tac[!] "a\<in>s")
  assume "a\<in>s" hence *:"insert a s = s" by auto
  assume ?lhs thus ?rhs unfolding * apply(rule_tac x=0 in exI) by auto
next
  assume ?lhs then obtain u where u:"\<forall>x\<in>insert a s. 0 \<le> u x" "setsum u (insert a s) = w" "(\<Sum>x\<in>insert a s. u x *\<^sub>R x) = y" by auto
  assume "a\<notin>s" thus ?rhs apply(rule_tac x="u a" in exI) using u(1)[THEN bspec[where x=a]] apply simp
    apply(rule_tac x=u in exI) using u[unfolded setsum_clauses(2)[OF assms]] and `a\<notin>s` by auto
next
  assume "a\<in>s" hence *:"insert a s = s" by auto
  have fin:"finite (insert a s)" using assms by auto
  assume ?rhs then obtain v u where uv:"v\<ge>0" "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = w - v" "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a" by auto
  show ?lhs apply(rule_tac x="\<lambda>x. (if a = x then v else 0) + u x" in exI) unfolding scaleR_left_distrib and setsum_addf and setsum_delta''[OF fin] and setsum_delta'[OF fin]
    unfolding setsum_clauses(2)[OF assms] using uv and uv(2)[THEN bspec[where x=a]] and `a\<in>s` by auto
next
  assume ?rhs then obtain v u where uv:"v\<ge>0" "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = w - v" "(\<Sum>x\<in>s. u x *\<^sub>R x) = y - v *\<^sub>R a" by auto
  moreover assume "a\<notin>s" moreover have "(\<Sum>x\<in>s. if a = x then v else u x) = setsum u s" "(\<Sum>x\<in>s. (if a = x then v else u x) *\<^sub>R x) = (\<Sum>x\<in>s. u x *\<^sub>R x)"
    apply(rule_tac setsum_cong2) defer apply(rule_tac setsum_cong2) using `a\<notin>s` by auto
  ultimately show ?lhs apply(rule_tac x="\<lambda>x. if a = x then v else u x" in exI)  unfolding setsum_clauses(2)[OF assms] by auto
qed

subsection {* Hence some special cases. *}

lemma convex_hull_2:
  "convex hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b | u v. 0 \<le> u \<and> 0 \<le> v \<and> u + v = 1}"
proof- have *:"\<And>u. (\<forall>x\<in>{a, b}. 0 \<le> u x) \<longleftrightarrow> 0 \<le> u a \<and> 0 \<le> u b" by auto have **:"finite {b}" by auto
show ?thesis apply(simp add: convex_hull_finite) unfolding convex_hull_finite_step[OF **, of a 1, unfolded * conj_assoc]
  apply auto apply(rule_tac x=v in exI) apply(rule_tac x="1 - v" in exI) apply simp
  apply(rule_tac x=u in exI) apply simp apply(rule_tac x="\<lambda>x. v" in exI) by simp qed

lemma convex_hull_2_alt: "convex hull {a,b} = {a + u *\<^sub>R (b - a) | u.  0 \<le> u \<and> u \<le> 1}"
  unfolding convex_hull_2 unfolding Collect_def 
proof(rule ext) have *:"\<And>x y ::real. x + y = 1 \<longleftrightarrow> x = 1 - y" by auto
  fix x show "(\<exists>v u. x = v *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> v \<and> 0 \<le> u \<and> v + u = 1) = (\<exists>u. x = a + u *\<^sub>R (b - a) \<and> 0 \<le> u \<and> u \<le> 1)"
    unfolding * apply auto apply(rule_tac[!] x=u in exI) by (auto simp add: algebra_simps) qed

lemma convex_hull_3:
  "convex hull {a,b,c} = { u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c | u v w. 0 \<le> u \<and> 0 \<le> v \<and> 0 \<le> w \<and> u + v + w = 1}"
proof-
  have fin:"finite {a,b,c}" "finite {b,c}" "finite {c}" by auto
  have *:"\<And>x y z ::real. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z"
         "\<And>x y z ::real^_. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z" by (auto simp add: ring_simps)
  show ?thesis unfolding convex_hull_finite[OF fin(1)] and Collect_def and convex_hull_finite_step[OF fin(2)] and *
    unfolding convex_hull_finite_step[OF fin(3)] apply(rule ext) apply simp apply auto
    apply(rule_tac x=va in exI) apply (rule_tac x="u c" in exI) apply simp
    apply(rule_tac x="1 - v - w" in exI) apply simp apply(rule_tac x=v in exI) apply simp apply(rule_tac x="\<lambda>x. w" in exI) by simp qed

lemma convex_hull_3_alt:
  "convex hull {a,b,c} = {a + u *\<^sub>R (b - a) + v *\<^sub>R (c - a) | u v.  0 \<le> u \<and> 0 \<le> v \<and> u + v \<le> 1}"
proof- have *:"\<And>x y z ::real. x + y + z = 1 \<longleftrightarrow> x = 1 - y - z" by auto
  show ?thesis unfolding convex_hull_3 apply (auto simp add: *) apply(rule_tac x=v in exI) apply(rule_tac x=w in exI) apply (simp add: algebra_simps)
    apply(rule_tac x=u in exI) apply(rule_tac x=v in exI) by (simp add: algebra_simps) qed

subsection {* Relations among closure notions and corresponding hulls. *}

text {* TODO: Generalize linear algebra concepts defined in @{text
Euclidean_Space.thy} so that we can generalize these lemmas. *}

lemma subspace_imp_affine:
  fixes s :: "(real ^ _) set" shows "subspace s \<Longrightarrow> affine s"
  unfolding subspace_def affine_def smult_conv_scaleR by auto

lemma affine_imp_convex: "affine s \<Longrightarrow> convex s"
  unfolding affine_def convex_def by auto

lemma subspace_imp_convex:
  fixes s :: "(real ^ _) set" shows "subspace s \<Longrightarrow> convex s"
  using subspace_imp_affine affine_imp_convex by auto

lemma affine_hull_subset_span:
  fixes s :: "(real ^ _) set" shows "(affine hull s) \<subseteq> (span s)"
  unfolding span_def apply(rule hull_antimono) unfolding subset_eq Ball_def mem_def
  using subspace_imp_affine  by auto

lemma convex_hull_subset_span:
  fixes s :: "(real ^ _) set" shows "(convex hull s) \<subseteq> (span s)"
  unfolding span_def apply(rule hull_antimono) unfolding subset_eq Ball_def mem_def
  using subspace_imp_convex by auto

lemma convex_hull_subset_affine_hull: "(convex hull s) \<subseteq> (affine hull s)"
  unfolding span_def apply(rule hull_antimono) unfolding subset_eq Ball_def mem_def
  using affine_imp_convex by auto

lemma affine_dependent_imp_dependent:
  fixes s :: "(real ^ _) set" shows "affine_dependent s \<Longrightarrow> dependent s"
  unfolding affine_dependent_def dependent_def 
  using affine_hull_subset_span by auto

lemma dependent_imp_affine_dependent:
  fixes s :: "(real ^ _) set"
  assumes "dependent {x - a| x . x \<in> s}" "a \<notin> s"
  shows "affine_dependent (insert a s)"
proof-
  from assms(1)[unfolded dependent_explicit smult_conv_scaleR] obtain S u v 
    where obt:"finite S" "S \<subseteq> {x - a |x. x \<in> s}" "v\<in>S" "u v  \<noteq> 0" "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0" by auto
  def t \<equiv> "(\<lambda>x. x + a) ` S"

  have inj:"inj_on (\<lambda>x. x + a) S" unfolding inj_on_def by auto
  have "0\<notin>S" using obt(2) assms(2) unfolding subset_eq by auto
  have fin:"finite t" and  "t\<subseteq>s" unfolding t_def using obt(1,2) by auto 

  hence "finite (insert a t)" and "insert a t \<subseteq> insert a s" by auto 
  moreover have *:"\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x)) = (\<Sum>x\<in>t. Q x)"
    apply(rule setsum_cong2) using `a\<notin>s` `t\<subseteq>s` by auto
  have "(\<Sum>x\<in>insert a t. if x = a then - (\<Sum>x\<in>t. u (x - a)) else u (x - a)) = 0"
    unfolding setsum_clauses(2)[OF fin] using `a\<notin>s` `t\<subseteq>s` apply auto unfolding * by auto
  moreover have "\<exists>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) \<noteq> 0"
    apply(rule_tac x="v + a" in bexI) using obt(3,4) and `0\<notin>S` unfolding t_def by auto
  moreover have *:"\<And>P Q. (\<Sum>x\<in>t. (if x = a then P x else Q x) *\<^sub>R x) = (\<Sum>x\<in>t. Q x *\<^sub>R x)"
    apply(rule setsum_cong2) using `a\<notin>s` `t\<subseteq>s` by auto
  have "(\<Sum>x\<in>t. u (x - a)) *\<^sub>R a = (\<Sum>v\<in>t. u (v - a) *\<^sub>R v)" 
    unfolding scaleR_left.setsum unfolding t_def and setsum_reindex[OF inj] and o_def
    using obt(5) by (auto simp add: setsum_addf scaleR_right_distrib)
  hence "(\<Sum>v\<in>insert a t. (if v = a then - (\<Sum>x\<in>t. u (x - a)) else u (v - a)) *\<^sub>R v) = 0"
    unfolding setsum_clauses(2)[OF fin] using `a\<notin>s` `t\<subseteq>s` by (auto simp add: *  vector_smult_lneg) 
  ultimately show ?thesis unfolding affine_dependent_explicit
    apply(rule_tac x="insert a t" in exI) by auto 
qed

lemma convex_cone:
  "convex s \<and> cone s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. (x + y) \<in> s) \<and> (\<forall>x\<in>s. \<forall>c\<ge>0. (c *\<^sub>R x) \<in> s)" (is "?lhs = ?rhs")
proof-
  { fix x y assume "x\<in>s" "y\<in>s" and ?lhs
    hence "2 *\<^sub>R x \<in>s" "2 *\<^sub>R y \<in> s" unfolding cone_def by auto
    hence "x + y \<in> s" using `?lhs`[unfolded convex_def, THEN conjunct1]
      apply(erule_tac x="2*\<^sub>R x" in ballE) apply(erule_tac x="2*\<^sub>R y" in ballE)
      apply(erule_tac x="1/2" in allE) apply simp apply(erule_tac x="1/2" in allE) by auto  }
  thus ?thesis unfolding convex_def cone_def by auto
qed

lemma affine_dependent_biggerset: fixes s::"(real^'n) set"
  assumes "finite s" "card s \<ge> CARD('n) + 2"
  shows "affine_dependent s"
proof-
  have "s\<noteq>{}" using assms by auto then obtain a where "a\<in>s" by auto
  have *:"{x - a |x. x \<in> s - {a}} = (\<lambda>x. x - a) ` (s - {a})" by auto
  have "card {x - a |x. x \<in> s - {a}} = card (s - {a})" unfolding * 
    apply(rule card_image) unfolding inj_on_def by auto
  also have "\<dots> > CARD('n)" using assms(2)
    unfolding card_Diff_singleton[OF assms(1) `a\<in>s`] by auto
  finally show ?thesis apply(subst insert_Diff[OF `a\<in>s`, THEN sym])
    apply(rule dependent_imp_affine_dependent)
    apply(rule dependent_biggerset) by auto qed

lemma affine_dependent_biggerset_general:
  assumes "finite (s::(real^'n) set)" "card s \<ge> dim s + 2"
  shows "affine_dependent s"
proof-
  from assms(2) have "s \<noteq> {}" by auto
  then obtain a where "a\<in>s" by auto
  have *:"{x - a |x. x \<in> s - {a}} = (\<lambda>x. x - a) ` (s - {a})" by auto
  have **:"card {x - a |x. x \<in> s - {a}} = card (s - {a})" unfolding * 
    apply(rule card_image) unfolding inj_on_def by auto
  have "dim {x - a |x. x \<in> s - {a}} \<le> dim s"
    apply(rule subset_le_dim) unfolding subset_eq
    using `a\<in>s` by (auto simp add:span_superset span_sub)
  also have "\<dots> < dim s + 1" by auto
  also have "\<dots> \<le> card (s - {a})" using assms
    using card_Diff_singleton[OF assms(1) `a\<in>s`] by auto
  finally show ?thesis apply(subst insert_Diff[OF `a\<in>s`, THEN sym])
    apply(rule dependent_imp_affine_dependent) apply(rule dependent_biggerset_general) unfolding ** by auto qed

subsection {* Caratheodory's theorem. *}

lemma convex_hull_caratheodory: fixes p::"(real^'n) set"
  shows "convex hull p = {y. \<exists>s u. finite s \<and> s \<subseteq> p \<and> card s \<le> CARD('n) + 1 \<and>
  (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> setsum (\<lambda>v. u v *\<^sub>R v) s = y}"
  unfolding convex_hull_explicit expand_set_eq mem_Collect_eq
proof(rule,rule)
  fix y let ?P = "\<lambda>n. \<exists>s u. finite s \<and> card s = n \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
  assume "\<exists>s u. finite s \<and> s \<subseteq> p \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y"
  then obtain N where "?P N" by auto
  hence "\<exists>n\<le>N. (\<forall>k<n. \<not> ?P k) \<and> ?P n" apply(rule_tac ex_least_nat_le) by auto
  then obtain n where "?P n" and smallest:"\<forall>k<n. \<not> ?P k" by blast
  then obtain s u where obt:"finite s" "card s = n" "s\<subseteq>p" "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = 1"  "(\<Sum>v\<in>s. u v *\<^sub>R v) = y" by auto

  have "card s \<le> CARD('n) + 1" proof(rule ccontr, simp only: not_le)
    assume "CARD('n) + 1 < card s"
    hence "affine_dependent s" using affine_dependent_biggerset[OF obt(1)] by auto
    then obtain w v where wv:"setsum w s = 0" "v\<in>s" "w v \<noteq> 0" "(\<Sum>v\<in>s. w v *\<^sub>R v) = 0"
      using affine_dependent_explicit_finite[OF obt(1)] by auto
    def i \<equiv> "(\<lambda>v. (u v) / (- w v)) ` {v\<in>s. w v < 0}"  def t \<equiv> "Min i"
    have "\<exists>x\<in>s. w x < 0" proof(rule ccontr, simp add: not_less)
      assume as:"\<forall>x\<in>s. 0 \<le> w x"
      hence "setsum w (s - {v}) \<ge> 0" apply(rule_tac setsum_nonneg) by auto
      hence "setsum w s > 0" unfolding setsum_diff1'[OF obt(1) `v\<in>s`]
        using as[THEN bspec[where x=v]] and `v\<in>s` using `w v \<noteq> 0` by auto
      thus False using wv(1) by auto
    qed hence "i\<noteq>{}" unfolding i_def by auto

    hence "t \<ge> 0" using Min_ge_iff[of i 0 ] and obt(1) unfolding t_def i_def
      using obt(4)[unfolded le_less] apply auto unfolding divide_le_0_iff by auto 
    have t:"\<forall>v\<in>s. u v + t * w v \<ge> 0" proof
      fix v assume "v\<in>s" hence v:"0\<le>u v" using obt(4)[THEN bspec[where x=v]] by auto
      show"0 \<le> u v + t * w v" proof(cases "w v < 0")
        case False thus ?thesis apply(rule_tac add_nonneg_nonneg) 
          using v apply simp apply(rule mult_nonneg_nonneg) using `t\<ge>0` by auto next
        case True hence "t \<le> u v / (- w v)" using `v\<in>s`
          unfolding t_def i_def apply(rule_tac Min_le) using obt(1) by auto 
        thus ?thesis unfolding real_0_le_add_iff
          using pos_le_divide_eq[OF True[unfolded neg_0_less_iff_less[THEN sym]]] by auto
      qed qed

    obtain a where "a\<in>s" and "t = (\<lambda>v. (u v) / (- w v)) a" and "w a < 0"
      using Min_in[OF _ `i\<noteq>{}`] and obt(1) unfolding i_def t_def by auto
    hence a:"a\<in>s" "u a + t * w a = 0" by auto
    have *:"\<And>f. setsum f (s - {a}) = setsum f s - ((f a)::'a::ring)" unfolding setsum_diff1'[OF obt(1) `a\<in>s`] by auto 
    have "(\<Sum>v\<in>s. u v + t * w v) = 1"
      unfolding setsum_addf wv(1) setsum_right_distrib[THEN sym] obt(5) by auto
    moreover have "(\<Sum>v\<in>s. u v *\<^sub>R v + (t * w v) *\<^sub>R v) - (u a *\<^sub>R a + (t * w a) *\<^sub>R a) = y" 
      unfolding setsum_addf obt(6) scaleR_scaleR[THEN sym] scaleR_right.setsum [symmetric] wv(4)
      using a(2) [THEN eq_neg_iff_add_eq_0 [THEN iffD2]]
      by (simp add: vector_smult_lneg)
    ultimately have "?P (n - 1)" apply(rule_tac x="(s - {a})" in exI)
      apply(rule_tac x="\<lambda>v. u v + t * w v" in exI) using obt(1-3) and t and a by (auto simp add: * scaleR_left_distrib)
    thus False using smallest[THEN spec[where x="n - 1"]] by auto qed
  thus "\<exists>s u. finite s \<and> s \<subseteq> p \<and> card s \<le> CARD('n) + 1
    \<and> (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s = 1 \<and> (\<Sum>v\<in>s. u v *\<^sub>R v) = y" using obt by auto
qed auto

lemma caratheodory:
 "convex hull p = {x::real^'n. \<exists>s. finite s \<and> s \<subseteq> p \<and>
      card s \<le> CARD('n) + 1 \<and> x \<in> convex hull s}"
  unfolding expand_set_eq apply(rule, rule) unfolding mem_Collect_eq proof-
  fix x assume "x \<in> convex hull p"
  then obtain s u where "finite s" "s \<subseteq> p" "card s \<le> CARD('n) + 1"
     "\<forall>x\<in>s. 0 \<le> u x" "setsum u s = 1" "(\<Sum>v\<in>s. u v *\<^sub>R v) = x"unfolding convex_hull_caratheodory by auto
  thus "\<exists>s. finite s \<and> s \<subseteq> p \<and> card s \<le> CARD('n) + 1 \<and> x \<in> convex hull s"
    apply(rule_tac x=s in exI) using hull_subset[of s convex]
  using convex_convex_hull[unfolded convex_explicit, of s, THEN spec[where x=s], THEN spec[where x=u]] by auto
next
  fix x assume "\<exists>s. finite s \<and> s \<subseteq> p \<and> card s \<le> CARD('n) + 1 \<and> x \<in> convex hull s"
  then obtain s where "finite s" "s \<subseteq> p" "card s \<le> CARD('n) + 1" "x \<in> convex hull s" by auto
  thus "x \<in> convex hull p" using hull_mono[OF `s\<subseteq>p`] by auto
qed

subsection {* Openness and compactness are preserved by convex hull operation. *}

lemma open_convex_hull:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
  shows "open(convex hull s)"
  unfolding open_contains_cball convex_hull_explicit unfolding mem_Collect_eq ball_simps(10) 
proof(rule, rule) fix a
  assume "\<exists>sa u. finite sa \<and> sa \<subseteq> s \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = a"
  then obtain t u where obt:"finite t" "t\<subseteq>s" "\<forall>x\<in>t. 0 \<le> u x" "setsum u t = 1" "(\<Sum>v\<in>t. u v *\<^sub>R v) = a" by auto

  from assms[unfolded open_contains_cball] obtain b where b:"\<forall>x\<in>s. 0 < b x \<and> cball x (b x) \<subseteq> s"
    using bchoice[of s "\<lambda>x e. e>0 \<and> cball x e \<subseteq> s"] by auto
  have "b ` t\<noteq>{}" unfolding i_def using obt by auto  def i \<equiv> "b ` t"

  show "\<exists>e>0. cball a e \<subseteq> {y. \<exists>sa u. finite sa \<and> sa \<subseteq> s \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y}"
    apply(rule_tac x="Min i" in exI) unfolding subset_eq apply rule defer apply rule unfolding mem_Collect_eq
  proof-
    show "0 < Min i" unfolding i_def and Min_gr_iff[OF finite_imageI[OF obt(1)] `b \` t\<noteq>{}`]
      using b apply simp apply rule apply(erule_tac x=x in ballE) using `t\<subseteq>s` by auto
  next  fix y assume "y \<in> cball a (Min i)"
    hence y:"norm (a - y) \<le> Min i" unfolding dist_norm[THEN sym] by auto
    { fix x assume "x\<in>t"
      hence "Min i \<le> b x" unfolding i_def apply(rule_tac Min_le) using obt(1) by auto
      hence "x + (y - a) \<in> cball x (b x)" using y unfolding mem_cball dist_norm by auto
      moreover from `x\<in>t` have "x\<in>s" using obt(2) by auto
      ultimately have "x + (y - a) \<in> s" using y and b[THEN bspec[where x=x]] unfolding subset_eq by auto }
    moreover
    have *:"inj_on (\<lambda>v. v + (y - a)) t" unfolding inj_on_def by auto
    have "(\<Sum>v\<in>(\<lambda>v. v + (y - a)) ` t. u (v - (y - a))) = 1"
      unfolding setsum_reindex[OF *] o_def using obt(4) by auto
    moreover have "(\<Sum>v\<in>(\<lambda>v. v + (y - a)) ` t. u (v - (y - a)) *\<^sub>R v) = y"
      unfolding setsum_reindex[OF *] o_def using obt(4,5)
      by (simp add: setsum_addf setsum_subtractf scaleR_left.setsum[THEN sym] scaleR_right_distrib)
    ultimately show "\<exists>sa u. finite sa \<and> (\<forall>x\<in>sa. x \<in> s) \<and> (\<forall>x\<in>sa. 0 \<le> u x) \<and> setsum u sa = 1 \<and> (\<Sum>v\<in>sa. u v *\<^sub>R v) = y"
      apply(rule_tac x="(\<lambda>v. v + (y - a)) ` t" in exI) apply(rule_tac x="\<lambda>v. u (v - (y - a))" in exI)
      using obt(1, 3) by auto
  qed
qed

lemma open_dest_vec1_vimage: "open S \<Longrightarrow> open (dest_vec1 -` S)"
unfolding open_vector_def all_1
by (auto simp add: dest_vec1_def)

lemma tendsto_dest_vec1 [tendsto_intros]:
  "(f ---> l) net \<Longrightarrow> ((\<lambda>x. dest_vec1 (f x)) ---> dest_vec1 l) net"
  unfolding tendsto_def
  apply clarify
  apply (drule_tac x="dest_vec1 -` S" in spec)
  apply (simp add: open_dest_vec1_vimage)
  done

lemma continuous_dest_vec1: "continuous net f \<Longrightarrow> continuous net (\<lambda>x. dest_vec1 (f x))"
  unfolding continuous_def by (rule tendsto_dest_vec1)

(* TODO: move *)
lemma compact_real_interval:
  fixes a b :: real shows "compact {a..b}"
proof -
  have "continuous_on {vec1 a .. vec1 b} dest_vec1"
    unfolding continuous_on
    by (simp add: tendsto_dest_vec1 Lim_at_within Lim_ident_at)
  moreover have "compact {vec1 a .. vec1 b}" by (rule compact_interval)
  ultimately have "compact (dest_vec1 ` {vec1 a .. vec1 b})"
    by (rule compact_continuous_image)
  also have "dest_vec1 ` {vec1 a .. vec1 b} = {a..b}"
    by (auto simp add: image_def Bex_def exists_vec1)
  finally show ?thesis .
qed

lemma compact_convex_combinations:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s" "compact t"
  shows "compact { (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> t}"
proof-
  let ?X = "{0..1} \<times> s \<times> t"
  let ?h = "(\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
  have *:"{ (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> t} = ?h ` ?X"
    apply(rule set_ext) unfolding image_iff mem_Collect_eq
    apply rule apply auto
    apply (rule_tac x=u in rev_bexI, simp)
    apply (erule rev_bexI, erule rev_bexI, simp)
    by auto
  have "continuous_on ({0..1} \<times> s \<times> t)
     (\<lambda>z. (1 - fst z) *\<^sub>R fst (snd z) + fst z *\<^sub>R snd (snd z))"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  thus ?thesis unfolding *
    apply (rule compact_continuous_image)
    apply (intro compact_Times compact_real_interval assms)
    done
qed

lemma compact_convex_hull: fixes s::"(real^'n) set"
  assumes "compact s"  shows "compact(convex hull s)"
proof(cases "s={}")
  case True thus ?thesis using compact_empty by simp
next
  case False then obtain w where "w\<in>s" by auto
  show ?thesis unfolding caratheodory[of s]
  proof(induct "CARD('n) + 1")
    have *:"{x.\<exists>sa. finite sa \<and> sa \<subseteq> s \<and> card sa \<le> 0 \<and> x \<in> convex hull sa} = {}" 
      using compact_empty by (auto simp add: convex_hull_empty)
    case 0 thus ?case unfolding * by simp
  next
    case (Suc n)
    show ?case proof(cases "n=0")
      case True have "{x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t} = s"
        unfolding expand_set_eq and mem_Collect_eq proof(rule, rule)
        fix x assume "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
        then obtain t where t:"finite t" "t \<subseteq> s" "card t \<le> Suc n" "x \<in> convex hull t" by auto
        show "x\<in>s" proof(cases "card t = 0")
          case True thus ?thesis using t(4) unfolding card_0_eq[OF t(1)] by(simp add: convex_hull_empty)
        next
          case False hence "card t = Suc 0" using t(3) `n=0` by auto
          then obtain a where "t = {a}" unfolding card_Suc_eq by auto
          thus ?thesis using t(2,4) by (simp add: convex_hull_singleton)
        qed
      next
        fix x assume "x\<in>s"
        thus "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
          apply(rule_tac x="{x}" in exI) unfolding convex_hull_singleton by auto 
      qed thus ?thesis using assms by simp
    next
      case False have "{x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t} =
        { (1 - u) *\<^sub>R x + u *\<^sub>R y | x y u. 
        0 \<le> u \<and> u \<le> 1 \<and> x \<in> s \<and> y \<in> {x. \<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> x \<in> convex hull t}}"
        unfolding expand_set_eq and mem_Collect_eq proof(rule,rule)
        fix x assume "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> s \<and> (\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> v \<in> convex hull t)"
        then obtain u v c t where obt:"x = (1 - c) *\<^sub>R u + c *\<^sub>R v"
          "0 \<le> c \<and> c \<le> 1" "u \<in> s" "finite t" "t \<subseteq> s" "card t \<le> n"  "v \<in> convex hull t" by auto
        moreover have "(1 - c) *\<^sub>R u + c *\<^sub>R v \<in> convex hull insert u t"
          apply(rule mem_convex) using obt(2) and convex_convex_hull and hull_subset[of "insert u t" convex]
          using obt(7) and hull_mono[of t "insert u t"] by auto
        ultimately show "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
          apply(rule_tac x="insert u t" in exI) by (auto simp add: card_insert_if)
      next
        fix x assume "\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> Suc n \<and> x \<in> convex hull t"
        then obtain t where t:"finite t" "t \<subseteq> s" "card t \<le> Suc n" "x \<in> convex hull t" by auto
        let ?P = "\<exists>u v c. x = (1 - c) *\<^sub>R u + c *\<^sub>R v \<and>
          0 \<le> c \<and> c \<le> 1 \<and> u \<in> s \<and> (\<exists>t. finite t \<and> t \<subseteq> s \<and> card t \<le> n \<and> v \<in> convex hull t)"
        show ?P proof(cases "card t = Suc n")
          case False hence "card t \<le> n" using t(3) by auto
          thus ?P apply(rule_tac x=w in exI, rule_tac x=x in exI, rule_tac x=1 in exI) using `w\<in>s` and t
            by(auto intro!: exI[where x=t])
        next
          case True then obtain a u where au:"t = insert a u" "a\<notin>u" apply(drule_tac card_eq_SucD) by auto
          show ?P proof(cases "u={}")
            case True hence "x=a" using t(4)[unfolded au] by auto
            show ?P unfolding `x=a` apply(rule_tac x=a in exI, rule_tac x=a in exI, rule_tac x=1 in exI)
              using t and `n\<noteq>0` unfolding au by(auto intro!: exI[where x="{a}"] simp add: convex_hull_singleton)
          next
            case False obtain ux vx b where obt:"ux\<ge>0" "vx\<ge>0" "ux + vx = 1" "b \<in> convex hull u" "x = ux *\<^sub>R a + vx *\<^sub>R b"
              using t(4)[unfolded au convex_hull_insert[OF False]] by auto
            have *:"1 - vx = ux" using obt(3) by auto
            show ?P apply(rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=vx in exI)
              using obt and t(1-3) unfolding au and * using card_insert_disjoint[OF _ au(2)]
              by(auto intro!: exI[where x=u])
          qed
        qed
      qed
      thus ?thesis using compact_convex_combinations[OF assms Suc] by simp 
    qed
  qed 
qed

lemma finite_imp_compact_convex_hull:
  fixes s :: "(real ^ _) set"
  shows "finite s \<Longrightarrow> compact(convex hull s)"
  apply(drule finite_imp_compact, drule compact_convex_hull) by assumption

subsection {* Extremal points of a simplex are some vertices. *}

lemma dist_increases_online:
  fixes a b d :: "'a::real_inner"
  assumes "d \<noteq> 0"
  shows "dist a (b + d) > dist a b \<or> dist a (b - d) > dist a b"
proof(cases "inner a d - inner b d > 0")
  case True hence "0 < inner d d + (inner a d * 2 - inner b d * 2)" 
    apply(rule_tac add_pos_pos) using assms by auto
  thus ?thesis apply(rule_tac disjI2) unfolding dist_norm and norm_eq_sqrt_inner and real_sqrt_less_iff
    by (simp add: algebra_simps inner_commute)
next
  case False hence "0 < inner d d + (inner b d * 2 - inner a d * 2)" 
    apply(rule_tac add_pos_nonneg) using assms by auto
  thus ?thesis apply(rule_tac disjI1) unfolding dist_norm and norm_eq_sqrt_inner and real_sqrt_less_iff
    by (simp add: algebra_simps inner_commute)
qed

lemma norm_increases_online:
  fixes d :: "'a::real_inner"
  shows "d \<noteq> 0 \<Longrightarrow> norm(a + d) > norm a \<or> norm(a - d) > norm a"
  using dist_increases_online[of d a 0] unfolding dist_norm by auto

lemma simplex_furthest_lt:
  fixes s::"'a::real_inner set" assumes "finite s"
  shows "\<forall>x \<in> (convex hull s).  x \<notin> s \<longrightarrow> (\<exists>y\<in>(convex hull s). norm(x - a) < norm(y - a))"
proof(induct_tac rule: finite_induct[of s])
  fix x s assume as:"finite s" "x\<notin>s" "\<forall>x\<in>convex hull s. x \<notin> s \<longrightarrow> (\<exists>y\<in>convex hull s. norm (x - a) < norm (y - a))"
  show "\<forall>xa\<in>convex hull insert x s. xa \<notin> insert x s \<longrightarrow> (\<exists>y\<in>convex hull insert x s. norm (xa - a) < norm (y - a))"
  proof(rule,rule,cases "s = {}")
    case False fix y assume y:"y \<in> convex hull insert x s" "y \<notin> insert x s"
    obtain u v b where obt:"u\<ge>0" "v\<ge>0" "u + v = 1" "b \<in> convex hull s" "y = u *\<^sub>R x + v *\<^sub>R b"
      using y(1)[unfolded convex_hull_insert[OF False]] by auto
    show "\<exists>z\<in>convex hull insert x s. norm (y - a) < norm (z - a)"
    proof(cases "y\<in>convex hull s")
      case True then obtain z where "z\<in>convex hull s" "norm (y - a) < norm (z - a)"
        using as(3)[THEN bspec[where x=y]] and y(2) by auto
      thus ?thesis apply(rule_tac x=z in bexI) unfolding convex_hull_insert[OF False] by auto
    next
      case False show ?thesis  using obt(3) proof(cases "u=0", case_tac[!] "v=0")
        assume "u=0" "v\<noteq>0" hence "y = b" using obt by auto
        thus ?thesis using False and obt(4) by auto
      next
        assume "u\<noteq>0" "v=0" hence "y = x" using obt by auto
        thus ?thesis using y(2) by auto
      next
        assume "u\<noteq>0" "v\<noteq>0"
        then obtain w where w:"w>0" "w<u" "w<v" using real_lbound_gt_zero[of u v] and obt(1,2) by auto
        have "x\<noteq>b" proof(rule ccontr) 
          assume "\<not> x\<noteq>b" hence "y=b" unfolding obt(5)
            using obt(3) by(auto simp add: scaleR_left_distrib[THEN sym])
          thus False using obt(4) and False by simp qed
        hence *:"w *\<^sub>R (x - b) \<noteq> 0" using w(1) by auto
        show ?thesis using dist_increases_online[OF *, of a y]
        proof(erule_tac disjE)
          assume "dist a y < dist a (y + w *\<^sub>R (x - b))"
          hence "norm (y - a) < norm ((u + w) *\<^sub>R x + (v - w) *\<^sub>R b - a)"
            unfolding dist_commute[of a] unfolding dist_norm obt(5) by (simp add: algebra_simps)
          moreover have "(u + w) *\<^sub>R x + (v - w) *\<^sub>R b \<in> convex hull insert x s"
            unfolding convex_hull_insert[OF `s\<noteq>{}`] and mem_Collect_eq
            apply(rule_tac x="u + w" in exI) apply rule defer 
            apply(rule_tac x="v - w" in exI) using `u\<ge>0` and w and obt(3,4) by auto
          ultimately show ?thesis by auto
        next
          assume "dist a y < dist a (y - w *\<^sub>R (x - b))"
          hence "norm (y - a) < norm ((u - w) *\<^sub>R x + (v + w) *\<^sub>R b - a)"
            unfolding dist_commute[of a] unfolding dist_norm obt(5) by (simp add: algebra_simps)
          moreover have "(u - w) *\<^sub>R x + (v + w) *\<^sub>R b \<in> convex hull insert x s"
            unfolding convex_hull_insert[OF `s\<noteq>{}`] and mem_Collect_eq
            apply(rule_tac x="u - w" in exI) apply rule defer 
            apply(rule_tac x="v + w" in exI) using `u\<ge>0` and w and obt(3,4) by auto
          ultimately show ?thesis by auto
        qed
      qed auto
    qed
  qed auto
qed (auto simp add: assms)

lemma simplex_furthest_le:
  fixes s :: "(real ^ _) set"
  assumes "finite s" "s \<noteq> {}"
  shows "\<exists>y\<in>s. \<forall>x\<in>(convex hull s). norm(x - a) \<le> norm(y - a)"
proof-
  have "convex hull s \<noteq> {}" using hull_subset[of s convex] and assms(2) by auto
  then obtain x where x:"x\<in>convex hull s" "\<forall>y\<in>convex hull s. norm (y - a) \<le> norm (x - a)"
    using distance_attains_sup[OF finite_imp_compact_convex_hull[OF assms(1)], of a]
    unfolding dist_commute[of a] unfolding dist_norm by auto
  thus ?thesis proof(cases "x\<in>s")
    case False then obtain y where "y\<in>convex hull s" "norm (x - a) < norm (y - a)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=x]] and x(1) by auto
    thus ?thesis using x(2)[THEN bspec[where x=y]] by auto
  qed auto
qed

lemma simplex_furthest_le_exists:
  fixes s :: "(real ^ _) set"
  shows "finite s \<Longrightarrow> (\<forall>x\<in>(convex hull s). \<exists>y\<in>s. norm(x - a) \<le> norm(y - a))"
  using simplex_furthest_le[of s] by (cases "s={}")auto

lemma simplex_extremal_le:
  fixes s :: "(real ^ _) set"
  assumes "finite s" "s \<noteq> {}"
  shows "\<exists>u\<in>s. \<exists>v\<in>s. \<forall>x\<in>convex hull s. \<forall>y \<in> convex hull s. norm(x - y) \<le> norm(u - v)"
proof-
  have "convex hull s \<noteq> {}" using hull_subset[of s convex] and assms(2) by auto
  then obtain u v where obt:"u\<in>convex hull s" "v\<in>convex hull s"
    "\<forall>x\<in>convex hull s. \<forall>y\<in>convex hull s. norm (x - y) \<le> norm (u - v)"
    using compact_sup_maxdistance[OF finite_imp_compact_convex_hull[OF assms(1)]] by auto
  thus ?thesis proof(cases "u\<notin>s \<or> v\<notin>s", erule_tac disjE)
    assume "u\<notin>s" then obtain y where "y\<in>convex hull s" "norm (u - v) < norm (y - v)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=u]] and obt(1) by auto
    thus ?thesis using obt(3)[THEN bspec[where x=y], THEN bspec[where x=v]] and obt(2) by auto
  next
    assume "v\<notin>s" then obtain y where "y\<in>convex hull s" "norm (v - u) < norm (y - u)"
      using simplex_furthest_lt[OF assms(1), THEN bspec[where x=v]] and obt(2) by auto
    thus ?thesis using obt(3)[THEN bspec[where x=u], THEN bspec[where x=y]] and obt(1)
      by (auto simp add: norm_minus_commute)
  qed auto
qed 

lemma simplex_extremal_le_exists:
  fixes s :: "(real ^ _) set"
  shows "finite s \<Longrightarrow> x \<in> convex hull s \<Longrightarrow> y \<in> convex hull s
  \<Longrightarrow> (\<exists>u\<in>s. \<exists>v\<in>s. norm(x - y) \<le> norm(u - v))"
  using convex_hull_empty simplex_extremal_le[of s] by(cases "s={}")auto

subsection {* Closest point of a convex set is unique, with a continuous projection. *}

definition
  closest_point :: "(real ^ 'n) set \<Rightarrow> real ^ 'n \<Rightarrow> real ^ 'n" where
 "closest_point s a = (SOME x. x \<in> s \<and> (\<forall>y\<in>s. dist a x \<le> dist a y))"

lemma closest_point_exists:
  assumes "closed s" "s \<noteq> {}"
  shows  "closest_point s a \<in> s" "\<forall>y\<in>s. dist a (closest_point s a) \<le> dist a y"
  unfolding closest_point_def apply(rule_tac[!] someI2_ex) 
  using distance_attains_inf[OF assms(1,2), of a] by auto

lemma closest_point_in_set:
  "closed s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> (closest_point s a) \<in> s"
  by(meson closest_point_exists)

lemma closest_point_le:
  "closed s \<Longrightarrow> x \<in> s \<Longrightarrow> dist a (closest_point s a) \<le> dist a x"
  using closest_point_exists[of s] by auto

lemma closest_point_self:
  assumes "x \<in> s"  shows "closest_point s x = x"
  unfolding closest_point_def apply(rule some1_equality, rule ex1I[of _ x]) 
  using assms by auto

lemma closest_point_refl:
 "closed s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> (closest_point s x = x \<longleftrightarrow> x \<in> s)"
  using closest_point_in_set[of s x] closest_point_self[of x s] by auto

(* TODO: move *)
lemma norm_lt: "norm x < norm y \<longleftrightarrow> inner x x < inner y y"
  unfolding norm_eq_sqrt_inner by simp

(* TODO: move *)
lemma norm_le: "norm x \<le> norm y \<longleftrightarrow> inner x x \<le> inner y y"
  unfolding norm_eq_sqrt_inner by simp

lemma closer_points_lemma: fixes y::"real^'n"
  assumes "inner y z > 0"
  shows "\<exists>u>0. \<forall>v>0. v \<le> u \<longrightarrow> norm(v *\<^sub>R z - y) < norm y"
proof- have z:"inner z z > 0" unfolding inner_gt_zero_iff using assms by auto
  thus ?thesis using assms apply(rule_tac x="inner y z / inner z z" in exI) apply(rule) defer proof(rule+)
    fix v assume "0<v" "v \<le> inner y z / inner z z"
    thus "norm (v *\<^sub>R z - y) < norm y" unfolding norm_lt using z and assms
      by (simp add: field_simps inner_diff inner_commute mult_strict_left_mono[OF _ `0<v`])
  qed(rule divide_pos_pos, auto) qed

lemma closer_point_lemma:
  fixes x y z :: "real ^ 'n"
  assumes "inner (y - x) (z - x) > 0"
  shows "\<exists>u>0. u \<le> 1 \<and> dist (x + u *\<^sub>R (z - x)) y < dist x y"
proof- obtain u where "u>0" and u:"\<forall>v>0. v \<le> u \<longrightarrow> norm (v *\<^sub>R (z - x) - (y - x)) < norm (y - x)"
    using closer_points_lemma[OF assms] by auto
  show ?thesis apply(rule_tac x="min u 1" in exI) using u[THEN spec[where x="min u 1"]] and `u>0`
    unfolding dist_norm by(auto simp add: norm_minus_commute field_simps) qed

lemma any_closest_point_dot:
  fixes s :: "(real ^ _) set"
  assumes "convex s" "closed s" "x \<in> s" "y \<in> s" "\<forall>z\<in>s. dist a x \<le> dist a z"
  shows "inner (a - x) (y - x) \<le> 0"
proof(rule ccontr) assume "\<not> inner (a - x) (y - x) \<le> 0"
  then obtain u where u:"u>0" "u\<le>1" "dist (x + u *\<^sub>R (y - x)) a < dist x a" using closer_point_lemma[of a x y] by auto
  let ?z = "(1 - u) *\<^sub>R x + u *\<^sub>R y" have "?z \<in> s" using mem_convex[OF assms(1,3,4), of u] using u by auto
  thus False using assms(5)[THEN bspec[where x="?z"]] and u(3) by (auto simp add: dist_commute algebra_simps) qed

(* TODO: move *)
lemma norm_le_square: "norm x \<le> a \<longleftrightarrow> 0 \<le> a \<and> inner x x \<le> a\<twosuperior>"
proof -
  have "norm x \<le> a \<longleftrightarrow> 0 \<le> a \<and> norm x \<le> a"
    using norm_ge_zero [of x] by arith
  also have "\<dots> \<longleftrightarrow> 0 \<le> a \<and> (norm x)\<twosuperior> \<le> a\<twosuperior>"
    by (auto intro: power_mono dest: power2_le_imp_le)
  also have "\<dots> \<longleftrightarrow> 0 \<le> a \<and> inner x x \<le> a\<twosuperior>"
    unfolding power2_norm_eq_inner ..
  finally show ?thesis .
qed

lemma any_closest_point_unique:
  fixes s :: "(real ^ _) set"
  assumes "convex s" "closed s" "x \<in> s" "y \<in> s"
  "\<forall>z\<in>s. dist a x \<le> dist a z" "\<forall>z\<in>s. dist a y \<le> dist a z"
  shows "x = y" using any_closest_point_dot[OF assms(1-4,5)] and any_closest_point_dot[OF assms(1-2,4,3,6)]
  unfolding norm_pths(1) and norm_le_square
  by (auto simp add: algebra_simps)

lemma closest_point_unique:
  assumes "convex s" "closed s" "x \<in> s" "\<forall>z\<in>s. dist a x \<le> dist a z"
  shows "x = closest_point s a"
  using any_closest_point_unique[OF assms(1-3) _ assms(4), of "closest_point s a"] 
  using closest_point_exists[OF assms(2)] and assms(3) by auto

lemma closest_point_dot:
  assumes "convex s" "closed s" "x \<in> s"
  shows "inner (a - closest_point s a) (x - closest_point s a) \<le> 0"
  apply(rule any_closest_point_dot[OF assms(1,2) _ assms(3)])
  using closest_point_exists[OF assms(2)] and assms(3) by auto

lemma closest_point_lt:
  assumes "convex s" "closed s" "x \<in> s" "x \<noteq> closest_point s a"
  shows "dist a (closest_point s a) < dist a x"
  apply(rule ccontr) apply(rule_tac notE[OF assms(4)])
  apply(rule closest_point_unique[OF assms(1-3), of a])
  using closest_point_le[OF assms(2), of _ a] by fastsimp

lemma closest_point_lipschitz:
  assumes "convex s" "closed s" "s \<noteq> {}"
  shows "dist (closest_point s x) (closest_point s y) \<le> dist x y"
proof-
  have "inner (x - closest_point s x) (closest_point s y - closest_point s x) \<le> 0"
       "inner (y - closest_point s y) (closest_point s x - closest_point s y) \<le> 0"
    apply(rule_tac[!] any_closest_point_dot[OF assms(1-2)])
    using closest_point_exists[OF assms(2-3)] by auto
  thus ?thesis unfolding dist_norm and norm_le
    using inner_ge_zero[of "(x - closest_point s x) - (y - closest_point s y)"]
    by (simp add: inner_add inner_diff inner_commute) qed

lemma continuous_at_closest_point:
  assumes "convex s" "closed s" "s \<noteq> {}"
  shows "continuous (at x) (closest_point s)"
  unfolding continuous_at_eps_delta 
  using le_less_trans[OF closest_point_lipschitz[OF assms]] by auto

lemma continuous_on_closest_point:
  assumes "convex s" "closed s" "s \<noteq> {}"
  shows "continuous_on t (closest_point s)"
  apply(rule continuous_at_imp_continuous_on) using continuous_at_closest_point[OF assms] by auto

subsection {* Various point-to-set separating/supporting hyperplane theorems. *}

lemma supporting_hyperplane_closed_point:
  fixes s :: "(real ^ _) set"
  assumes "convex s" "closed s" "s \<noteq> {}" "z \<notin> s"
  shows "\<exists>a b. \<exists>y\<in>s. inner a z < b \<and> (inner a y = b) \<and> (\<forall>x\<in>s. inner a x \<ge> b)"
proof-
  from distance_attains_inf[OF assms(2-3)] obtain y where "y\<in>s" and y:"\<forall>x\<in>s. dist z y \<le> dist z x" by auto
  show ?thesis apply(rule_tac x="y - z" in exI, rule_tac x="inner (y - z) y" in exI, rule_tac x=y in bexI)
    apply rule defer apply rule defer apply(rule, rule ccontr) using `y\<in>s` proof-
    show "inner (y - z) z < inner (y - z) y" apply(subst diff_less_iff(1)[THEN sym])
      unfolding inner_diff_right[THEN sym] and inner_gt_zero_iff using `y\<in>s` `z\<notin>s` by auto
  next
    fix x assume "x\<in>s" have *:"\<forall>u. 0 \<le> u \<and> u \<le> 1 \<longrightarrow> dist z y \<le> dist z ((1 - u) *\<^sub>R y + u *\<^sub>R x)"
      using assms(1)[unfolded convex_alt] and y and `x\<in>s` and `y\<in>s` by auto
    assume "\<not> inner (y - z) y \<le> inner (y - z) x" then obtain v where
      "v>0" "v\<le>1" "dist (y + v *\<^sub>R (x - y)) z < dist y z" using closer_point_lemma[of z y x] apply - by (auto simp add: inner_diff)
    thus False using *[THEN spec[where x=v]] by(auto simp add: dist_commute algebra_simps)
  qed auto
qed

lemma separating_hyperplane_closed_point:
  fixes s :: "(real ^ _) set"
  assumes "convex s" "closed s" "z \<notin> s"
  shows "\<exists>a b. inner a z < b \<and> (\<forall>x\<in>s. inner a x > b)"
proof(cases "s={}")
  case True thus ?thesis apply(rule_tac x="-z" in exI, rule_tac x=1 in exI)
    using less_le_trans[OF _ inner_ge_zero[of z]] by auto
next
  case False obtain y where "y\<in>s" and y:"\<forall>x\<in>s. dist z y \<le> dist z x"
    using distance_attains_inf[OF assms(2) False] by auto
  show ?thesis apply(rule_tac x="y - z" in exI, rule_tac x="inner (y - z) z + (norm(y - z))\<twosuperior> / 2" in exI)
    apply rule defer apply rule proof-
    fix x assume "x\<in>s"
    have "\<not> 0 < inner (z - y) (x - y)" apply(rule_tac notI) proof(drule closer_point_lemma)
      assume "\<exists>u>0. u \<le> 1 \<and> dist (y + u *\<^sub>R (x - y)) z < dist y z"
      then obtain u where "u>0" "u\<le>1" "dist (y + u *\<^sub>R (x - y)) z < dist y z" by auto
      thus False using y[THEN bspec[where x="y + u *\<^sub>R (x - y)"]]
        using assms(1)[unfolded convex_alt, THEN bspec[where x=y]]
        using `x\<in>s` `y\<in>s` by (auto simp add: dist_commute algebra_simps) qed
    moreover have "0 < norm (y - z) ^ 2" using `y\<in>s` `z\<notin>s` by auto
    hence "0 < inner (y - z) (y - z)" unfolding power2_norm_eq_inner by simp
    ultimately show "inner (y - z) z + (norm (y - z))\<twosuperior> / 2 < inner (y - z) x"
      unfolding power2_norm_eq_inner and not_less by (auto simp add: field_simps inner_commute inner_diff)
  qed(insert `y\<in>s` `z\<notin>s`, auto)
qed

lemma separating_hyperplane_closed_0:
  assumes "convex (s::(real^'n) set)" "closed s" "0 \<notin> s"
  shows "\<exists>a b. a \<noteq> 0 \<and> 0 < b \<and> (\<forall>x\<in>s. inner a x > b)"
  proof(cases "s={}") guess a using UNIV_witness[where 'a='n] ..
  case True have "norm ((basis a)::real^'n) = 1" 
    using norm_basis and dimindex_ge_1 by auto
  thus ?thesis apply(rule_tac x="basis a" in exI, rule_tac x=1 in exI) using True by auto
next case False thus ?thesis using False using separating_hyperplane_closed_point[OF assms]
    apply - apply(erule exE)+ unfolding dot_rzero apply(rule_tac x=a in exI, rule_tac x=b in exI) by auto qed

subsection {* Now set-to-set for closed/compact sets. *}

lemma separating_hyperplane_closed_compact:
  assumes "convex (s::(real^'n) set)" "closed s" "convex t" "compact t" "t \<noteq> {}" "s \<inter> t = {}"
  shows "\<exists>a b. (\<forall>x\<in>s. inner a x < b) \<and> (\<forall>x\<in>t. inner a x > b)"
proof(cases "s={}")
  case True
  obtain b where b:"b>0" "\<forall>x\<in>t. norm x \<le> b" using compact_imp_bounded[OF assms(4)] unfolding bounded_pos by auto
  obtain z::"real^'n" where z:"norm z = b + 1" using vector_choose_size[of "b + 1"] and b(1) by auto
  hence "z\<notin>t" using b(2)[THEN bspec[where x=z]] by auto
  then obtain a b where ab:"inner a z < b" "\<forall>x\<in>t. b < inner a x"
    using separating_hyperplane_closed_point[OF assms(3) compact_imp_closed[OF assms(4)], of z] by auto
  thus ?thesis using True by auto
next
  case False then obtain y where "y\<in>s" by auto
  obtain a b where "0 < b" "\<forall>x\<in>{x - y |x y. x \<in> s \<and> y \<in> t}. b < inner a x"
    using separating_hyperplane_closed_point[OF convex_differences[OF assms(1,3)], of 0]
    using closed_compact_differences[OF assms(2,4)] using assms(6) by(auto, blast)
  hence ab:"\<forall>x\<in>s. \<forall>y\<in>t. b + inner a y < inner a x" apply- apply(rule,rule) apply(erule_tac x="x - y" in ballE) by (auto simp add: inner_diff)
  def k \<equiv> "Sup ((\<lambda>x. inner a x) ` t)"
  show ?thesis apply(rule_tac x="-a" in exI, rule_tac x="-(k + b / 2)" in exI)
    apply(rule,rule) defer apply(rule) unfolding inner_minus_left and neg_less_iff_less proof-
    from ab have "((\<lambda>x. inner a x) ` t) *<= (inner a y - b)"
      apply(erule_tac x=y in ballE) apply(rule setleI) using `y\<in>s` by auto
    hence k:"isLub UNIV ((\<lambda>x. inner a x) ` t) k" unfolding k_def apply(rule_tac Sup) using assms(5) by auto
    fix x assume "x\<in>t" thus "inner a x < (k + b / 2)" using `0<b` and isLubD2[OF k, of "inner a x"] by auto
  next
    fix x assume "x\<in>s" 
    hence "k \<le> inner a x - b" unfolding k_def apply(rule_tac Sup_least) using assms(5)
      using ab[THEN bspec[where x=x]] by auto
    thus "k + b / 2 < inner a x" using `0 < b` by auto
  qed
qed

lemma separating_hyperplane_compact_closed:
  fixes s :: "(real ^ _) set"
  assumes "convex s" "compact s" "s \<noteq> {}" "convex t" "closed t" "s \<inter> t = {}"
  shows "\<exists>a b. (\<forall>x\<in>s. inner a x < b) \<and> (\<forall>x\<in>t. inner a x > b)"
proof- obtain a b where "(\<forall>x\<in>t. inner a x < b) \<and> (\<forall>x\<in>s. b < inner a x)"
    using separating_hyperplane_closed_compact[OF assms(4-5,1-2,3)] and assms(6) by auto
  thus ?thesis apply(rule_tac x="-a" in exI, rule_tac x="-b" in exI) by auto qed

subsection {* General case without assuming closure and getting non-strict separation. *}

lemma separating_hyperplane_set_0:
  assumes "convex s" "(0::real^'n) \<notin> s"
  shows "\<exists>a. a \<noteq> 0 \<and> (\<forall>x\<in>s. 0 \<le> inner a x)"
proof- let ?k = "\<lambda>c. {x::real^'n. 0 \<le> inner c x}"
  have "frontier (cball 0 1) \<inter> (\<Inter> (?k ` s)) \<noteq> {}"
    apply(rule compact_imp_fip) apply(rule compact_frontier[OF compact_cball])
    defer apply(rule,rule,erule conjE) proof-
    fix f assume as:"f \<subseteq> ?k ` s" "finite f"
    obtain c where c:"f = ?k ` c" "c\<subseteq>s" "finite c" using finite_subset_image[OF as(2,1)] by auto
    then obtain a b where ab:"a \<noteq> 0" "0 < b"  "\<forall>x\<in>convex hull c. b < inner a x"
      using separating_hyperplane_closed_0[OF convex_convex_hull, of c]
      using finite_imp_compact_convex_hull[OF c(3), THEN compact_imp_closed] and assms(2)
      using subset_hull[unfolded mem_def, of convex, OF assms(1), THEN sym, of c] by auto
    hence "\<exists>x. norm x = 1 \<and> (\<forall>y\<in>c. 0 \<le> inner y x)" apply(rule_tac x="inverse(norm a) *\<^sub>R a" in exI)
       using hull_subset[of c convex] unfolding subset_eq and inner_scaleR
       apply- apply rule defer apply rule apply(rule mult_nonneg_nonneg)
       by(auto simp add: inner_commute elim!: ballE)
    thus "frontier (cball 0 1) \<inter> \<Inter>f \<noteq> {}" unfolding c(1) frontier_cball dist_norm by auto
  qed(insert closed_halfspace_ge, auto)
  then obtain x where "norm x = 1" "\<forall>y\<in>s. x\<in>?k y" unfolding frontier_cball dist_norm by auto
  thus ?thesis apply(rule_tac x=x in exI) by(auto simp add: inner_commute) qed

lemma separating_hyperplane_sets:
  assumes "convex s" "convex (t::(real^'n) set)" "s \<noteq> {}" "t \<noteq> {}" "s \<inter> t = {}"
  shows "\<exists>a b. a \<noteq> 0 \<and> (\<forall>x\<in>s. inner a x \<le> b) \<and> (\<forall>x\<in>t. inner a x \<ge> b)"
proof- from separating_hyperplane_set_0[OF convex_differences[OF assms(2,1)]]
  obtain a where "a\<noteq>0" "\<forall>x\<in>{x - y |x y. x \<in> t \<and> y \<in> s}. 0 \<le> inner a x" 
    using assms(3-5) by auto 
  hence "\<forall>x\<in>t. \<forall>y\<in>s. inner a y \<le> inner a x"
    by (force simp add: inner_diff)
  thus ?thesis
    apply(rule_tac x=a in exI, rule_tac x="Sup ((\<lambda>x. inner a x) ` s)" in exI) using `a\<noteq>0`
    apply auto
    apply (rule Sup[THEN isLubD2]) 
    prefer 4
    apply (rule Sup_least) 
     using assms(3-5) apply (auto simp add: setle_def)
    apply (metis COMBC_def Collect_def Collect_mem_eq) 
    done
qed

subsection {* More convexity generalities. *}

lemma convex_closure:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s" shows "convex(closure s)"
  unfolding convex_def Ball_def closure_sequential
  apply(rule,rule,rule,rule,rule,rule,rule,rule,rule) apply(erule_tac exE)+
  apply(rule_tac x="\<lambda>n. u *\<^sub>R xb n + v *\<^sub>R xc n" in exI) apply(rule,rule)
  apply(rule assms[unfolded convex_def, rule_format]) prefer 6
  apply(rule Lim_add) apply(rule_tac [1-2] Lim_cmul) by auto

lemma convex_interior:
  fixes s :: "'a::real_normed_vector set"
  assumes "convex s" shows "convex(interior s)"
  unfolding convex_alt Ball_def mem_interior apply(rule,rule,rule,rule,rule,rule) apply(erule exE | erule conjE)+ proof-
  fix x y u assume u:"0 \<le> u" "u \<le> (1::real)"
  fix e d assume ed:"ball x e \<subseteq> s" "ball y d \<subseteq> s" "0<d" "0<e" 
  show "\<exists>e>0. ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) e \<subseteq> s" apply(rule_tac x="min d e" in exI)
    apply rule unfolding subset_eq defer apply rule proof-
    fix z assume "z \<in> ball ((1 - u) *\<^sub>R x + u *\<^sub>R y) (min d e)"
    hence "(1- u) *\<^sub>R (z - u *\<^sub>R (y - x)) + u *\<^sub>R (z + (1 - u) *\<^sub>R (y - x)) \<in> s"
      apply(rule_tac assms[unfolded convex_alt, rule_format])
      using ed(1,2) and u unfolding subset_eq mem_ball Ball_def dist_norm by(auto simp add: algebra_simps)
    thus "z \<in> s" using u by (auto simp add: algebra_simps) qed(insert u ed(3-4), auto) qed

lemma convex_hull_eq_empty: "convex hull s = {} \<longleftrightarrow> s = {}"
  using hull_subset[of s convex] convex_hull_empty by auto

subsection {* Moving and scaling convex hulls. *}

lemma convex_hull_translation_lemma:
  "convex hull ((\<lambda>x. a + x) ` s) \<subseteq> (\<lambda>x. a + x) ` (convex hull s)"
  apply(rule hull_minimal, rule image_mono, rule hull_subset) unfolding mem_def
  using convex_translation[OF convex_convex_hull, of a s] by assumption

lemma convex_hull_bilemma: fixes neg
  assumes "(\<forall>s a. (convex hull (up a s)) \<subseteq> up a (convex hull s))"
  shows "(\<forall>s. up a (up (neg a) s) = s) \<and> (\<forall>s. up (neg a) (up a s) = s) \<and> (\<forall>s t a. s \<subseteq> t \<longrightarrow> up a s \<subseteq> up a t)
  \<Longrightarrow> \<forall>s. (convex hull (up a s)) = up a (convex hull s)"
  using assms by(metis subset_antisym) 

lemma convex_hull_translation:
  "convex hull ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (convex hull s)"
  apply(rule convex_hull_bilemma[rule_format, of _ _ "\<lambda>a. -a"], rule convex_hull_translation_lemma) unfolding image_image by auto

lemma convex_hull_scaling_lemma:
 "(convex hull ((\<lambda>x. c *\<^sub>R x) ` s)) \<subseteq> (\<lambda>x. c *\<^sub>R x) ` (convex hull s)"
  apply(rule hull_minimal, rule image_mono, rule hull_subset)
  unfolding mem_def by(rule convex_scaling, rule convex_convex_hull)

lemma convex_hull_scaling:
  "convex hull ((\<lambda>x. c *\<^sub>R x) ` s) = (\<lambda>x. c *\<^sub>R x) ` (convex hull s)"
  apply(cases "c=0") defer apply(rule convex_hull_bilemma[rule_format, of _ _ inverse]) apply(rule convex_hull_scaling_lemma)
  unfolding image_image scaleR_scaleR by(auto simp add:image_constant_conv convex_hull_eq_empty)

lemma convex_hull_affinity:
  "convex hull ((\<lambda>x. a + c *\<^sub>R x) ` s) = (\<lambda>x. a + c *\<^sub>R x) ` (convex hull s)"
  unfolding image_image[THEN sym] convex_hull_scaling convex_hull_translation  ..

subsection {* Convex set as intersection of halfspaces. *}

lemma convex_halfspace_intersection:
  fixes s :: "(real ^ _) set"
  assumes "closed s" "convex s"
  shows "s = \<Inter> {h. s \<subseteq> h \<and> (\<exists>a b. h = {x. inner a x \<le> b})}"
  apply(rule set_ext, rule) unfolding Inter_iff Ball_def mem_Collect_eq apply(rule,rule,erule conjE) proof- 
  fix x  assume "\<forall>xa. s \<subseteq> xa \<and> (\<exists>a b. xa = {x. inner a x \<le> b}) \<longrightarrow> x \<in> xa"
  hence "\<forall>a b. s \<subseteq> {x. inner a x \<le> b} \<longrightarrow> x \<in> {x. inner a x \<le> b}" by blast
  thus "x\<in>s" apply(rule_tac ccontr) apply(drule separating_hyperplane_closed_point[OF assms(2,1)])
    apply(erule exE)+ apply(erule_tac x="-a" in allE, erule_tac x="-b" in allE) by auto
qed auto

subsection {* Radon's theorem (from Lars Schewe). *}

lemma radon_ex_lemma:
  assumes "finite c" "affine_dependent c"
  shows "\<exists>u. setsum u c = 0 \<and> (\<exists>v\<in>c. u v \<noteq> 0) \<and> setsum (\<lambda>v. u v *\<^sub>R v) c = 0"
proof- from assms(2)[unfolded affine_dependent_explicit] guess s .. then guess u ..
  thus ?thesis apply(rule_tac x="\<lambda>v. if v\<in>s then u v else 0" in exI) unfolding if_smult scaleR_zero_left
    and setsum_restrict_set[OF assms(1), THEN sym] by(auto simp add: Int_absorb1) qed

lemma radon_s_lemma:
  assumes "finite s" "setsum f s = (0::real)"
  shows "setsum f {x\<in>s. 0 < f x} = - setsum f {x\<in>s. f x < 0}"
proof- have *:"\<And>x. (if f x < 0 then f x else 0) + (if 0 < f x then f x else 0) = f x" by auto
  show ?thesis unfolding real_add_eq_0_iff[THEN sym] and setsum_restrict_set''[OF assms(1)] and setsum_addf[THEN sym] and *
    using assms(2) by assumption qed

lemma radon_v_lemma:
  assumes "finite s" "setsum f s = 0" "\<forall>x. g x = (0::real) \<longrightarrow> f x = (0::real^_)"
  shows "(setsum f {x\<in>s. 0 < g x}) = - setsum f {x\<in>s. g x < 0}"
proof-
  have *:"\<And>x. (if 0 < g x then f x else 0) + (if g x < 0 then f x else 0) = f x" using assms(3) by auto 
  show ?thesis unfolding eq_neg_iff_add_eq_0 and setsum_restrict_set''[OF assms(1)] and setsum_addf[THEN sym] and *
    using assms(2) by assumption qed

lemma radon_partition:
  assumes "finite c" "affine_dependent c"
  shows "\<exists>m p. m \<inter> p = {} \<and> m \<union> p = c \<and> (convex hull m) \<inter> (convex hull p) \<noteq> {}" proof-
  obtain u v where uv:"setsum u c = 0" "v\<in>c" "u v \<noteq> 0"  "(\<Sum>v\<in>c. u v *\<^sub>R v) = 0" using radon_ex_lemma[OF assms] by auto
  have fin:"finite {x \<in> c. 0 < u x}" "finite {x \<in> c. 0 > u x}" using assms(1) by auto
  def z \<equiv> "(inverse (setsum u {x\<in>c. u x > 0})) *\<^sub>R setsum (\<lambda>x. u x *\<^sub>R x) {x\<in>c. u x > 0}"
  have "setsum u {x \<in> c. 0 < u x} \<noteq> 0" proof(cases "u v \<ge> 0")
    case False hence "u v < 0" by auto
    thus ?thesis proof(cases "\<exists>w\<in>{x \<in> c. 0 < u x}. u w > 0") 
      case True thus ?thesis using setsum_nonneg_eq_0_iff[of _ u, OF fin(1)] by auto
    next
      case False hence "setsum u c \<le> setsum (\<lambda>x. if x=v then u v else 0) c" apply(rule_tac setsum_mono) by auto
      thus ?thesis unfolding setsum_delta[OF assms(1)] using uv(2) and `u v < 0` and uv(1) by auto qed
  qed (insert setsum_nonneg_eq_0_iff[of _ u, OF fin(1)] uv(2-3), auto)

  hence *:"setsum u {x\<in>c. u x > 0} > 0" unfolding real_less_def apply(rule_tac conjI, rule_tac setsum_nonneg) by auto
  moreover have "setsum u ({x \<in> c. 0 < u x} \<union> {x \<in> c. u x < 0}) = setsum u c"
    "(\<Sum>x\<in>{x \<in> c. 0 < u x} \<union> {x \<in> c. u x < 0}. u x *\<^sub>R x) = (\<Sum>x\<in>c. u x *\<^sub>R x)"
    using assms(1) apply(rule_tac[!] setsum_mono_zero_left) by auto
  hence "setsum u {x \<in> c. 0 < u x} = - setsum u {x \<in> c. 0 > u x}"
   "(\<Sum>x\<in>{x \<in> c. 0 < u x}. u x *\<^sub>R x) = - (\<Sum>x\<in>{x \<in> c. 0 > u x}. u x *\<^sub>R x)" 
    unfolding eq_neg_iff_add_eq_0 using uv(1,4) by (auto simp add:  setsum_Un_zero[OF fin, THEN sym]) 
  moreover have "\<forall>x\<in>{v \<in> c. u v < 0}. 0 \<le> inverse (setsum u {x \<in> c. 0 < u x}) * - u x" 
    apply (rule) apply (rule mult_nonneg_nonneg) using * by auto

  ultimately have "z \<in> convex hull {v \<in> c. u v \<le> 0}" unfolding convex_hull_explicit mem_Collect_eq
    apply(rule_tac x="{v \<in> c. u v < 0}" in exI, rule_tac x="\<lambda>y. inverse (setsum u {x\<in>c. u x > 0}) * - u y" in exI)
    using assms(1) unfolding scaleR_scaleR[THEN sym] scaleR_right.setsum [symmetric] and z_def
    by(auto simp add: setsum_negf vector_smult_lneg mult_right.setsum[THEN sym])
  moreover have "\<forall>x\<in>{v \<in> c. 0 < u v}. 0 \<le> inverse (setsum u {x \<in> c. 0 < u x}) * u x" 
    apply (rule) apply (rule mult_nonneg_nonneg) using * by auto 
  hence "z \<in> convex hull {v \<in> c. u v > 0}" unfolding convex_hull_explicit mem_Collect_eq
    apply(rule_tac x="{v \<in> c. 0 < u v}" in exI, rule_tac x="\<lambda>y. inverse (setsum u {x\<in>c. u x > 0}) * u y" in exI)
    using assms(1) unfolding scaleR_scaleR[THEN sym] scaleR_right.setsum [symmetric] and z_def using *
    by(auto simp add: setsum_negf vector_smult_lneg mult_right.setsum[THEN sym])
  ultimately show ?thesis apply(rule_tac x="{v\<in>c. u v \<le> 0}" in exI, rule_tac x="{v\<in>c. u v > 0}" in exI) by auto
qed

lemma radon: assumes "affine_dependent c"
  obtains m p where "m\<subseteq>c" "p\<subseteq>c" "m \<inter> p = {}" "(convex hull m) \<inter> (convex hull p) \<noteq> {}"
proof- from assms[unfolded affine_dependent_explicit] guess s .. then guess u ..
  hence *:"finite s" "affine_dependent s" and s:"s \<subseteq> c" unfolding affine_dependent_explicit by auto
  from radon_partition[OF *] guess m .. then guess p ..
  thus ?thesis apply(rule_tac that[of p m]) using s by auto qed

subsection {* Helly's theorem. *}

lemma helly_induct: fixes f::"(real^'n) set set"
  assumes "card f = n" "n \<ge> CARD('n) + 1"
  "\<forall>s\<in>f. convex s" "\<forall>t\<subseteq>f. card t = CARD('n) + 1 \<longrightarrow> \<Inter> t \<noteq> {}"
  shows "\<Inter> f \<noteq> {}"
using assms proof(induct n arbitrary: f)
case (Suc n)
have "finite f" using `card f = Suc n` by (auto intro: card_ge_0_finite)
show "\<Inter> f \<noteq> {}" apply(cases "n = CARD('n)") apply(rule Suc(5)[rule_format])
  unfolding `card f = Suc n` proof-
  assume ng:"n \<noteq> CARD('n)" hence "\<exists>X. \<forall>s\<in>f. X s \<in> \<Inter>(f - {s})" apply(rule_tac bchoice) unfolding ex_in_conv
    apply(rule, rule Suc(1)[rule_format]) unfolding card_Diff_singleton_if[OF `finite f`] `card f = Suc n`
    defer defer apply(rule Suc(4)[rule_format]) defer apply(rule Suc(5)[rule_format]) using Suc(3) `finite f` by auto
  then obtain X where X:"\<forall>s\<in>f. X s \<in> \<Inter>(f - {s})" by auto
  show ?thesis proof(cases "inj_on X f")
    case False then obtain s t where st:"s\<noteq>t" "s\<in>f" "t\<in>f" "X s = X t" unfolding inj_on_def by auto
    hence *:"\<Inter> f = \<Inter> (f - {s}) \<inter> \<Inter> (f - {t})" by auto
    show ?thesis unfolding * unfolding ex_in_conv[THEN sym] apply(rule_tac x="X s" in exI)
      apply(rule, rule X[rule_format]) using X st by auto
  next case True then obtain m p where mp:"m \<inter> p = {}" "m \<union> p = X ` f" "convex hull m \<inter> convex hull p \<noteq> {}"
      using radon_partition[of "X ` f"] and affine_dependent_biggerset[of "X ` f"]
      unfolding card_image[OF True] and `card f = Suc n` using Suc(3) `finite f` and ng by auto
    have "m \<subseteq> X ` f" "p \<subseteq> X ` f" using mp(2) by auto
    then obtain g h where gh:"m = X ` g" "p = X ` h" "g \<subseteq> f" "h \<subseteq> f" unfolding subset_image_iff by auto 
    hence "f \<union> (g \<union> h) = f" by auto
    hence f:"f = g \<union> h" using inj_on_Un_image_eq_iff[of X f "g \<union> h"] and True
      unfolding mp(2)[unfolded image_Un[THEN sym] gh] by auto
    have *:"g \<inter> h = {}" using mp(1) unfolding gh using inj_on_image_Int[OF True gh(3,4)] by auto
    have "convex hull (X ` h) \<subseteq> \<Inter> g" "convex hull (X ` g) \<subseteq> \<Inter> h"
      apply(rule_tac [!] hull_minimal) using Suc gh(3-4)  unfolding mem_def unfolding subset_eq
      apply(rule_tac [2] convex_Inter, rule_tac [4] convex_Inter) apply rule prefer 3 apply rule proof-
      fix x assume "x\<in>X ` g" then guess y unfolding image_iff ..
      thus "x\<in>\<Inter>h" using X[THEN bspec[where x=y]] using * f by auto next
      fix x assume "x\<in>X ` h" then guess y unfolding image_iff ..
      thus "x\<in>\<Inter>g" using X[THEN bspec[where x=y]] using * f by auto
    qed(auto)
    thus ?thesis unfolding f using mp(3)[unfolded gh] by blast qed
qed(insert dimindex_ge_1, auto) qed(auto)

lemma helly: fixes f::"(real^'n) set set"
  assumes "card f \<ge> CARD('n) + 1" "\<forall>s\<in>f. convex s"
          "\<forall>t\<subseteq>f. card t = CARD('n) + 1 \<longrightarrow> \<Inter> t \<noteq> {}"
  shows "\<Inter> f \<noteq>{}"
  apply(rule helly_induct) using assms by auto

subsection {* Convex hull is "preserved" by a linear function. *}

lemma convex_hull_linear_image:
  assumes "bounded_linear f"
  shows "f ` (convex hull s) = convex hull (f ` s)"
  apply rule unfolding subset_eq ball_simps apply(rule_tac[!] hull_induct, rule hull_inc) prefer 3  
  apply(erule imageE)apply(rule_tac x=xa in image_eqI) apply assumption
  apply(rule hull_subset[unfolded subset_eq, rule_format]) apply assumption
proof-
  interpret f: bounded_linear f by fact
  show "convex {x. f x \<in> convex hull f ` s}" 
  unfolding convex_def by(auto simp add: f.scaleR f.add convex_convex_hull[unfolded convex_def, rule_format]) next
  interpret f: bounded_linear f by fact
  show "convex {x. x \<in> f ` (convex hull s)}" using  convex_convex_hull[unfolded convex_def, of s] 
    unfolding convex_def by (auto simp add: f.scaleR [symmetric] f.add [symmetric])
qed auto

lemma in_convex_hull_linear_image:
  assumes "bounded_linear f" "x \<in> convex hull s"
  shows "(f x) \<in> convex hull (f ` s)"
using convex_hull_linear_image[OF assms(1)] assms(2) by auto

subsection {* Homeomorphism of all convex compact sets with nonempty interior. *}

lemma compact_frontier_line_lemma:
  fixes s :: "(real ^ _) set"
  assumes "compact s" "0 \<in> s" "x \<noteq> 0" 
  obtains u where "0 \<le> u" "(u *\<^sub>R x) \<in> frontier s" "\<forall>v>u. (v *\<^sub>R x) \<notin> s"
proof-
  obtain b where b:"b>0" "\<forall>x\<in>s. norm x \<le> b" using compact_imp_bounded[OF assms(1), unfolded bounded_pos] by auto
  let ?A = "{y. \<exists>u. 0 \<le> u \<and> u \<le> b / norm(x) \<and> (y = u *\<^sub>R x)}"
  have A:"?A = (\<lambda>u. dest_vec1 u *\<^sub>R x) ` {0 .. vec1 (b / norm x)}"
    unfolding image_image[of "\<lambda>u. u *\<^sub>R x" "\<lambda>x. dest_vec1 x", THEN sym]
    unfolding dest_vec1_inverval vec1_dest_vec1 by auto
  have "compact ?A" unfolding A apply(rule compact_continuous_image, rule continuous_at_imp_continuous_on)
    apply(rule, rule continuous_vmul)
    apply (rule continuous_dest_vec1)
    apply(rule continuous_at_id) by(rule compact_interval)
  moreover have "{y. \<exists>u\<ge>0. u \<le> b / norm x \<and> y = u *\<^sub>R x} \<inter> s \<noteq> {}" apply(rule not_disjointI[OF _ assms(2)])
    unfolding mem_Collect_eq using `b>0` assms(3) by(auto intro!: divide_nonneg_pos)
  ultimately obtain u y where obt: "u\<ge>0" "u \<le> b / norm x" "y = u *\<^sub>R x"
    "y\<in>?A" "y\<in>s" "\<forall>z\<in>?A \<inter> s. dist 0 z \<le> dist 0 y" using distance_attains_sup[OF compact_inter[OF _ assms(1), of ?A], of 0] by auto

  have "norm x > 0" using assms(3)[unfolded zero_less_norm_iff[THEN sym]] by auto
  { fix v assume as:"v > u" "v *\<^sub>R x \<in> s"
    hence "v \<le> b / norm x" using b(2)[rule_format, OF as(2)] 
      using `u\<ge>0` unfolding pos_le_divide_eq[OF `norm x > 0`] by auto
    hence "norm (v *\<^sub>R x) \<le> norm y" apply(rule_tac obt(6)[rule_format, unfolded dist_0_norm]) apply(rule IntI) defer 
      apply(rule as(2)) unfolding mem_Collect_eq apply(rule_tac x=v in exI) 
      using as(1) `u\<ge>0` by(auto simp add:field_simps) 
    hence False unfolding obt(3) using `u\<ge>0` `norm x > 0` `v>u` by(auto simp add:field_simps)
  } note u_max = this

  have "u *\<^sub>R x \<in> frontier s" unfolding frontier_straddle apply(rule,rule,rule) apply(rule_tac x="u *\<^sub>R x" in bexI) unfolding obt(3)[THEN sym]
    prefer 3 apply(rule_tac x="(u + (e / 2) / norm x) *\<^sub>R x" in exI) apply(rule, rule) proof-
    fix e  assume "0 < e" and as:"(u + e / 2 / norm x) *\<^sub>R x \<in> s"
    hence "u + e / 2 / norm x > u" using`norm x > 0` by(auto simp del:zero_less_norm_iff intro!: divide_pos_pos)
    thus False using u_max[OF _ as] by auto
  qed(insert `y\<in>s`, auto simp add: dist_norm scaleR_left_distrib obt(3))
  thus ?thesis apply(rule_tac that[of u]) apply(rule obt(1), assumption)
    apply(rule,rule,rule ccontr) apply(rule u_max) by auto qed

lemma starlike_compact_projective:
  assumes "compact s" "cball (0::real^'n) 1 \<subseteq> s "
  "\<forall>x\<in>s. \<forall>u. 0 \<le> u \<and> u < 1 \<longrightarrow> (u *\<^sub>R x) \<in> (s - frontier s )"
  shows "s homeomorphic (cball (0::real^'n) 1)"
proof-
  have fs:"frontier s \<subseteq> s" apply(rule frontier_subset_closed) using compact_imp_closed[OF assms(1)] by simp
  def pi \<equiv> "\<lambda>x::real^'n. inverse (norm x) *\<^sub>R x"
  have "0 \<notin> frontier s" unfolding frontier_straddle apply(rule ccontr) unfolding not_not apply(erule_tac x=1 in allE)
    using assms(2)[unfolded subset_eq Ball_def mem_cball] by auto
  have injpi:"\<And>x y. pi x = pi y \<and> norm x = norm y \<longleftrightarrow> x = y" unfolding pi_def by auto

  have contpi:"continuous_on (UNIV - {0}) pi" apply(rule continuous_at_imp_continuous_on)
    apply rule unfolding pi_def
    apply (rule continuous_mul)
    apply (rule continuous_at_inv[unfolded o_def])
    apply (rule continuous_at_norm)
    apply simp
    apply (rule continuous_at_id)
    done
  def sphere \<equiv> "{x::real^'n. norm x = 1}"
  have pi:"\<And>x. x \<noteq> 0 \<Longrightarrow> pi x \<in> sphere" "\<And>x u. u>0 \<Longrightarrow> pi (u *\<^sub>R x) = pi x" unfolding pi_def sphere_def by auto

  have "0\<in>s" using assms(2) and centre_in_cball[of 0 1] by auto
  have front_smul:"\<forall>x\<in>frontier s. \<forall>u\<ge>0. u *\<^sub>R x \<in> s \<longleftrightarrow> u \<le> 1" proof(rule,rule,rule)
    fix x u assume x:"x\<in>frontier s" and "(0::real)\<le>u"
    hence "x\<noteq>0" using `0\<notin>frontier s` by auto
    obtain v where v:"0 \<le> v" "v *\<^sub>R x \<in> frontier s" "\<forall>w>v. w *\<^sub>R x \<notin> s"
      using compact_frontier_line_lemma[OF assms(1) `0\<in>s` `x\<noteq>0`] by auto
    have "v=1" apply(rule ccontr) unfolding neq_iff apply(erule disjE) proof-
      assume "v<1" thus False using v(3)[THEN spec[where x=1]] using x and fs by auto next
      assume "v>1" thus False using assms(3)[THEN bspec[where x="v *\<^sub>R x"], THEN spec[where x="inverse v"]]
        using v and x and fs unfolding inverse_less_1_iff by auto qed
    show "u *\<^sub>R x \<in> s \<longleftrightarrow> u \<le> 1" apply rule  using v(3)[unfolded `v=1`, THEN spec[where x=u]] proof-
      assume "u\<le>1" thus "u *\<^sub>R x \<in> s" apply(cases "u=1")
        using assms(3)[THEN bspec[where x=x], THEN spec[where x=u]] using `0\<le>u` and x and fs by auto qed auto qed

  have "\<exists>surf. homeomorphism (frontier s) sphere pi surf"
    apply(rule homeomorphism_compact) apply(rule compact_frontier[OF assms(1)])
    apply(rule continuous_on_subset[OF contpi]) defer apply(rule set_ext,rule) 
    unfolding inj_on_def prefer 3 apply(rule,rule,rule)
  proof- fix x assume "x\<in>pi ` frontier s" then obtain y where "y\<in>frontier s" "x = pi y" by auto
    thus "x \<in> sphere" using pi(1)[of y] and `0 \<notin> frontier s` by auto
  next fix x assume "x\<in>sphere" hence "norm x = 1" "x\<noteq>0" unfolding sphere_def by auto
    then obtain u where "0 \<le> u" "u *\<^sub>R x \<in> frontier s" "\<forall>v>u. v *\<^sub>R x \<notin> s"
      using compact_frontier_line_lemma[OF assms(1) `0\<in>s`, of x] by auto
    thus "x \<in> pi ` frontier s" unfolding image_iff le_less pi_def apply(rule_tac x="u *\<^sub>R x" in bexI) using `norm x = 1` `0\<notin>frontier s` by auto
  next fix x y assume as:"x \<in> frontier s" "y \<in> frontier s" "pi x = pi y"
    hence xys:"x\<in>s" "y\<in>s" using fs by auto
    from as(1,2) have nor:"norm x \<noteq> 0" "norm y \<noteq> 0" using `0\<notin>frontier s` by auto 
    from nor have x:"x = norm x *\<^sub>R ((inverse (norm y)) *\<^sub>R y)" unfolding as(3)[unfolded pi_def, THEN sym] by auto 
    from nor have y:"y = norm y *\<^sub>R ((inverse (norm x)) *\<^sub>R x)" unfolding as(3)[unfolded pi_def] by auto 
    have "0 \<le> norm y * inverse (norm x)" "0 \<le> norm x * inverse (norm y)"
      unfolding divide_inverse[THEN sym] apply(rule_tac[!] divide_nonneg_pos) using nor by auto
    hence "norm x = norm y" apply(rule_tac ccontr) unfolding neq_iff
      using x y and front_smul[THEN bspec, OF as(1), THEN spec[where x="norm y * (inverse (norm x))"]]
      using front_smul[THEN bspec, OF as(2), THEN spec[where x="norm x * (inverse (norm y))"]]
      using xys nor by(auto simp add:field_simps divide_le_eq_1 divide_inverse[THEN sym])
    thus "x = y" apply(subst injpi[THEN sym]) using as(3) by auto
  qed(insert `0 \<notin> frontier s`, auto)
  then obtain surf where surf:"\<forall>x\<in>frontier s. surf (pi x) = x"  "pi ` frontier s = sphere" "continuous_on (frontier s) pi"
    "\<forall>y\<in>sphere. pi (surf y) = y" "surf ` sphere = frontier s" "continuous_on sphere surf" unfolding homeomorphism_def by auto
  
  have cont_surfpi:"continuous_on (UNIV -  {0}) (surf \<circ> pi)" apply(rule continuous_on_compose, rule contpi)
    apply(rule continuous_on_subset[of sphere], rule surf(6)) using pi(1) by auto

  { fix x assume as:"x \<in> cball (0::real^'n) 1"
    have "norm x *\<^sub>R surf (pi x) \<in> s" proof(cases "x=0 \<or> norm x = 1") 
      case False hence "pi x \<in> sphere" "norm x < 1" using pi(1)[of x] as by(auto simp add: dist_norm)
      thus ?thesis apply(rule_tac assms(3)[rule_format, THEN DiffD1])
        apply(rule_tac fs[unfolded subset_eq, rule_format])
        unfolding surf(5)[THEN sym] by auto
    next case True thus ?thesis apply rule defer unfolding pi_def apply(rule fs[unfolded subset_eq, rule_format])
        unfolding  surf(5)[unfolded sphere_def, THEN sym] using `0\<in>s` by auto qed } note hom = this

  { fix x assume "x\<in>s"
    hence "x \<in> (\<lambda>x. norm x *\<^sub>R surf (pi x)) ` cball 0 1" proof(cases "x=0")
      case True show ?thesis unfolding image_iff True apply(rule_tac x=0 in bexI) by auto
    next let ?a = "inverse (norm (surf (pi x)))"
      case False hence invn:"inverse (norm x) \<noteq> 0" by auto
      from False have pix:"pi x\<in>sphere" using pi(1) by auto
      hence "pi (surf (pi x)) = pi x" apply(rule_tac surf(4)[rule_format]) by assumption
      hence **:"norm x *\<^sub>R (?a *\<^sub>R surf (pi x)) = x" apply(rule_tac scaleR_left_imp_eq[OF invn]) unfolding pi_def using invn by auto
      hence *:"?a * norm x > 0" and"?a > 0" "?a \<noteq> 0" using surf(5) `0\<notin>frontier s` apply -
        apply(rule_tac mult_pos_pos) using False[unfolded zero_less_norm_iff[THEN sym]] by auto
      have "norm (surf (pi x)) \<noteq> 0" using ** False by auto
      hence "norm x = norm ((?a * norm x) *\<^sub>R surf (pi x))"
        unfolding norm_scaleR abs_mult abs_norm_cancel abs_of_pos[OF `?a > 0`] by auto
      moreover have "pi x = pi ((inverse (norm (surf (pi x))) * norm x) *\<^sub>R surf (pi x))" 
        unfolding pi(2)[OF *] surf(4)[rule_format, OF pix] ..
      moreover have "surf (pi x) \<in> frontier s" using surf(5) pix by auto
      hence "dist 0 (inverse (norm (surf (pi x))) *\<^sub>R x) \<le> 1" unfolding dist_norm
        using ** and * using front_smul[THEN bspec[where x="surf (pi x)"], THEN spec[where x="norm x * ?a"]]
        using False `x\<in>s` by(auto simp add:field_simps)
      ultimately show ?thesis unfolding image_iff apply(rule_tac x="inverse (norm (surf(pi x))) *\<^sub>R x" in bexI)
        apply(subst injpi[THEN sym]) unfolding abs_mult abs_norm_cancel abs_of_pos[OF `?a > 0`]
        unfolding pi(2)[OF `?a > 0`] by auto
    qed } note hom2 = this

  show ?thesis apply(subst homeomorphic_sym) apply(rule homeomorphic_compact[where f="\<lambda>x. norm x *\<^sub>R surf (pi x)"])
    apply(rule compact_cball) defer apply(rule set_ext, rule, erule imageE, drule hom)
    prefer 4 apply(rule continuous_at_imp_continuous_on, rule) apply(rule_tac [3] hom2) proof-
    fix x::"real^'n" assume as:"x \<in> cball 0 1"
    thus "continuous (at x) (\<lambda>x. norm x *\<^sub>R surf (pi x))" proof(cases "x=0")
      case False thus ?thesis apply(rule_tac continuous_mul, rule_tac continuous_at_norm)
        using cont_surfpi unfolding continuous_on_eq_continuous_at[OF open_delete[OF open_UNIV]] o_def by auto
    next guess a using UNIV_witness[where 'a = 'n] ..
      obtain B where B:"\<forall>x\<in>s. norm x \<le> B" using compact_imp_bounded[OF assms(1)] unfolding bounded_iff by auto
      hence "B > 0" using assms(2) unfolding subset_eq apply(erule_tac x="basis a" in ballE) defer apply(erule_tac x="basis a" in ballE)
        unfolding Ball_def mem_cball dist_norm by (auto simp add: norm_basis[unfolded One_nat_def])
      case True show ?thesis unfolding True continuous_at Lim_at apply(rule,rule) apply(rule_tac x="e / B" in exI)
        apply(rule) apply(rule divide_pos_pos) prefer 3 apply(rule,rule,erule conjE)
        unfolding norm_0 scaleR_zero_left dist_norm diff_0_right norm_scaleR abs_norm_cancel proof-
        fix e and x::"real^'n" assume as:"norm x < e / B" "0 < norm x" "0<e"
        hence "surf (pi x) \<in> frontier s" using pi(1)[of x] unfolding surf(5)[THEN sym] by auto
        hence "norm (surf (pi x)) \<le> B" using B fs by auto
        hence "norm x * norm (surf (pi x)) \<le> norm x * B" using as(2) by auto
        also have "\<dots> < e / B * B" apply(rule mult_strict_right_mono) using as(1) `B>0` by auto
        also have "\<dots> = e" using `B>0` by auto
        finally show "norm x * norm (surf (pi x)) < e" by assumption
      qed(insert `B>0`, auto) qed
  next { fix x assume as:"surf (pi x) = 0"
      have "x = 0" proof(rule ccontr)
        assume "x\<noteq>0" hence "pi x \<in> sphere" using pi(1) by auto
        hence "surf (pi x) \<in> frontier s" using surf(5) by auto
        thus False using `0\<notin>frontier s` unfolding as by simp qed
    } note surf_0 = this
    show "inj_on (\<lambda>x. norm x *\<^sub>R surf (pi x)) (cball 0 1)" unfolding inj_on_def proof(rule,rule,rule)
      fix x y assume as:"x \<in> cball 0 1" "y \<in> cball 0 1" "norm x *\<^sub>R surf (pi x) = norm y *\<^sub>R surf (pi y)"
      thus "x=y" proof(cases "x=0 \<or> y=0") 
        case True thus ?thesis using as by(auto elim: surf_0) next
        case False
        hence "pi (surf (pi x)) = pi (surf (pi y))" using as(3)
          using pi(2)[of "norm x" "surf (pi x)"] pi(2)[of "norm y" "surf (pi y)"] by auto
        moreover have "pi x \<in> sphere" "pi y \<in> sphere" using pi(1) False by auto
        ultimately have *:"pi x = pi y" using surf(4)[THEN bspec[where x="pi x"]] surf(4)[THEN bspec[where x="pi y"]] by auto 
        moreover have "norm x = norm y" using as(3)[unfolded *] using False by(auto dest:surf_0)
        ultimately show ?thesis using injpi by auto qed qed
  qed auto qed

lemma homeomorphic_convex_compact_lemma: fixes s::"(real^'n) set"
  assumes "convex s" "compact s" "cball 0 1 \<subseteq> s"
  shows "s homeomorphic (cball (0::real^'n) 1)"
  apply(rule starlike_compact_projective[OF assms(2-3)]) proof(rule,rule,rule,erule conjE)
  fix x u assume as:"x \<in> s" "0 \<le> u" "u < (1::real)"
  hence "u *\<^sub>R x \<in> interior s" unfolding interior_def mem_Collect_eq
    apply(rule_tac x="ball (u *\<^sub>R x) (1 - u)" in exI) apply(rule, rule open_ball)
    unfolding centre_in_ball apply rule defer apply(rule) unfolding mem_ball proof-
    fix y assume "dist (u *\<^sub>R x) y < 1 - u"
    hence "inverse (1 - u) *\<^sub>R (y - u *\<^sub>R x) \<in> s"
      using assms(3) apply(erule_tac subsetD) unfolding mem_cball dist_commute dist_norm
      unfolding group_add_class.diff_0 group_add_class.diff_0_right norm_minus_cancel norm_scaleR
      apply (rule mult_left_le_imp_le[of "1 - u"])
      unfolding class_semiring.mul_a using `u<1` by auto
    thus "y \<in> s" using assms(1)[unfolded convex_def, rule_format, of "inverse(1 - u) *\<^sub>R (y - u *\<^sub>R x)" x "1 - u" u]
      using as unfolding scaleR_scaleR by auto qed auto
  thus "u *\<^sub>R x \<in> s - frontier s" using frontier_def and interior_subset by auto qed

lemma homeomorphic_convex_compact_cball: fixes e::real and s::"(real^'n) set"
  assumes "convex s" "compact s" "interior s \<noteq> {}" "0 < e"
  shows "s homeomorphic (cball (b::real^'n) e)"
proof- obtain a where "a\<in>interior s" using assms(3) by auto
  then obtain d where "d>0" and d:"cball a d \<subseteq> s" unfolding mem_interior_cball by auto
  let ?d = "inverse d" and ?n = "0::real^'n"
  have "cball ?n 1 \<subseteq> (\<lambda>x. inverse d *\<^sub>R (x - a)) ` s"
    apply(rule, rule_tac x="d *\<^sub>R x + a" in image_eqI) defer
    apply(rule d[unfolded subset_eq, rule_format]) using `d>0` unfolding mem_cball dist_norm
    by(auto simp add: mult_right_le_one_le)
  hence "(\<lambda>x. inverse d *\<^sub>R (x - a)) ` s homeomorphic cball ?n 1"
    using homeomorphic_convex_compact_lemma[of "(\<lambda>x. ?d *\<^sub>R -a + ?d *\<^sub>R x) ` s", OF convex_affinity compact_affinity]
    using assms(1,2) by(auto simp add: uminus_add_conv_diff scaleR_right_diff_distrib)
  thus ?thesis apply(rule_tac homeomorphic_trans[OF _ homeomorphic_balls(2)[of 1 _ ?n]])
    apply(rule homeomorphic_trans[OF homeomorphic_affinity[of "?d" s "?d *\<^sub>R -a"]])
    using `d>0` `e>0` by(auto simp add: uminus_add_conv_diff scaleR_right_diff_distrib) qed

lemma homeomorphic_convex_compact: fixes s::"(real^'n) set" and t::"(real^'n) set"
  assumes "convex s" "compact s" "interior s \<noteq> {}"
          "convex t" "compact t" "interior t \<noteq> {}"
  shows "s homeomorphic t"
  using assms by(meson zero_less_one homeomorphic_trans homeomorphic_convex_compact_cball homeomorphic_sym)

subsection {* Epigraphs of convex functions. *}

definition "epigraph s (f::real^'n \<Rightarrow> real) = {xy. fstcart xy \<in> s \<and> f(fstcart xy) \<le> dest_vec1 (sndcart xy)}"

lemma mem_epigraph: "(pastecart x (vec1 y)) \<in> epigraph s f \<longleftrightarrow> x \<in> s \<and> f x \<le> y" unfolding epigraph_def by auto

lemma convex_epigraph: 
  "convex(epigraph s f) \<longleftrightarrow> convex_on s f \<and> convex s"
  unfolding convex_def convex_on_def unfolding Ball_def forall_pastecart epigraph_def
  unfolding mem_Collect_eq fstcart_pastecart sndcart_pastecart sndcart_add sndcart_cmul [where 'a=real, unfolded smult_conv_scaleR] fstcart_add fstcart_cmul [where 'a=real, unfolded smult_conv_scaleR]
  unfolding Ball_def[symmetric] unfolding dest_vec1_add dest_vec1_cmul [where 'a=real, unfolded smult_conv_scaleR]
  apply(subst forall_dest_vec1[THEN sym])+ by(meson real_le_refl real_le_trans add_mono mult_left_mono) 

lemma convex_epigraphI: assumes "convex_on s f" "convex s"
  shows "convex(epigraph s f)" using assms unfolding convex_epigraph by auto

lemma convex_epigraph_convex: "convex s \<Longrightarrow> (convex_on s f \<longleftrightarrow> convex(epigraph s f))"
  using convex_epigraph by auto

subsection {* Use this to derive general bound property of convex function. *}

lemma forall_of_pastecart:
  "(\<forall>p. P (\<lambda>x. fstcart (p x)) (\<lambda>x. sndcart (p x))) \<longleftrightarrow> (\<forall>x y. P x y)" apply meson
  apply(erule_tac x="\<lambda>a. pastecart (x a) (y a)" in allE) unfolding o_def by auto

lemma forall_of_pastecart':
  "(\<forall>p. P (fstcart p) (sndcart p)) \<longleftrightarrow> (\<forall>x y. P x y)" apply meson
  apply(erule_tac x="pastecart x y" in allE) unfolding o_def by auto

lemma forall_of_dest_vec1: "(\<forall>v. P (\<lambda>x. dest_vec1 (v x))) \<longleftrightarrow> (\<forall>x. P x)"
  apply rule apply rule apply(erule_tac x="(vec1 \<circ> x)" in allE) unfolding o_def vec1_dest_vec1 by auto 

lemma forall_of_dest_vec1': "(\<forall>v. P (dest_vec1 v)) \<longleftrightarrow> (\<forall>x. P x)"
  apply rule apply rule apply(erule_tac x="(vec1 x)" in allE) defer apply rule 
  apply(erule_tac x="dest_vec1 v" in allE) unfolding o_def vec1_dest_vec1 by auto

lemma convex_on:
  fixes s :: "(real ^ _) set"
  assumes "convex s"
  shows "convex_on s f \<longleftrightarrow> (\<forall>k u x. (\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> x i \<in> s) \<and> setsum u {1..k} = 1 \<longrightarrow>
   f (setsum (\<lambda>i. u i *\<^sub>R x i) {1..k} ) \<le> setsum (\<lambda>i. u i * f(x i)) {1..k} ) "
  unfolding convex_epigraph_convex[OF assms] convex epigraph_def Ball_def mem_Collect_eq
  unfolding sndcart_setsum[OF finite_atLeastAtMost] fstcart_setsum[OF finite_atLeastAtMost] dest_vec1_setsum[OF finite_atLeastAtMost]
  unfolding fstcart_pastecart sndcart_pastecart sndcart_add sndcart_cmul [where 'a=real, unfolded smult_conv_scaleR] fstcart_add fstcart_cmul [where 'a=real, unfolded smult_conv_scaleR]
  unfolding dest_vec1_add dest_vec1_cmul [where 'a=real, unfolded smult_conv_scaleR] apply(subst forall_of_pastecart)+ apply(subst forall_of_dest_vec1)+ apply rule
  using assms[unfolded convex] apply simp apply(rule,rule,rule)
  apply(erule_tac x=k in allE, erule_tac x=u in allE, erule_tac x=x in allE) apply rule apply rule apply rule defer
  apply(rule_tac j="\<Sum>i = 1..k. u i * f (x i)" in real_le_trans)
  defer apply(rule setsum_mono) apply(erule conjE)+ apply(erule_tac x=i in allE)apply(rule mult_left_mono)
  using assms[unfolded convex] by auto

subsection {* Convexity of general and special intervals. *}

lemma is_interval_convex:
  fixes s :: "(real ^ _) set"
  assumes "is_interval s" shows "convex s"
  unfolding convex_def apply(rule,rule,rule,rule,rule,rule,rule) proof-
  fix x y u v assume as:"x \<in> s" "y \<in> s" "0 \<le> u" "0 \<le> v" "u + v = (1::real)"
  hence *:"u = 1 - v" "1 - v \<ge> 0" and **:"v = 1 - u" "1 - u \<ge> 0" by auto
  { fix a b assume "\<not> b \<le> u * a + v * b"
    hence "u * a < (1 - v) * b" unfolding not_le using as(4) by(auto simp add: field_simps)
    hence "a < b" unfolding * using as(4) *(2) apply(rule_tac mult_left_less_imp_less[of "1 - v"]) by(auto simp add: field_simps)
    hence "a \<le> u * a + v * b" unfolding * using as(4) by (auto simp add: field_simps intro!:mult_right_mono)
  } moreover
  { fix a b assume "\<not> u * a + v * b \<le> a"
    hence "v * b > (1 - u) * a" unfolding not_le using as(4) by(auto simp add: field_simps)
    hence "a < b" unfolding * using as(4) apply(rule_tac mult_left_less_imp_less) by(auto simp add: ring_simps)
    hence "u * a + v * b \<le> b" unfolding ** using **(2) as(3) by(auto simp add: field_simps intro!:mult_right_mono) }
  ultimately show "u *\<^sub>R x + v *\<^sub>R y \<in> s" apply- apply(rule assms[unfolded is_interval_def, rule_format, OF as(1,2)])
    using as(3-) dimindex_ge_1 apply- by(auto simp add: vector_component) qed

lemma is_interval_connected:
  fixes s :: "(real ^ _) set"
  shows "is_interval s \<Longrightarrow> connected s"
  using is_interval_convex convex_connected by auto

lemma convex_interval: "convex {a .. b}" "convex {a<..<b::real^'n}"
  apply(rule_tac[!] is_interval_convex) using is_interval_interval by auto

subsection {* On @{text "real^1"}, @{text "is_interval"}, @{text "convex"} and @{text "connected"} are all equivalent. *}

lemma is_interval_1:
  "is_interval s \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. \<forall> x. dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b \<longrightarrow> x \<in> s)"
  unfolding is_interval_def dest_vec1_def forall_1 by auto

lemma is_interval_connected_1: "is_interval s \<longleftrightarrow> connected (s::(real^1) set)"
  apply(rule, rule is_interval_connected, assumption) unfolding is_interval_1
  apply(rule,rule,rule,rule,erule conjE,rule ccontr) proof-
  fix a b x assume as:"connected s" "a \<in> s" "b \<in> s" "dest_vec1 a \<le> dest_vec1 x" "dest_vec1 x \<le> dest_vec1 b" "x\<notin>s"
  hence *:"dest_vec1 a < dest_vec1 x" "dest_vec1 x < dest_vec1 b" apply(rule_tac [!] ccontr) unfolding not_less by auto
  let ?halfl = "{z. inner (basis 1) z < dest_vec1 x} " and ?halfr = "{z. inner (basis 1) z > dest_vec1 x} "
  { fix y assume "y \<in> s" have "y \<in> ?halfr \<union> ?halfl" apply(rule ccontr)
    using as(6) `y\<in>s` by (auto simp add: inner_vector_def dest_vec1_eq [unfolded dest_vec1_def] dest_vec1_def) }
  moreover have "a\<in>?halfl" "b\<in>?halfr" using * by (auto simp add: inner_vector_def dest_vec1_def)
  hence "?halfl \<inter> s \<noteq> {}" "?halfr \<inter> s \<noteq> {}"  using as(2-3) by auto
  ultimately show False apply(rule_tac notE[OF as(1)[unfolded connected_def]])
    apply(rule_tac x="?halfl" in exI, rule_tac x="?halfr" in exI) 
    apply(rule, rule open_halfspace_lt, rule, rule open_halfspace_gt) apply(rule, rule, rule ccontr)
    by(auto simp add: basis_component field_simps) qed 

lemma is_interval_convex_1:
  "is_interval s \<longleftrightarrow> convex (s::(real^1) set)" 
  using is_interval_convex convex_connected is_interval_connected_1 by auto

lemma convex_connected_1:
  "connected s \<longleftrightarrow> convex (s::(real^1) set)" 
  using is_interval_convex convex_connected is_interval_connected_1 by auto

subsection {* Another intermediate value theorem formulation. *}

lemma ivt_increasing_component_on_1: fixes f::"real^1 \<Rightarrow> real^'n"
  assumes "dest_vec1 a \<le> dest_vec1 b" "continuous_on {a .. b} f" "(f a)$k \<le> y" "y \<le> (f b)$k"
  shows "\<exists>x\<in>{a..b}. (f x)$k = y"
proof- have "f a \<in> f ` {a..b}" "f b \<in> f ` {a..b}" apply(rule_tac[!] imageI) 
    using assms(1) by(auto simp add: vector_le_def dest_vec1_def)
  thus ?thesis using connected_ivt_component[of "f ` {a..b}" "f a" "f b" k y]
    using connected_continuous_image[OF assms(2) convex_connected[OF convex_interval(1)]]
    using assms by(auto intro!: imageI) qed

lemma ivt_increasing_component_1: fixes f::"real^1 \<Rightarrow> real^'n"
  assumes "dest_vec1 a \<le> dest_vec1 b"
  "\<forall>x\<in>{a .. b}. continuous (at x) f" "f a$k \<le> y" "y \<le> f b$k"
  shows "\<exists>x\<in>{a..b}. (f x)$k = y"
  apply(rule ivt_increasing_component_on_1) using assms using continuous_at_imp_continuous_on by auto

lemma ivt_decreasing_component_on_1: fixes f::"real^1 \<Rightarrow> real^'n"
  assumes "dest_vec1 a \<le> dest_vec1 b" "continuous_on {a .. b} f" "(f b)$k \<le> y" "y \<le> (f a)$k"
  shows "\<exists>x\<in>{a..b}. (f x)$k = y"
  apply(subst neg_equal_iff_equal[THEN sym]) unfolding vector_uminus_component[THEN sym]
  apply(rule ivt_increasing_component_on_1) using assms using continuous_on_neg
  by(auto simp add:vector_uminus_component)

lemma ivt_decreasing_component_1: fixes f::"real^1 \<Rightarrow> real^'n"
  assumes "dest_vec1 a \<le> dest_vec1 b" "\<forall>x\<in>{a .. b}. continuous (at x) f" "f b$k \<le> y" "y \<le> f a$k"
  shows "\<exists>x\<in>{a..b}. (f x)$k = y"
  apply(rule ivt_decreasing_component_on_1) using assms using continuous_at_imp_continuous_on by auto

subsection {* A bound within a convex hull, and so an interval. *}

lemma convex_on_convex_hull_bound:
  fixes s :: "(real ^ _) set"
  assumes "convex_on (convex hull s) f" "\<forall>x\<in>s. f x \<le> b"
  shows "\<forall>x\<in> convex hull s. f x \<le> b" proof
  fix x assume "x\<in>convex hull s"
  then obtain k u v where obt:"\<forall>i\<in>{1..k::nat}. 0 \<le> u i \<and> v i \<in> s" "setsum u {1..k} = 1" "(\<Sum>i = 1..k. u i *\<^sub>R v i) = x"
    unfolding convex_hull_indexed mem_Collect_eq by auto
  have "(\<Sum>i = 1..k. u i * f (v i)) \<le> b" using setsum_mono[of "{1..k}" "\<lambda>i. u i * f (v i)" "\<lambda>i. u i * b"]
    unfolding setsum_left_distrib[THEN sym] obt(2) mult_1 apply(drule_tac meta_mp) apply(rule mult_left_mono)
    using assms(2) obt(1) by auto
  thus "f x \<le> b" using assms(1)[unfolded convex_on[OF convex_convex_hull], rule_format, of k u v]
    unfolding obt(2-3) using obt(1) and hull_subset[unfolded subset_eq, rule_format, of _ s] by auto qed

lemma unit_interval_convex_hull:
  "{0::real^'n .. 1} = convex hull {x. \<forall>i. (x$i = 0) \<or> (x$i = 1)}" (is "?int = convex hull ?points")
proof- have 01:"{0,1} \<subseteq> convex hull ?points" apply rule apply(rule_tac hull_subset[unfolded subset_eq, rule_format]) by auto
  { fix n x assume "x\<in>{0::real^'n .. 1}" "n \<le> CARD('n)" "card {i. x$i \<noteq> 0} \<le> n" 
  hence "x\<in>convex hull ?points" proof(induct n arbitrary: x)
    case 0 hence "x = 0" apply(subst Cart_eq) apply rule by auto
    thus "x\<in>convex hull ?points" using 01 by auto
  next
    case (Suc n) show "x\<in>convex hull ?points" proof(cases "{i. x$i \<noteq> 0} = {}")
      case True hence "x = 0" unfolding Cart_eq by auto
      thus "x\<in>convex hull ?points" using 01 by auto
    next
      case False def xi \<equiv> "Min ((\<lambda>i. x$i) ` {i. x$i \<noteq> 0})"
      have "xi \<in> (\<lambda>i. x$i) ` {i. x$i \<noteq> 0}" unfolding xi_def apply(rule Min_in) using False by auto
      then obtain i where i':"x$i = xi" "x$i \<noteq> 0" by auto
      have i:"\<And>j. x$j > 0 \<Longrightarrow> x$i \<le> x$j"
        unfolding i'(1) xi_def apply(rule_tac Min_le) unfolding image_iff
        defer apply(rule_tac x=j in bexI) using i' by auto
      have i01:"x$i \<le> 1" "x$i > 0" using Suc(2)[unfolded mem_interval,rule_format,of i] using i'(2) `x$i \<noteq> 0`
        by(auto simp add: Cart_lambda_beta) 
      show ?thesis proof(cases "x$i=1")
        case True have "\<forall>j\<in>{i. x$i \<noteq> 0}. x$j = 1" apply(rule, rule ccontr) unfolding mem_Collect_eq proof-
          fix j assume "x $ j \<noteq> 0" "x $ j \<noteq> 1"
          hence j:"x$j \<in> {0<..<1}" using Suc(2) by(auto simp add: vector_le_def elim!:allE[where x=j])
          hence "x$j \<in> op $ x ` {i. x $ i \<noteq> 0}" by auto 
          hence "x$j \<ge> x$i" unfolding i'(1) xi_def apply(rule_tac Min_le) by auto
          thus False using True Suc(2) j by(auto simp add: vector_le_def elim!:ballE[where x=j]) qed
        thus "x\<in>convex hull ?points" apply(rule_tac hull_subset[unfolded subset_eq, rule_format])
          by(auto simp add: Cart_lambda_beta)
      next let ?y = "\<lambda>j. if x$j = 0 then 0 else (x$j - x$i) / (1 - x$i)"
        case False hence *:"x = x$i *\<^sub>R (\<chi> j. if x$j = 0 then 0 else 1) + (1 - x$i) *\<^sub>R (\<chi> j. ?y j)" unfolding Cart_eq
          by(auto simp add: Cart_lambda_beta vector_add_component vector_smult_component vector_minus_component field_simps)
        { fix j have "x$j \<noteq> 0 \<Longrightarrow> 0 \<le> (x $ j - x $ i) / (1 - x $ i)" "(x $ j - x $ i) / (1 - x $ i) \<le> 1"
            apply(rule_tac divide_nonneg_pos) using i(1)[of j] using False i01
            using Suc(2)[unfolded mem_interval, rule_format, of j] by(auto simp add:field_simps Cart_lambda_beta) 
          hence "0 \<le> ?y j \<and> ?y j \<le> 1" by auto }
        moreover have "i\<in>{j. x$j \<noteq> 0} - {j. ((\<chi> j. ?y j)::real^'n) $ j \<noteq> 0}" using i01 by(auto simp add: Cart_lambda_beta)
        hence "{j. x$j \<noteq> 0} \<noteq> {j. ((\<chi> j. ?y j)::real^'n) $ j \<noteq> 0}" by auto
        hence **:"{j. ((\<chi> j. ?y j)::real^'n) $ j \<noteq> 0} \<subset> {j. x$j \<noteq> 0}" apply - apply rule by(auto simp add: Cart_lambda_beta)  
        have "card {j. ((\<chi> j. ?y j)::real^'n) $ j \<noteq> 0} \<le> n" using less_le_trans[OF psubset_card_mono[OF _ **] Suc(4)] by auto
        ultimately show ?thesis apply(subst *) apply(rule convex_convex_hull[unfolded convex_def, rule_format])
          apply(rule_tac hull_subset[unfolded subset_eq, rule_format]) defer apply(rule Suc(1))
          unfolding mem_interval using i01 Suc(3) by (auto simp add: Cart_lambda_beta)
      qed qed qed } note * = this
  show ?thesis apply rule defer apply(rule hull_minimal) unfolding subset_eq prefer 3 apply rule 
    apply(rule_tac n2="CARD('n)" in *) prefer 3 apply(rule card_mono) using 01 and convex_interval(1) prefer 5 apply - apply rule
    unfolding mem_interval apply rule unfolding mem_Collect_eq apply(erule_tac x=i in allE)
    by(auto simp add: vector_le_def mem_def[of _ convex]) qed

subsection {* And this is a finite set of vertices. *}

lemma unit_cube_convex_hull: obtains s where "finite s" "{0 .. 1::real^'n} = convex hull s"
  apply(rule that[of "{x::real^'n. \<forall>i. x$i=0 \<or> x$i=1}"])
  apply(rule finite_subset[of _ "(\<lambda>s. (\<chi> i. if i\<in>s then 1::real else 0)::real^'n) ` UNIV"])
  prefer 3 apply(rule unit_interval_convex_hull) apply rule unfolding mem_Collect_eq proof-
  fix x::"real^'n" assume as:"\<forall>i. x $ i = 0 \<or> x $ i = 1"
  show "x \<in> (\<lambda>s. \<chi> i. if i \<in> s then 1 else 0) ` UNIV" apply(rule image_eqI[where x="{i. x$i = 1}"])
    unfolding Cart_eq using as by(auto simp add:Cart_lambda_beta) qed auto

subsection {* Hence any cube (could do any nonempty interval). *}

lemma cube_convex_hull:
  assumes "0 < d" obtains s::"(real^'n) set" where "finite s" "{x - (\<chi> i. d) .. x + (\<chi> i. d)} = convex hull s" proof-
  let ?d = "(\<chi> i. d)::real^'n"
  have *:"{x - ?d .. x + ?d} = (\<lambda>y. x - ?d + (2 * d) *\<^sub>R y) ` {0 .. 1}" apply(rule set_ext, rule)
    unfolding image_iff defer apply(erule bexE) proof-
    fix y assume as:"y\<in>{x - ?d .. x + ?d}"
    { fix i::'n have "x $ i \<le> d + y $ i" "y $ i \<le> d + x $ i" using as[unfolded mem_interval, THEN spec[where x=i]]
        by(auto simp add: vector_component)
      hence "1 \<ge> inverse d * (x $ i - y $ i)" "1 \<ge> inverse d * (y $ i - x $ i)"
        apply(rule_tac[!] mult_left_le_imp_le[OF _ assms]) unfolding mult_assoc[THEN sym]
        using assms by(auto simp add: field_simps right_inverse) 
      hence "inverse d * (x $ i * 2) \<le> 2 + inverse d * (y $ i * 2)"
            "inverse d * (y $ i * 2) \<le> 2 + inverse d * (x $ i * 2)" by(auto simp add:field_simps) }
    hence "inverse (2 * d) *\<^sub>R (y - (x - ?d)) \<in> {0..1}" unfolding mem_interval using assms
      by(auto simp add: Cart_eq vector_component_simps field_simps)
    thus "\<exists>z\<in>{0..1}. y = x - ?d + (2 * d) *\<^sub>R z" apply- apply(rule_tac x="inverse (2 * d) *\<^sub>R (y - (x - ?d))" in bexI) 
      using assms by(auto simp add: Cart_eq vector_le_def Cart_lambda_beta)
  next
    fix y z assume as:"z\<in>{0..1}" "y = x - ?d + (2*d) *\<^sub>R z" 
    have "\<And>i. 0 \<le> d * z $ i \<and> d * z $ i \<le> d" using assms as(1)[unfolded mem_interval] apply(erule_tac x=i in allE)
      apply rule apply(rule mult_nonneg_nonneg) prefer 3 apply(rule mult_right_le_one_le)
      using assms by(auto simp add: vector_component_simps Cart_eq)
    thus "y \<in> {x - ?d..x + ?d}" unfolding as(2) mem_interval apply- apply rule using as(1)[unfolded mem_interval]
      apply(erule_tac x=i in allE) using assms by(auto simp add:  vector_component_simps Cart_eq) qed
  obtain s where "finite s" "{0..1::real^'n} = convex hull s" using unit_cube_convex_hull by auto
  thus ?thesis apply(rule_tac that[of "(\<lambda>y. x - ?d + (2 * d) *\<^sub>R y)` s"]) unfolding * and convex_hull_affinity by auto qed

subsection {* Bounded convex function on open set is continuous. *}

lemma convex_on_bounded_continuous:
  fixes s :: "(real ^ _) set"
  assumes "open s" "convex_on s f" "\<forall>x\<in>s. abs(f x) \<le> b"
  shows "continuous_on s f"
  apply(rule continuous_at_imp_continuous_on) unfolding continuous_at_real_range proof(rule,rule,rule)
  fix x e assume "x\<in>s" "(0::real) < e"
  def B \<equiv> "abs b + 1"
  have B:"0 < B" "\<And>x. x\<in>s \<Longrightarrow> abs (f x) \<le> B"
    unfolding B_def defer apply(drule assms(3)[rule_format]) by auto
  obtain k where "k>0"and k:"cball x k \<subseteq> s" using assms(1)[unfolded open_contains_cball, THEN bspec[where x=x]] using `x\<in>s` by auto
  show "\<exists>d>0. \<forall>x'. norm (x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e"
    apply(rule_tac x="min (k / 2) (e / (2 * B) * k)" in exI) apply rule defer proof(rule,rule)
    fix y assume as:"norm (y - x) < min (k / 2) (e / (2 * B) * k)" 
    show "\<bar>f y - f x\<bar> < e" proof(cases "y=x")
      case False def t \<equiv> "k / norm (y - x)"
      have "2 < t" "0<t" unfolding t_def using as False and `k>0` by(auto simp add:field_simps)
      have "y\<in>s" apply(rule k[unfolded subset_eq,rule_format]) unfolding mem_cball dist_norm
        apply(rule order_trans[of _ "2 * norm (x - y)"]) using as by(auto simp add: field_simps norm_minus_commute) 
      { def w \<equiv> "x + t *\<^sub>R (y - x)"
        have "w\<in>s" unfolding w_def apply(rule k[unfolded subset_eq,rule_format]) unfolding mem_cball dist_norm 
          unfolding t_def using `k>0` by auto
        have "(1 / t) *\<^sub>R x + - x + ((t - 1) / t) *\<^sub>R x = (1 / t - 1 + (t - 1) / t) *\<^sub>R x" by (auto simp add: algebra_simps)
        also have "\<dots> = 0"  using `t>0` by(auto simp add:field_simps)
        finally have w:"(1 / t) *\<^sub>R w + ((t - 1) / t) *\<^sub>R x = y" unfolding w_def using False and `t>0` by (auto simp add: algebra_simps)
        have  "2 * B < e * t" unfolding t_def using `0<e` `0<k` `B>0` and as and False by (auto simp add:field_simps) 
        hence "(f w - f x) / t < e"
          using B(2)[OF `w\<in>s`] and B(2)[OF `x\<in>s`] using `t>0` by(auto simp add:field_simps) 
        hence th1:"f y - f x < e" apply- apply(rule le_less_trans) defer apply assumption
          using assms(2)[unfolded convex_on_def,rule_format,of w x "1/t" "(t - 1)/t", unfolded w]
          using `0<t` `2<t` and `x\<in>s` `w\<in>s` by(auto simp add:field_simps) }
      moreover 
      { def w \<equiv> "x - t *\<^sub>R (y - x)"
        have "w\<in>s" unfolding w_def apply(rule k[unfolded subset_eq,rule_format]) unfolding mem_cball dist_norm 
          unfolding t_def using `k>0` by auto
        have "(1 / (1 + t)) *\<^sub>R x + (t / (1 + t)) *\<^sub>R x = (1 / (1 + t) + t / (1 + t)) *\<^sub>R x" by (auto simp add: algebra_simps)
        also have "\<dots>=x" using `t>0` by (auto simp add:field_simps)
        finally have w:"(1 / (1+t)) *\<^sub>R w + (t / (1 + t)) *\<^sub>R y = x" unfolding w_def using False and `t>0` by (auto simp add: algebra_simps)
        have  "2 * B < e * t" unfolding t_def using `0<e` `0<k` `B>0` and as and False by (auto simp add:field_simps) 
        hence *:"(f w - f y) / t < e" using B(2)[OF `w\<in>s`] and B(2)[OF `y\<in>s`] using `t>0` by(auto simp add:field_simps) 
        have "f x \<le> 1 / (1 + t) * f w + (t / (1 + t)) * f y" 
          using assms(2)[unfolded convex_on_def,rule_format,of w y "1/(1+t)" "t / (1+t)",unfolded w]
          using `0<t` `2<t` and `y\<in>s` `w\<in>s` by (auto simp add:field_simps)
        also have "\<dots> = (f w + t * f y) / (1 + t)" using `t>0` unfolding real_divide_def by (auto simp add:field_simps)
        also have "\<dots> < e + f y" using `t>0` * `e>0` by(auto simp add:field_simps)
        finally have "f x - f y < e" by auto }
      ultimately show ?thesis by auto 
    qed(insert `0<e`, auto) 
  qed(insert `0<e` `0<k` `0<B`, auto simp add:field_simps intro!:mult_pos_pos) qed

subsection {* Upper bound on a ball implies upper and lower bounds. *}

lemma convex_bounds_lemma:
  fixes x :: "real ^ _"
  assumes "convex_on (cball x e) f"  "\<forall>y \<in> cball x e. f y \<le> b"
  shows "\<forall>y \<in> cball x e. abs(f y) \<le> b + 2 * abs(f x)"
  apply(rule) proof(cases "0 \<le> e") case True
  fix y assume y:"y\<in>cball x e" def z \<equiv> "2 *\<^sub>R x - y"
  have *:"x - (2 *\<^sub>R x - y) = y - x" by vector
  have z:"z\<in>cball x e" using y unfolding z_def mem_cball dist_norm * by(auto simp add: norm_minus_commute)
  have "(1 / 2) *\<^sub>R y + (1 / 2) *\<^sub>R z = x" unfolding z_def by (auto simp add: algebra_simps)
  thus "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>" using assms(1)[unfolded convex_on_def,rule_format, OF y z, of "1/2" "1/2"]
    using assms(2)[rule_format,OF y] assms(2)[rule_format,OF z] by(auto simp add:field_simps)
next case False fix y assume "y\<in>cball x e" 
  hence "dist x y < 0" using False unfolding mem_cball not_le by (auto simp del: dist_not_less_zero)
  thus "\<bar>f y\<bar> \<le> b + 2 * \<bar>f x\<bar>" using zero_le_dist[of x y] by auto qed

subsection {* Hence a convex function on an open set is continuous. *}

lemma convex_on_continuous:
  assumes "open (s::(real^'n) set)" "convex_on s f" 
  shows "continuous_on s f"
  unfolding continuous_on_eq_continuous_at[OF assms(1)] proof
  note dimge1 = dimindex_ge_1[where 'a='n]
  fix x assume "x\<in>s"
  then obtain e where e:"cball x e \<subseteq> s" "e>0" using assms(1) unfolding open_contains_cball by auto
  def d \<equiv> "e / real CARD('n)"
  have "0 < d" unfolding d_def using `e>0` dimge1 by(rule_tac divide_pos_pos, auto) 
  let ?d = "(\<chi> i. d)::real^'n"
  obtain c where c:"finite c" "{x - ?d..x + ?d} = convex hull c" using cube_convex_hull[OF `d>0`, of x] by auto
  have "x\<in>{x - ?d..x + ?d}" using `d>0` unfolding mem_interval by(auto simp add:vector_component_simps)
  hence "c\<noteq>{}" apply(rule_tac ccontr) using c by(auto simp add:convex_hull_empty)
  def k \<equiv> "Max (f ` c)"
  have "convex_on {x - ?d..x + ?d} f" apply(rule convex_on_subset[OF assms(2)])
    apply(rule subset_trans[OF _ e(1)]) unfolding subset_eq mem_cball proof 
    fix z assume z:"z\<in>{x - ?d..x + ?d}"
    have e:"e = setsum (\<lambda>i. d) (UNIV::'n set)" unfolding setsum_constant d_def using dimge1
      by (metis card_enum field_simps d_def not_one_le_zero of_nat_le_iff real_eq_of_nat real_of_nat_1)
    show "dist x z \<le> e" unfolding dist_norm e apply(rule_tac order_trans[OF norm_le_l1], rule setsum_mono)
      using z[unfolded mem_interval] apply(erule_tac x=i in allE) by(auto simp add:field_simps vector_component_simps) qed
  hence k:"\<forall>y\<in>{x - ?d..x + ?d}. f y \<le> k" unfolding c(2) apply(rule_tac convex_on_convex_hull_bound) apply assumption
    unfolding k_def apply(rule, rule Max_ge) using c(1) by auto
  have "d \<le> e" unfolding d_def apply(rule mult_imp_div_pos_le) using `e>0` dimge1 unfolding mult_le_cancel_left1 using real_dimindex_ge_1 by auto
  hence dsube:"cball x d \<subseteq> cball x e" unfolding subset_eq Ball_def mem_cball by auto
  have conv:"convex_on (cball x d) f" apply(rule convex_on_subset, rule convex_on_subset[OF assms(2)]) apply(rule e(1)) using dsube by auto
  hence "\<forall>y\<in>cball x d. abs (f y) \<le> k + 2 * abs (f x)" apply(rule_tac convex_bounds_lemma) apply assumption proof
    fix y assume y:"y\<in>cball x d"
    { fix i::'n have "x $ i - d \<le> y $ i"  "y $ i \<le> x $ i + d" 
        using order_trans[OF component_le_norm y[unfolded mem_cball dist_norm], of i] by(auto simp add: vector_component)  }
    thus "f y \<le> k" apply(rule_tac k[rule_format]) unfolding mem_cball mem_interval dist_norm 
      by(auto simp add: vector_component_simps) qed
  hence "continuous_on (ball x d) f" apply(rule_tac convex_on_bounded_continuous)
    apply(rule open_ball, rule convex_on_subset[OF conv], rule ball_subset_cball)
    apply force
    done
  thus "continuous (at x) f" unfolding continuous_on_eq_continuous_at[OF open_ball]
    using `d>0` by auto 
qed

subsection {* Line segments, Starlike Sets, etc.*}

(* Use the same overloading tricks as for intervals, so that 
   segment[a,b] is closed and segment(a,b) is open relative to affine hull. *)

definition
  midpoint :: "real ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow> real ^ 'n" where
  "midpoint a b = (inverse (2::real)) *\<^sub>R (a + b)"

definition
  open_segment :: "real ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow> (real ^ 'n) set" where
  "open_segment a b = {(1 - u) *\<^sub>R a + u *\<^sub>R b | u::real.  0 < u \<and> u < 1}"

definition
  closed_segment :: "real ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow> (real ^ 'n) set" where
  "closed_segment a b = {(1 - u) *\<^sub>R a + u *\<^sub>R b | u::real. 0 \<le> u \<and> u \<le> 1}"

definition "between = (\<lambda> (a,b). closed_segment a b)"

lemmas segment = open_segment_def closed_segment_def

definition "starlike s \<longleftrightarrow> (\<exists>a\<in>s. \<forall>x\<in>s. closed_segment a x \<subseteq> s)"

lemma midpoint_refl: "midpoint x x = x"
  unfolding midpoint_def unfolding scaleR_right_distrib unfolding scaleR_left_distrib[THEN sym] by auto

lemma midpoint_sym: "midpoint a b = midpoint b a" unfolding midpoint_def by (auto simp add: scaleR_right_distrib)

lemma dist_midpoint:
  "dist a (midpoint a b) = (dist a b) / 2" (is ?t1)
  "dist b (midpoint a b) = (dist a b) / 2" (is ?t2)
  "dist (midpoint a b) a = (dist a b) / 2" (is ?t3)
  "dist (midpoint a b) b = (dist a b) / 2" (is ?t4)
proof-
  have *: "\<And>x y::real^'n. 2 *\<^sub>R x = - y \<Longrightarrow> norm x = (norm y) / 2" unfolding equation_minus_iff by auto
  have **:"\<And>x y::real^'n. 2 *\<^sub>R x =   y \<Longrightarrow> norm x = (norm y) / 2" by auto
  note scaleR_right_distrib [simp]
  show ?t1 unfolding midpoint_def dist_norm apply (rule **) by(auto,vector)
  show ?t2 unfolding midpoint_def dist_norm apply (rule *)  by(auto,vector)
  show ?t3 unfolding midpoint_def dist_norm apply (rule *)  by(auto,vector)
  show ?t4 unfolding midpoint_def dist_norm apply (rule **) by(auto,vector) qed

lemma midpoint_eq_endpoint:
  "midpoint a b = a \<longleftrightarrow> a = (b::real^'n)"
  "midpoint a b = b \<longleftrightarrow> a = b"
  unfolding dist_eq_0_iff[where 'a="real^'n", THEN sym] dist_midpoint by auto

lemma convex_contains_segment:
  "convex s \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. closed_segment a b \<subseteq> s)"
  unfolding convex_alt closed_segment_def by auto

lemma convex_imp_starlike:
  "convex s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> starlike s"
  unfolding convex_contains_segment starlike_def by auto

lemma segment_convex_hull:
 "closed_segment a b = convex hull {a,b}" proof-
  have *:"\<And>x. {x} \<noteq> {}" by auto
  have **:"\<And>u v. u + v = 1 \<longleftrightarrow> u = 1 - (v::real)" by auto
  show ?thesis unfolding segment convex_hull_insert[OF *] convex_hull_singleton apply(rule set_ext)
    unfolding mem_Collect_eq apply(rule,erule exE) 
    apply(rule_tac x="1 - u" in exI) apply rule defer apply(rule_tac x=u in exI) defer
    apply(erule exE, (erule conjE)?)+ apply(rule_tac x="1 - u" in exI) unfolding ** by auto qed

lemma convex_segment: "convex (closed_segment a b)"
  unfolding segment_convex_hull by(rule convex_convex_hull)

lemma ends_in_segment: "a \<in> closed_segment a b" "b \<in> closed_segment a b"
  unfolding segment_convex_hull apply(rule_tac[!] hull_subset[unfolded subset_eq, rule_format]) by auto

lemma segment_furthest_le:
  assumes "x \<in> closed_segment a b" shows "norm(y - x) \<le> norm(y - a) \<or>  norm(y - x) \<le> norm(y - b)" proof-
  obtain z where "z\<in>{a, b}" "norm (x - y) \<le> norm (z - y)" using simplex_furthest_le[of "{a, b}" y]
    using assms[unfolded segment_convex_hull] by auto
  thus ?thesis by(auto simp add:norm_minus_commute) qed

lemma segment_bound:
  assumes "x \<in> closed_segment a b"
  shows "norm(x - a) \<le> norm(b - a)" "norm(x - b) \<le> norm(b - a)"
  using segment_furthest_le[OF assms, of a]
  using segment_furthest_le[OF assms, of b]
  by (auto simp add:norm_minus_commute) 

lemma segment_refl:"closed_segment a a = {a}" unfolding segment by (auto simp add: algebra_simps)

lemma between_mem_segment: "between (a,b) x \<longleftrightarrow> x \<in> closed_segment a b"
  unfolding between_def mem_def by auto

lemma between:"between (a,b) (x::real^'n) \<longleftrightarrow> dist a b = (dist a x) + (dist x b)"
proof(cases "a = b")
  case True thus ?thesis unfolding between_def split_conv mem_def[of x, symmetric]
    by(auto simp add:segment_refl dist_commute) next
  case False hence Fal:"norm (a - b) \<noteq> 0" and Fal2: "norm (a - b) > 0" by auto 
  have *:"\<And>u. a - ((1 - u) *\<^sub>R a + u *\<^sub>R b) = u *\<^sub>R (a - b)" by (auto simp add: algebra_simps)
  show ?thesis unfolding between_def split_conv mem_def[of x, symmetric] closed_segment_def mem_Collect_eq
    apply rule apply(erule exE, (erule conjE)+) apply(subst dist_triangle_eq) proof-
      fix u assume as:"x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1" 
      hence *:"a - x = u *\<^sub>R (a - b)" "x - b = (1 - u) *\<^sub>R (a - b)"
        unfolding as(1) by(auto simp add:algebra_simps)
      show "norm (a - x) *\<^sub>R (x - b) = norm (x - b) *\<^sub>R (a - x)"
        unfolding norm_minus_commute[of x a] * Cart_eq using as(2,3)
        by(auto simp add: vector_component_simps field_simps)
    next assume as:"dist a b = dist a x + dist x b"
      have "norm (a - x) / norm (a - b) \<le> 1" unfolding divide_le_eq_1_pos[OF Fal2] unfolding as[unfolded dist_norm] norm_ge_zero by auto 
      thus "\<exists>u. x = (1 - u) *\<^sub>R a + u *\<^sub>R b \<and> 0 \<le> u \<and> u \<le> 1" apply(rule_tac x="dist a x / dist a b" in exI)
        unfolding dist_norm Cart_eq apply- apply rule defer apply(rule, rule divide_nonneg_pos) prefer 4 proof rule
          fix i::'n have "((1 - norm (a - x) / norm (a - b)) *\<^sub>R a + (norm (a - x) / norm (a - b)) *\<^sub>R b) $ i =
            ((norm (a - b) - norm (a - x)) * (a $ i) + norm (a - x) * (b $ i)) / norm (a - b)"
            using Fal by(auto simp add:vector_component_simps field_simps)
          also have "\<dots> = x$i" apply(rule divide_eq_imp[OF Fal])
            unfolding as[unfolded dist_norm] using as[unfolded dist_triangle_eq Cart_eq,rule_format, of i]
            by(auto simp add:field_simps vector_component_simps)
          finally show "x $ i = ((1 - norm (a - x) / norm (a - b)) *\<^sub>R a + (norm (a - x) / norm (a - b)) *\<^sub>R b) $ i" by auto
        qed(insert Fal2, auto) qed qed

lemma between_midpoint: fixes a::"real^'n" shows
  "between (a,b) (midpoint a b)" (is ?t1) 
  "between (b,a) (midpoint a b)" (is ?t2)
proof- have *:"\<And>x y z. x = (1/2::real) *\<^sub>R z \<Longrightarrow> y = (1/2) *\<^sub>R z \<Longrightarrow> norm z = norm x + norm y" by auto
  show ?t1 ?t2 unfolding between midpoint_def dist_norm apply(rule_tac[!] *)
    by(auto simp add:field_simps Cart_eq vector_component_simps) qed

lemma between_mem_convex_hull:
  "between (a,b) x \<longleftrightarrow> x \<in> convex hull {a,b}"
  unfolding between_mem_segment segment_convex_hull ..

subsection {* Shrinking towards the interior of a convex set. *}

lemma mem_interior_convex_shrink:
  fixes s :: "(real ^ _) set"
  assumes "convex s" "c \<in> interior s" "x \<in> s" "0 < e" "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> interior s"
proof- obtain d where "d>0" and d:"ball c d \<subseteq> s" using assms(2) unfolding mem_interior by auto
  show ?thesis unfolding mem_interior apply(rule_tac x="e*d" in exI)
    apply(rule) defer unfolding subset_eq Ball_def mem_ball proof(rule,rule)
    fix y assume as:"dist (x - e *\<^sub>R (x - c)) y < e * d"
    have *:"y = (1 - (1 - e)) *\<^sub>R ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) + (1 - e) *\<^sub>R x" using `e>0` by (auto simp add: scaleR_left_diff_distrib scaleR_right_diff_distrib)
    have "dist c ((1 / e) *\<^sub>R y - ((1 - e) / e) *\<^sub>R x) = abs(1/e) * norm (e *\<^sub>R c - y + (1 - e) *\<^sub>R x)"
      unfolding dist_norm unfolding norm_scaleR[THEN sym] apply(rule norm_eqI) using `e>0`
      by(auto simp add:vector_component_simps Cart_eq field_simps) 
    also have "\<dots> = abs(1/e) * norm (x - e *\<^sub>R (x - c) - y)" by(auto intro!:norm_eqI simp add: algebra_simps)
    also have "\<dots> < d" using as[unfolded dist_norm] and `e>0`
      by(auto simp add:pos_divide_less_eq[OF `e>0`] real_mult_commute)
    finally show "y \<in> s" apply(subst *) apply(rule assms(1)[unfolded convex_alt,rule_format])
      apply(rule d[unfolded subset_eq,rule_format]) unfolding mem_ball using assms(3-5) by auto
  qed(rule mult_pos_pos, insert `e>0` `d>0`, auto) qed

lemma mem_interior_closure_convex_shrink:
  fixes s :: "(real ^ _) set"
  assumes "convex s" "c \<in> interior s" "x \<in> closure s" "0 < e" "e \<le> 1"
  shows "x - e *\<^sub>R (x - c) \<in> interior s"
proof- obtain d where "d>0" and d:"ball c d \<subseteq> s" using assms(2) unfolding mem_interior by auto
  have "\<exists>y\<in>s. norm (y - x) * (1 - e) < e * d" proof(cases "x\<in>s")
    case True thus ?thesis using `e>0` `d>0` by(rule_tac bexI[where x=x], auto intro!: mult_pos_pos) next
    case False hence x:"x islimpt s" using assms(3)[unfolded closure_def] by auto
    show ?thesis proof(cases "e=1")
      case True obtain y where "y\<in>s" "y \<noteq> x" "dist y x < 1"
        using x[unfolded islimpt_approachable,THEN spec[where x=1]] by auto
      thus ?thesis apply(rule_tac x=y in bexI) unfolding True using `d>0` by auto next
      case False hence "0 < e * d / (1 - e)" and *:"1 - e > 0"
        using `e\<le>1` `e>0` `d>0` by(auto intro!:mult_pos_pos divide_pos_pos)
      then obtain y where "y\<in>s" "y \<noteq> x" "dist y x < e * d / (1 - e)"
        using x[unfolded islimpt_approachable,THEN spec[where x="e*d / (1 - e)"]] by auto
      thus ?thesis apply(rule_tac x=y in bexI) unfolding dist_norm using pos_less_divide_eq[OF *] by auto qed qed
  then obtain y where "y\<in>s" and y:"norm (y - x) * (1 - e) < e * d" by auto
  def z \<equiv> "c + ((1 - e) / e) *\<^sub>R (x - y)"
  have *:"x - e *\<^sub>R (x - c) = y - e *\<^sub>R (y - z)" unfolding z_def using `e>0` by (auto simp add: scaleR_right_diff_distrib scaleR_right_distrib scaleR_left_diff_distrib)
  have "z\<in>interior s" apply(rule subset_interior[OF d,unfolded subset_eq,rule_format])
    unfolding interior_open[OF open_ball] mem_ball z_def dist_norm using y and assms(4,5)
    by(auto simp add:field_simps norm_minus_commute)
  thus ?thesis unfolding * apply - apply(rule mem_interior_convex_shrink) 
    using assms(1,4-5) `y\<in>s` by auto qed

subsection {* Some obvious but surprisingly hard simplex lemmas. *}

lemma simplex:
  assumes "finite s" "0 \<notin> s"
  shows "convex hull (insert 0 s) =  { y. (\<exists>u. (\<forall>x\<in>s. 0 \<le> u x) \<and> setsum u s \<le> 1 \<and> setsum (\<lambda>x. u x *\<^sub>R x) s = y)}"
  unfolding convex_hull_finite[OF finite.insertI[OF assms(1)]] apply(rule set_ext, rule) unfolding mem_Collect_eq
  apply(erule_tac[!] exE) apply(erule_tac[!] conjE)+ unfolding setsum_clauses(2)[OF assms(1)]
  apply(rule_tac x=u in exI) defer apply(rule_tac x="\<lambda>x. if x = 0 then 1 - setsum u s else u x" in exI) using assms(2)
  unfolding if_smult and setsum_delta_notmem[OF assms(2)] by auto

lemma std_simplex:
  "convex hull (insert 0 { basis i | i. i\<in>UNIV}) =
        {x::real^'n . (\<forall>i. 0 \<le> x$i) \<and> setsum (\<lambda>i. x$i) UNIV \<le> 1 }" (is "convex hull (insert 0 ?p) = ?s")
proof- let ?D = "UNIV::'n set"
  have "0\<notin>?p" by(auto simp add: basis_nonzero)
  have "{(basis i)::real^'n |i. i \<in> ?D} = basis ` ?D" by auto
  note sumbas = this  setsum_reindex[OF basis_inj, unfolded o_def]
  show ?thesis unfolding simplex[OF finite_stdbasis `0\<notin>?p`] apply(rule set_ext) unfolding mem_Collect_eq apply rule
    apply(erule exE, (erule conjE)+) apply(erule_tac[2] conjE)+ proof-
    fix x::"real^'n" and u assume as: "\<forall>x\<in>{basis i |i. i \<in>?D}. 0 \<le> u x" "setsum u {basis i |i. i \<in> ?D} \<le> 1" "(\<Sum>x\<in>{basis i |i. i \<in>?D}. u x *\<^sub>R x) = x"
    have *:"\<forall>i. u (basis i) = x$i" using as(3) unfolding sumbas and basis_expansion_unique [where 'a=real, unfolded smult_conv_scaleR] by auto
    hence **:"setsum u {basis i |i. i \<in> ?D} = setsum (op $ x) ?D" unfolding sumbas by(rule_tac setsum_cong, auto)
    show " (\<forall>i. 0 \<le> x $ i) \<and> setsum (op $ x) ?D \<le> 1" apply - proof(rule,rule)
      fix i::'n show "0 \<le> x$i" unfolding *[rule_format,of i,THEN sym] apply(rule_tac as(1)[rule_format]) by auto
    qed(insert as(2)[unfolded **], auto)
  next fix x::"real^'n" assume as:"\<forall>i. 0 \<le> x $ i" "setsum (op $ x) ?D \<le> 1"
    show "\<exists>u. (\<forall>x\<in>{basis i |i. i \<in> ?D}. 0 \<le> u x) \<and> setsum u {basis i |i. i \<in> ?D} \<le> 1 \<and> (\<Sum>x\<in>{basis i |i. i \<in> ?D}. u x *\<^sub>R x) = x"
      apply(rule_tac x="\<lambda>y. inner y x" in exI) apply(rule,rule) unfolding mem_Collect_eq apply(erule exE) using as(1) apply(erule_tac x=i in allE) 
      unfolding sumbas using as(2) and basis_expansion_unique [where 'a=real, unfolded smult_conv_scaleR] by(auto simp add:inner_basis) qed qed 

lemma interior_std_simplex:
  "interior (convex hull (insert 0 { basis i| i. i\<in>UNIV})) =
  {x::real^'n. (\<forall>i. 0 < x$i) \<and> setsum (\<lambda>i. x$i) UNIV < 1 }"
  apply(rule set_ext) unfolding mem_interior std_simplex unfolding subset_eq mem_Collect_eq Ball_def mem_ball
  unfolding Ball_def[symmetric] apply rule apply(erule exE, (erule conjE)+) defer apply(erule conjE) proof-
  fix x::"real^'n" and e assume "0<e" and as:"\<forall>xa. dist x xa < e \<longrightarrow> (\<forall>x. 0 \<le> xa $ x) \<and> setsum (op $ xa) UNIV \<le> 1"
  show "(\<forall>xa. 0 < x $ xa) \<and> setsum (op $ x) UNIV < 1" apply(rule,rule) proof-
    fix i::'n show "0 < x $ i" using as[THEN spec[where x="x - (e / 2) *\<^sub>R basis i"]] and `e>0`
      unfolding dist_norm by(auto simp add: norm_basis vector_component_simps basis_component elim:allE[where x=i])
  next guess a using UNIV_witness[where 'a='n] ..
    have **:"dist x (x + (e / 2) *\<^sub>R basis a) < e" using  `e>0` and norm_basis[of a]
      unfolding dist_norm by(auto simp add: vector_component_simps basis_component intro!: mult_strict_left_mono_comm)
    have "\<And>i. (x + (e / 2) *\<^sub>R basis a) $ i = x$i + (if i = a then e/2 else 0)" by(auto simp add:vector_component_simps)
    hence *:"setsum (op $ (x + (e / 2) *\<^sub>R basis a)) UNIV = setsum (\<lambda>i. x$i + (if a = i then e/2 else 0)) UNIV" by(rule_tac setsum_cong, auto) 
    have "setsum (op $ x) UNIV < setsum (op $ (x + (e / 2) *\<^sub>R basis a)) UNIV" unfolding * setsum_addf
      using `0<e` dimindex_ge_1 by(auto simp add: setsum_delta')
    also have "\<dots> \<le> 1" using ** apply(drule_tac as[rule_format]) by auto
    finally show "setsum (op $ x) UNIV < 1" by auto qed
next
  fix x::"real^'n" assume as:"\<forall>i. 0 < x $ i" "setsum (op $ x) UNIV < 1"
  guess a using UNIV_witness[where 'a='b] ..
  let ?d = "(1 - setsum (op $ x) UNIV) / real (CARD('n))"
  have "Min ((op $ x) ` UNIV) > 0" apply(rule Min_grI) using as(1) dimindex_ge_1 by auto
  moreover have"?d > 0" apply(rule divide_pos_pos) using as(2) using dimindex_ge_1 by(auto simp add: Suc_le_eq)
  ultimately show "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> (\<forall>i. 0 \<le> y $ i) \<and> setsum (op $ y) UNIV \<le> 1"
    apply(rule_tac x="min (Min ((op $ x) ` UNIV)) ?D" in exI) apply rule defer apply(rule,rule) proof-
    fix y assume y:"dist x y < min (Min (op $ x ` UNIV)) ?d"
    have "setsum (op $ y) UNIV \<le> setsum (\<lambda>i. x$i + ?d) UNIV" proof(rule setsum_mono)
      fix i::'n have "abs (y$i - x$i) < ?d" apply(rule le_less_trans) using component_le_norm[of "y - x" i]
        using y[unfolded min_less_iff_conj dist_norm, THEN conjunct2] by(auto simp add:vector_component_simps norm_minus_commute)
      thus "y $ i \<le> x $ i + ?d" by auto qed
    also have "\<dots> \<le> 1" unfolding setsum_addf setsum_constant card_enum real_eq_of_nat using dimindex_ge_1 by(auto simp add: Suc_le_eq)
    finally show "(\<forall>i. 0 \<le> y $ i) \<and> setsum (op $ y) UNIV \<le> 1" apply- proof(rule,rule)
      fix i::'n have "norm (x - y) < x$i" using y[unfolded min_less_iff_conj dist_norm, THEN conjunct1]
        using Min_gr_iff[of "op $ x ` dimset x"] dimindex_ge_1 by auto
      thus "0 \<le> y$i" using component_le_norm[of "x - y" i] and as(1)[rule_format, of i] by(auto simp add: vector_component_simps)
    qed auto qed auto qed

lemma interior_std_simplex_nonempty: obtains a::"real^'n" where
  "a \<in> interior(convex hull (insert 0 {basis i | i . i \<in> UNIV}))" proof-
  let ?D = "UNIV::'n set" let ?a = "setsum (\<lambda>b::real^'n. inverse (2 * real CARD('n)) *\<^sub>R b) {(basis i) | i. i \<in> ?D}"
  have *:"{basis i :: real ^ 'n | i. i \<in> ?D} = basis ` ?D" by auto
  { fix i have "?a $ i = inverse (2 * real CARD('n))"
    unfolding setsum_component vector_smult_component and * and setsum_reindex[OF basis_inj] and o_def
    apply(rule trans[of _ "setsum (\<lambda>j. if i = j then inverse (2 * real CARD('n)) else 0) ?D"]) apply(rule setsum_cong2)
      unfolding setsum_delta'[OF finite_UNIV[where 'a='n]] and real_dimindex_ge_1[where 'n='n] by(auto simp add: basis_component[of i]) }
  note ** = this
  show ?thesis apply(rule that[of ?a]) unfolding interior_std_simplex mem_Collect_eq proof(rule,rule)
    fix i::'n show "0 < ?a $ i" unfolding ** using dimindex_ge_1 by(auto simp add: Suc_le_eq) next
    have "setsum (op $ ?a) ?D = setsum (\<lambda>i. inverse (2 * real CARD('n))) ?D" by(rule setsum_cong2, rule **) 
    also have "\<dots> < 1" unfolding setsum_constant card_enum real_eq_of_nat real_divide_def[THEN sym] by (auto simp add:field_simps)
    finally show "setsum (op $ ?a) ?D < 1" by auto qed qed

subsection {* Paths. *}

definition "path (g::real^1 \<Rightarrow> real^'n) \<longleftrightarrow> continuous_on {0 .. 1} g"

definition "pathstart (g::real^1 \<Rightarrow> real^'n) = g 0"

definition "pathfinish (g::real^1 \<Rightarrow> real^'n) = g 1"

definition "path_image (g::real^1 \<Rightarrow> real^'n) = g ` {0 .. 1}"

definition "reversepath (g::real^1 \<Rightarrow> real^'n) = (\<lambda>x. g(1 - x))"

definition joinpaths:: "(real^1 \<Rightarrow> real^'n) \<Rightarrow> (real^1 \<Rightarrow> real^'n) \<Rightarrow> (real^1 \<Rightarrow> real^'n)" (infixr "+++" 75)
  where "joinpaths g1 g2 = (\<lambda>x. if dest_vec1 x \<le> ((1 / 2)::real) then g1 (2 *\<^sub>R x) else g2(2 *\<^sub>R x - 1))"
definition "simple_path (g::real^1 \<Rightarrow> real^'n) \<longleftrightarrow>
  (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. g x = g y \<longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0)"

definition "injective_path (g::real^1 \<Rightarrow> real^'n) \<longleftrightarrow>
  (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. g x = g y \<longrightarrow> x = y)"

subsection {* Some lemmas about these concepts. *}

lemma injective_imp_simple_path:
  "injective_path g \<Longrightarrow> simple_path g"
  unfolding injective_path_def simple_path_def by auto

lemma path_image_nonempty: "path_image g \<noteq> {}"
  unfolding path_image_def image_is_empty interval_eq_empty by auto 

lemma pathstart_in_path_image[intro]: "(pathstart g) \<in> path_image g"
  unfolding pathstart_def path_image_def apply(rule imageI)
  unfolding mem_interval_1 vec_1[THEN sym] dest_vec1_vec by auto

lemma pathfinish_in_path_image[intro]: "(pathfinish g) \<in> path_image g"
  unfolding pathfinish_def path_image_def apply(rule imageI)
  unfolding mem_interval_1 vec_1[THEN sym] dest_vec1_vec by auto

lemma connected_path_image[intro]: "path g \<Longrightarrow> connected(path_image g)"
  unfolding path_def path_image_def apply(rule connected_continuous_image, assumption)
  by(rule convex_connected, rule convex_interval)

lemma compact_path_image[intro]: "path g \<Longrightarrow> compact(path_image g)"
  unfolding path_def path_image_def apply(rule compact_continuous_image, assumption)
  by(rule compact_interval)

lemma reversepath_reversepath[simp]: "reversepath(reversepath g) = g"
  unfolding reversepath_def by auto

lemma pathstart_reversepath[simp]: "pathstart(reversepath g) = pathfinish g"
  unfolding pathstart_def reversepath_def pathfinish_def by auto

lemma pathfinish_reversepath[simp]: "pathfinish(reversepath g) = pathstart g"
  unfolding pathstart_def reversepath_def pathfinish_def by auto

lemma pathstart_join[simp]: "pathstart(g1 +++ g2) = pathstart g1"
  unfolding pathstart_def joinpaths_def pathfinish_def by auto

lemma pathfinish_join[simp]:"pathfinish(g1 +++ g2) = pathfinish g2" proof-
  have "2 *\<^sub>R 1 - 1 = (1::real^1)" unfolding Cart_eq by(auto simp add:vector_component_simps)
  thus ?thesis unfolding pathstart_def joinpaths_def pathfinish_def
    unfolding vec_1[THEN sym] dest_vec1_vec by auto qed

lemma path_image_reversepath[simp]: "path_image(reversepath g) = path_image g" proof-
  have *:"\<And>g. path_image(reversepath g) \<subseteq> path_image g"
    unfolding path_image_def subset_eq reversepath_def Ball_def image_iff apply(rule,rule,erule bexE)  
    apply(rule_tac x="1 - xa" in bexI) by(auto simp add:vector_le_def vector_component_simps elim!:ballE)
  show ?thesis using *[of g] *[of "reversepath g"] unfolding reversepath_reversepath by auto qed

lemma path_reversepath[simp]: "path(reversepath g) \<longleftrightarrow> path g" proof-
  have *:"\<And>g. path g \<Longrightarrow> path(reversepath g)" unfolding path_def reversepath_def
    apply(rule continuous_on_compose[unfolded o_def, of _ "\<lambda>x. 1 - x"])
    apply(rule continuous_on_sub, rule continuous_on_const, rule continuous_on_id)
    apply(rule continuous_on_subset[of "{0..1}"], assumption)
    by (auto, auto simp add:vector_le_def vector_component_simps elim!:ballE)
  show ?thesis using *[of g] *[of "reversepath g"] unfolding reversepath_reversepath by auto qed

lemmas reversepath_simps = path_reversepath path_image_reversepath pathstart_reversepath pathfinish_reversepath

lemma path_join[simp]: assumes "pathfinish g1 = pathstart g2" shows "path (g1 +++ g2) \<longleftrightarrow>  path g1 \<and> path g2"
  unfolding path_def pathfinish_def pathstart_def apply rule defer apply(erule conjE) proof-
  assume as:"continuous_on {0..1} (g1 +++ g2)"
  have *:"g1 = (\<lambda>x. g1 (2 *\<^sub>R x)) \<circ> (\<lambda>x. (1/2) *\<^sub>R x)" 
         "g2 = (\<lambda>x. g2 (2 *\<^sub>R x - 1)) \<circ> (\<lambda>x. (1/2) *\<^sub>R (x + 1))" unfolding o_def by auto
  have "op *\<^sub>R (1 / 2) ` {0::real^1..1} \<subseteq> {0..1}"  "(\<lambda>x. (1 / 2) *\<^sub>R (x + 1)) ` {(0::real^1)..1} \<subseteq> {0..1}"
    unfolding image_smult_interval by (auto, auto simp add:vector_le_def vector_component_simps elim!:ballE)
  thus "continuous_on {0..1} g1 \<and> continuous_on {0..1} g2" apply -apply rule
    apply(subst *) defer apply(subst *) apply (rule_tac[!] continuous_on_compose)
    apply (rule continuous_on_cmul, rule continuous_on_add, rule continuous_on_id, rule continuous_on_const) defer
    apply (rule continuous_on_cmul, rule continuous_on_id) apply(rule_tac[!] continuous_on_eq[of _ "g1 +++ g2"]) defer prefer 3
    apply(rule_tac[1-2] continuous_on_subset[of "{0 .. 1}"]) apply(rule as, assumption, rule as, assumption)
    apply(rule) defer apply rule proof-
    fix x assume "x \<in> op *\<^sub>R (1 / 2) ` {0::real^1..1}"
    hence "dest_vec1 x \<le> 1 / 2" unfolding image_iff by(auto simp add: vector_component_simps)
    thus "(g1 +++ g2) x = g1 (2 *\<^sub>R x)" unfolding joinpaths_def by auto next
    fix x assume "x \<in> (\<lambda>x. (1 / 2) *\<^sub>R (x + 1)) ` {0::real^1..1}"
    hence "dest_vec1 x \<ge> 1 / 2" unfolding image_iff by(auto simp add: vector_component_simps)
    thus "(g1 +++ g2) x = g2 (2 *\<^sub>R x - 1)" proof(cases "dest_vec1 x = 1 / 2")
      case True hence "x = (1/2) *\<^sub>R 1" unfolding Cart_eq by(auto simp add: forall_1 vector_component_simps)
      thus ?thesis unfolding joinpaths_def using assms[unfolded pathstart_def pathfinish_def] by auto
    qed (auto simp add:le_less joinpaths_def) qed
next assume as:"continuous_on {0..1} g1" "continuous_on {0..1} g2"
  have *:"{0 .. 1::real^1} = {0.. (1/2)*\<^sub>R 1} \<union> {(1/2) *\<^sub>R 1 .. 1}" by(auto simp add: vector_component_simps) 
  have **:"op *\<^sub>R 2 ` {0..(1 / 2) *\<^sub>R 1} = {0..1::real^1}" apply(rule set_ext, rule) unfolding image_iff 
    defer apply(rule_tac x="(1/2)*\<^sub>R x" in bexI) by(auto simp add: vector_component_simps)
  have ***:"(\<lambda>x. 2 *\<^sub>R x - 1) ` {(1 / 2) *\<^sub>R 1..1} = {0..1::real^1}"
    unfolding image_affinity_interval[of _ "- 1", unfolded diff_def[symmetric]] and interval_eq_empty_1
    by(auto simp add: vector_component_simps)
  have ****:"\<And>x::real^1. x $ 1 * 2 = 1 \<longleftrightarrow> x = (1/2) *\<^sub>R 1" unfolding Cart_eq by(auto simp add: forall_1 vector_component_simps)
  show "continuous_on {0..1} (g1 +++ g2)" unfolding * apply(rule continuous_on_union) apply(rule closed_interval)+ proof-
    show "continuous_on {0..(1 / 2) *\<^sub>R 1} (g1 +++ g2)" apply(rule continuous_on_eq[of _ "\<lambda>x. g1 (2 *\<^sub>R x)"]) defer
      unfolding o_def[THEN sym] apply(rule continuous_on_compose) apply(rule continuous_on_cmul, rule continuous_on_id)
      unfolding ** apply(rule as(1)) unfolding joinpaths_def by(auto simp add: vector_component_simps) next
    show "continuous_on {(1/2)*\<^sub>R1..1} (g1 +++ g2)" apply(rule continuous_on_eq[of _ "g2 \<circ> (\<lambda>x. 2 *\<^sub>R x - 1)"]) defer
      apply(rule continuous_on_compose) apply(rule continuous_on_sub, rule continuous_on_cmul, rule continuous_on_id, rule continuous_on_const)
      unfolding *** o_def joinpaths_def apply(rule as(2)) using assms[unfolded pathstart_def pathfinish_def]
      by(auto simp add: vector_component_simps ****) qed qed

lemma path_image_join_subset: "path_image(g1 +++ g2) \<subseteq> (path_image g1 \<union> path_image g2)" proof
  fix x assume "x \<in> path_image (g1 +++ g2)"
  then obtain y where y:"y\<in>{0..1}" "x = (if dest_vec1 y \<le> 1 / 2 then g1 (2 *\<^sub>R y) else g2 (2 *\<^sub>R y - 1))"
    unfolding path_image_def image_iff joinpaths_def by auto
  thus "x \<in> path_image g1 \<union> path_image g2" apply(cases "dest_vec1 y \<le> 1/2")
    apply(rule_tac UnI1) defer apply(rule_tac UnI2) unfolding y(2) path_image_def using y(1)
    by(auto intro!: imageI simp add: vector_component_simps) qed

lemma subset_path_image_join:
  assumes "path_image g1 \<subseteq> s" "path_image g2 \<subseteq> s" shows "path_image(g1 +++ g2) \<subseteq> s"
  using path_image_join_subset[of g1 g2] and assms by auto

lemma path_image_join:
  assumes "path g1" "path g2" "pathfinish g1 = pathstart g2"
  shows "path_image(g1 +++ g2) = (path_image g1) \<union> (path_image g2)"
apply(rule, rule path_image_join_subset, rule) unfolding Un_iff proof(erule disjE)
  fix x assume "x \<in> path_image g1"
  then obtain y where y:"y\<in>{0..1}" "x = g1 y" unfolding path_image_def image_iff by auto
  thus "x \<in> path_image (g1 +++ g2)" unfolding joinpaths_def path_image_def image_iff
    apply(rule_tac x="(1/2) *\<^sub>R y" in bexI) by(auto simp add: vector_component_simps) next
  fix x assume "x \<in> path_image g2"
  then obtain y where y:"y\<in>{0..1}" "x = g2 y" unfolding path_image_def image_iff by auto
  moreover have *:"y $ 1 = 0 \<Longrightarrow> y = 0" unfolding Cart_eq by auto
  ultimately show "x \<in> path_image (g1 +++ g2)" unfolding joinpaths_def path_image_def image_iff
    apply(rule_tac x="(1/2) *\<^sub>R (y + 1)" in bexI) using assms(3)[unfolded pathfinish_def pathstart_def]
    by(auto simp add: vector_component_simps) qed 

lemma not_in_path_image_join:
  assumes "x \<notin> path_image g1" "x \<notin> path_image g2" shows "x \<notin> path_image(g1 +++ g2)"
  using assms and path_image_join_subset[of g1 g2] by auto

lemma simple_path_reversepath: assumes "simple_path g" shows "simple_path (reversepath g)"
  using assms unfolding simple_path_def reversepath_def apply- apply(rule ballI)+
  apply(erule_tac x="1-x" in ballE, erule_tac x="1-y" in ballE)
  unfolding mem_interval_1 by(auto simp add:vector_component_simps)

lemma dest_vec1_scaleR [simp]:
  "dest_vec1 (scaleR a x) = scaleR a (dest_vec1 x)"
unfolding dest_vec1_def by simp

lemma simple_path_join_loop:
  assumes "injective_path g1" "injective_path g2" "pathfinish g2 = pathstart g1"
  "(path_image g1 \<inter> path_image g2) \<subseteq> {pathstart g1,pathstart g2}"
  shows "simple_path(g1 +++ g2)"
unfolding simple_path_def proof((rule ballI)+, rule impI) let ?g = "g1 +++ g2"
  note inj = assms(1,2)[unfolded injective_path_def, rule_format]
  fix x y::"real^1" assume xy:"x \<in> {0..1}" "y \<in> {0..1}" "?g x = ?g y"
  show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0" proof(case_tac "x$1 \<le> 1/2",case_tac[!] "y$1 \<le> 1/2", unfold not_le)
    assume as:"x $ 1 \<le> 1 / 2" "y $ 1 \<le> 1 / 2"
    hence "g1 (2 *\<^sub>R x) = g1 (2 *\<^sub>R y)" using xy(3) unfolding joinpaths_def dest_vec1_def by auto
    moreover have "2 *\<^sub>R x \<in> {0..1}" "2 *\<^sub>R y \<in> {0..1}" using xy(1,2) as
      unfolding mem_interval_1 dest_vec1_def by(auto simp add:vector_component_simps)
    ultimately show ?thesis using inj(1)[of "2*\<^sub>R x" "2*\<^sub>R y"] by auto
  next assume as:"x $ 1 > 1 / 2" "y $ 1 > 1 / 2"
    hence "g2 (2 *\<^sub>R x - 1) = g2 (2 *\<^sub>R y - 1)" using xy(3) unfolding joinpaths_def dest_vec1_def by auto
    moreover have "2 *\<^sub>R x - 1 \<in> {0..1}" "2 *\<^sub>R y - 1 \<in> {0..1}" using xy(1,2) as
      unfolding mem_interval_1 dest_vec1_def by(auto simp add:vector_component_simps)
    ultimately show ?thesis using inj(2)[of "2*\<^sub>R x - 1" "2*\<^sub>R y - 1"] by auto
  next assume as:"x $ 1 \<le> 1 / 2" "y $ 1 > 1 / 2"
    hence "?g x \<in> path_image g1" "?g y \<in> path_image g2" unfolding path_image_def joinpaths_def
      using xy(1,2)[unfolded mem_interval_1] by(auto simp add:vector_component_simps intro!: imageI)
    moreover have "?g y \<noteq> pathstart g2" using as(2) unfolding pathstart_def joinpaths_def
      using inj(2)[of "2 *\<^sub>R y - 1" 0] and xy(2)[unfolded mem_interval_1]
      apply(rule_tac ccontr) by(auto simp add:vector_component_simps field_simps Cart_eq)
    ultimately have *:"?g x = pathstart g1" using assms(4) unfolding xy(3) by auto
    hence "x = 0" unfolding pathstart_def joinpaths_def using as(1) and xy(1)[unfolded mem_interval_1]
      using inj(1)[of "2 *\<^sub>R x" 0] by(auto simp add:vector_component_simps)
    moreover have "y = 1" using * unfolding xy(3) assms(3)[THEN sym]
      unfolding joinpaths_def pathfinish_def using as(2) and xy(2)[unfolded mem_interval_1]
      using inj(2)[of "2 *\<^sub>R y - 1" 1] by (auto simp add:vector_component_simps Cart_eq)
    ultimately show ?thesis by auto 
  next assume as:"x $ 1 > 1 / 2" "y $ 1 \<le> 1 / 2"
    hence "?g x \<in> path_image g2" "?g y \<in> path_image g1" unfolding path_image_def joinpaths_def
      using xy(1,2)[unfolded mem_interval_1] by(auto simp add:vector_component_simps intro!: imageI)
    moreover have "?g x \<noteq> pathstart g2" using as(1) unfolding pathstart_def joinpaths_def
      using inj(2)[of "2 *\<^sub>R x - 1" 0] and xy(1)[unfolded mem_interval_1]
      apply(rule_tac ccontr) by(auto simp add:vector_component_simps field_simps Cart_eq)
    ultimately have *:"?g y = pathstart g1" using assms(4) unfolding xy(3) by auto
    hence "y = 0" unfolding pathstart_def joinpaths_def using as(2) and xy(2)[unfolded mem_interval_1]
      using inj(1)[of "2 *\<^sub>R y" 0] by(auto simp add:vector_component_simps)
    moreover have "x = 1" using * unfolding xy(3)[THEN sym] assms(3)[THEN sym]
      unfolding joinpaths_def pathfinish_def using as(1) and xy(1)[unfolded mem_interval_1]
      using inj(2)[of "2 *\<^sub>R x - 1" 1] by(auto simp add:vector_component_simps Cart_eq)
    ultimately show ?thesis by auto qed qed

lemma injective_path_join:
  assumes "injective_path g1" "injective_path g2" "pathfinish g1 = pathstart g2"
  "(path_image g1 \<inter> path_image g2) \<subseteq> {pathstart g2}"
  shows "injective_path(g1 +++ g2)"
  unfolding injective_path_def proof(rule,rule,rule) let ?g = "g1 +++ g2"
  note inj = assms(1,2)[unfolded injective_path_def, rule_format]
  fix x y assume xy:"x \<in> {0..1}" "y \<in> {0..1}" "(g1 +++ g2) x = (g1 +++ g2) y"
  show "x = y" proof(cases "x$1 \<le> 1/2", case_tac[!] "y$1 \<le> 1/2", unfold not_le)
    assume "x $ 1 \<le> 1 / 2" "y $ 1 \<le> 1 / 2" thus ?thesis using inj(1)[of "2*\<^sub>R x" "2*\<^sub>R y"] and xy
      unfolding mem_interval_1 joinpaths_def by(auto simp add:vector_component_simps)
  next assume "x $ 1 > 1 / 2" "y $ 1 > 1 / 2" thus ?thesis using inj(2)[of "2*\<^sub>R x - 1" "2*\<^sub>R y - 1"] and xy
      unfolding mem_interval_1 joinpaths_def by(auto simp add:vector_component_simps)
  next assume as:"x $ 1 \<le> 1 / 2" "y $ 1 > 1 / 2" 
    hence "?g x \<in> path_image g1" "?g y \<in> path_image g2" unfolding path_image_def joinpaths_def
      using xy(1,2)[unfolded mem_interval_1] by(auto simp add:vector_component_simps intro!: imageI)
    hence "?g x = pathfinish g1" "?g y = pathstart g2" using assms(4) unfolding assms(3) xy(3) by auto
    thus ?thesis using as and inj(1)[of "2 *\<^sub>R x" 1] inj(2)[of "2 *\<^sub>R y - 1" 0] and xy(1,2)
      unfolding pathstart_def pathfinish_def joinpaths_def mem_interval_1
      by(auto simp add:vector_component_simps Cart_eq forall_1)
  next assume as:"x $ 1 > 1 / 2" "y $ 1 \<le> 1 / 2" 
    hence "?g x \<in> path_image g2" "?g y \<in> path_image g1" unfolding path_image_def joinpaths_def
      using xy(1,2)[unfolded mem_interval_1] by(auto simp add:vector_component_simps intro!: imageI)
    hence "?g x = pathstart g2" "?g y = pathfinish g1" using assms(4) unfolding assms(3) xy(3) by auto
    thus ?thesis using as and inj(2)[of "2 *\<^sub>R x - 1" 0] inj(1)[of "2 *\<^sub>R y" 1] and xy(1,2)
      unfolding pathstart_def pathfinish_def joinpaths_def mem_interval_1
      by(auto simp add:vector_component_simps forall_1 Cart_eq) qed qed

lemmas join_paths_simps = path_join path_image_join pathstart_join pathfinish_join
 
subsection {* Reparametrizing a closed curve to start at some chosen point. *}

definition "shiftpath a (f::real^1 \<Rightarrow> real^'n) =
  (\<lambda>x. if dest_vec1 (a + x) \<le> 1 then f(a + x) else f(a + x - 1))"

lemma pathstart_shiftpath: "a \<le> 1 \<Longrightarrow> pathstart(shiftpath a g) = g a"
  unfolding pathstart_def shiftpath_def by auto

(** move this **)
declare forall_1[simp] ex_1[simp]

lemma pathfinish_shiftpath: assumes "0 \<le> a" "pathfinish g = pathstart g"
  shows "pathfinish(shiftpath a g) = g a"
  using assms unfolding pathstart_def pathfinish_def shiftpath_def
  by(auto simp add: vector_component_simps)

lemma endpoints_shiftpath:
  assumes "pathfinish g = pathstart g" "a \<in> {0 .. 1}" 
  shows "pathfinish(shiftpath a g) = g a" "pathstart(shiftpath a g) = g a"
  using assms by(auto intro!:pathfinish_shiftpath pathstart_shiftpath)

lemma closed_shiftpath:
  assumes "pathfinish g = pathstart g" "a \<in> {0..1}"
  shows "pathfinish(shiftpath a g) = pathstart(shiftpath a g)"
  using endpoints_shiftpath[OF assms] by auto

lemma path_shiftpath:
  assumes "path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
  shows "path(shiftpath a g)" proof-
  have *:"{0 .. 1} = {0 .. 1-a} \<union> {1-a .. 1}" using assms(3) by(auto simp add: vector_component_simps)
  have **:"\<And>x. x + a = 1 \<Longrightarrow> g (x + a - 1) = g (x + a)"
    using assms(2)[unfolded pathfinish_def pathstart_def] by auto
  show ?thesis unfolding path_def shiftpath_def * apply(rule continuous_on_union)
    apply(rule closed_interval)+ apply(rule continuous_on_eq[of _ "g \<circ> (\<lambda>x. a + x)"]) prefer 3
    apply(rule continuous_on_eq[of _ "g \<circ> (\<lambda>x. a - 1 + x)"]) defer prefer 3
    apply(rule continuous_on_intros)+ prefer 2 apply(rule continuous_on_intros)+
    apply(rule_tac[1-2] continuous_on_subset[OF assms(1)[unfolded path_def]])
    using assms(3) and ** by(auto simp add:vector_component_simps field_simps Cart_eq) qed

lemma shiftpath_shiftpath: assumes "pathfinish g = pathstart g" "a \<in> {0..1}" "x \<in> {0..1}" 
  shows "shiftpath (1 - a) (shiftpath a g) x = g x"
  using assms unfolding pathfinish_def pathstart_def shiftpath_def 
  by(auto simp add: vector_component_simps)

lemma path_image_shiftpath:
  assumes "a \<in> {0..1}" "pathfinish g = pathstart g"
  shows "path_image(shiftpath a g) = path_image g" proof-
  { fix x assume as:"g 1 = g 0" "x \<in> {0..1::real^1}" " \<forall>y\<in>{0..1} \<inter> {x. \<not> a $ 1 + x $ 1 \<le> 1}. g x \<noteq> g (a + y - 1)" 
    hence "\<exists>y\<in>{0..1} \<inter> {x. a $ 1 + x $ 1 \<le> 1}. g x = g (a + y)" proof(cases "a \<le> x")
      case False thus ?thesis apply(rule_tac x="1 + x - a" in bexI)
        using as(1,2) and as(3)[THEN bspec[where x="1 + x - a"]] and assms(1)
        by(auto simp add:vector_component_simps field_simps atomize_not) next
      case True thus ?thesis using as(1-2) and assms(1) apply(rule_tac x="x - a" in bexI)
        by(auto simp add:vector_component_simps field_simps) qed }
  thus ?thesis using assms unfolding shiftpath_def path_image_def pathfinish_def pathstart_def 
    by(auto simp add:vector_component_simps image_iff) qed

subsection {* Special case of straight-line paths. *}

definition
  linepath :: "real ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow> real ^ 1 \<Rightarrow> real ^ 'n" where
  "linepath a b = (\<lambda>x. (1 - dest_vec1 x) *\<^sub>R a + dest_vec1 x *\<^sub>R b)"

lemma pathstart_linepath[simp]: "pathstart(linepath a b) = a"
  unfolding pathstart_def linepath_def by auto

lemma pathfinish_linepath[simp]: "pathfinish(linepath a b) = b"
  unfolding pathfinish_def linepath_def by auto

lemma continuous_linepath_at[intro]: "continuous (at x) (linepath a b)"
  unfolding linepath_def
  by (intro continuous_intros continuous_dest_vec1)

lemma continuous_on_linepath[intro]: "continuous_on s (linepath a b)"
  using continuous_linepath_at by(auto intro!: continuous_at_imp_continuous_on)

lemma path_linepath[intro]: "path(linepath a b)"
  unfolding path_def by(rule continuous_on_linepath)

lemma path_image_linepath[simp]: "path_image(linepath a b) = (closed_segment a b)"
  unfolding path_image_def segment linepath_def apply (rule set_ext, rule) defer
  unfolding mem_Collect_eq image_iff apply(erule exE) apply(rule_tac x="u *\<^sub>R 1" in bexI)
  by(auto simp add:vector_component_simps)

lemma reversepath_linepath[simp]:  "reversepath(linepath a b) = linepath b a"
  unfolding reversepath_def linepath_def by(rule ext, auto simp add:vector_component_simps)

lemma injective_path_linepath: assumes "a \<noteq> b" shows "injective_path(linepath a b)" proof- 
  { obtain i where i:"a$i \<noteq> b$i" using assms[unfolded Cart_eq] by auto
    fix x y::"real^1" assume "x $ 1 *\<^sub>R b + y $ 1 *\<^sub>R a = x $ 1 *\<^sub>R a + y $ 1 *\<^sub>R b"
    hence "x$1 * (b$i - a$i) = y$1 * (b$i - a$i)" unfolding Cart_eq by(auto simp add:field_simps vector_component_simps)
    hence "x = y" unfolding mult_cancel_right Cart_eq using i(1) by(auto simp add:field_simps) }
  thus ?thesis unfolding injective_path_def linepath_def by(auto simp add:vector_component_simps algebra_simps) qed

lemma simple_path_linepath[intro]: "a \<noteq> b \<Longrightarrow> simple_path(linepath a b)" by(auto intro!: injective_imp_simple_path injective_path_linepath)

subsection {* Bounding a point away from a path. *}

lemma not_on_path_ball: assumes "path g" "z \<notin> path_image g"
  shows "\<exists>e>0. ball z e \<inter> (path_image g) = {}" proof-
  obtain a where "a\<in>path_image g" "\<forall>y\<in>path_image g. dist z a \<le> dist z y"
    using distance_attains_inf[OF _ path_image_nonempty, of g z]
    using compact_path_image[THEN compact_imp_closed, OF assms(1)] by auto
  thus ?thesis apply(rule_tac x="dist z a" in exI) using assms(2) by(auto intro!: dist_pos_lt) qed

lemma not_on_path_cball: assumes "path g" "z \<notin> path_image g"
  shows "\<exists>e>0. cball z e \<inter> (path_image g) = {}" proof-
  obtain e where "ball z e \<inter> path_image g = {}" "e>0" using not_on_path_ball[OF assms] by auto
  moreover have "cball z (e/2) \<subseteq> ball z e" using `e>0` by auto
  ultimately show ?thesis apply(rule_tac x="e/2" in exI) by auto qed

subsection {* Path component, considered as a "joinability" relation (from Tom Hales). *}

definition "path_component s x y \<longleftrightarrow> (\<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)"

lemmas path_defs = path_def pathstart_def pathfinish_def path_image_def path_component_def 

lemma path_component_mem: assumes "path_component s x y" shows "x \<in> s" "y \<in> s"
  using assms unfolding path_defs by auto

lemma path_component_refl: assumes "x \<in> s" shows "path_component s x x"
  unfolding path_defs apply(rule_tac x="\<lambda>u. x" in exI) using assms 
  by(auto intro!:continuous_on_intros)    

lemma path_component_refl_eq: "path_component s x x \<longleftrightarrow> x \<in> s"
  by(auto intro!: path_component_mem path_component_refl) 

lemma path_component_sym: "path_component s x y \<Longrightarrow> path_component s y x"
  using assms unfolding path_component_def apply(erule exE) apply(rule_tac x="reversepath g" in exI) 
  by(auto simp add: reversepath_simps)

lemma path_component_trans: assumes "path_component s x y" "path_component s y z" shows "path_component s x z"
  using assms unfolding path_component_def apply- apply(erule exE)+ apply(rule_tac x="g +++ ga" in exI) by(auto simp add: path_image_join)

lemma path_component_of_subset: "s \<subseteq> t \<Longrightarrow>  path_component s x y \<Longrightarrow> path_component t x y"
  unfolding path_component_def by auto

subsection {* Can also consider it as a set, as the name suggests. *}

lemma path_component_set: "path_component s x = { y. (\<exists>g. path g \<and> path_image g \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y )}"
  apply(rule set_ext) unfolding mem_Collect_eq unfolding mem_def path_component_def by auto

lemma mem_path_component_set:"x \<in> path_component s y \<longleftrightarrow> path_component s y x" unfolding mem_def by auto

lemma path_component_subset: "(path_component s x) \<subseteq> s"
  apply(rule, rule path_component_mem(2)) by(auto simp add:mem_def)

lemma path_component_eq_empty: "path_component s x = {} \<longleftrightarrow> x \<notin> s"
  apply rule apply(drule equals0D[of _ x]) defer apply(rule equals0I) unfolding mem_path_component_set
  apply(drule path_component_mem(1)) using path_component_refl by auto

subsection {* Path connectedness of a space. *}

definition "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. \<exists>g. path g \<and> (path_image g) \<subseteq> s \<and> pathstart g = x \<and> pathfinish g = y)"

lemma path_connected_component: "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. \<forall>y\<in>s. path_component s x y)"
  unfolding path_connected_def path_component_def by auto

lemma path_connected_component_set: "path_connected s \<longleftrightarrow> (\<forall>x\<in>s. path_component s x = s)" 
  unfolding path_connected_component apply(rule, rule, rule, rule path_component_subset) 
  unfolding subset_eq mem_path_component_set Ball_def mem_def by auto

subsection {* Some useful lemmas about path-connectedness. *}

lemma convex_imp_path_connected: assumes "convex s" shows "path_connected s"
  unfolding path_connected_def apply(rule,rule,rule_tac x="linepath x y" in exI)
  unfolding path_image_linepath using assms[unfolded convex_contains_segment] by auto

lemma path_connected_imp_connected: assumes "path_connected s" shows "connected s"
  unfolding connected_def not_ex apply(rule,rule,rule ccontr) unfolding not_not apply(erule conjE)+ proof-
  fix e1 e2 assume as:"open e1" "open e2" "s \<subseteq> e1 \<union> e2" "e1 \<inter> e2 \<inter> s = {}" "e1 \<inter> s \<noteq> {}" "e2 \<inter> s \<noteq> {}"
  then obtain x1 x2 where obt:"x1\<in>e1\<inter>s" "x2\<in>e2\<inter>s" by auto
  then obtain g where g:"path g" "path_image g \<subseteq> s" "pathstart g = x1" "pathfinish g = x2"
    using assms[unfolded path_connected_def,rule_format,of x1 x2] by auto
  have *:"connected {0..1::real^1}" by(auto intro!: convex_connected convex_interval)
  have "{0..1} \<subseteq> {x \<in> {0..1}. g x \<in> e1} \<union> {x \<in> {0..1}. g x \<in> e2}" using as(3) g(2)[unfolded path_defs] by blast
  moreover have "{x \<in> {0..1}. g x \<in> e1} \<inter> {x \<in> {0..1}. g x \<in> e2} = {}" using as(4) g(2)[unfolded path_defs] unfolding subset_eq by auto 
  moreover have "{x \<in> {0..1}. g x \<in> e1} \<noteq> {} \<and> {x \<in> {0..1}. g x \<in> e2} \<noteq> {}" using g(3,4)[unfolded path_defs] using obt by(auto intro!: exI)
  ultimately show False using *[unfolded connected_local not_ex,rule_format, of "{x\<in>{0..1}. g x \<in> e1}" "{x\<in>{0..1}. g x \<in> e2}"]
    using continuous_open_in_preimage[OF g(1)[unfolded path_def] as(1)]
    using continuous_open_in_preimage[OF g(1)[unfolded path_def] as(2)] by auto qed

lemma open_path_component: assumes "open s" shows "open(path_component s x)"
  unfolding open_contains_ball proof
  fix y assume as:"y \<in> path_component s x"
  hence "y\<in>s" apply- apply(rule path_component_mem(2)) unfolding mem_def by auto
  then obtain e where e:"e>0" "ball y e \<subseteq> s" using assms[unfolded open_contains_ball] by auto
  show "\<exists>e>0. ball y e \<subseteq> path_component s x" apply(rule_tac x=e in exI) apply(rule,rule `e>0`,rule) unfolding mem_ball mem_path_component_set proof-
    fix z assume "dist y z < e" thus "path_component s x z" apply(rule_tac path_component_trans[of _ _ y]) defer 
      apply(rule path_component_of_subset[OF e(2)]) apply(rule convex_imp_path_connected[OF convex_ball, unfolded path_connected_component, rule_format]) using `e>0`
      using as[unfolded mem_def] by auto qed qed

lemma open_non_path_component: assumes "open s" shows "open(s - path_component s x)" unfolding open_contains_ball proof
  fix y assume as:"y\<in>s - path_component s x" 
  then obtain e where e:"e>0" "ball y e \<subseteq> s" using assms[unfolded open_contains_ball] by auto
  show "\<exists>e>0. ball y e \<subseteq> s - path_component s x" apply(rule_tac x=e in exI) apply(rule,rule `e>0`,rule,rule) defer proof(rule ccontr)
    fix z assume "z\<in>ball y e" "\<not> z \<notin> path_component s x" 
    hence "y \<in> path_component s x" unfolding not_not mem_path_component_set using `e>0` 
      apply- apply(rule path_component_trans,assumption) apply(rule path_component_of_subset[OF e(2)])
      apply(rule convex_imp_path_connected[OF convex_ball, unfolded path_connected_component, rule_format]) by auto
    thus False using as by auto qed(insert e(2), auto) qed

lemma connected_open_path_connected: assumes "open s" "connected s" shows "path_connected s"
  unfolding path_connected_component_set proof(rule,rule,rule path_component_subset, rule)
  fix x y assume "x \<in> s" "y \<in> s" show "y \<in> path_component s x" proof(rule ccontr)
    assume "y \<notin> path_component s x" moreover
    have "path_component s x \<inter> s \<noteq> {}" using `x\<in>s` path_component_eq_empty path_component_subset[of s x] by auto
    ultimately show False using `y\<in>s` open_non_path_component[OF assms(1)] open_path_component[OF assms(1)]
    using assms(2)[unfolded connected_def not_ex, rule_format, of"path_component s x" "s - path_component s x"] by auto
qed qed

lemma path_connected_continuous_image:
  assumes "continuous_on s f" "path_connected s" shows "path_connected (f ` s)"
  unfolding path_connected_def proof(rule,rule)
  fix x' y' assume "x' \<in> f ` s" "y' \<in> f ` s"
  then obtain x y where xy:"x\<in>s" "y\<in>s" "x' = f x" "y' = f y" by auto
  guess g using assms(2)[unfolded path_connected_def,rule_format,OF xy(1,2)] ..
  thus "\<exists>g. path g \<and> path_image g \<subseteq> f ` s \<and> pathstart g = x' \<and> pathfinish g = y'"
    unfolding xy apply(rule_tac x="f \<circ> g" in exI) unfolding path_defs
    using assms(1) by(auto intro!: continuous_on_compose continuous_on_subset[of _ _ "g ` {0..1}"]) qed

lemma homeomorphic_path_connectedness:
  "s homeomorphic t \<Longrightarrow> (path_connected s \<longleftrightarrow> path_connected t)"
  unfolding homeomorphic_def homeomorphism_def apply(erule exE|erule conjE)+ apply rule
  apply(drule_tac f=f in path_connected_continuous_image) prefer 3
  apply(drule_tac f=g in path_connected_continuous_image) by auto

lemma path_connected_empty: "path_connected {}"
  unfolding path_connected_def by auto

lemma path_connected_singleton: "path_connected {a}"
  unfolding path_connected_def apply(rule,rule)
  apply(rule_tac x="linepath a a" in exI) by(auto simp add:segment scaleR_left_diff_distrib)

lemma path_connected_Un: assumes "path_connected s" "path_connected t" "s \<inter> t \<noteq> {}"
  shows "path_connected (s \<union> t)" unfolding path_connected_component proof(rule,rule)
  fix x y assume as:"x \<in> s \<union> t" "y \<in> s \<union> t" 
  from assms(3) obtain z where "z \<in> s \<inter> t" by auto
  thus "path_component (s \<union> t) x y" using as using assms(1-2)[unfolded path_connected_component] apply- 
    apply(erule_tac[!] UnE)+ apply(rule_tac[2-3] path_component_trans[of _ _ z])
    by(auto simp add:path_component_of_subset [OF Un_upper1] path_component_of_subset[OF Un_upper2]) qed

subsection {* sphere is path-connected. *}

lemma path_connected_punctured_universe:
 assumes "2 \<le> CARD('n::finite)" shows "path_connected((UNIV::(real^'n) set) - {a})" proof-
  obtain \<psi> where \<psi>:"bij_betw \<psi> {1..CARD('n)} (UNIV::'n set)" using ex_bij_betw_nat_finite_1[OF finite_UNIV] by auto
  let ?U = "UNIV::(real^'n) set" let ?u = "?U - {0}"
  let ?basis = "\<lambda>k. basis (\<psi> k)"
  let ?A = "\<lambda>k. {x::real^'n. \<exists>i\<in>{1..k}. inner (basis (\<psi> i)) x \<noteq> 0}"
  have "\<forall>k\<in>{2..CARD('n)}. path_connected (?A k)" proof
    have *:"\<And>k. ?A (Suc k) = {x. inner (?basis (Suc k)) x < 0} \<union> {x. inner (?basis (Suc k)) x > 0} \<union> ?A k" apply(rule set_ext,rule) defer
      apply(erule UnE)+  unfolding mem_Collect_eq apply(rule_tac[1-2] x="Suc k" in bexI)
      by(auto elim!: ballE simp add: not_less le_Suc_eq)
    fix k assume "k \<in> {2..CARD('n)}" thus "path_connected (?A k)" proof(induct k)
      case (Suc k) show ?case proof(cases "k = 1")
        case False from Suc have d:"k \<in> {1..CARD('n)}" "Suc k \<in> {1..CARD('n)}" by auto
        hence "\<psi> k \<noteq> \<psi> (Suc k)" using \<psi>[unfolded bij_betw_def inj_on_def, THEN conjunct1, THEN bspec[where x=k]] by auto
        hence **:"?basis k + ?basis (Suc k) \<in> {x. 0 < inner (?basis (Suc k)) x} \<inter> (?A k)" 
          "?basis k - ?basis (Suc k) \<in> {x. 0 > inner (?basis (Suc k)) x} \<inter> ({x. 0 < inner (?basis (Suc k)) x} \<union> (?A k))" using d
          by(auto simp add: inner_basis vector_component_simps intro!:bexI[where x=k])
        show ?thesis unfolding * Un_assoc apply(rule path_connected_Un) defer apply(rule path_connected_Un) 
          prefer 5 apply(rule_tac[1-2] convex_imp_path_connected, rule convex_halfspace_lt, rule convex_halfspace_gt)
          apply(rule Suc(1)) apply(rule_tac[2-3] ccontr) using d ** False by auto
      next case True hence d:"1\<in>{1..CARD('n)}" "2\<in>{1..CARD('n)}" using Suc(2) by auto
        have ***:"Suc 1 = 2" by auto
        have **:"\<And>s t P Q. s \<union> t \<union> {x. P x \<or> Q x} = (s \<union> {x. P x}) \<union> (t \<union> {x. Q x})" by auto
        have "\<psi> 2 \<noteq> \<psi> (Suc 0)" apply(rule ccontr) using \<psi>[unfolded bij_betw_def inj_on_def, THEN conjunct1, THEN bspec[where x=2]] using assms by auto
        thus ?thesis unfolding * True unfolding ** neq_iff bex_disj_distrib apply -
          apply(rule path_connected_Un, rule_tac[1-2] path_connected_Un) defer 3 apply(rule_tac[1-4] convex_imp_path_connected) 
          apply(rule_tac[5] x=" ?basis 1 + ?basis 2" in nequals0I)
          apply(rule_tac[6] x="-?basis 1 + ?basis 2" in nequals0I)
          apply(rule_tac[7] x="-?basis 1 - ?basis 2" in nequals0I)
          using d unfolding *** by(auto intro!: convex_halfspace_gt convex_halfspace_lt, auto simp add:vector_component_simps inner_basis)
  qed qed auto qed note lem = this

  have ***:"\<And>x::real^'n. (\<exists>i\<in>{1..CARD('n)}. inner (basis (\<psi> i)) x \<noteq> 0) \<longleftrightarrow> (\<exists>i. inner (basis i) x \<noteq> 0)"
    apply rule apply(erule bexE) apply(rule_tac x="\<psi> i" in exI) defer apply(erule exE) proof- 
    fix x::"real^'n" and i assume as:"inner (basis i) x \<noteq> 0"
    have "i\<in>\<psi> ` {1..CARD('n)}" using \<psi>[unfolded bij_betw_def, THEN conjunct2] by auto
    then obtain j where "j\<in>{1..CARD('n)}" "\<psi> j = i" by auto
    thus "\<exists>i\<in>{1..CARD('n)}. inner (basis (\<psi> i)) x \<noteq> 0" apply(rule_tac x=j in bexI) using as by auto qed auto
  have *:"?U - {a} = (\<lambda>x. x + a) ` {x. x \<noteq> 0}" apply(rule set_ext) unfolding image_iff 
    apply rule apply(rule_tac x="x - a" in bexI) by auto
  have **:"\<And>x::real^'n. x\<noteq>0 \<longleftrightarrow> (\<exists>i. inner (basis i) x \<noteq> 0)" unfolding Cart_eq by(auto simp add: inner_basis)
  show ?thesis unfolding * apply(rule path_connected_continuous_image) apply(rule continuous_on_intros)+ 
    unfolding ** apply(rule lem[THEN bspec[where x="CARD('n)"], unfolded ***]) using assms by auto qed

lemma path_connected_sphere: assumes "2 \<le> CARD('n::finite)" shows "path_connected {x::real^'n. norm(x - a) = r}" proof(cases "r\<le>0")
  case True thus ?thesis proof(cases "r=0") 
    case False hence "{x::real^'n. norm(x - a) = r} = {}" using True by auto
    thus ?thesis using path_connected_empty by auto
  qed(auto intro!:path_connected_singleton) next
  case False hence *:"{x::real^'n. norm(x - a) = r} = (\<lambda>x. a + r *\<^sub>R x) ` {x. norm x = 1}" unfolding not_le apply -apply(rule set_ext,rule)
    unfolding image_iff apply(rule_tac x="(1/r) *\<^sub>R (x - a)" in bexI) unfolding mem_Collect_eq norm_scaleR by (auto simp add: scaleR_right_diff_distrib)
  have **:"{x::real^'n. norm x = 1} = (\<lambda>x. (1/norm x) *\<^sub>R x) ` (UNIV - {0})" apply(rule set_ext,rule)
    unfolding image_iff apply(rule_tac x=x in bexI) unfolding mem_Collect_eq by(auto split:split_if_asm)
  have "continuous_on (UNIV - {0}) (\<lambda>x::real^'n. 1 / norm x)" unfolding o_def continuous_on_eq_continuous_within
    apply(rule, rule continuous_at_within_inv[unfolded o_def inverse_eq_divide]) apply(rule continuous_at_within)
    apply(rule continuous_at_norm[unfolded o_def]) by auto
  thus ?thesis unfolding * ** using path_connected_punctured_universe[OF assms]
    by(auto intro!: path_connected_continuous_image continuous_on_intros continuous_on_mul) qed

lemma connected_sphere: "2 \<le> CARD('n) \<Longrightarrow> connected {x::real^'n. norm(x - a) = r}"
  using path_connected_sphere path_connected_imp_connected by auto

end
