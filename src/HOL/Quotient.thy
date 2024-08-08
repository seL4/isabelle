(*  Title:      HOL/Quotient.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

section \<open>Definition of Quotient Types\<close>

theory Quotient
imports Lifting
keywords
  "print_quotmapsQ3" "print_quotientsQ3" "print_quotconsts" :: diag and
  "quotient_type" :: thy_goal_defn and "/" and
  "quotient_definition" :: thy_goal_defn and
  "copy_bnf" :: thy_defn and
  "lift_bnf" :: thy_goal_defn
begin

text \<open>
  Basic definition for equivalence relations
  that are represented by predicates.
\<close>

text \<open>Composition of Relations\<close>

abbreviation
  rel_conj :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" (infixr "OOO" 75)
where
  "r1 OOO r2 \<equiv> r1 OO r2 OO r1"

lemma eq_comp_r:
  shows "((=) OOO R) = R"
  by (auto simp add: fun_eq_iff)

context includes lifting_syntax
begin

subsection \<open>Quotient Predicate\<close>

definition
  "Quotient3 R Abs Rep \<longleftrightarrow>
     (\<forall>a. Abs (Rep a) = a) \<and> (\<forall>a. R (Rep a) (Rep a)) \<and>
     (\<forall>r s. R r s \<longleftrightarrow> R r r \<and> R s s \<and> Abs r = Abs s)"

lemma Quotient3I:
  assumes "\<And>a. Abs (Rep a) = a"
    and "\<And>a. R (Rep a) (Rep a)"
    and "\<And>r s. R r s \<longleftrightarrow> R r r \<and> R s s \<and> Abs r = Abs s"
  shows "Quotient3 R Abs Rep"
  using assms unfolding Quotient3_def by blast

context
  fixes R Abs Rep
  assumes a: "Quotient3 R Abs Rep"
begin

lemma Quotient3_abs_rep:
  "Abs (Rep a) = a"
  using a
  unfolding Quotient3_def
  by simp

lemma Quotient3_rep_reflp:
  "R (Rep a) (Rep a)"
  using a
  unfolding Quotient3_def
  by blast

lemma Quotient3_rel:
  "R r r \<and> R s s \<and> Abs r = Abs s \<longleftrightarrow> R r s" \<comment> \<open>orientation does not loop on rewriting\<close>
  using a
  unfolding Quotient3_def
  by blast

lemma Quotient3_refl1:
  "R r s \<Longrightarrow> R r r"
  using a unfolding Quotient3_def
  by fast

lemma Quotient3_refl2:
  "R r s \<Longrightarrow> R s s"
  using a unfolding Quotient3_def
  by fast

lemma Quotient3_rel_rep:
  "R (Rep a) (Rep b) \<longleftrightarrow> a = b"
  using a
  unfolding Quotient3_def
  by metis

lemma Quotient3_rep_abs:
  "R r r \<Longrightarrow> R (Rep (Abs r)) r"
  using a unfolding Quotient3_def
  by blast

lemma Quotient3_rel_abs:
  "R r s \<Longrightarrow> Abs r = Abs s"
  using a unfolding Quotient3_def
  by blast

lemma Quotient3_symp:
  "symp R"
  using a unfolding Quotient3_def using sympI by metis

lemma Quotient3_transp:
  "transp R"
  using a unfolding Quotient3_def using transpI by (metis (full_types))

lemma Quotient3_part_equivp:
  "part_equivp R"
  by (metis Quotient3_rep_reflp Quotient3_symp Quotient3_transp part_equivpI)

lemma abs_o_rep:
  "Abs \<circ> Rep = id"
  unfolding fun_eq_iff
  by (simp add: Quotient3_abs_rep)

lemma equals_rsp:
  assumes b: "R xa xb" "R ya yb"
  shows "R xa ya = R xb yb"
  using b Quotient3_symp Quotient3_transp
  by (blast elim: sympE transpE)

lemma rep_abs_rsp:
  assumes b: "R x1 x2"
  shows "R x1 (Rep (Abs x2))"
  using b Quotient3_rel Quotient3_abs_rep Quotient3_rep_reflp
  by metis

lemma rep_abs_rsp_left:
  assumes b: "R x1 x2"
  shows "R (Rep (Abs x1)) x2"
  using b Quotient3_rel Quotient3_abs_rep Quotient3_rep_reflp
  by metis

end

lemma identity_quotient3:
  "Quotient3 (=) id id"
  unfolding Quotient3_def id_def
  by blast

lemma fun_quotient3:
  assumes q1: "Quotient3 R1 abs1 rep1"
  and     q2: "Quotient3 R2 abs2 rep2"
  shows "Quotient3 (R1 ===> R2) (rep1 ---> abs2) (abs1 ---> rep2)"
proof -
  have "(rep1 ---> abs2) ((abs1 ---> rep2) a) = a" for a
    using q1 q2 by (simp add: Quotient3_def fun_eq_iff)
  moreover
  have "(R1 ===> R2) ((abs1 ---> rep2) a) ((abs1 ---> rep2) a)" for a
    by (rule rel_funI)
       (use q1 q2 Quotient3_rel_abs [of R1 abs1 rep1] Quotient3_rel_rep [of R2 abs2 rep2]
         in \<open>simp (no_asm) add: Quotient3_def, simp\<close>)
  moreover
  have "(R1 ===> R2) r s = ((R1 ===> R2) r r \<and> (R1 ===> R2) s s \<and>
        (rep1 ---> abs2) r  = (rep1 ---> abs2) s)" for r s
  proof -
    have "(R1 ===> R2) r s \<Longrightarrow> (R1 ===> R2) r r" unfolding rel_fun_def
      using Quotient3_part_equivp[OF q1] Quotient3_part_equivp[OF q2]
      by (metis (full_types) part_equivp_def)
    moreover have "(R1 ===> R2) r s \<Longrightarrow> (R1 ===> R2) s s" unfolding rel_fun_def
      using Quotient3_part_equivp[OF q1] Quotient3_part_equivp[OF q2]
      by (metis (full_types) part_equivp_def)
    moreover have "(R1 ===> R2) r s \<Longrightarrow> (rep1 ---> abs2) r  = (rep1 ---> abs2) s"
      by (auto simp add: rel_fun_def fun_eq_iff)
        (use q1 q2 in \<open>unfold Quotient3_def, metis\<close>)
    moreover have "((R1 ===> R2) r r \<and> (R1 ===> R2) s s \<and>
        (rep1 ---> abs2) r  = (rep1 ---> abs2) s) \<Longrightarrow> (R1 ===> R2) r s"
      by (auto simp add: rel_fun_def fun_eq_iff)
        (use q1 q2 in \<open>unfold Quotient3_def, metis map_fun_apply\<close>)
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis by (intro Quotient3I) (assumption+)
qed

lemma lambda_prs:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep1 ---> Abs2) (\<lambda>x. Rep2 (f (Abs1 x))) = (\<lambda>x. f x)"
  unfolding fun_eq_iff
  using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2]
  by simp

lemma lambda_prs1:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep1 ---> Abs2) (\<lambda>x. (Abs1 ---> Rep2) f x) = (\<lambda>x. f x)"
  unfolding fun_eq_iff
  using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2]
  by simp

text\<open>
  In the following theorem R1 can be instantiated with anything,
  but we know some of the types of the Rep and Abs functions;
  so by solving Quotient assumptions we can get a unique R1 that
  will be provable; which is why we need to use \<open>apply_rsp\<close> and
  not the primed version\<close>

lemma apply_rspQ3:
  fixes f g::"'a \<Rightarrow> 'c"
  assumes q: "Quotient3 R1 Abs1 Rep1"
  and     a: "(R1 ===> R2) f g" "R1 x y"
  shows "R2 (f x) (g y)"
  using a by (auto elim: rel_funE)

lemma apply_rspQ3'':
  assumes "Quotient3 R Abs Rep"
  and "(R ===> S) f f"
  shows "S (f (Rep x)) (f (Rep x))"
proof -
  from assms(1) have "R (Rep x) (Rep x)" by (rule Quotient3_rep_reflp)
  then show ?thesis using assms(2) by (auto intro: apply_rsp')
qed

subsection \<open>lemmas for regularisation of ball and bex\<close>

lemma ball_reg_eqv:
  fixes P :: "'a \<Rightarrow> bool"
  assumes a: "equivp R"
  shows "Ball (Respects R) P = (All P)"
  using a
  unfolding equivp_def
  by (auto simp add: in_respects)

lemma bex_reg_eqv:
  fixes P :: "'a \<Rightarrow> bool"
  assumes a: "equivp R"
  shows "Bex (Respects R) P = (Ex P)"
  using a
  unfolding equivp_def
  by (auto simp add: in_respects)

lemma ball_reg_right:
  assumes a: "\<And>x. x \<in> R \<Longrightarrow> P x \<longrightarrow> Q x"
  shows "All P \<longrightarrow> Ball R Q"
  using a by fast

lemma bex_reg_left:
  assumes a: "\<And>x. x \<in> R \<Longrightarrow> Q x \<longrightarrow> P x"
  shows "Bex R Q \<longrightarrow> Ex P"
  using a by fast

lemma ball_reg_left:
  assumes a: "equivp R"
  shows "(\<And>x. (Q x \<longrightarrow> P x)) \<Longrightarrow> Ball (Respects R) Q \<longrightarrow> All P"
  using a by (metis equivp_reflp in_respects)

lemma bex_reg_right:
  assumes a: "equivp R"
  shows "(\<And>x. (Q x \<longrightarrow> P x)) \<Longrightarrow> Ex Q \<longrightarrow> Bex (Respects R) P"
  using a by (metis equivp_reflp in_respects)

lemma ball_reg_eqv_range:
  fixes P::"'a \<Rightarrow> bool"
  and x::"'a"
  assumes a: "equivp R2"
  shows "(Ball (Respects (R1 ===> R2)) (\<lambda>f. P (f x)) = All (\<lambda>f. P (f x)))"
proof (intro allI iffI)
  fix f
  assume "\<forall>f \<in> Respects (R1 ===> R2). P (f x)"
  moreover have "(\<lambda>y. f x) \<in> Respects (R1 ===> R2)"
    using a equivp_reflp_symp_transp[of "R2"]
    by(auto simp add: in_respects rel_fun_def elim: equivpE reflpE)
  ultimately show "P (f x)"
    by auto
qed auto

lemma bex_reg_eqv_range:
  assumes a: "equivp R2"
  shows   "(Bex (Respects (R1 ===> R2)) (\<lambda>f. P (f x)) = Ex (\<lambda>f. P (f x)))"
proof -
  have "(\<lambda>y. f x) \<in> Respects (R1 ===> R2)" for f
    using a equivp_reflp_symp_transp[of "R2"]
    by (auto simp add: Respects_def in_respects rel_fun_def elim: equivpE reflpE)
  then show ?thesis
    by auto
qed

(* Next four lemmas are unused *)
lemma all_reg:
  assumes a: "\<forall>x :: 'a. (P x \<longrightarrow> Q x)"
  and     b: "All P"
  shows "All Q"
  using a b by fast

lemma ex_reg:
  assumes a: "\<forall>x :: 'a. (P x \<longrightarrow> Q x)"
  and     b: "Ex P"
  shows "Ex Q"
  using a b by fast

lemma ball_reg:
  assumes a: "\<forall>x :: 'a. (x \<in> R \<longrightarrow> P x \<longrightarrow> Q x)"
  and     b: "Ball R P"
  shows "Ball R Q"
  using a b by fast

lemma bex_reg:
  assumes a: "\<forall>x :: 'a. (x \<in> R \<longrightarrow> P x \<longrightarrow> Q x)"
  and     b: "Bex R P"
  shows "Bex R Q"
  using a b by fast


lemma ball_all_comm:
  assumes "\<And>y. (\<forall>x\<in>P. A x y) \<longrightarrow> (\<forall>x. B x y)"
  shows "(\<forall>x\<in>P. \<forall>y. A x y) \<longrightarrow> (\<forall>x. \<forall>y. B x y)"
  using assms by auto

lemma bex_ex_comm:
  assumes "(\<exists>y. \<exists>x. A x y) \<longrightarrow> (\<exists>y. \<exists>x\<in>P. B x y)"
  shows "(\<exists>x. \<exists>y. A x y) \<longrightarrow> (\<exists>x\<in>P. \<exists>y. B x y)"
  using assms by auto

subsection \<open>Bounded abstraction\<close>

definition
  Babs :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where
  "x \<in> p \<Longrightarrow> Babs p m x = m x"

lemma babs_rsp:
  assumes q: "Quotient3 R1 Abs1 Rep1"
      and a: "(R1 ===> R2) f g"
    shows "(R1 ===> R2) (Babs (Respects R1) f) (Babs (Respects R1) g)"
proof
  fix x y
  assume "R1 x y"
  then have "x \<in> Respects R1 \<and> y \<in> Respects R1"
    unfolding in_respects rel_fun_def using Quotient3_rel[OF q]by metis
  then show "R2 (Babs (Respects R1) f x) (Babs (Respects R1) g y)"
  using \<open>R1 x y\<close> a by (simp add: Babs_def rel_fun_def)
qed

lemma babs_prs:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
shows "((Rep1 ---> Abs2) (Babs (Respects R1) ((Abs1 ---> Rep2) f))) = f"
proof -
  have "Abs2 (Babs (Respects R1) ((Abs1 ---> Rep2) f) (Rep1 x)) = f x" for x
  proof -
    have "Rep1 x \<in> Respects R1"
      by (simp add: in_respects Quotient3_rel_rep[OF q1])
    then show ?thesis
      by (simp add: Babs_def Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2])
  qed
  then show ?thesis
    by force
qed

lemma babs_simp:
  assumes q: "Quotient3 R1 Abs Rep"
  shows "((R1 ===> R2) (Babs (Respects R1) f) (Babs (Respects R1) g)) = ((R1 ===> R2) f g)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding rel_fun_def by (metis Babs_def in_respects  Quotient3_rel[OF q])
qed (simp add: babs_rsp[OF q])

text \<open>If a user proves that a particular functional relation
   is an equivalence, this may be useful in regularising\<close>
lemma babs_reg_eqv:
  shows "equivp R \<Longrightarrow> Babs (Respects R) P = P"
  by (simp add: fun_eq_iff Babs_def in_respects equivp_reflp)


(* 3 lemmas needed for proving repabs_inj *)
lemma ball_rsp:
  assumes a: "(R ===> (=)) f g"
  shows "Ball (Respects R) f = Ball (Respects R) g"
  using a by (auto simp add: Ball_def in_respects elim: rel_funE)

lemma bex_rsp:
  assumes a: "(R ===> (=)) f g"
  shows "(Bex (Respects R) f = Bex (Respects R) g)"
  using a by (auto simp add: Bex_def in_respects elim: rel_funE)

lemma bex1_rsp:
  assumes a: "(R ===> (=)) f g"
  shows "Ex1 (\<lambda>x. x \<in> Respects R \<and> f x) = Ex1 (\<lambda>x. x \<in> Respects R \<and> g x)"
  using a by (auto elim: rel_funE simp add: Ex1_def in_respects)

text \<open>Two lemmas needed for cleaning of quantifiers\<close>

lemma all_prs:
  assumes a: "Quotient3 R absf repf"
  shows "Ball (Respects R) ((absf ---> id) f) = All f"
  using a unfolding Quotient3_def Ball_def in_respects id_apply comp_def map_fun_def
  by metis

lemma ex_prs:
  assumes a: "Quotient3 R absf repf"
  shows "Bex (Respects R) ((absf ---> id) f) = Ex f"
  using a unfolding Quotient3_def Bex_def in_respects id_apply comp_def map_fun_def
  by metis

subsection \<open>\<open>Bex1_rel\<close> quantifier\<close>

definition
  Bex1_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "Bex1_rel R P \<longleftrightarrow> (\<exists>x \<in> Respects R. P x) \<and> (\<forall>x \<in> Respects R. \<forall>y \<in> Respects R. ((P x \<and> P y) \<longrightarrow> (R x y)))"

lemma bex1_rel_aux:
  "\<lbrakk>\<forall>xa ya. R xa ya \<longrightarrow> x xa = y ya; Bex1_rel R x\<rbrakk> \<Longrightarrow> Bex1_rel R y"
  unfolding Bex1_rel_def
  by (metis in_respects)

lemma bex1_rel_aux2:
  "\<lbrakk>\<forall>xa ya. R xa ya \<longrightarrow> x xa = y ya; Bex1_rel R y\<rbrakk> \<Longrightarrow> Bex1_rel R x"
  unfolding Bex1_rel_def
  by (metis in_respects)

lemma bex1_rel_rsp:
  assumes a: "Quotient3 R absf repf"
  shows "((R ===> (=)) ===> (=)) (Bex1_rel R) (Bex1_rel R)"
  unfolding rel_fun_def by (metis bex1_rel_aux bex1_rel_aux2)

lemma ex1_prs:
  assumes "Quotient3 R absf repf"
  shows "((absf ---> id) ---> id) (Bex1_rel R) f = Ex1 f"
         (is "?lhs = ?rhs")
  using assms
  by (auto simp add: Bex1_rel_def Respects_def) (metis (full_types) Quotient3_def)+

lemma bex1_bexeq_reg:
  shows "(\<exists>!x\<in>Respects R. P x) \<longrightarrow> (Bex1_rel R (\<lambda>x. P x))"
  by (auto simp add: Ex1_def Bex1_rel_def Bex_def Ball_def in_respects)

lemma bex1_bexeq_reg_eqv:
  assumes a: "equivp R"
  shows "(\<exists>!x. P x) \<longrightarrow> Bex1_rel R P"
  using equivp_reflp[OF a]
  by (metis (full_types) Bex1_rel_def in_respects)

subsection \<open>Various respects and preserve lemmas\<close>

lemma quot_rel_rsp:
  assumes a: "Quotient3 R Abs Rep"
  shows "(R ===> R ===> (=)) R R"
  by (rule rel_funI)+ (meson assms equals_rsp)

lemma o_prs:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  and     q3: "Quotient3 R3 Abs3 Rep3"
  shows "((Abs2 ---> Rep3) ---> (Abs1 ---> Rep2) ---> (Rep1 ---> Abs3)) (\<circ>) = (\<circ>)"
  and   "(id ---> (Abs1 ---> id) ---> Rep1 ---> id) (\<circ>) = (\<circ>)"
  using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2] Quotient3_abs_rep[OF q3]
  by (simp_all add: fun_eq_iff)

lemma o_rsp:
  "((R2 ===> R3) ===> (R1 ===> R2) ===> (R1 ===> R3)) (\<circ>) (\<circ>)"
  "((=) ===> (R1 ===> (=)) ===> R1 ===> (=)) (\<circ>) (\<circ>)"
  by (force elim: rel_funE)+

lemma cond_prs:
  assumes a: "Quotient3 R absf repf"
  shows "absf (if a then repf b else repf c) = (if a then b else c)"
  using a unfolding Quotient3_def by auto

lemma if_prs:
  assumes q: "Quotient3 R Abs Rep"
  shows "(id ---> Rep ---> Rep ---> Abs) If = If"
  using Quotient3_abs_rep[OF q]
  by (auto simp add: fun_eq_iff)

lemma if_rsp:
  assumes q: "Quotient3 R Abs Rep"
  shows "((=) ===> R ===> R ===> R) If If"
  by force

lemma let_prs:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep2 ---> (Abs2 ---> Rep1) ---> Abs1) Let = Let"
  using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2]
  by (auto simp add: fun_eq_iff)

lemma let_rsp:
  shows "(R1 ===> (R1 ===> R2) ===> R2) Let Let"
  by (force elim: rel_funE)

lemma id_rsp:
  shows "(R ===> R) id id"
  by auto

lemma id_prs:
  assumes a: "Quotient3 R Abs Rep"
  shows "(Rep ---> Abs) id = id"
  by (simp add: fun_eq_iff Quotient3_abs_rep [OF a])

end

locale quot_type =
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and   Abs :: "'a set \<Rightarrow> 'b"
  and   Rep :: "'b \<Rightarrow> 'a set"
  assumes equivp: "part_equivp R"
  and     rep_prop: "\<And>y. \<exists>x. R x x \<and> Rep y = Collect (R x)"
  and     rep_inverse: "\<And>x. Abs (Rep x) = x"
  and     abs_inverse: "\<And>c. (\<exists>x. ((R x x) \<and> (c = Collect (R x)))) \<Longrightarrow> (Rep (Abs c)) = c"
  and     rep_inject: "\<And>x y. (Rep x = Rep y) = (x = y)"
begin

definition
  abs :: "'a \<Rightarrow> 'b"
where
  "abs x = Abs (Collect (R x))"

definition
  rep :: "'b \<Rightarrow> 'a"
where
  "rep a = (SOME x. x \<in> Rep a)"

lemma some_collect:
  assumes "R r r"
  shows "R (SOME x. x \<in> Collect (R r)) = R r"
  by simp (metis assms exE_some equivp[simplified part_equivp_def])

lemma Quotient: "Quotient3 R abs rep"
  unfolding Quotient3_def abs_def rep_def
proof (intro conjI allI)
  fix a r s
  show x: "R (SOME x. x \<in> Rep a) (SOME x. x \<in> Rep a)" proof -
    obtain x where r: "R x x" and rep: "Rep a = Collect (R x)" using rep_prop[of a] by auto
    have "R (SOME x. x \<in> Rep a) x"  using r rep some_collect by metis
    then have "R x (SOME x. x \<in> Rep a)" using part_equivp_symp[OF equivp] by fast
    then show "R (SOME x. x \<in> Rep a) (SOME x. x \<in> Rep a)"
      using part_equivp_transp[OF equivp] by (metis \<open>R (SOME x. x \<in> Rep a) x\<close>)
  qed
  have "Collect (R (SOME x. x \<in> Rep a)) = (Rep a)" by (metis some_collect rep_prop)
  then show "Abs (Collect (R (SOME x. x \<in> Rep a))) = a" using rep_inverse by auto
  have "R r r \<Longrightarrow> R s s \<Longrightarrow> Abs (Collect (R r)) = Abs (Collect (R s)) \<longleftrightarrow> R r = R s"
  proof -
    assume "R r r" and "R s s"
    then have "Abs (Collect (R r)) = Abs (Collect (R s)) \<longleftrightarrow> Collect (R r) = Collect (R s)"
      by (metis abs_inverse)
    also have "Collect (R r) = Collect (R s) \<longleftrightarrow> (\<lambda>A x. x \<in> A) (Collect (R r)) = (\<lambda>A x. x \<in> A) (Collect (R s))"
      by (rule iffI) simp_all
    finally show "Abs (Collect (R r)) = Abs (Collect (R s)) \<longleftrightarrow> R r = R s" by simp
  qed
  then show "R r s \<longleftrightarrow> R r r \<and> R s s \<and> (Abs (Collect (R r)) = Abs (Collect (R s)))"
    using equivp[simplified part_equivp_def] by metis
qed

end

subsection \<open>Quotient composition\<close>

lemma OOO_quotient3:
  fixes R1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes Abs1 :: "'a \<Rightarrow> 'b" and Rep1 :: "'b \<Rightarrow> 'a"
  fixes Abs2 :: "'b \<Rightarrow> 'c" and Rep2 :: "'c \<Rightarrow> 'b"
  fixes R2' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes R2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes R1: "Quotient3 R1 Abs1 Rep1"
  assumes R2: "Quotient3 R2 Abs2 Rep2"
  assumes Abs1: "\<And>x y. R2' x y \<Longrightarrow> R1 x x \<Longrightarrow> R1 y y \<Longrightarrow> R2 (Abs1 x) (Abs1 y)"
  assumes Rep1: "\<And>x y. R2 x y \<Longrightarrow> R2' (Rep1 x) (Rep1 y)"
  shows "Quotient3 (R1 OO R2' OO R1) (Abs2 \<circ> Abs1) (Rep1 \<circ> Rep2)"
proof -
  have *: "(R1 OOO R2') r r \<and> (R1 OOO R2') s s \<and> (Abs2 \<circ> Abs1) r = (Abs2 \<circ> Abs1) s
           \<longleftrightarrow> (R1 OOO R2') r s" for r s
  proof (intro iffI conjI; clarify) 
    show "(R1 OOO R2') r s"
      if r: "R1 r a" "R2' a b" "R1 b r" and eq: "(Abs2 \<circ> Abs1) r = (Abs2 \<circ> Abs1) s" 
        and s: "R1 s c" "R2' c d" "R1 d s" for a b c d
    proof -
      have "R1 r (Rep1 (Abs1 r))"
        using r Quotient3_refl1 R1 rep_abs_rsp by fastforce
      moreover have "R2' (Rep1 (Abs1 r)) (Rep1 (Abs1 s))"
        using that
        by simp (metis (full_types) Rep1 Abs1 Quotient3_rel R2 Quotient3_refl1 [OF R1]
            Quotient3_refl2 [OF R1] Quotient3_rel_abs [OF R1])
      moreover have "R1 (Rep1 (Abs1 s)) s"
        by (metis s Quotient3_rel R1 rep_abs_rsp_left)
      ultimately show ?thesis
        by (metis relcomppI)
    qed
  next
    fix x y
    assume xy: "R1 r x" "R2' x y" "R1 y s"
    then have "R2 (Abs1 x) (Abs1 y)"
      by (iprover dest: Abs1 elim: Quotient3_refl1 [OF R1] Quotient3_refl2 [OF R1])
    then have "R2' (Rep1 (Abs1 x)) (Rep1 (Abs1 x))" "R2' (Rep1 (Abs1 y)) (Rep1 (Abs1 y))"
      by (simp_all add: Quotient3_refl1 [OF R2] Quotient3_refl2 [OF R2] Rep1)
    with \<open>R1 r x\<close> \<open>R1 y s\<close> show "(R1 OOO R2') r r" "(R1 OOO R2') s s"
      by (metis (full_types) Quotient3_def R1 relcompp.relcompI)+
    show "(Abs2 \<circ> Abs1) r = (Abs2 \<circ> Abs1) s"
      using xy by simp (metis (full_types) Abs1 Quotient3_rel R1 R2)
  qed
  show ?thesis
    apply (rule Quotient3I)
    using * apply (simp_all add: o_def Quotient3_abs_rep [OF R2] Quotient3_abs_rep [OF R1])
    apply (metis Quotient3_rep_reflp R1 R2 Rep1 relcompp.relcompI)
    done
qed

lemma OOO_eq_quotient3:
  fixes R1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes Abs1 :: "'a \<Rightarrow> 'b" and Rep1 :: "'b \<Rightarrow> 'a"
  fixes Abs2 :: "'b \<Rightarrow> 'c" and Rep2 :: "'c \<Rightarrow> 'b"
  assumes R1: "Quotient3 R1 Abs1 Rep1"
  assumes R2: "Quotient3 (=) Abs2 Rep2"
  shows "Quotient3 (R1 OOO (=)) (Abs2 \<circ> Abs1) (Rep1 \<circ> Rep2)"
using assms
by (rule OOO_quotient3) auto

subsection \<open>Quotient3 to Quotient\<close>

lemma Quotient3_to_Quotient:
  assumes "Quotient3 R Abs Rep"
    and "T \<equiv> \<lambda>x y. R x x \<and> Abs x = y"
  shows "Quotient R Abs Rep T"
  using assms unfolding Quotient3_def by (intro QuotientI) blast+

lemma Quotient3_to_Quotient_equivp:
  assumes q: "Quotient3 R Abs Rep"
    and T_def: "T \<equiv> \<lambda>x y. Abs x = y"
    and eR: "equivp R"
  shows "Quotient R Abs Rep T"
proof (intro QuotientI)
  show "Abs (Rep a) = a" for a
    using q by(rule Quotient3_abs_rep)
  show "R (Rep a) (Rep a)" for a
    using q by(rule Quotient3_rep_reflp)
  show "R r s = (R r r \<and> R s s \<and> Abs r = Abs s)" for r s
    using q by(rule Quotient3_rel[symmetric])
  show "T = (\<lambda>x y. R x x \<and> Abs x = y)"
    using T_def equivp_reflp[OF eR] by simp
qed

subsection \<open>ML setup\<close>

text \<open>Auxiliary data for the quotient package\<close>

named_theorems quot_equiv "equivalence relation theorems"
  and quot_respect "respectfulness theorems"
  and quot_preserve "preservation theorems"
  and id_simps "identity simp rules for maps"
  and quot_thm "quotient theorems"
ML_file \<open>Tools/Quotient/quotient_info.ML\<close>

declare [[mapQ3 "fun" = (rel_fun, fun_quotient3)]]

lemmas [quot_thm] = fun_quotient3
lemmas [quot_respect] = quot_rel_rsp if_rsp o_rsp let_rsp id_rsp
lemmas [quot_preserve] = if_prs o_prs let_prs id_prs
lemmas [quot_equiv] = identity_equivp


text \<open>Lemmas about simplifying id's.\<close>
lemmas [id_simps] =
  id_def[symmetric]
  map_fun_id
  id_apply
  id_o
  o_id
  eq_comp_r
  vimage_id

text \<open>Translation functions for the lifting process.\<close>
ML_file \<open>Tools/Quotient/quotient_term.ML\<close>


text \<open>Definitions of the quotient types.\<close>
ML_file \<open>Tools/Quotient/quotient_type.ML\<close>


text \<open>Definitions for quotient constants.\<close>
ML_file \<open>Tools/Quotient/quotient_def.ML\<close>


text \<open>
  An auxiliary constant for recording some information
  about the lifted theorem in a tactic.
\<close>
definition
  Quot_True :: "'a \<Rightarrow> bool"
where
  "Quot_True x \<longleftrightarrow> True"

lemma
  shows QT_all: "Quot_True (All P) \<Longrightarrow> Quot_True P"
  and   QT_ex:  "Quot_True (Ex P) \<Longrightarrow> Quot_True P"
  and   QT_ex1: "Quot_True (Ex1 P) \<Longrightarrow> Quot_True P"
  and   QT_lam: "Quot_True (\<lambda>x. P x) \<Longrightarrow> (\<And>x. Quot_True (P x))"
  and   QT_ext: "(\<And>x. Quot_True (a x) \<Longrightarrow> f x = g x) \<Longrightarrow> (Quot_True a \<Longrightarrow> f = g)"
  by (simp_all add: Quot_True_def ext)

lemma QT_imp: "Quot_True a \<equiv> Quot_True b"
  by (simp add: Quot_True_def)

context includes lifting_syntax
begin

text \<open>Tactics for proving the lifted theorems\<close>
ML_file \<open>Tools/Quotient/quotient_tacs.ML\<close>

end

subsection \<open>Methods / Interface\<close>

method_setup lifting =
  \<open>Attrib.thms >> (fn thms => fn ctxt =>
       SIMPLE_METHOD' (Quotient_Tacs.lift_tac ctxt [] thms))\<close>
  \<open>lift theorems to quotient types\<close>

method_setup lifting_setup =
  \<open>Attrib.thm >> (fn thm => fn ctxt =>
       SIMPLE_METHOD' (Quotient_Tacs.lift_procedure_tac ctxt [] thm))\<close>
  \<open>set up the three goals for the quotient lifting procedure\<close>

method_setup descending =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Quotient_Tacs.descend_tac ctxt []))\<close>
  \<open>decend theorems to the raw level\<close>

method_setup descending_setup =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Quotient_Tacs.descend_procedure_tac ctxt []))\<close>
  \<open>set up the three goals for the decending theorems\<close>

method_setup partiality_descending =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Quotient_Tacs.partiality_descend_tac ctxt []))\<close>
  \<open>decend theorems to the raw level\<close>

method_setup partiality_descending_setup =
  \<open>Scan.succeed (fn ctxt =>
       SIMPLE_METHOD' (Quotient_Tacs.partiality_descend_procedure_tac ctxt []))\<close>
  \<open>set up the three goals for the decending theorems\<close>

method_setup regularize =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Quotient_Tacs.regularize_tac ctxt))\<close>
  \<open>prove the regularization goals from the quotient lifting procedure\<close>

method_setup injection =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Quotient_Tacs.all_injection_tac ctxt))\<close>
  \<open>prove the rep/abs injection goals from the quotient lifting procedure\<close>

method_setup cleaning =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Quotient_Tacs.clean_tac ctxt))\<close>
  \<open>prove the cleaning goals from the quotient lifting procedure\<close>

attribute_setup quot_lifted =
  \<open>Scan.succeed Quotient_Tacs.lifted_attrib\<close>
  \<open>lift theorems to quotient types\<close>

no_notation
  rel_conj (infixr "OOO" 75)

section \<open>Lifting of BNFs\<close>

lemma sum_insert_Inl_unit: "x \<in> A \<Longrightarrow> (\<And>y. x = Inr y \<Longrightarrow> Inr y \<in> B) \<Longrightarrow> x \<in> insert (Inl ()) B"
  by (cases x) (simp_all)

lemma lift_sum_unit_vimage_commute:
  "insert (Inl ()) (Inr ` f -` A) = map_sum id f -` insert (Inl ()) (Inr ` A)"
  by (auto simp: map_sum_def split: sum.splits)

lemma insert_Inl_int_map_sum_unit: "insert (Inl ()) A \<inter> range (map_sum id f) \<noteq> {}"
  by (auto simp: map_sum_def split: sum.splits)

lemma image_map_sum_unit_subset:
  "A \<subseteq> insert (Inl ()) (Inr ` B) \<Longrightarrow> map_sum id f ` A \<subseteq> insert (Inl ()) (Inr ` f ` B)"
  by auto

lemma subset_lift_sum_unitD: "A \<subseteq> insert (Inl ()) (Inr ` B) \<Longrightarrow> Inr x \<in> A \<Longrightarrow> x \<in> B"
  unfolding insert_def by auto

lemma UNIV_sum_unit_conv: "insert (Inl ()) (range Inr) = UNIV"
  unfolding UNIV_sum UNIV_unit image_insert image_empty Un_insert_left sup_bot.left_neutral..

lemma subset_vimage_image_subset: "A \<subseteq> f -` B \<Longrightarrow> f ` A \<subseteq> B"
  by auto

lemma relcompp_mem_Grp_neq_bot:
  "A \<inter> range f \<noteq> {} \<Longrightarrow> (\<lambda>x y. x \<in> A \<and> y \<in> A) OO (Grp UNIV f)\<inverse>\<inverse> \<noteq> bot"
  unfolding Grp_def relcompp_apply fun_eq_iff by blast

lemma comp_projr_Inr: "projr \<circ> Inr = id"
  by auto

lemma in_rel_sum_in_image_projr:
  "B \<subseteq> {(x,y). rel_sum ((=) :: unit \<Rightarrow> unit \<Rightarrow> bool) A x y} \<Longrightarrow>
   Inr ` C = fst ` B \<Longrightarrow> snd ` B = Inr ` D \<Longrightarrow> map_prod projr projr ` B \<subseteq> {(x,y). A x y}"
  by (force simp: projr_def image_iff dest!: spec[of _ "Inl ()"]  split: sum.splits)

lemma subset_rel_sumI: "B \<subseteq> {(x,y). A x y} \<Longrightarrow> rel_sum ((=) :: unit => unit => bool) A
    (if x \<in> B then Inr (fst x) else Inl ())
    (if x \<in> B then Inr (snd x) else Inl ())"
  by auto

lemma relcompp_eq_Grp_neq_bot: "(=) OO (Grp UNIV f)\<inverse>\<inverse> \<noteq> bot"
  unfolding Grp_def relcompp_apply fun_eq_iff by blast

lemma rel_fun_rel_OO1: "(rel_fun Q (rel_fun R (=))) A B \<Longrightarrow> conversep Q OO A OO R \<le> B"
  by (auto simp: rel_fun_def)

lemma rel_fun_rel_OO2: "(rel_fun Q (rel_fun R (=))) A B \<Longrightarrow> Q OO B OO conversep R \<le> A"
  by (auto simp: rel_fun_def)

lemma rel_sum_eq2_nonempty: "rel_sum (=) A OO rel_sum (=) B \<noteq> bot"
  by (auto simp: fun_eq_iff relcompp_apply intro!: exI[of _ "Inl _"])

lemma rel_sum_eq3_nonempty: "rel_sum (=) A OO (rel_sum (=) B OO rel_sum (=) C) \<noteq> bot"
  by (auto simp: fun_eq_iff relcompp_apply intro!: exI[of _ "Inl _"])

lemma hypsubst: "A = B \<Longrightarrow> x \<in> B \<Longrightarrow> (x \<in> A \<Longrightarrow> P) \<Longrightarrow> P" by simp

lemma Quotient_crel_quotient: "Quotient R Abs Rep T \<Longrightarrow> equivp R \<Longrightarrow> T \<equiv> (\<lambda>x y. Abs x = y)"
  by (drule Quotient_cr_rel) (auto simp: fun_eq_iff equivp_reflp intro!: eq_reflection)

lemma Quotient_crel_typedef: "Quotient (eq_onp P) Abs Rep T \<Longrightarrow> T \<equiv> (\<lambda>x y. x = Rep y)"
  unfolding Quotient_def
  by (auto 0 4 simp: fun_eq_iff eq_onp_def intro: sym intro!: eq_reflection)

lemma Quotient_crel_typecopy: "Quotient (=) Abs Rep T \<Longrightarrow> T \<equiv> (\<lambda>x y. x = Rep y)"
  by (subst (asm) eq_onp_True[symmetric]) (rule Quotient_crel_typedef)

lemma equivp_add_relconj:
  assumes equiv: "equivp R" "equivp R'" and le: "S OO T OO U \<le> R OO STU OO R'"
  shows "R OO S OO T OO U OO R' \<le> R OO STU OO R'"
proof -
  have trans: "R OO R \<le> R" "R' OO R' \<le> R'"
    using equiv unfolding equivp_reflp_symp_transp transp_relcompp by blast+
  have "R OO S OO T OO U OO R' = R OO (S OO T OO U) OO R'"
    unfolding relcompp_assoc ..
  also have "\<dots> \<le> R OO (R OO STU OO R') OO R'"
    by (intro le relcompp_mono order_refl)
  also have "\<dots> \<le> (R OO R) OO STU OO (R' OO R')"
    unfolding relcompp_assoc ..
  also have "\<dots> \<le> R OO STU OO R'"
    by (intro trans relcompp_mono order_refl)
  finally show ?thesis .
qed

lemma Grp_conversep_eq_onp: "((BNF_Def.Grp UNIV f)\<inverse>\<inverse> OO BNF_Def.Grp UNIV f) = eq_onp (\<lambda>x. x \<in> range f)"
  by (auto simp: fun_eq_iff Grp_def eq_onp_def image_iff)

lemma Grp_conversep_nonempty: "(BNF_Def.Grp UNIV f)\<inverse>\<inverse> OO BNF_Def.Grp UNIV f \<noteq> bot"
  by (auto simp: fun_eq_iff Grp_def)

lemma relcomppI2: "r a b \<Longrightarrow> s b c \<Longrightarrow> t c d \<Longrightarrow> (r OO s OO t) a d"
  by (auto)

lemma rel_conj_eq_onp: "equivp R \<Longrightarrow> rel_conj R (eq_onp P) \<le> R"
  by (auto simp: eq_onp_def transp_def equivp_def)

lemma Quotient_Quotient3: "Quotient R Abs Rep T \<Longrightarrow> Quotient3 R Abs Rep"
  unfolding Quotient_def Quotient3_def by blast

lemma Quotient_reflp_imp_equivp: "Quotient R Abs Rep T \<Longrightarrow> reflp R \<Longrightarrow> equivp R"
  using Quotient_symp Quotient_transp equivpI by blast

lemma Quotient_eq_onp_typedef:
  "Quotient (eq_onp P) Abs Rep cr \<Longrightarrow> type_definition Rep Abs {x. P x}"
  unfolding Quotient_def eq_onp_def
  by unfold_locales auto

lemma Quotient_eq_onp_type_copy:
  "Quotient (=) Abs Rep cr \<Longrightarrow> type_definition Rep Abs UNIV"
  unfolding Quotient_def eq_onp_def
  by unfold_locales auto

ML_file \<open>Tools/BNF/bnf_lift.ML\<close>

hide_fact
  sum_insert_Inl_unit lift_sum_unit_vimage_commute insert_Inl_int_map_sum_unit
  image_map_sum_unit_subset subset_lift_sum_unitD UNIV_sum_unit_conv subset_vimage_image_subset
  relcompp_mem_Grp_neq_bot comp_projr_Inr in_rel_sum_in_image_projr subset_rel_sumI
  relcompp_eq_Grp_neq_bot rel_fun_rel_OO1 rel_fun_rel_OO2 rel_sum_eq2_nonempty rel_sum_eq3_nonempty
  hypsubst equivp_add_relconj Grp_conversep_eq_onp Grp_conversep_nonempty relcomppI2 rel_conj_eq_onp
  Quotient_reflp_imp_equivp Quotient_Quotient3

end
