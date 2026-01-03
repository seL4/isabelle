(*  Title:      HOL/Wfrec.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Konrad Slind
*)

section \<open>Well-Founded Recursion Combinator\<close>

theory Wfrec
  imports Wellfounded
begin

inductive wfrec_rel :: "('a \<times> 'a) set \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" for R F
  where wfrecI: "(\<And>z. (z, x) \<in> R \<Longrightarrow> wfrec_rel R F z (g z)) \<Longrightarrow> wfrec_rel R F x (F g x)"

definition cut :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b"
  where "cut f R x = (\<lambda>y. if (y, x) \<in> R then f y else undefined)"

definition adm_wf :: "('a \<times> 'a) set \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> bool"
  where "adm_wf R F \<longleftrightarrow> (\<forall>f g x. (\<forall>z. (z, x) \<in> R \<longrightarrow> f z = g z) \<longrightarrow> F f x = F g x)"

definition wfrec :: "('a \<times> 'a) set \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "wfrec R F = (\<lambda>x. THE y. wfrec_rel R (\<lambda>f x. F (cut f R x) x) x y)"

lemma cuts_eq: "(cut f R x = cut g R x) \<longleftrightarrow> (\<forall>y. (y, x) \<in> R \<longrightarrow> f y = g y)"
  by (simp add: fun_eq_iff cut_def)

lemma cut_apply: "(x, a) \<in> R \<Longrightarrow> cut f R a x = f x"
  by (simp add: cut_def)

text \<open>
  Inductive characterization of \<open>wfrec\<close> combinator; for details see:
  John Harrison, "Inductive definitions: automation and application".
\<close>

lemma theI_unique: "\<exists>!x. P x \<Longrightarrow> P x \<longleftrightarrow> x = The P"
  by (auto intro: the_equality[symmetric] theI)

lemma wfrec_unique:
  assumes "adm_wf R F" "wf R"
  shows "\<exists>!y. wfrec_rel R F x y"
  using \<open>wf R\<close>
proof induct
  define f where "f y = (THE z. wfrec_rel R F y z)" for y
  case (less x)
  then have "\<And>y z. (y, x) \<in> R \<Longrightarrow> wfrec_rel R F y z \<longleftrightarrow> z = f y"
    unfolding f_def by (rule theI_unique)
  with \<open>adm_wf R F\<close> show ?case
    by (subst wfrec_rel.simps) (auto simp: adm_wf_def)
qed

lemma adm_lemma: "adm_wf R (\<lambda>f x. F (cut f R x) x)"
  by (auto simp: adm_wf_def intro!: arg_cong[where f="\<lambda>x. F x y" for y] cuts_eq[THEN iffD2])

lemma wfrec: "wf R \<Longrightarrow> wfrec R F a = F (cut (wfrec R F) R a) a"
  apply (simp add: wfrec_def)
  apply (rule adm_lemma [THEN wfrec_unique, THEN the1_equality])
   apply assumption
  apply (rule wfrec_rel.wfrecI)
  apply (erule adm_lemma [THEN wfrec_unique, THEN theI'])
  done


text \<open>This form avoids giant explosions in proofs.  NOTE USE OF \<open>\<equiv>\<close>.\<close>
lemma def_wfrec: "f \<equiv> wfrec R F \<Longrightarrow> wf R \<Longrightarrow> f a = F (cut f R a) a"
  by (auto intro: wfrec)


subsubsection \<open>Well-founded recursion via genuine fixpoints\<close>

lemma wfrec_fixpoint:
  assumes wf: "wf R"
    and adm: "adm_wf R F"
  shows "wfrec R F = F (wfrec R F)"
proof (rule ext)
  fix x
  have "wfrec R F x = F (cut (wfrec R F) R x) x"
    using wfrec[of R F] wf by simp
  also
  have "\<And>y. (y, x) \<in> R \<Longrightarrow> cut (wfrec R F) R x y = wfrec R F y"
    by (auto simp add: cut_apply)
  then have "F (cut (wfrec R F) R x) x = F (wfrec R F) x"
    using adm adm_wf_def[of R F] by auto
  finally show "wfrec R F x = F (wfrec R F) x" .
qed

lemma wfrec_def_adm: "f \<equiv> wfrec R F \<Longrightarrow> wf R \<Longrightarrow> adm_wf R F \<Longrightarrow> f = F f"
  using wfrec_fixpoint by simp

text \<open>For completeness: uniqueness of fixed points\<close>

lemma fixp_same_if_wf_adm_wf:
  assumes "wf R" "adm_wf R F" "f = F f" "g = F g"
  shows "f = g"
proof
  fix x
  show "f x = g x"
  using \<open>wf R\<close> proof induction
    case (less u)
    with \<open>adm_wf R F\<close>
    have "F f u = F g u"
      by (simp add: adm_wf_def)
    with \<open>f = F f\<close> \<open>g = F g\<close>
    show "f u = g u"
      by auto
  qed
qed

corollary fixp_eq_wfrec_if_wf_adm_wf:
 "\<lbrakk> wf R; adm_wf R F; f = F f \<rbrakk> \<Longrightarrow> f = wfrec R F"
using wfrec_def_adm fixp_same_if_wf_adm_wf by blast


subsection \<open>Wellfoundedness of \<open>same_fst\<close>\<close>

definition same_fst :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('b \<times> 'b) set) \<Rightarrow> (('a \<times> 'b) \<times> ('a \<times> 'b)) set"
  where "same_fst P R = {((x', y'), (x, y)) . x' = x \<and> P x \<and> (y',y) \<in> R x}"
   \<comment> \<open>For \<^const>\<open>wfrec\<close> declarations where the first n parameters
       stay unchanged in the recursive call.\<close>

lemma same_fstI [intro!]: "P x \<Longrightarrow> (y', y) \<in> R x \<Longrightarrow> ((x, y'), (x, y)) \<in> same_fst P R"
  by (simp add: same_fst_def)

lemma wf_same_fst:
  assumes "\<And>x. P x \<Longrightarrow> wf (R x)"
  shows "wf (same_fst P R)"
proof -
  have "\<And>a b Q. \<forall>a b. (\<forall>x. P a \<and> (x, b) \<in> R a \<longrightarrow> Q (a, x)) \<longrightarrow> Q (a, b) \<Longrightarrow> Q (a, b)"
  proof -
    fix Q a b
    assume *: "\<forall>a b. (\<forall>x. P a \<and> (x,b) \<in> R a \<longrightarrow> Q (a,x)) \<longrightarrow> Q (a,b)"
    show "Q(a,b)"
    proof (cases "wf (R a)")
      case True
      then show ?thesis
        by (induction b rule: wf_induct_rule) (use * in blast)
    qed (use * assms in blast)
  qed
  then show ?thesis
    by (clarsimp simp add: wf_def same_fst_def)
qed

hide_const (open) cut

end
