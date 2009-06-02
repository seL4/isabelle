
(* Author: Florian Haftmann, TU Muenchen *)

header {* Comparing growth of functions on natural numbers by a preorder relation *}

theory Landau
imports Main Preorder
begin

text {*
  We establish a preorder releation @{text "\<lesssim>"} on functions
  from @{text "\<nat>"} to @{text "\<nat>"} such that @{text "f \<lesssim> g \<longleftrightarrow> f \<in> O(g)"}.
*}

subsection {* Auxiliary *}

lemma Ex_All_bounded:
  fixes n :: nat
  assumes "\<exists>n. \<forall>m\<ge>n. P m"
  obtains m where "m \<ge> n" and "P m"
proof -
  from assms obtain q where m_q: "\<forall>m\<ge>q. P m" ..
  let ?m = "max q n"
  have "?m \<ge> n" by auto
  moreover from m_q have "P ?m" by auto
  ultimately show thesis ..
qed
    

subsection {* The @{text "\<lesssim>"} relation *}

definition less_eq_fun :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" (infix "\<lesssim>" 50) where
  "f \<lesssim> g \<longleftrightarrow> (\<exists>c n. \<forall>m\<ge>n. f m \<le> Suc c * g m)"

lemma less_eq_fun_intro:
  assumes "\<exists>c n. \<forall>m\<ge>n. f m \<le> Suc c * g m"
  shows "f \<lesssim> g"
  unfolding less_eq_fun_def by (rule assms)

lemma less_eq_fun_not_intro:
  assumes "\<And>c n. \<exists>m\<ge>n. Suc c * g m < f m"
  shows "\<not> f \<lesssim> g"
  using assms unfolding less_eq_fun_def linorder_not_le [symmetric]
  by blast

lemma less_eq_fun_elim:
  assumes "f \<lesssim> g"
  obtains n c where "\<And>m. m \<ge> n \<Longrightarrow> f m \<le> Suc c * g m"
  using assms unfolding less_eq_fun_def by blast

lemma less_eq_fun_not_elim:
  assumes "\<not> f \<lesssim> g"
  obtains m where "m \<ge> n" and "Suc c * g m < f m"
  using assms unfolding less_eq_fun_def linorder_not_le [symmetric]
  by blast

lemma less_eq_fun_refl:
  "f \<lesssim> f"
proof (rule less_eq_fun_intro)
  have "\<exists>n. \<forall>m\<ge>n. f m \<le> Suc 0 * f m" by auto
  then show "\<exists>c n. \<forall>m\<ge>n. f m \<le> Suc c * f m" by blast
qed

lemma less_eq_fun_trans:
  assumes f_g: "f \<lesssim> g" and g_h: "g \<lesssim> h"
  shows f_h: "f \<lesssim> h"
proof -
  from f_g obtain n\<^isub>1 c\<^isub>1
    where P1: "\<And>m. m \<ge> n\<^isub>1 \<Longrightarrow> f m \<le> Suc c\<^isub>1 * g m"
  by (erule less_eq_fun_elim)
  moreover from g_h obtain n\<^isub>2 c\<^isub>2
    where P2: "\<And>m. m \<ge> n\<^isub>2 \<Longrightarrow> g m \<le> Suc c\<^isub>2 * h m"
  by (erule less_eq_fun_elim)
  ultimately have "\<And>m. m \<ge> max n\<^isub>1 n\<^isub>2 \<Longrightarrow> f m \<le> Suc c\<^isub>1 * g m \<and> g m \<le> Suc c\<^isub>2 * h m"
  by auto
  moreover {
    fix k l r :: nat
    assume k_l: "k \<le> Suc c\<^isub>1 * l" and l_r: "l \<le> Suc c\<^isub>2 * r"
    from l_r have "Suc c\<^isub>1 * l \<le> (Suc c\<^isub>1 * Suc c\<^isub>2) * r"
    by (auto simp add: mult_le_cancel_left mult_assoc simp del: times_nat.simps mult_Suc_right)
    with k_l have "k \<le> (Suc c\<^isub>1 * Suc c\<^isub>2) * r" by (rule preorder_class.order_trans)
  }
  ultimately have "\<And>m. m \<ge> max n\<^isub>1 n\<^isub>2 \<Longrightarrow> f m \<le> (Suc c\<^isub>1 * Suc c\<^isub>2) * h m" by auto
  then have "\<And>m. m \<ge> max n\<^isub>1 n\<^isub>2 \<Longrightarrow> f m \<le> Suc ((Suc c\<^isub>1 * Suc c\<^isub>2) - 1) * h m" by auto
  then show ?thesis unfolding less_eq_fun_def by blast
qed


subsection {* The @{text "\<approx>"} relation, the equivalence relation induced by @{text "\<lesssim>"} *}

definition equiv_fun :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" (infix "\<cong>" 50) where
  "f \<cong> g \<longleftrightarrow> (\<exists>d c n. \<forall>m\<ge>n. g m \<le> Suc d * f m \<and> f m \<le> Suc c * g m)"

lemma equiv_fun_intro:
  assumes "\<exists>d c n. \<forall>m\<ge>n. g m \<le> Suc d * f m \<and> f m \<le> Suc c * g m"
  shows "f \<cong> g"
  unfolding equiv_fun_def by (rule assms)

lemma equiv_fun_not_intro:
  assumes "\<And>d c n. \<exists>m\<ge>n. Suc d * f m < g m \<or> Suc c * g m < f m"
  shows "\<not> f \<cong> g"
  unfolding equiv_fun_def
  by (auto simp add: assms linorder_not_le
    simp del: times_nat.simps mult_Suc_right)

lemma equiv_fun_elim:
  assumes "f \<cong> g"
  obtains n d c
    where "\<And>m. m \<ge> n \<Longrightarrow> g m \<le> Suc d * f m \<and> f m \<le> Suc c * g m"
  using assms unfolding equiv_fun_def by blast

lemma equiv_fun_not_elim:
  fixes n d c
  assumes "\<not> f \<cong> g"
  obtains m where "m \<ge> n"
    and "Suc d * f m < g m \<or> Suc c * g m < f m"
  using assms unfolding equiv_fun_def
  by (auto simp add: linorder_not_le, blast)

lemma equiv_fun_less_eq_fun:
  "f \<cong> g \<longleftrightarrow> f \<lesssim> g \<and> g \<lesssim> f"
proof
  assume x_y: "f \<cong> g"
  then obtain n d c
    where interv: "\<And>m. m \<ge> n \<Longrightarrow> g m \<le> Suc d * f m \<and> f m \<le> Suc c * g m"
  by (erule equiv_fun_elim)
  from interv have "\<exists>c n. \<forall>m \<ge> n. f m \<le> Suc c * g m" by auto
  then have f_g: "f \<lesssim> g" by (rule less_eq_fun_intro)
  from interv have "\<exists>d n. \<forall>m \<ge> n. g m \<le> Suc d * f m" by auto
  then have g_f: "g \<lesssim> f" by (rule less_eq_fun_intro)
  from f_g g_f show "f \<lesssim> g \<and> g \<lesssim> f" by auto
next
  assume assm: "f \<lesssim> g \<and> g \<lesssim> f"
  from assm less_eq_fun_elim obtain c n\<^isub>1 where
    bound1: "\<And>m. m \<ge> n\<^isub>1 \<Longrightarrow> f m \<le> Suc c * g m" 
    by blast
  from assm less_eq_fun_elim obtain d n\<^isub>2 where
    bound2: "\<And>m. m \<ge> n\<^isub>2 \<Longrightarrow> g m \<le> Suc d * f m"
    by blast
  from bound2 have "\<And>m. m \<ge> max n\<^isub>1 n\<^isub>2 \<Longrightarrow> g m \<le> Suc d * f m"
  by auto
  with bound1
    have "\<forall>m \<ge> max n\<^isub>1 n\<^isub>2. g m \<le> Suc d * f m \<and> f m \<le> Suc c * g m"
    by auto
  then
    have "\<exists>d c n. \<forall>m\<ge>n. g m \<le> Suc d * f m \<and> f m \<le> Suc c * g m"
    by blast
  then show "f \<cong> g" by (rule equiv_fun_intro)
qed

subsection {* The @{text "\<prec>"} relation, the strict part of @{text "\<lesssim>"} *}

definition less_fun :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" (infix "\<prec>" 50) where
  "f \<prec> g \<longleftrightarrow> f \<lesssim> g \<and> \<not> g \<lesssim> f"

lemma less_fun_intro:
  assumes "\<And>c. \<exists>n. \<forall>m\<ge>n. Suc c * f m < g m"
  shows "f \<prec> g"
proof (unfold less_fun_def, rule conjI)
  from assms obtain n
    where "\<forall>m\<ge>n. Suc 0 * f m < g m" ..
  then have "\<forall>m\<ge>n. f m \<le> Suc 0 * g m" by auto
  then have "\<exists>c n. \<forall>m\<ge>n. f m \<le> Suc c * g m" by blast
  then show "f \<lesssim> g" by (rule less_eq_fun_intro)
next
  show "\<not> g \<lesssim> f"
  proof (rule less_eq_fun_not_intro)
    fix c n :: nat
    from assms have "\<exists>n. \<forall>m\<ge>n. Suc c * f m < g m" by blast
    then obtain m where "m \<ge> n" and "Suc c * f m < g m"
      by (rule Ex_All_bounded)
    then show "\<exists>m\<ge>n. Suc c * f m < g m" by blast
  qed
qed

text {*
  We would like to show (or refute) that @{text "f \<prec> g \<longleftrightarrow> f \<in> o(g)"},
  i.e.~@{prop "f \<prec> g \<longleftrightarrow> (\<forall>c. \<exists>n. \<forall>m>n. f m < Suc c * g m)"} but did not manage to
  do so.
*}


subsection {* Assert that @{text "\<lesssim>"} is ineed a preorder *}

interpretation fun_order: preorder_equiv less_eq_fun less_fun
  where "preorder_equiv.equiv less_eq_fun = equiv_fun"
proof -
  interpret preorder_equiv less_eq_fun less_fun proof
  qed (simp_all add: less_fun_def less_eq_fun_refl, auto intro: less_eq_fun_trans)
  show "preorder_equiv less_eq_fun less_fun" using preorder_equiv_axioms .
  show "preorder_equiv.equiv less_eq_fun = equiv_fun"
    by (simp add: expand_fun_eq equiv_def equiv_fun_less_eq_fun)
qed


subsection {* Simple examples *}

lemma "(\<lambda>_. n) \<lesssim> (\<lambda>n. n)"
proof (rule less_eq_fun_intro)
  show "\<exists>c q. \<forall>m\<ge>q. n \<le> Suc c * m"
  proof -
    have "\<forall>m\<ge>n. n \<le> Suc 0 * m" by simp
    then show ?thesis by blast
  qed
qed

lemma "(\<lambda>n. n) \<cong> (\<lambda>n. Suc k * n)"
proof (rule equiv_fun_intro)
  show "\<exists>d c n. \<forall>m\<ge>n. Suc k * m \<le> Suc d * m \<and> m \<le> Suc c * (Suc k * m)"
  proof -
    have "\<forall>m\<ge>n. Suc k * m \<le> Suc k * m \<and> m \<le> Suc c * (Suc k * m)" by simp
    then show ?thesis by blast
  qed
qed  

lemma "(\<lambda>_. n) \<prec> (\<lambda>n. n)"
proof (rule less_fun_intro)
  fix c
  show "\<exists>q. \<forall>m\<ge>q. Suc c * n < m"
  proof -
    have "\<forall>m\<ge>Suc c * n + 1. Suc c * n < m" by simp
    then show ?thesis by blast
  qed
qed

end
