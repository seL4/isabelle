(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Lexical order on functions\<close>

theory Fun_Lexorder
imports Main
begin

definition less_fun :: "('a::linorder \<Rightarrow> 'b::linorder) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "less_fun f g \<longleftrightarrow> (\<exists>k. f k < g k \<and> (\<forall>k' < k. f k' = g k'))"

lemma less_funI:
  assumes "\<exists>k. f k < g k \<and> (\<forall>k' < k. f k' = g k')"
  shows "less_fun f g"
  using assms by (simp add: less_fun_def)

lemma less_funE:
  assumes "less_fun f g"
  obtains k where "f k < g k" and "\<And>k'. k' < k \<Longrightarrow> f k' = g k'"
  using assms unfolding less_fun_def by blast

lemma less_fun_asym:
  assumes "less_fun f g"
  shows "\<not> less_fun g f"
proof
  from assms obtain k1 where k1: "f k1 < g k1" "\<And>k'. k' < k1 \<Longrightarrow> f k' = g k'"
    by (blast elim!: less_funE) 
  assume "less_fun g f" then obtain k2 where k2: "g k2 < f k2" "\<And>k'. k' < k2 \<Longrightarrow> g k' = f k'"
    by (blast elim!: less_funE) 
  show False proof (cases k1 k2 rule: linorder_cases)
    case equal with k1 k2 show False by simp
  next
    case less with k2 have "g k1 = f k1" by simp
    with k1 show False by simp
  next
    case greater with k1 have "f k2 = g k2" by simp
    with k2 show False by simp
  qed
qed

lemma less_fun_irrefl:
  "\<not> less_fun f f"
proof
  assume "less_fun f f"
  then obtain k where k: "f k < f k"
    by (blast elim!: less_funE)
  then show False by simp
qed

lemma less_fun_trans:
  assumes "less_fun f g" and "less_fun g h"
  shows "less_fun f h"
proof (rule less_funI)
  from `less_fun f g` obtain k1 where k1: "f k1 < g k1" "\<And>k'. k' < k1 \<Longrightarrow> f k' = g k'"
    by (blast elim!: less_funE) 
  from `less_fun g h` obtain k2 where k2: "g k2 < h k2" "\<And>k'. k' < k2 \<Longrightarrow> g k' = h k'"
    by (blast elim!: less_funE) 
  show "\<exists>k. f k < h k \<and> (\<forall>k'<k. f k' = h k')"
  proof (cases k1 k2 rule: linorder_cases)
    case equal with k1 k2 show ?thesis by (auto simp add: exI [of _ k2])
  next
    case less with k2 have "g k1 = h k1" "\<And>k'. k' < k1 \<Longrightarrow> g k' = h k'" by simp_all
    with k1 show ?thesis by (auto intro: exI [of _ k1])
  next
    case greater with k1 have "f k2 = g k2" "\<And>k'. k' < k2 \<Longrightarrow> f k' = g k'" by simp_all
    with k2 show ?thesis by (auto intro: exI [of _ k2])
  qed
qed

lemma order_less_fun:
  "class.order (\<lambda>f g. less_fun f g \<or> f = g) less_fun"
  by (rule order_strictI) (auto intro: less_fun_trans intro!: less_fun_irrefl less_fun_asym)

lemma less_fun_trichotomy:
  assumes "finite {k. f k \<noteq> g k}"
  shows "less_fun f g \<or> f = g \<or> less_fun g f"
proof -
  { def K \<equiv> "{k. f k \<noteq> g k}"
    assume "f \<noteq> g"
    then obtain k' where "f k' \<noteq> g k'" by auto
    then have [simp]: "K \<noteq> {}" by (auto simp add: K_def)
    with assms have [simp]: "finite K" by (simp add: K_def)
    def q \<equiv> "Min K"
    then have "q \<in> K" and "\<And>k. k \<in> K \<Longrightarrow> k \<ge> q" by auto
    then have "\<And>k. \<not> k \<ge> q \<Longrightarrow> k \<notin> K" by blast
    then have *: "\<And>k. k < q \<Longrightarrow> f k = g k" by (simp add: K_def)
    from `q \<in> K` have "f q \<noteq> g q" by (simp add: K_def)
    then have "f q < g q \<or> f q > g q" by auto
    with * have "less_fun f g \<or> less_fun g f"
      by (auto intro!: less_funI)
  } then show ?thesis by blast
qed

end
