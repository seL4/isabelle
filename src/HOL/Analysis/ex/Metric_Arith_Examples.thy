theory Metric_Arith_Examples
imports "HOL-Analysis.Elementary_Metric_Spaces"
begin


text \<open>simple examples\<close>

lemma "\<exists>x::'a::metric_space. x=x"
  by metric
lemma "\<forall>(x::'a::metric_space). \<exists>y. x = y"
  by metric


text \<open>reasoning with "dist x y = 0 \<longleftrightarrow> x = y"\<close>

lemma "\<exists>x y. dist x y = 0"
  by metric

lemma "\<exists>y. dist x y = 0"
  by metric

lemma "0 = dist x y \<Longrightarrow> x = y"
  by metric

lemma "x \<noteq> y \<Longrightarrow> dist x y \<noteq> 0"
  by metric

lemma "\<exists>y. dist x y \<noteq> 1"
  by metric

lemma "x = y \<longleftrightarrow> dist x x = dist y x \<and> dist x y = dist y y"
  by metric

lemma "dist a b \<noteq> dist a c \<Longrightarrow> b \<noteq> c"
  by metric

text \<open>reasoning with positive semidefiniteness\<close>

lemma "dist y x + c \<ge> c"
  by metric

lemma "dist x y + dist x z \<ge> 0"
  by metric

lemma "dist x y \<ge> v \<Longrightarrow> dist x y + dist (a::'a) b \<ge> v" for x::"('a::metric_space)"
  by metric

lemma "dist x y < 0 \<longrightarrow> P"
  by metric

text \<open>reasoning with the triangle inequality\<close>

lemma "dist a d \<le> dist a b + dist b c + dist c d"
  by metric

lemma "dist a e \<le> dist a b + dist b c + dist c d + dist d e"
  by metric

lemma "max (dist x y) \<bar>dist x z - dist z y\<bar> = dist x y"
  by metric

lemma
  "dist w x < e/3 \<Longrightarrow> dist x y < e/3 \<Longrightarrow> dist y z < e/3 \<Longrightarrow> dist w x < e"
  by metric

lemma "dist w x < e/4 \<Longrightarrow> dist x y < e/4 \<Longrightarrow> dist y z < e/2 \<Longrightarrow> dist w z < e"
  by metric


text \<open>more complex examples\<close>

lemma "dist x y \<le> e \<Longrightarrow> dist x z \<le> e \<Longrightarrow> dist y z \<le> e
  \<Longrightarrow> p \<in> (cball x e \<union> cball y e \<union> cball z e) \<Longrightarrow> dist p x \<le> 2*e"
  by metric

lemma hol_light_example:
  "\<not> disjnt (ball x r) (ball y s) \<longrightarrow>
    (\<forall>p q. p \<in> ball x r \<union> ball y s \<and> q \<in> ball x r \<union> ball y s \<longrightarrow> dist p q < 2 * (r + s))"
  unfolding disjnt_iff
  by metric

lemma "dist x y \<le> e \<Longrightarrow> z \<in> ball x f \<Longrightarrow> dist z y < e + f"
  by metric

lemma "dist x y = r / 2 \<Longrightarrow> (\<forall>z. dist x z < r / 4 \<longrightarrow> dist y z \<le> 3 * r / 4)"
  by metric

lemma "s \<ge> 0 \<Longrightarrow> t \<ge> 0 \<Longrightarrow> z \<in> (ball x s) \<union> (ball y t) \<Longrightarrow> dist z y \<le> dist x y + s + t"
  by metric

lemma "0 < r \<Longrightarrow> ball x r \<subseteq> ball y s \<Longrightarrow> ball x r \<subseteq> ball z t \<Longrightarrow> dist y z \<le> s + t"
  by metric


text \<open>non-trivial quantifier structure\<close>

lemma "\<exists>x. \<forall>r\<le>0. \<exists>z. dist x z \<ge> r"
  by metric

lemma "\<And>a r x y. dist x a + dist a y = r \<Longrightarrow> \<forall>z. r \<le> dist x z + dist z y \<Longrightarrow> dist x y = r"
  by metric

end