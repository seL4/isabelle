(* Author:     Amine Chaieb, TU Muenchen *)

section \<open>Examples for Ferrante and Rackoff's quantifier elimination procedure\<close>

theory Dense_Linear_Order_Ex
imports "../Dense_Linear_Order"
begin

lemma "\<exists>(y::'a::linordered_field) < 2. x + 3* y < 0 \<and> x - y > 0"
  by ferrack

lemma "\<not> (\<forall>x (y::'a::linordered_field). x < y \<longrightarrow> 10 * x < 11 * y)"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y. x < y \<longrightarrow> 10 * (x + 5 * y + -1) < 60 * y"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y. x \<noteq> y \<longrightarrow> x < y"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y. x \<noteq> y \<and> 10 * x \<noteq> 9 * y \<and> 10 * x < y \<longrightarrow> x < y"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y. x \<noteq> y \<and> 5 * x \<le> y \<longrightarrow> 500 * x \<le> 100 * y"
  by ferrack

lemma "\<forall>x::'a::linordered_field. \<exists>y::'a::linordered_field. 4 * x + 3 * y \<le> 0 \<and> 4 * x + 3 * y \<ge> -1"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) < 0. \<exists>(y::'a::linordered_field) > 0. 7 * x + y > 0 \<and> x - y \<le> 9"
  by ferrack

lemma "\<exists>x::'a::linordered_field. 0 < x \<and> x < 1 \<longrightarrow> (\<forall>y > 1. x + y \<noteq> 1)"
  by ferrack

lemma "\<exists>x. \<forall>y::'a::linordered_field. y < 2 \<longrightarrow> 2 * (y - x) \<le> 0"
  by ferrack

lemma "\<forall>x::'a::linordered_field. x < 10 \<or> x > 20 \<or> (\<exists>y. y \<ge> 0 \<and> y \<le> 10 \<and> x + y = 20)"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y z. x + y < z \<longrightarrow> y \<ge> z \<longrightarrow> x < 0"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y z. x + 7 * y < 5 * z \<and> 5 * y \<ge> 7 * z \<and> x < 0"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y z. \<bar>x + y\<bar> \<le> z \<longrightarrow> \<bar>z\<bar> = z"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y z. x + 7 * y - 5 * z < 0 \<and> 5 * y + 7 * z + 3 * x < 0"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y z.
  (\<bar>5 * x + 3 * y + z\<bar> \<le> 5 * x + 3 * y + z \<and> \<bar>5 * x + 3 * y + z\<bar> \<ge> - (5 * x + 3 * y + z)) \<or>
  (\<bar>5 * x + 3 * y + z\<bar> \<ge> 5 * x + 3 * y + z \<and> \<bar>5 * x + 3 * y + z\<bar> \<le> - (5 * x + 3 * y + z))"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y. x < y \<longrightarrow> (\<exists>z>0. x + z = y)"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y. x < y \<longrightarrow> (\<exists>z>0. x + z = y)"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y. \<exists>z>0. \<bar>x - y\<bar> \<le> z"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y. \<forall>z<0. (z < x \<longrightarrow> z \<le> y) \<and> (z > y \<longrightarrow> z \<ge> x)"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y. \<forall>z\<ge>0. \<bar>3 * x + 7 * y\<bar> \<le> 2 * z + 1"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y. \<forall>z<0. (z < x \<longrightarrow> z \<le> y) \<and> (z > y \<longrightarrow> z \<ge> x)"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) > 0. \<forall>y. \<exists>z. 13 * \<bar>z\<bar> \<noteq> \<bar>12 * y - x\<bar> \<and> 5 * x - 3 * \<bar>y\<bar> \<le> 7 * z"
  by ferrack

lemma "\<exists>x::'a::linordered_field.
  \<bar>4 * x + 17\<bar> < 4 \<and> (\<forall>y. \<bar>x * 34 - 34 * y - 9\<bar> \<noteq> 0 \<longrightarrow> (\<exists>z. 5 * x - 3 * \<bar>y\<bar> \<le> 7 * z))"
  by ferrack

lemma "\<forall>x::'a::linordered_field. \<exists>y > \<bar>23 * x - 9\<bar>. \<forall>z > \<bar>3 * y - 19 * \<bar>x\<bar>\<bar>. x + z > 2 * y"
  by ferrack

lemma "\<forall>x::'a::linordered_field.
  \<exists>y < \<bar>3 * x - 1\<bar>. \<forall>z \<ge> 3 * \<bar>x\<bar> - 1. \<bar>12 * x - 13 * y + 19 * z\<bar> > \<bar>23 * x\<bar>"
  by ferrack

lemma "\<exists>x::'a::linordered_field. \<bar>x\<bar> < 100 \<and> (\<forall>y > x. (\<exists>z < 2 * y - x. 5 * x - 3 * y \<le> 7 * z))"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y z w.
  7 * x < 3 * y \<longrightarrow> 5 * y < 7 * z \<longrightarrow> z < 2 * w \<longrightarrow> 7 * (2 * w - x) > 2 * y"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y z w. 5 * x + 3 * z - 17 * w + \<bar>y - 8 * x + z\<bar> \<le> 89"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y z w.
  5 * x + 3 * z - 17 * w + 7 * (y - 8 * x + z) \<le> max y (7 * z - x + w)"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y z w.
  min (5 * x + 3 * z) (17 * w) + 5 * \<bar>y - 8 * x + z\<bar> \<le> max y (7 * z - x + w)"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y z. \<exists>w \<ge> x + y + z. w \<le> \<bar>x\<bar> + \<bar>y\<bar> + \<bar>z\<bar>"
  by ferrack

lemma "\<not> (\<forall>x::'a::linordered_field. \<exists>y z w.
  3 * x + z * 4 = 3 * y \<and> x + y < z \<and> x > w \<and> 3 * x < w + y)"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y. \<exists>z w. \<bar>x - y\<bar> = z - w \<and> z * 1234 < 233 * x \<and> w \<noteq> y"
  by ferrack

lemma "\<forall>x::'a::linordered_field. \<exists>y z w.
  min (5 * x + 3 * z) (17 * w) + 5 * \<bar>y - 8 * x + z\<bar> \<le> max y (7 * z - x + w)"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y z. \<forall>w \<ge> \<bar>x + y + z\<bar>. w \<ge> \<bar>x\<bar> + \<bar>y\<bar> + \<bar>z\<bar>"
  by ferrack

lemma "\<exists>z. \<forall>(x::'a::linordered_field) y. \<exists>w \<ge> x + y + z. w \<le> \<bar>x\<bar> + \<bar>y\<bar> + \<bar>z\<bar>"
  by ferrack

lemma "\<exists>z. \<forall>(x::'a::linordered_field) < \<bar>z\<bar>. \<exists>y w. x < y \<and> x < z \<and> x > w \<and> 3 * x < w + y"
  by ferrack

lemma "\<forall>(x::'a::linordered_field) y. \<exists>z. \<forall>w. \<bar>x - y\<bar> = \<bar>z - w\<bar> \<longrightarrow> z < x \<and> w \<noteq> y"
  by ferrack

lemma "\<exists>y. \<forall>x::'a::linordered_field. \<exists>z w.
  min (5 * x + 3 * z) (17 * w) + 5 * \<bar>y - 8 * x + z\<bar> \<le> max y (7 * z - x + w)"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) z. \<forall>w \<ge> 13 * x - 4 * z. \<exists>y. w \<ge> \<bar>x\<bar> + \<bar>y\<bar> + z"
  by ferrack

lemma "\<exists>x::'a::linordered_field. \<forall>y < x. \<exists>z > x + y.
  \<forall>w. 5 * w + 10 * x - z \<ge> y \<longrightarrow> w + 7 * x + 3 * z \<ge> 2 * y"
  by ferrack

lemma "\<exists>x::'a::linordered_field. \<forall>y. \<exists>z > y.
  \<forall>w. w < 13 \<longrightarrow> w + 10 * x - z \<ge> y \<longrightarrow> 5 * w + 7 * x + 13 * z \<ge> 2 * y"
  by ferrack

lemma "\<exists>(x::'a::linordered_field) y z w.
  min (5 * x + 3 * z) (17 * w) + 5 * \<bar>y - 8 * x + z\<bar> \<le> max y (7 * z - x + w)"
  by ferrack

lemma "\<forall>x::'a::linordered_field. \<exists>y. \<forall>z>19. y \<le> x + z \<and> (\<exists>w. \<bar>y - x\<bar> < w)"
  by ferrack

lemma "\<forall>x::'a::linordered_field. \<exists>y. \<forall>z>19. y \<le> x + z \<and> (\<exists>w. \<bar>x + z\<bar> < w - y)"
  by ferrack

lemma "\<forall>x::'a::linordered_field. \<exists>y.
  \<bar>y\<bar> \<noteq> \<bar>x\<bar> \<and> (\<forall>z > max x y. \<exists>w. w \<noteq> y \<and> w \<noteq> z \<and> 3 * w - z \<ge> x + y)"
  by ferrack

end
