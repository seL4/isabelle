(*  Title:      HOL/SPARK/SPARK_Setup.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG

Setup for SPARK/Ada verification environment.
*)

theory SPARK_Setup
imports Word
keywords
  "spark_open" "spark_proof_functions" "spark_types" "spark_end" :: thy_decl and
  "spark_vc" :: thy_goal and "spark_status" :: diag
begin

ML_file "Tools/fdl_lexer.ML"
ML_file "Tools/fdl_parser.ML"

text {*
SPARK version of div, see section 4.4.1.1 of SPARK Proof Manual
*}

definition sdiv :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "sdiv" 70) where
  "a sdiv b = sgn a * sgn b * (\<bar>a\<bar> div \<bar>b\<bar>)"

lemma sdiv_minus_dividend: "- a sdiv b = - (a sdiv b)"
  by (simp add: sdiv_def sgn_if)

lemma sdiv_minus_divisor: "a sdiv - b = - (a sdiv b)"
  by (simp add: sdiv_def sgn_if)

text {*
Correspondence between HOL's and SPARK's version of div
*}

lemma sdiv_pos_pos: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a sdiv b = a div b"
  by (simp add: sdiv_def sgn_if)

lemma sdiv_pos_neg: "0 \<le> a \<Longrightarrow> b < 0 \<Longrightarrow> a sdiv b = - (a div - b)"
  by (simp add: sdiv_def sgn_if)

lemma sdiv_neg_pos: "a < 0 \<Longrightarrow> 0 \<le> b \<Longrightarrow> a sdiv b = - (- a div b)"
  by (simp add: sdiv_def sgn_if)

lemma sdiv_neg_neg: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> a sdiv b = - a div - b"
  by (simp add: sdiv_def sgn_if)


text {*
Updating a function at a set of points. Useful for building arrays.
*}

definition fun_upds :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" where
  "fun_upds f xs y z = (if z \<in> xs then y else f z)"

syntax
  "_updsbind" :: "['a, 'a] => updbind"             ("(2_ [:=]/ _)")

translations
  "f(xs[:=]y)" == "CONST fun_upds f xs y"

lemma fun_upds_in [simp]: "z \<in> xs \<Longrightarrow> (f(xs [:=] y)) z = y"
  by (simp add: fun_upds_def)

lemma fun_upds_notin [simp]: "z \<notin> xs \<Longrightarrow> (f(xs [:=] y)) z = f z"
  by (simp add: fun_upds_def)

lemma upds_singleton [simp]: "f({x} [:=] y) = f(x := y)"
  by (simp add: fun_eq_iff)


text {* Enumeration types *}

class spark_enum = ord + finite +
  fixes pos :: "'a \<Rightarrow> int"
  assumes range_pos: "range pos = {0..<int (card (UNIV::'a set))}"
  and less_pos: "(x < y) = (pos x < pos y)"
  and less_eq_pos: "(x \<le> y) = (pos x \<le> pos y)"
begin

definition "val = inv pos"

definition "succ x = val (pos x + 1)"

definition "pred x = val (pos x - 1)"

lemma inj_pos: "inj pos"
  using finite_UNIV
  by (rule eq_card_imp_inj_on) (simp add: range_pos)

lemma val_pos: "val (pos x) = x"
  unfolding val_def using inj_pos
  by (rule inv_f_f)

lemma pos_val: "z \<in> range pos \<Longrightarrow> pos (val z) = z"
  unfolding val_def
  by (rule f_inv_into_f)

subclass linorder
proof
  fix x::'a and y show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_pos less_eq_pos less_le_not_le)
next
  fix x::'a show "x \<le> x" by (simp add: less_eq_pos)
next
  fix x::'a and y z assume "x \<le> y" and "y \<le> z"
  then show "x \<le> z" by (simp add: less_eq_pos)
next
  fix x::'a and y assume "x \<le> y" and "y \<le> x"
  with inj_pos show "x = y"
    by (auto dest: injD simp add: less_eq_pos)
next
  fix x::'a and y show "x \<le> y \<or> y \<le> x"
    by (simp add: less_eq_pos linear)
qed

definition "first_el = val 0"

definition "last_el = val (int (card (UNIV::'a set)) - 1)"

lemma first_el_smallest: "first_el \<le> x"
proof -
  have "pos x \<in> range pos" by (rule rangeI)
  then have "pos (val 0) \<le> pos x"
    by (simp add: range_pos pos_val)
  then show ?thesis by (simp add: first_el_def less_eq_pos)
qed

lemma last_el_greatest: "x \<le> last_el"
proof -
  have "pos x \<in> range pos" by (rule rangeI)
  then have "pos x \<le> pos (val (int (card (UNIV::'a set)) - 1))"
    by (simp add: range_pos pos_val)
  then show ?thesis by (simp add: last_el_def less_eq_pos)
qed

lemma pos_succ:
  assumes "x \<noteq> last_el"
  shows "pos (succ x) = pos x + 1"
proof -
  have "x \<le> last_el" by (rule last_el_greatest)
  with assms have "x < last_el" by simp
  then have "pos x < pos last_el"
    by (simp add: less_pos)
  with rangeI [of pos x]
  have "pos x + 1 \<in> range pos"
    by (simp add: range_pos last_el_def pos_val)
  then show ?thesis
    by (simp add: succ_def pos_val)
qed

lemma pos_pred:
  assumes "x \<noteq> first_el"
  shows "pos (pred x) = pos x - 1"
proof -
  have "first_el \<le> x" by (rule first_el_smallest)
  with assms have "first_el < x" by simp
  then have "pos first_el < pos x"
    by (simp add: less_pos)
  with rangeI [of pos x]
  have "pos x - 1 \<in> range pos"
    by (simp add: range_pos first_el_def pos_val)
  then show ?thesis
    by (simp add: pred_def pos_val)
qed

lemma succ_val: "x \<in> range pos \<Longrightarrow> succ (val x) = val (x + 1)"
  by (simp add: succ_def pos_val)

lemma pred_val: "x \<in> range pos \<Longrightarrow> pred (val x) = val (x - 1)"
  by (simp add: pred_def pos_val)

end

lemma interval_expand:
  "x < y \<Longrightarrow> (z::int) \<in> {x..<y} = (z = x \<or> z \<in> {x+1..<y})"
  by auto


text {* Load the package *}

ML_file "Tools/spark_vcs.ML"
ML_file "Tools/spark_commands.ML"

setup SPARK_Commands.setup

end
