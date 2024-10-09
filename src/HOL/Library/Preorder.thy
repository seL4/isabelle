(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Preorders with explicit equivalence relation\<close>

theory Preorder
imports Main
begin

class preorder_equiv = preorder
begin

definition equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "equiv x y \<longleftrightarrow> x \<le> y \<and> y \<le> x"

notation
  equiv (\<open>'(\<approx>')\<close>) and
  equiv (\<open>(\<open>notation=\<open>infix \<approx>\<close>\<close>_/ \<approx> _)\<close>  [51, 51] 50)

lemma equivD1: "x \<le> y" if "x \<approx> y"
  using that by (simp add: equiv_def)

lemma equivD2: "y \<le> x" if "x \<approx> y"
  using that by (simp add: equiv_def)

lemma equiv_refl [iff]: "x \<approx> x"
  by (simp add: equiv_def)

lemma equiv_sym: "x \<approx> y \<longleftrightarrow> y \<approx> x"
  by (auto simp add: equiv_def)

lemma equiv_trans: "x \<approx> y \<Longrightarrow> y \<approx> z \<Longrightarrow> x \<approx> z"
  by (auto simp: equiv_def intro: order_trans)

lemma equiv_antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x \<approx> y"
  by (simp only: equiv_def)

lemma less_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> x \<approx> y"
  by (auto simp add: equiv_def less_le_not_le)

lemma le_less: "x \<le> y \<longleftrightarrow> x < y \<or> x \<approx> y"
  by (auto simp add: equiv_def less_le)

lemma le_imp_less_or_equiv: "x \<le> y \<Longrightarrow> x < y \<or> x \<approx> y"
  by (simp add: less_le)

lemma less_imp_not_equiv: "x < y \<Longrightarrow> \<not> x \<approx> y"
  by (simp add: less_le)

lemma not_equiv_le_trans: "\<not> a \<approx> b \<Longrightarrow> a \<le> b \<Longrightarrow> a < b"
  by (simp add: less_le)

lemma le_not_equiv_trans: "a \<le> b \<Longrightarrow> \<not> a \<approx> b \<Longrightarrow> a < b"
  by (rule not_equiv_le_trans)

lemma antisym_conv: "y \<le> x \<Longrightarrow> x \<le> y \<longleftrightarrow> x \<approx> y"
  by (simp add: equiv_def)

end

ML_file \<open>~~/src/Provers/preorder.ML\<close>

ML \<open>
structure Quasi = Quasi_Tac(
struct

val le_trans = @{thm order_trans};
val le_refl = @{thm order_refl};
val eqD1 = @{thm equivD1};
val eqD2 = @{thm equivD2};
val less_reflE = @{thm less_irrefl};
val less_imp_le = @{thm less_imp_le};
val le_neq_trans = @{thm le_not_equiv_trans};
val neq_le_trans = @{thm not_equiv_le_trans};
val less_imp_neq = @{thm less_imp_not_equiv};

fun decomp_quasi thy (Const (@{const_name less_eq}, _) $ t1 $ t2) = SOME (t1, "<=", t2)
  | decomp_quasi thy (Const (@{const_name less}, _) $ t1 $ t2) = SOME (t1, "<", t2)
  | decomp_quasi thy (Const (@{const_name equiv}, _) $ t1 $ t2) = SOME (t1, "=", t2)
  | decomp_quasi thy (Const (@{const_name Not}, _) $ (Const (@{const_name equiv}, _) $ t1 $ t2)) = SOME (t1, "~=", t2)
  | decomp_quasi thy _ = NONE;

fun decomp_trans thy t = case decomp_quasi thy t of
    x as SOME (t1, "<=", t2) => x
  | _ => NONE;

end
);
\<close>

end
