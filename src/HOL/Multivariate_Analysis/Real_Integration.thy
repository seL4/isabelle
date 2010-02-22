header{*Integration on real intervals*}

theory Real_Integration
imports Integration
begin

text{*We follow John Harrison in formalizing the Gauge integral.*}

definition Integral :: "real set \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "Integral s f k = (f o dest_vec1 has_integral k) (vec1 ` s)"

lemmas integral_unfold = Integral_def split_conv o_def vec1_interval

lemma Integral_unique:
    "[| Integral{a..b} f k1; Integral{a..b} f k2 |] ==> k1 = k2"
  unfolding integral_unfold apply(rule has_integral_unique) by assumption+

lemma Integral_zero [simp]: "Integral{a..a} f 0"
  unfolding integral_unfold by auto

lemma Integral_eq_diff_bounds: assumes "a \<le> b" shows "Integral{a..b} (%x. 1) (b - a)"
  unfolding integral_unfold using has_integral_const[of "1::real" "vec1 a" "vec1 b"]
  unfolding content_1'[OF assms] by auto

lemma Integral_mult_const: assumes "a \<le> b" shows "Integral{a..b} (%x. c)  (c*(b - a))"
  unfolding integral_unfold using has_integral_const[of "c::real" "vec1 a" "vec1 b"]
  unfolding content_1'[OF assms] by(auto simp add:field_simps)

lemma Integral_mult: assumes "Integral{a..b} f k" shows "Integral{a..b} (%x. c * f x) (c * k)"
  using assms unfolding integral_unfold  apply(drule_tac has_integral_cmul[where c=c]) by auto

lemma Integral_add:
  assumes "Integral {a..b} f x1" "Integral {b..c} f x2"  "a \<le> b" and "b \<le> c"
  shows "Integral {a..c} f (x1 + x2)"
  using assms unfolding integral_unfold apply-
  apply(rule has_integral_combine[of "vec1 a" "vec1 b" "vec1 c"]) by  auto

lemma FTC1: assumes "a \<le> b" "\<forall>x. a \<le> x & x \<le> b --> DERIV f x :> f'(x)"
  shows "Integral{a..b} f' (f(b) - f(a))"
proof-note fundamental_theorem_of_calculus[OF assms(1), of"f o dest_vec1" "f' o dest_vec1"]
  note * = this[unfolded o_def vec1_dest_vec1]
  have **:"\<And>x. (\<lambda>xa\<Colon>real. xa * f' x) =  op * (f' x)" apply(rule ext) by(auto simp add:field_simps)
  show ?thesis unfolding integral_unfold apply(rule *)
    using assms(2) unfolding DERIV_conv_has_derivative has_vector_derivative_def
    apply safe apply(rule has_derivative_at_within) by(auto simp add:**) qed

lemma Integral_subst: "[| Integral{a..b} f k1; k2=k1 |] ==> Integral{a..b} f k2"
by simp

subsection {* Additivity Theorem of Gauge Integral *}

text{* Bartle/Sherbert: Theorem 10.1.5 p. 278 *}
lemma Integral_add_fun: "[| Integral{a..b} f k1; Integral{a..b} g k2 |] ==> Integral{a..b} (%x. f x + g x) (k1 + k2)"
  unfolding integral_unfold apply(rule has_integral_add) by assumption+

lemma norm_vec1'[simp]:"norm (vec1 x) = norm x"
  using norm_vector_1[of "vec1 x"] by auto

lemma Integral_le: assumes "a \<le> b" "\<forall>x. a \<le> x & x \<le> b --> f(x) \<le> g(x)" "Integral{a..b} f k1" "Integral{a..b} g k2" shows "k1 \<le> k2"
proof- note assms(3-4)[unfolded integral_unfold] note has_integral_vec1[OF this(1)] has_integral_vec1[OF this(2)]
  note has_integral_component_le[OF this,of 1] thus ?thesis using assms(2) by auto qed

lemma monotonic_anti_derivative:
  fixes f g :: "real => real" shows
     "[| a \<le> b; \<forall>c. a \<le> c & c \<le> b --> f' c \<le> g' c;
         \<forall>x. DERIV f x :> f' x; \<forall>x. DERIV g x :> g' x |]
      ==> f b - f a \<le> g b - g a"
apply (rule Integral_le, assumption)
apply (auto intro: FTC1)
done

end
