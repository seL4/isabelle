section\<open>Poly Mappings as a Real Normed Vector\<close>

(*  Author:  LC Paulson
*)

theory Finite_Function_Topology
  imports Function_Topology  "HOL-Library.Poly_Mapping" 
           
begin

instantiation "poly_mapping" :: (type, real_vector) real_vector
begin

definition scaleR_poly_mapping_def:
  "scaleR r x \<equiv> Abs_poly_mapping (\<lambda>i. (scaleR r (Poly_Mapping.lookup x i)))"

instance
proof 
qed (simp_all add: scaleR_poly_mapping_def plus_poly_mapping.abs_eq eq_onp_def lookup_add scaleR_add_left scaleR_add_right)

end

instantiation "poly_mapping" :: (type, real_normed_vector) metric_space
begin

definition dist_poly_mapping :: "['a \<Rightarrow>\<^sub>0 'b,'a \<Rightarrow>\<^sub>0 'b] \<Rightarrow> real"
  where dist_poly_mapping_def:
    "dist_poly_mapping \<equiv> \<lambda>x y. (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. dist (Poly_Mapping.lookup x n) (Poly_Mapping.lookup y n))"

definition uniformity_poly_mapping:: "(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) filter"
  where uniformity_poly_mapping_def:
    "uniformity_poly_mapping \<equiv> INF e\<in>{0<..}. principal {(x, y). dist (x::'a\<Rightarrow>\<^sub>0'b) y < e}"

definition open_poly_mapping:: "('a \<Rightarrow>\<^sub>0 'b)set \<Rightarrow> bool"
  where open_poly_mapping_def:
    "open_poly_mapping U \<equiv> (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"

instance
proof
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y::'a \<Rightarrow>\<^sub>0 'b). dist x y < e})"
    by (simp add: uniformity_poly_mapping_def)
next
  fix U :: "('a \<Rightarrow>\<^sub>0 'b) set"
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    by (simp add: open_poly_mapping_def)
next
  fix x :: "'a \<Rightarrow>\<^sub>0 'b" and y :: "'a \<Rightarrow>\<^sub>0 'b"
  show "dist x y = 0 \<longleftrightarrow> x = y"
  proof
    assume "dist x y = 0"
    then have "(\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. dist (poly_mapping.lookup x n) (poly_mapping.lookup y n)) = 0"
      by (simp add: dist_poly_mapping_def)
    then have "poly_mapping.lookup x n = poly_mapping.lookup y n"
      if "n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y" for n
      using that by (simp add: ordered_comm_monoid_add_class.sum_nonneg_eq_0_iff)
    then show "x = y"
      by (metis Un_iff in_keys_iff poly_mapping_eqI)
  qed (simp add: dist_poly_mapping_def)
next
  fix x :: "'a \<Rightarrow>\<^sub>0 'b" and y :: "'a \<Rightarrow>\<^sub>0 'b" and z :: "'a \<Rightarrow>\<^sub>0 'b"
  have "dist x y = (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y \<union> Poly_Mapping.keys z. dist (Poly_Mapping.lookup x n) (Poly_Mapping.lookup y n))"
    by (force simp add: dist_poly_mapping_def in_keys_iff intro: sum.mono_neutral_left)
  also have "... \<le> (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y \<union> Poly_Mapping.keys z. 
                     dist (Poly_Mapping.lookup x n) (Poly_Mapping.lookup z n) + dist (Poly_Mapping.lookup y n) (Poly_Mapping.lookup z n))"
    by (simp add: ordered_comm_monoid_add_class.sum_mono dist_triangle2)
  also have "... = (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y \<union> Poly_Mapping.keys z. dist (Poly_Mapping.lookup x n) (Poly_Mapping.lookup z n))
                 + (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y \<union> Poly_Mapping.keys z. dist (Poly_Mapping.lookup y n) (Poly_Mapping.lookup z n))"
    by (simp add: sum.distrib)
  also have "... = (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys z. dist (Poly_Mapping.lookup x n) (Poly_Mapping.lookup z n))
                 + (\<Sum>n \<in> Poly_Mapping.keys y \<union> Poly_Mapping.keys z. dist (Poly_Mapping.lookup y n) (Poly_Mapping.lookup z n))"
    by (force simp add: dist_poly_mapping_def in_keys_iff intro: sum.mono_neutral_right arg_cong2 [where f = "(+)"])
  also have "... = dist x z + dist y z"
    by (simp add: dist_poly_mapping_def)
  finally show "dist x y \<le> dist x z + dist y z" .
qed

end

instantiation "poly_mapping" :: (type, real_normed_vector) real_normed_vector
begin

definition norm_poly_mapping :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> real"
  where norm_poly_mapping_def:
    "norm_poly_mapping \<equiv> \<lambda>x. dist x 0"

definition sgn_poly_mapping :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where sgn_poly_mapping_def:
    "sgn_poly_mapping \<equiv> \<lambda>x. x /\<^sub>R norm x"

instance
proof 
  fix x :: "'a \<Rightarrow>\<^sub>0 'b" and y :: "'a \<Rightarrow>\<^sub>0 'b"
  have 0: "\<forall>i\<in>Poly_Mapping.keys x \<union> Poly_Mapping.keys y - Poly_Mapping.keys (x - y). norm (poly_mapping.lookup (x - y) i) = 0"
    by (force simp add: dist_poly_mapping_def in_keys_iff intro: sum.mono_neutral_left)
  have "dist x y = (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. dist (poly_mapping.lookup x n) (poly_mapping.lookup y n))"
    by (simp add: dist_poly_mapping_def)  
  also have "... = (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. norm (poly_mapping.lookup x n - poly_mapping.lookup y n))"
    by (simp add: dist_norm)
  also have "... = (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. norm (poly_mapping.lookup (x-y) n))"
    by (simp add: lookup_minus)
  also have "... = (\<Sum>n \<in> Poly_Mapping.keys (x-y). norm (poly_mapping.lookup (x-y) n))"
    by (simp add: "0" sum.mono_neutral_cong_right keys_diff)
  also have "... = norm (x - y)"
    by (simp add: norm_poly_mapping_def dist_poly_mapping_def)  
  finally show "dist x y = norm (x - y)" .
next
  fix x :: "'a \<Rightarrow>\<^sub>0 'b"
  show "sgn x = x /\<^sub>R norm x"
    by (simp add: sgn_poly_mapping_def)
next
  fix x :: "'a \<Rightarrow>\<^sub>0 'b"
  show "norm x = 0 \<longleftrightarrow> x = 0"
    by (simp add: norm_poly_mapping_def)  
next
  fix x :: "'a \<Rightarrow>\<^sub>0 'b" and y :: "'a \<Rightarrow>\<^sub>0 'b"
  have "norm (x + y) = (\<Sum>n \<in> Poly_Mapping.keys (x + y). norm (poly_mapping.lookup x n + poly_mapping.lookup y n))"
    by (simp add: norm_poly_mapping_def dist_poly_mapping_def lookup_add)
  also have "... = (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. norm (poly_mapping.lookup x n + poly_mapping.lookup y n))"
    by (auto simp: simp add: plus_poly_mapping.rep_eq in_keys_iff intro: sum.mono_neutral_left)
  also have "... \<le> (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. norm (poly_mapping.lookup x n) + norm (poly_mapping.lookup y n))"
    by (simp add: norm_triangle_ineq sum_mono)
  also have "... = (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. norm (poly_mapping.lookup x n))
                 + (\<Sum>n \<in> Poly_Mapping.keys x \<union> Poly_Mapping.keys y. norm (poly_mapping.lookup y n))"
    by (simp add: sum.distrib)
  also have "... = (\<Sum>n \<in> Poly_Mapping.keys x. norm (poly_mapping.lookup x n))
                 + (\<Sum>n \<in> Poly_Mapping.keys y. norm (poly_mapping.lookup y n))"
    by (force simp add: in_keys_iff intro: arg_cong2 [where f = "(+)"] sum.mono_neutral_right)
  also have "... = norm x + norm y"
    by (simp add: norm_poly_mapping_def dist_poly_mapping_def)
  finally show "norm (x + y) \<le> norm x + norm y" .
next
  fix a :: "real" and x :: "'a \<Rightarrow>\<^sub>0 'b"
  show "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x"
  proof (cases "a = 0")
    case False
    then have [simp]: "Poly_Mapping.keys (a *\<^sub>R x) = Poly_Mapping.keys x"
      by (auto simp add: scaleR_poly_mapping_def in_keys_iff)
    then show ?thesis
      by (simp add: norm_poly_mapping_def dist_poly_mapping_def scaleR_poly_mapping_def sum_distrib_left)
  qed (simp add: norm_poly_mapping_def)
qed

end

end
