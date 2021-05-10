section \<open>Transposition function\<close>

theory Transposition
  imports Main
begin

definition transpose :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>transpose a b c = (if c = a then b else if c = b then a else c)\<close>

lemma transpose_apply_first [simp]:
  \<open>transpose a b a = b\<close>
  by (simp add: transpose_def)

lemma transpose_apply_second [simp]:
  \<open>transpose a b b = a\<close>
  by (simp add: transpose_def)

lemma transpose_apply_other [simp]:
  \<open>transpose a b c = c\<close> if \<open>c \<noteq> a\<close> \<open>c \<noteq> b\<close>
  using that by (simp add: transpose_def)

lemma transpose_same [simp]:
  \<open>transpose a a = id\<close>
  by (simp add: fun_eq_iff transpose_def)

lemma transpose_eq_iff:
  \<open>transpose a b c = d \<longleftrightarrow> (c \<noteq> a \<and> c \<noteq> b \<and> d = c) \<or> (c = a \<and> d = b) \<or> (c = b \<and> d = a)\<close>
  by (auto simp add: transpose_def)

lemma transpose_eq_imp_eq:
  \<open>c = d\<close> if \<open>transpose a b c = transpose a b d\<close>
  using that by (auto simp add: transpose_eq_iff)

lemma transpose_commute [ac_simps]:
  \<open>transpose b a = transpose a b\<close>
  by (auto simp add: fun_eq_iff transpose_eq_iff)

lemma transpose_involutory [simp]:
  \<open>transpose a b (transpose a b c) = c\<close>
  by (auto simp add: transpose_eq_iff)

lemma transpose_comp_involutory [simp]:
  \<open>transpose a b \<circ> transpose a b = id\<close>
  by (rule ext) simp

lemma transpose_triple:
  \<open>transpose a b (transpose b c (transpose a b d)) = transpose a c d\<close>
  if \<open>a \<noteq> c\<close> and \<open>b \<noteq> c\<close>
  using that by (simp add: transpose_def)

lemma transpose_comp_triple:
  \<open>transpose a b \<circ> transpose b c \<circ> transpose a b = transpose a c\<close>
  if \<open>a \<noteq> c\<close> and \<open>b \<noteq> c\<close>
  using that by (simp add: fun_eq_iff transpose_triple)

lemma transpose_image_eq [simp]:
  \<open>transpose a b ` A = A\<close> if \<open>a \<in> A \<longleftrightarrow> b \<in> A\<close>
  using that by (auto simp add: transpose_def [abs_def])

lemma inj_on_transpose [simp]:
  \<open>inj_on (transpose a b) A\<close>
  by rule (drule transpose_eq_imp_eq)

lemma inj_transpose:
  \<open>inj (transpose a b)\<close>
  by (fact inj_on_transpose)

lemma surj_transpose:
  \<open>surj (transpose a b)\<close>
  by simp

lemma bij_betw_transpose_iff [simp]:
  \<open>bij_betw (transpose a b) A A\<close> if \<open>a \<in> A \<longleftrightarrow> b \<in> A\<close>
  using that by (auto simp: bij_betw_def)

lemma bij_transpose [simp]:
  \<open>bij (transpose a b)\<close>
  by (rule bij_betw_transpose_iff) simp

lemma bijection_transpose:
  \<open>bijection (transpose a b)\<close>
  by standard (fact bij_transpose)

lemma inv_transpose_eq [simp]:
  \<open>inv (transpose a b) = transpose a b\<close>
  by (rule inv_unique_comp) simp_all

lemma transpose_apply_commute:
  \<open>transpose a b (f c) = f (transpose (inv f a) (inv f b) c)\<close>
  if \<open>bij f\<close>
proof -
  from that have \<open>surj f\<close>
    by (rule bij_is_surj)
  with that show ?thesis
    by (simp add: transpose_def bij_inv_eq_iff surj_f_inv_f)
qed

lemma transpose_comp_eq:
  \<open>transpose a b \<circ> f = f \<circ> transpose (inv f a) (inv f b)\<close>
  if \<open>bij f\<close>
  using that by (simp add: fun_eq_iff transpose_apply_commute)

lemma in_transpose_image_iff:
  \<open>x \<in> transpose a b ` S \<longleftrightarrow> transpose a b x \<in> S\<close>
  by (auto intro!: image_eqI)


text \<open>Legacy input alias\<close>

setup \<open>Context.theory_map (Name_Space.map_naming (Name_Space.qualified_path true \<^binding>\<open>Fun\<close>))\<close>

abbreviation (input) swap :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close>
  where \<open>swap a b f \<equiv> f \<circ> transpose a b\<close>

lemma swap_def:
  \<open>Fun.swap a b f = f (a := f b, b:= f a)\<close>
  by (simp add: fun_eq_iff)

setup \<open>Context.theory_map (Name_Space.map_naming (Name_Space.parent_path))\<close>

lemma swap_apply:
  "Fun.swap a b f a = f b"
  "Fun.swap a b f b = f a"
  "c \<noteq> a \<Longrightarrow> c \<noteq> b \<Longrightarrow> Fun.swap a b f c = f c"
  by simp_all

lemma swap_self: "Fun.swap a a f = f"
  by simp

lemma swap_commute: "Fun.swap a b f = Fun.swap b a f"
  by (simp add: ac_simps)

lemma swap_nilpotent: "Fun.swap a b (Fun.swap a b f) = f"
  by (simp add: comp_assoc)

lemma swap_comp_involutory: "Fun.swap a b \<circ> Fun.swap a b = id"
  by (simp add: fun_eq_iff)

lemma swap_triple:
  assumes "a \<noteq> c" and "b \<noteq> c"
  shows "Fun.swap a b (Fun.swap b c (Fun.swap a b f)) = Fun.swap a c f"
  using assms transpose_comp_triple [of a c b]
  by (simp add: comp_assoc)

lemma comp_swap: "f \<circ> Fun.swap a b g = Fun.swap a b (f \<circ> g)"
  by (simp add: comp_assoc)

lemma swap_image_eq:
  assumes "a \<in> A" "b \<in> A"
  shows "Fun.swap a b f ` A = f ` A"
  using assms by (metis image_comp transpose_image_eq)

lemma inj_on_imp_inj_on_swap: "inj_on f A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> inj_on (Fun.swap a b f) A"
  by (simp add: comp_inj_on)
  
lemma inj_on_swap_iff:
  assumes A: "a \<in> A" "b \<in> A"
  shows "inj_on (Fun.swap a b f) A \<longleftrightarrow> inj_on f A"
  using assms by (metis inj_on_imageI inj_on_imp_inj_on_swap transpose_image_eq)

lemma surj_imp_surj_swap: "surj f \<Longrightarrow> surj (Fun.swap a b f)"
  by (meson comp_surj surj_transpose)

lemma surj_swap_iff: "surj (Fun.swap a b f) \<longleftrightarrow> surj f"
  by (metis fun.set_map surj_transpose)

lemma bij_betw_swap_iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> bij_betw (Fun.swap x y f) A B \<longleftrightarrow> bij_betw f A B"
  by (meson bij_betw_comp_iff bij_betw_transpose_iff)

lemma bij_swap_iff: "bij (Fun.swap a b f) \<longleftrightarrow> bij f"
  by (simp add: bij_betw_swap_iff)

lemma swap_image:
  \<open>Fun.swap i j f ` A = f ` (A - {i, j}
    \<union> (if i \<in> A then {j} else {}) \<union> (if j \<in> A then {i} else {}))\<close>
  by (auto simp add: Fun.swap_def)

lemma inv_swap_id: "inv (Fun.swap a b id) = Fun.swap a b id"
  by simp

lemma bij_swap_comp:
  assumes "bij p"
  shows "Fun.swap a b id \<circ> p = Fun.swap (inv p a) (inv p b) p"
  using assms by (simp add: transpose_comp_eq) 

lemma swap_id_eq: "Fun.swap a b id x = (if x = a then b else if x = b then a else x)"
  by (simp add: Fun.swap_def)

lemma swap_unfold:
  \<open>Fun.swap a b p = p \<circ> Fun.swap a b id\<close>
  by simp

lemma swap_id_idempotent: "Fun.swap a b id \<circ> Fun.swap a b id = id"
  by simp

lemma bij_swap_compose_bij:
  \<open>bij (Fun.swap a b id \<circ> p)\<close> if \<open>bij p\<close>
  using that by (rule bij_comp) simp

end
