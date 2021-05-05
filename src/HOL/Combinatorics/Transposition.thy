section \<open>Transposition function\<close>

theory Transposition
  imports Main
begin

setup \<open>Context.theory_map (Name_Space.map_naming (Name_Space.qualified_path true \<^binding>\<open>Fun\<close>))\<close>

definition swap :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  where \<open>swap a b f = f (a := f b, b:= f a)\<close>

setup \<open>Context.theory_map (Name_Space.map_naming (Name_Space.parent_path))\<close>

lemma swap_apply [simp]:
  "Fun.swap a b f a = f b"
  "Fun.swap a b f b = f a"
  "c \<noteq> a \<Longrightarrow> c \<noteq> b \<Longrightarrow> Fun.swap a b f c = f c"
  by (simp_all add: Fun.swap_def)

lemma swap_self [simp]: "Fun.swap a a f = f"
  by (simp add: Fun.swap_def)

lemma swap_commute: "Fun.swap a b f = Fun.swap b a f"
  by (simp add: fun_upd_def Fun.swap_def fun_eq_iff)

lemma swap_nilpotent [simp]: "Fun.swap a b (Fun.swap a b f) = f"
  by (rule ext) (simp add: fun_upd_def Fun.swap_def)

lemma swap_comp_involutory [simp]: "Fun.swap a b \<circ> Fun.swap a b = id"
  by (rule ext) simp

lemma swap_triple:
  assumes "a \<noteq> c" and "b \<noteq> c"
  shows "Fun.swap a b (Fun.swap b c (Fun.swap a b f)) = Fun.swap a c f"
  using assms by (simp add: fun_eq_iff Fun.swap_def)

lemma comp_swap: "f \<circ> Fun.swap a b g = Fun.swap a b (f \<circ> g)"
  by (rule ext) (simp add: fun_upd_def Fun.swap_def)

lemma swap_image_eq [simp]:
  assumes "a \<in> A" "b \<in> A"
  shows "Fun.swap a b f ` A = f ` A"
proof -
  have subset: "\<And>f. Fun.swap a b f ` A \<subseteq> f ` A"
    using assms by (auto simp: image_iff Fun.swap_def)
  then have "Fun.swap a b (Fun.swap a b f) ` A \<subseteq> (Fun.swap a b f) ` A" .
  with subset[of f] show ?thesis by auto
qed

lemma inj_on_imp_inj_on_swap: "inj_on f A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> inj_on (Fun.swap a b f) A"
  by (auto simp add: inj_on_def Fun.swap_def)

lemma inj_on_swap_iff [simp]:
  assumes A: "a \<in> A" "b \<in> A"
  shows "inj_on (Fun.swap a b f) A \<longleftrightarrow> inj_on f A"
proof
  assume "inj_on (Fun.swap a b f) A"
  with A have "inj_on (Fun.swap a b (Fun.swap a b f)) A"
    by (iprover intro: inj_on_imp_inj_on_swap)
  then show "inj_on f A" by simp
next
  assume "inj_on f A"
  with A show "inj_on (Fun.swap a b f) A"
    by (iprover intro: inj_on_imp_inj_on_swap)
qed

lemma surj_imp_surj_swap: "surj f \<Longrightarrow> surj (Fun.swap a b f)"
  by simp

lemma surj_swap_iff [simp]: "surj (Fun.swap a b f) \<longleftrightarrow> surj f"
  by simp

lemma bij_betw_swap_iff [simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> bij_betw (Fun.swap x y f) A B \<longleftrightarrow> bij_betw f A B"
  by (auto simp: bij_betw_def)

lemma bij_swap_iff [simp]: "bij (Fun.swap a b f) \<longleftrightarrow> bij f"
  by simp

lemma swap_image:
  \<open>Fun.swap i j f ` A = f ` (A - {i, j}
    \<union> (if i \<in> A then {j} else {}) \<union> (if j \<in> A then {i} else {}))\<close>
  by (auto simp add: Fun.swap_def)

lemma inv_swap_id: "inv (Fun.swap a b id) = Fun.swap a b id"
  by (rule inv_unique_comp) (simp_all add: fun_eq_iff Fun.swap_def)

lemma bij_swap_comp:
  assumes "bij p"
  shows "Fun.swap a b id \<circ> p = Fun.swap (inv p a) (inv p b) p"
  using surj_f_inv_f[OF bij_is_surj[OF \<open>bij p\<close>]]
  by (simp add: fun_eq_iff Fun.swap_def bij_inv_eq_iff[OF \<open>bij p\<close>])


subsection \<open>Transpositions\<close>

lemma swap_id_eq: "Fun.swap a b id x = (if x = a then b else if x = b then a else x)"
  by (simp add: Fun.swap_def)

lemma swap_unfold:
  \<open>Fun.swap a b p = p \<circ> Fun.swap a b id\<close>
  by (simp add: fun_eq_iff Fun.swap_def)

lemma swap_id_idempotent [simp]: "Fun.swap a b id \<circ> Fun.swap a b id = id"
  by (simp flip: swap_unfold)

lemma bij_swap_compose_bij:
  \<open>bij (Fun.swap a b id \<circ> p)\<close> if \<open>bij p\<close>
  using that by (rule bij_comp) simp

end
