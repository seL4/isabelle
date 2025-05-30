(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Finite types as explicit enumerations\<close>

theory Enum
imports Map Groups_List
begin

subsection \<open>Class \<open>enum\<close>\<close>

class enum =
  fixes enum :: "'a list"
  fixes enum_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  fixes enum_ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  assumes UNIV_enum: "UNIV = set enum"
    and enum_distinct: "distinct enum"
  assumes enum_all_UNIV: "enum_all P \<longleftrightarrow> Ball UNIV P"
  assumes enum_ex_UNIV: "enum_ex P \<longleftrightarrow> Bex UNIV P" 
   \<comment> \<open>tailored towards simple instantiation\<close>
begin

subclass finite proof
qed (simp add: UNIV_enum)

lemma enum_UNIV:
  "set enum = UNIV"
  by (simp only: UNIV_enum)

lemma in_enum: "x \<in> set enum"
  by (simp add: enum_UNIV)

lemma enum_eq_I:
  assumes "\<And>x. x \<in> set xs"
  shows "set enum = set xs"
proof -
  from assms UNIV_eq_I have "UNIV = set xs" by auto
  with enum_UNIV show ?thesis by simp
qed

lemma card_UNIV_length_enum:
  "card (UNIV :: 'a set) = length enum"
  by (simp add: UNIV_enum distinct_card enum_distinct)

lemma enum_all [simp]:
  "enum_all = HOL.All"
  by (simp add: fun_eq_iff enum_all_UNIV)

lemma enum_ex [simp]:
  "enum_ex = HOL.Ex" 
  by (simp add: fun_eq_iff enum_ex_UNIV)

end


subsection \<open>Implementations using \<^class>\<open>enum\<close>\<close>

subsubsection \<open>Unbounded operations and quantifiers\<close>

lemma Collect_code [code]:
  "Collect P = set (filter P enum)"
  by (simp add: enum_UNIV)

lemma vimage_code [code]:
  "f -` B = set (filter (\<lambda>x. f x \<in> B) enum_class.enum)"
  unfolding vimage_def Collect_code ..

definition card_UNIV :: "'a itself \<Rightarrow> nat"
where
  "card_UNIV TYPE('a) = card (UNIV :: 'a set)"

lemma [code]:
  "card_UNIV TYPE('a :: enum) = card (set (Enum.enum :: 'a list))"
  by (simp only: card_UNIV_def enum_UNIV)

lemma all_code [code]: "(\<forall>x. P x) \<longleftrightarrow> enum_all P"
  by simp

lemma exists_code [code]: "(\<exists>x. P x) \<longleftrightarrow> enum_ex P"
  by simp

lemma exists1_code [code]: "(\<exists>!x. P x) \<longleftrightarrow> list_ex1 P enum"
  by (simp add: list_ex1_iff enum_UNIV)


subsubsection \<open>An executable choice operator\<close>

definition
  "enum_the = The"

lemma [code]:
  "The P = (case filter P enum of [x] \<Rightarrow> x | _ \<Rightarrow> enum_the P)"
proof -
  {
    fix a
    assume filter_enum: "filter P enum = [a]"
    have "The P = a"
    proof (rule the_equality)
      fix x
      assume "P x"
      show "x = a"
      proof (rule ccontr)
        assume "x \<noteq> a"
        from filter_enum obtain us vs
          where enum_eq: "enum = us @ [a] @ vs"
          and "\<forall> x \<in> set us. \<not> P x"
          and "\<forall> x \<in> set vs. \<not> P x"
          and "P a"
          by (auto simp add: filter_eq_Cons_iff) (simp only: filter_empty_conv[symmetric])
        with \<open>P x\<close> in_enum[of x, unfolded enum_eq] \<open>x \<noteq> a\<close> show "False" by auto
      qed
    next
      from filter_enum show "P a" by (auto simp add: filter_eq_Cons_iff)
    qed
  }
  from this show ?thesis
    unfolding enum_the_def by (auto split: list.split)
qed

declare [[code abort: enum_the]]

code_printing
  constant enum_the \<rightharpoonup> (Eval) "(fn '_ => raise Match)"


subsubsection \<open>Equality and order on functions\<close>

instantiation "fun" :: (enum, equal) equal
begin

definition
  "HOL.equal f g \<longleftrightarrow> (\<forall>x \<in> set enum. f x = g x)"

instance proof
qed (simp_all add: equal_fun_def fun_eq_iff enum_UNIV)

end

lemma [code]:
  "HOL.equal f g \<longleftrightarrow> enum_all (%x. f x = g x)"
  by (auto simp add: equal fun_eq_iff)

lemma [code nbe]:
  "HOL.equal (f :: _ \<Rightarrow> _) f \<longleftrightarrow> True"
  by (fact equal_refl)

lemma order_fun [code]:
  fixes f g :: "'a::enum \<Rightarrow> 'b::order"
  shows "f \<le> g \<longleftrightarrow> enum_all (\<lambda>x. f x \<le> g x)"
    and "f < g \<longleftrightarrow> f \<le> g \<and> enum_ex (\<lambda>x. f x \<noteq> g x)"
  by (simp_all add: fun_eq_iff le_fun_def order_less_le)


subsubsection \<open>Operations on relations\<close>

lemma [code]:
  "Id = image (\<lambda>x. (x, x)) (set Enum.enum)"
  by (auto intro: imageI in_enum)

lemma tranclp_unfold [code]:
  "tranclp r a b \<longleftrightarrow> (a, b) \<in> trancl {(x, y). r x y}"
  by (simp add: trancl_def)

lemma rtranclp_rtrancl_eq [code]:
  "rtranclp r x y \<longleftrightarrow> (x, y) \<in> rtrancl {(x, y). r x y}"
  by (simp add: rtrancl_def)

lemma max_ext_eq [code]:
  "max_ext R = {(X, Y). finite X \<and> finite Y \<and> Y \<noteq> {} \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>xa \<in> Y. (x, xa) \<in> R))}"
  by (auto simp add: max_ext.simps)

lemma max_extp_eq [code]:
  "max_extp r x y \<longleftrightarrow> (x, y) \<in> max_ext {(x, y). r x y}"
  by (simp add: max_ext_def)

lemma mlex_eq [code]:
  "f <*mlex*> R = {(x, y). f x < f y \<or> (f x \<le> f y \<and> (x, y) \<in> R)}"
  by (auto simp add: mlex_prod_def)


subsubsection \<open>Bounded accessible part\<close>

primrec bacc :: "('a \<times> 'a) set \<Rightarrow> nat \<Rightarrow> 'a set" 
where
  "bacc r 0 = {x. \<forall> y. (y, x) \<notin> r}"
| "bacc r (Suc n) = (bacc r n \<union> {x. \<forall>y. (y, x) \<in> r \<longrightarrow> y \<in> bacc r n})"

lemma bacc_subseteq_acc:
  "bacc r n \<subseteq> Wellfounded.acc r"
  by (induct n) (auto intro: acc.intros)

lemma bacc_mono:
  "n \<le> m \<Longrightarrow> bacc r n \<subseteq> bacc r m"
  by (induct rule: dec_induct) auto
  
lemma bacc_upper_bound:
  "bacc (r :: ('a \<times> 'a) set)  (card (UNIV :: 'a::finite set)) = (\<Union>n. bacc r n)"
proof -
  have "mono (bacc r)" unfolding mono_def by (simp add: bacc_mono)
  moreover have "\<forall>n. bacc r n = bacc r (Suc n) \<longrightarrow> bacc r (Suc n) = bacc r (Suc (Suc n))" by auto
  moreover have "finite (range (bacc r))" by auto
  ultimately show ?thesis
   by (intro finite_mono_strict_prefix_implies_finite_fixpoint)
     (auto intro: finite_mono_remains_stable_implies_strict_prefix)
qed

lemma acc_subseteq_bacc:
  assumes "finite r"
  shows "Wellfounded.acc r \<subseteq> (\<Union>n. bacc r n)"
proof
  fix x
  assume "x \<in> Wellfounded.acc r"
  then have "\<exists>n. x \<in> bacc r n"
  proof (induct x arbitrary: rule: acc.induct)
    case (accI x)
    then have "\<forall>y. \<exists> n. (y, x) \<in> r \<longrightarrow> y \<in> bacc r n" by simp
    from choice[OF this] obtain n where n: "\<forall>y. (y, x) \<in> r \<longrightarrow> y \<in> bacc r (n y)" ..
    obtain n where "\<And>y. (y, x) \<in> r \<Longrightarrow> y \<in> bacc r n"
    proof
      fix y assume y: "(y, x) \<in> r"
      with n have "y \<in> bacc r (n y)" by auto
      moreover have "n y <= Max ((\<lambda>(y, x). n y) ` r)"
        using y \<open>finite r\<close> by (auto intro!: Max_ge)
      note bacc_mono[OF this, of r]
      ultimately show "y \<in> bacc r (Max ((\<lambda>(y, x). n y) ` r))" by auto
    qed
    then show ?case
      by (auto simp add: Let_def intro!: exI[of _ "Suc n"])
  qed
  then show "x \<in> (\<Union>n. bacc r n)" by auto
qed

lemma acc_bacc_eq:
  fixes A :: "('a :: finite \<times> 'a) set"
  assumes "finite A"
  shows "Wellfounded.acc A = bacc A (card (UNIV :: 'a set))"
  using assms by (metis acc_subseteq_bacc bacc_subseteq_acc bacc_upper_bound order_eq_iff)

lemma [code]:
  fixes xs :: "('a::finite \<times> 'a) list"
  shows "Wellfounded.acc (set xs) = bacc (set xs) (card_UNIV TYPE('a))"
  by (simp add: card_UNIV_def acc_bacc_eq)


subsection \<open>Default instances for \<^class>\<open>enum\<close>\<close>

lemma map_of_zip_enum_is_Some:
  assumes "length ys = length (enum :: 'a::enum list)"
  shows "\<exists>y. map_of (zip (enum :: 'a::enum list) ys) x = Some y"
proof -
  from assms have "x \<in> set (enum :: 'a::enum list) \<longleftrightarrow>
    (\<exists>y. map_of (zip (enum :: 'a::enum list) ys) x = Some y)"
    by (auto intro!: map_of_zip_is_Some)
  then show ?thesis using enum_UNIV by auto
qed

lemma map_of_zip_enum_inject:
  fixes xs ys :: "'b::enum list"
  assumes length: "length xs = length (enum :: 'a::enum list)"
      "length ys = length (enum :: 'a::enum list)"
    and map_of: "the \<circ> map_of (zip (enum :: 'a::enum list) xs) = the \<circ> map_of (zip (enum :: 'a::enum list) ys)"
  shows "xs = ys"
proof -
  have "map_of (zip (enum :: 'a list) xs) = map_of (zip (enum :: 'a list) ys)"
  proof
    fix x :: 'a
    from length map_of_zip_enum_is_Some obtain y1 y2
      where "map_of (zip (enum :: 'a list) xs) x = Some y1"
        and "map_of (zip (enum :: 'a list) ys) x = Some y2" by blast
    moreover from map_of
      have "the (map_of (zip (enum :: 'a::enum list) xs) x) = the (map_of (zip (enum :: 'a::enum list) ys) x)"
      by (auto dest: fun_cong)
    ultimately show "map_of (zip (enum :: 'a::enum list) xs) x = map_of (zip (enum :: 'a::enum list) ys) x"
      by simp
  qed
  with length enum_distinct show "xs = ys" by (rule map_of_zip_inject)
qed

definition all_n_lists :: "(('a :: enum) list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"
where
  "all_n_lists P n \<longleftrightarrow> (\<forall>xs \<in> set (List.n_lists n enum). P xs)"

lemma [code]:
  "all_n_lists P n \<longleftrightarrow> (if n = 0 then P [] else enum_all (%x. all_n_lists (%xs. P (x # xs)) (n - 1)))"
  unfolding all_n_lists_def enum_all
  by (cases n) (auto simp add: enum_UNIV)

definition ex_n_lists :: "(('a :: enum) list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"
where
  "ex_n_lists P n \<longleftrightarrow> (\<exists>xs \<in> set (List.n_lists n enum). P xs)"

lemma [code]:
  "ex_n_lists P n \<longleftrightarrow> (if n = 0 then P [] else enum_ex (%x. ex_n_lists (%xs. P (x # xs)) (n - 1)))"
  unfolding ex_n_lists_def enum_ex
  by (cases n) (auto simp add: enum_UNIV)

instantiation "fun" :: (enum, enum) enum
begin

definition
  "enum = map (\<lambda>ys. the \<circ> map_of (zip (enum::'a list) ys)) (List.n_lists (length (enum::'a::enum list)) enum)"

definition
  "enum_all P = all_n_lists (\<lambda>bs. P (the \<circ> map_of (zip enum bs))) (length (enum :: 'a list))"

definition
  "enum_ex P = ex_n_lists (\<lambda>bs. P (the \<circ> map_of (zip enum bs))) (length (enum :: 'a list))"

instance proof
  show "UNIV = set (enum :: ('a \<Rightarrow> 'b) list)"
  proof (rule UNIV_eq_I)
    fix f :: "'a \<Rightarrow> 'b"
    have "f = the \<circ> map_of (zip (enum :: 'a::enum list) (map f enum))"
      by (auto simp add: map_of_zip_map fun_eq_iff intro: in_enum)
    then show "f \<in> set enum"
      by (auto simp add: enum_fun_def set_n_lists intro: in_enum)
  qed
next
  from map_of_zip_enum_inject
  show "distinct (enum :: ('a \<Rightarrow> 'b) list)"
    by (auto intro!: inj_onI simp add: enum_fun_def
      distinct_map distinct_n_lists enum_distinct set_n_lists)
next
  fix P
  show "enum_all (P :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) = Ball UNIV P"
  proof
    assume "enum_all P"
    show "Ball UNIV P"
    proof
      fix f :: "'a \<Rightarrow> 'b"
      have f: "f = the \<circ> map_of (zip (enum :: 'a::enum list) (map f enum))"
        by (auto simp add: map_of_zip_map fun_eq_iff intro: in_enum)
      from \<open>enum_all P\<close> have "P (the \<circ> map_of (zip enum (map f enum)))"
        unfolding enum_all_fun_def all_n_lists_def
        apply (simp add: set_n_lists)
        apply (erule_tac x="map f enum" in allE)
        apply (auto intro!: in_enum)
        done
      from this f show "P f" by auto
    qed
  next
    assume "Ball UNIV P"
    from this show "enum_all P"
      unfolding enum_all_fun_def all_n_lists_def by auto
  qed
next
  fix P
  show "enum_ex (P :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) = Bex UNIV P"
  proof
    assume "enum_ex P"
    from this show "Bex UNIV P"
      unfolding enum_ex_fun_def ex_n_lists_def by auto
  next
    assume "Bex UNIV P"
    from this obtain f where "P f" ..
    have f: "f = the \<circ> map_of (zip (enum :: 'a::enum list) (map f enum))"
      by (auto simp add: map_of_zip_map fun_eq_iff intro: in_enum) 
    from \<open>P f\<close> this have "P (the \<circ> map_of (zip (enum :: 'a::enum list) (map f enum)))"
      by auto
    from  this show "enum_ex P"
      unfolding enum_ex_fun_def ex_n_lists_def
      apply (auto simp add: set_n_lists)
      apply (rule_tac x="map f enum" in exI)
      apply (auto intro!: in_enum)
      done
  qed
qed

end

lemma enum_fun_code [code]: "enum = (let enum_a = (enum :: 'a::{enum, equal} list)
  in map (\<lambda>ys. the \<circ> map_of (zip enum_a ys)) (List.n_lists (length enum_a) enum))"
  by (simp add: enum_fun_def Let_def)

lemma enum_all_fun_code [code]:
  "enum_all P = (let enum_a = (enum :: 'a::{enum, equal} list)
   in all_n_lists (\<lambda>bs. P (the \<circ> map_of (zip enum_a bs))) (length enum_a))"
  by (simp only: enum_all_fun_def Let_def)

lemma enum_ex_fun_code [code]:
  "enum_ex P = (let enum_a = (enum :: 'a::{enum, equal} list)
   in ex_n_lists (\<lambda>bs. P (the \<circ> map_of (zip enum_a bs))) (length enum_a))"
  by (simp only: enum_ex_fun_def Let_def)

instantiation set :: (enum) enum
begin

definition
  "enum = map set (subseqs enum)"

definition
  "enum_all P \<longleftrightarrow> (\<forall>A\<in>set enum. P (A::'a set))"

definition
  "enum_ex P \<longleftrightarrow> (\<exists>A\<in>set enum. P (A::'a set))"

instance proof
qed (simp_all add: enum_set_def enum_all_set_def enum_ex_set_def subseqs_powset distinct_set_subseqs
  enum_distinct enum_UNIV)

end

instantiation unit :: enum
begin

definition
  "enum = [()]"

definition
  "enum_all P = P ()"

definition
  "enum_ex P = P ()"

instance proof
qed (auto simp add: enum_unit_def enum_all_unit_def enum_ex_unit_def)

end

instantiation bool :: enum
begin

definition
  "enum = [False, True]"

definition
  "enum_all P \<longleftrightarrow> P False \<and> P True"

definition
  "enum_ex P \<longleftrightarrow> P False \<or> P True"

instance proof
qed (simp_all only: enum_bool_def enum_all_bool_def enum_ex_bool_def UNIV_bool, simp_all)

end

instantiation prod :: (enum, enum) enum
begin

definition
  "enum = List.product enum enum"

definition
  "enum_all P = enum_all (%x. enum_all (%y. P (x, y)))"

definition
  "enum_ex P = enum_ex (%x. enum_ex (%y. P (x, y)))"

 
instance
  by standard
    (simp_all add: enum_prod_def distinct_product
      enum_UNIV enum_distinct enum_all_prod_def enum_ex_prod_def)

end

instantiation sum :: (enum, enum) enum
begin

definition
  "enum = map Inl enum @ map Inr enum"

definition
  "enum_all P \<longleftrightarrow> enum_all (\<lambda>x. P (Inl x)) \<and> enum_all (\<lambda>x. P (Inr x))"

definition
  "enum_ex P \<longleftrightarrow> enum_ex (\<lambda>x. P (Inl x)) \<or> enum_ex (\<lambda>x. P (Inr x))"

instance proof
qed (simp_all only: enum_sum_def enum_all_sum_def enum_ex_sum_def UNIV_sum,
  auto simp add: enum_UNIV distinct_map enum_distinct)

end

instantiation option :: (enum) enum
begin

definition
  "enum = None # map Some enum"

definition
  "enum_all P \<longleftrightarrow> P None \<and> enum_all (\<lambda>x. P (Some x))"

definition
  "enum_ex P \<longleftrightarrow> P None \<or> enum_ex (\<lambda>x. P (Some x))"

instance proof
qed (simp_all only: enum_option_def enum_all_option_def enum_ex_option_def UNIV_option_conv,
  auto simp add: distinct_map enum_UNIV enum_distinct)

end


subsection \<open>Small finite types\<close>

text \<open>We define small finite types for use in Quickcheck\<close>

datatype (plugins only: code "quickcheck" extraction) finite_1 =
  a\<^sub>1

notation (output) a\<^sub>1  (\<open>a\<^sub>1\<close>)

lemma UNIV_finite_1:
  "UNIV = {a\<^sub>1}"
  by (auto intro: finite_1.exhaust)

instantiation finite_1 :: enum
begin

definition
  "enum = [a\<^sub>1]"

definition
  "enum_all P = P a\<^sub>1"

definition
  "enum_ex P = P a\<^sub>1"

instance proof
qed (simp_all only: enum_finite_1_def enum_all_finite_1_def enum_ex_finite_1_def UNIV_finite_1, simp_all)

end

instantiation finite_1 :: linorder
begin

definition less_finite_1 :: "finite_1 \<Rightarrow> finite_1 \<Rightarrow> bool"
where
  "x < (y :: finite_1) \<longleftrightarrow> False"

definition less_eq_finite_1 :: "finite_1 \<Rightarrow> finite_1 \<Rightarrow> bool"
where
  "x \<le> (y :: finite_1) \<longleftrightarrow> True"

instance
apply (intro_classes)
apply (auto simp add: less_finite_1_def less_eq_finite_1_def)
apply (metis (full_types) finite_1.exhaust)
done

end

instance finite_1 :: "{dense_linorder, wellorder}"
by intro_classes (simp_all add: less_finite_1_def)

instantiation finite_1 :: complete_lattice
begin

definition [simp]: "Inf = (\<lambda>_. a\<^sub>1)"
definition [simp]: "Sup = (\<lambda>_. a\<^sub>1)"
definition [simp]: "bot = a\<^sub>1"
definition [simp]: "top = a\<^sub>1"
definition [simp]: "inf = (\<lambda>_ _. a\<^sub>1)"
definition [simp]: "sup = (\<lambda>_ _. a\<^sub>1)"

instance by intro_classes(simp_all add: less_eq_finite_1_def)
end

instance finite_1 :: complete_distrib_lattice
  by standard simp_all

instance finite_1 :: complete_linorder ..

lemma finite_1_eq: "x = a\<^sub>1"
by(cases x) simp

simproc_setup finite_1_eq ("x::finite_1") = \<open>
  K (K (fn ct =>
    (case Thm.term_of ct of
      Const (\<^const_name>\<open>a\<^sub>1\<close>, _) => NONE
    | _ => SOME (mk_meta_eq @{thm finite_1_eq}))))
\<close>

instantiation finite_1 :: complete_boolean_algebra
begin
definition [simp]: "(-) = (\<lambda>_ _. a\<^sub>1)"
definition [simp]: "uminus = (\<lambda>_. a\<^sub>1)"
instance by intro_classes simp_all
end

instantiation finite_1 :: 
  "{linordered_ring_strict, linordered_comm_semiring_strict, ordered_comm_ring,
    ordered_cancel_comm_monoid_diff, comm_monoid_mult, ordered_ring_abs,
    one, modulo, sgn, inverse}"
begin
definition [simp]: "Groups.zero = a\<^sub>1"
definition [simp]: "Groups.one = a\<^sub>1"
definition [simp]: "(+) = (\<lambda>_ _. a\<^sub>1)"
definition [simp]: "(*) = (\<lambda>_ _. a\<^sub>1)"
definition [simp]: "(mod) = (\<lambda>_ _. a\<^sub>1)" 
definition [simp]: "abs = (\<lambda>_. a\<^sub>1)"
definition [simp]: "sgn = (\<lambda>_. a\<^sub>1)"
definition [simp]: "inverse = (\<lambda>_. a\<^sub>1)"
definition [simp]: "divide = (\<lambda>_ _. a\<^sub>1)"

instance by intro_classes(simp_all add: less_finite_1_def)
end

declare [[simproc del: finite_1_eq]]
hide_const (open) a\<^sub>1

datatype (plugins only: code "quickcheck" extraction) finite_2 =
  a\<^sub>1 | a\<^sub>2

notation (output) a\<^sub>1  (\<open>a\<^sub>1\<close>)
notation (output) a\<^sub>2  (\<open>a\<^sub>2\<close>)

lemma UNIV_finite_2:
  "UNIV = {a\<^sub>1, a\<^sub>2}"
  by (auto intro: finite_2.exhaust)

instantiation finite_2 :: enum
begin

definition
  "enum = [a\<^sub>1, a\<^sub>2]"

definition
  "enum_all P \<longleftrightarrow> P a\<^sub>1 \<and> P a\<^sub>2"

definition
  "enum_ex P \<longleftrightarrow> P a\<^sub>1 \<or> P a\<^sub>2"

instance proof
qed (simp_all only: enum_finite_2_def enum_all_finite_2_def enum_ex_finite_2_def UNIV_finite_2, simp_all)

end

instantiation finite_2 :: linorder
begin

definition less_finite_2 :: "finite_2 \<Rightarrow> finite_2 \<Rightarrow> bool"
where
  "x < y \<longleftrightarrow> x = a\<^sub>1 \<and> y = a\<^sub>2"

definition less_eq_finite_2 :: "finite_2 \<Rightarrow> finite_2 \<Rightarrow> bool"
where
  "x \<le> y \<longleftrightarrow> x = y \<or> x < (y :: finite_2)"

instance
apply (intro_classes)
apply (auto simp add: less_finite_2_def less_eq_finite_2_def)
apply (metis finite_2.nchotomy)+
done

end

instance finite_2 :: wellorder
by(rule wf_wellorderI)(simp add: less_finite_2_def, intro_classes)

instantiation finite_2 :: complete_lattice
begin

definition "\<Sqinter>A = (if a\<^sub>1 \<in> A then a\<^sub>1 else a\<^sub>2)"
definition "\<Squnion>A = (if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>1)"
definition [simp]: "bot = a\<^sub>1"
definition [simp]: "top = a\<^sub>2"
definition "x \<sqinter> y = (if x = a\<^sub>1 \<or> y = a\<^sub>1 then a\<^sub>1 else a\<^sub>2)"
definition "x \<squnion> y = (if x = a\<^sub>2 \<or> y = a\<^sub>2 then a\<^sub>2 else a\<^sub>1)"

lemma neq_finite_2_a\<^sub>1_iff [simp]: "x \<noteq> a\<^sub>1 \<longleftrightarrow> x = a\<^sub>2"
by(cases x) simp_all

lemma neq_finite_2_a\<^sub>1_iff' [simp]: "a\<^sub>1 \<noteq> x \<longleftrightarrow> x = a\<^sub>2"
by(cases x) simp_all

lemma neq_finite_2_a\<^sub>2_iff [simp]: "x \<noteq> a\<^sub>2 \<longleftrightarrow> x = a\<^sub>1"
by(cases x) simp_all

lemma neq_finite_2_a\<^sub>2_iff' [simp]: "a\<^sub>2 \<noteq> x \<longleftrightarrow> x = a\<^sub>1"
by(cases x) simp_all

instance
proof
  fix x :: finite_2 and A
  assume "x \<in> A"
  then show "\<Sqinter>A \<le> x" "x \<le> \<Squnion>A"
    by(cases x; auto simp add: less_eq_finite_2_def less_finite_2_def Inf_finite_2_def Sup_finite_2_def)+
qed(auto simp add: less_eq_finite_2_def less_finite_2_def inf_finite_2_def sup_finite_2_def Inf_finite_2_def Sup_finite_2_def)
end

instance finite_2 :: complete_linorder ..

instance finite_2 :: complete_distrib_lattice ..

instantiation finite_2 :: "{field, idom_abs_sgn, idom_modulo}" begin
definition [simp]: "0 = a\<^sub>1"
definition [simp]: "1 = a\<^sub>2"
definition "x + y = (case (x, y) of (a\<^sub>1, a\<^sub>1) \<Rightarrow> a\<^sub>1 | (a\<^sub>2, a\<^sub>2) \<Rightarrow> a\<^sub>1 | _ \<Rightarrow> a\<^sub>2)"
definition "uminus = (\<lambda>x :: finite_2. x)"
definition "(-) = ((+) :: finite_2 \<Rightarrow> _)"
definition "x * y = (case (x, y) of (a\<^sub>2, a\<^sub>2) \<Rightarrow> a\<^sub>2 | _ \<Rightarrow> a\<^sub>1)"
definition "inverse = (\<lambda>x :: finite_2. x)"
definition "divide = ((*) :: finite_2 \<Rightarrow> _)"
definition "x mod y = (case (x, y) of (a\<^sub>2, a\<^sub>1) \<Rightarrow> a\<^sub>2 | _ \<Rightarrow> a\<^sub>1)"
definition "abs = (\<lambda>x :: finite_2. x)"
definition "sgn = (\<lambda>x :: finite_2. x)"
instance
  by standard
    (subproofs
      \<open>simp_all add: plus_finite_2_def uminus_finite_2_def minus_finite_2_def
        times_finite_2_def
        inverse_finite_2_def divide_finite_2_def modulo_finite_2_def
        abs_finite_2_def sgn_finite_2_def
        split: finite_2.splits\<close>)
end

lemma two_finite_2 [simp]:
  "2 = a\<^sub>1"
  by (simp add: numeral.simps plus_finite_2_def)

lemma dvd_finite_2_unfold:
  "x dvd y \<longleftrightarrow> x = a\<^sub>2 \<or> y = a\<^sub>1"
  by (auto simp add: dvd_def times_finite_2_def split: finite_2.splits)

instantiation finite_2 :: "{normalization_semidom, unique_euclidean_semiring}" begin
definition [simp]: "normalize = (id :: finite_2 \<Rightarrow> _)"
definition [simp]: "unit_factor = (id :: finite_2 \<Rightarrow> _)"
definition [simp]: "euclidean_size x = (case x of a\<^sub>1 \<Rightarrow> 0 | a\<^sub>2 \<Rightarrow> 1)"
definition [simp]: "division_segment (x :: finite_2) = 1"
instance
  by standard
    (subproofs
      \<open>auto simp add: divide_finite_2_def times_finite_2_def dvd_finite_2_unfold
        split: finite_2.splits\<close>)
end

 
hide_const (open) a\<^sub>1 a\<^sub>2

datatype (plugins only: code "quickcheck" extraction) finite_3 =
  a\<^sub>1 | a\<^sub>2 | a\<^sub>3

notation (output) a\<^sub>1  (\<open>a\<^sub>1\<close>)
notation (output) a\<^sub>2  (\<open>a\<^sub>2\<close>)
notation (output) a\<^sub>3  (\<open>a\<^sub>3\<close>)

lemma UNIV_finite_3:
  "UNIV = {a\<^sub>1, a\<^sub>2, a\<^sub>3}"
  by (auto intro: finite_3.exhaust)

instantiation finite_3 :: enum
begin

definition
  "enum = [a\<^sub>1, a\<^sub>2, a\<^sub>3]"

definition
  "enum_all P \<longleftrightarrow> P a\<^sub>1 \<and> P a\<^sub>2 \<and> P a\<^sub>3"

definition
  "enum_ex P \<longleftrightarrow> P a\<^sub>1 \<or> P a\<^sub>2 \<or> P a\<^sub>3"

instance proof
qed (simp_all only: enum_finite_3_def enum_all_finite_3_def enum_ex_finite_3_def UNIV_finite_3, simp_all)

end

lemma finite_3_not_eq_unfold:
  "x \<noteq> a\<^sub>1 \<longleftrightarrow> x \<in> {a\<^sub>2, a\<^sub>3}"
  "x \<noteq> a\<^sub>2 \<longleftrightarrow> x \<in> {a\<^sub>1, a\<^sub>3}"
  "x \<noteq> a\<^sub>3 \<longleftrightarrow> x \<in> {a\<^sub>1, a\<^sub>2}"
  by (cases x; simp)+

instantiation finite_3 :: linorder
begin

definition less_finite_3 :: "finite_3 \<Rightarrow> finite_3 \<Rightarrow> bool"
where
  "x < y = (case x of a\<^sub>1 \<Rightarrow> y \<noteq> a\<^sub>1 | a\<^sub>2 \<Rightarrow> y = a\<^sub>3 | a\<^sub>3 \<Rightarrow> False)"

definition less_eq_finite_3 :: "finite_3 \<Rightarrow> finite_3 \<Rightarrow> bool"
where
  "x \<le> y \<longleftrightarrow> x = y \<or> x < (y :: finite_3)"

instance proof (intro_classes)
qed (auto simp add: less_finite_3_def less_eq_finite_3_def split: finite_3.split_asm)

end

instance finite_3 :: wellorder
proof(rule wf_wellorderI)
  have "inv_image less_than (case_finite_3 0 1 2) = {(x, y). x < y}"
    by(auto simp add: less_finite_3_def split: finite_3.splits)
  from this[symmetric] show "wf \<dots>" by simp
qed intro_classes

class finite_lattice = finite +  lattice + Inf + Sup  + bot + top +
  assumes Inf_finite_empty: "Inf {} = Sup UNIV"
  assumes Inf_finite_insert: "Inf (insert a A) = a \<sqinter> Inf A"
  assumes Sup_finite_empty: "Sup {} = Inf UNIV"
  assumes Sup_finite_insert: "Sup (insert a A) = a \<squnion> Sup A"
  assumes bot_finite_def: "bot = Inf UNIV"
  assumes top_finite_def: "top = Sup UNIV"
begin

subclass complete_lattice
proof
  fix x A
  show "x \<in> A \<Longrightarrow> \<Sqinter>A \<le> x"
    by (metis Set.set_insert abel_semigroup.commute local.Inf_finite_insert local.inf.abel_semigroup_axioms local.inf.left_idem local.inf.orderI)
  show "x \<in> A \<Longrightarrow> x \<le> \<Squnion>A"
    by (metis Set.set_insert insert_absorb2 local.Sup_finite_insert local.sup.absorb_iff2)
next
  fix A z
  have "\<Squnion> UNIV = z \<squnion> \<Squnion>UNIV"
    by (subst Sup_finite_insert [symmetric], simp add: insert_UNIV)
  from this have [simp]: "z \<le> \<Squnion>UNIV"
    using local.le_iff_sup by auto
  have "(\<forall> x. x \<in> A \<longrightarrow> z \<le> x) \<longrightarrow> z \<le> \<Sqinter>A"
    by (rule finite_induct [of A "\<lambda> A . (\<forall> x. x \<in> A \<longrightarrow> z \<le> x) \<longrightarrow> z \<le> \<Sqinter>A"])
      (simp_all add: Inf_finite_empty Inf_finite_insert)
  from this show "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sqinter>A"
    by simp

  have "\<Sqinter> UNIV = z \<sqinter> \<Sqinter>UNIV"
    by (subst Inf_finite_insert [symmetric], simp add: insert_UNIV)
  from this have [simp]: "\<Sqinter>UNIV \<le> z"
    by (simp add: local.inf.absorb_iff2)
  have "(\<forall> x. x \<in> A \<longrightarrow> x \<le> z) \<longrightarrow> \<Squnion>A \<le> z"
    by (rule finite_induct [of A "\<lambda> A . (\<forall> x. x \<in> A \<longrightarrow> x \<le> z) \<longrightarrow> \<Squnion>A \<le> z" ], simp_all add: Sup_finite_empty Sup_finite_insert)
  from this show " (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion>A \<le> z"
    by blast
next
  show "\<Sqinter>{} = \<top>"
    by (simp add: Inf_finite_empty top_finite_def)
  show " \<Squnion>{} = \<bottom>"
    by (simp add: Sup_finite_empty bot_finite_def)
qed
end

class finite_distrib_lattice = finite_lattice + distrib_lattice 
begin
lemma finite_inf_Sup: "a \<sqinter> (Sup A) = Sup {a \<sqinter> b | b . b \<in> A}"
proof (rule finite_induct [of A "\<lambda> A . a \<sqinter> (Sup A) = Sup {a \<sqinter> b | b . b \<in> A}"], simp_all)
  fix x::"'a"
  fix F
  assume "x \<notin> F"
  assume [simp]: "a \<sqinter> \<Squnion>F = \<Squnion>{a \<sqinter> b |b. b \<in> F}"
  have [simp]: " insert (a \<sqinter> x) {a \<sqinter> b |b. b \<in> F} = {a \<sqinter> b |b. b = x \<or> b \<in> F}"
    by blast
  have "a \<sqinter> (x \<squnion> \<Squnion>F) = a \<sqinter> x \<squnion> a \<sqinter> \<Squnion>F"
    by (simp add: inf_sup_distrib1)
  also have "... = a \<sqinter> x \<squnion> \<Squnion>{a \<sqinter> b |b. b \<in> F}"
    by simp
  also have "... = \<Squnion>{a \<sqinter> b |b. b = x \<or> b \<in> F}"
    by (unfold Sup_insert[THEN sym], simp)
  finally show "a \<sqinter> (x \<squnion> \<Squnion>F) = \<Squnion>{a \<sqinter> b |b. b = x \<or> b \<in> F}"
    by simp
qed

lemma finite_Inf_Sup: "\<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y})"
proof (rule finite_induct [of A "\<lambda>A. \<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y})"], simp_all add: finite_UnionD)
  fix x::"'a set"
  fix F
  assume "x \<notin> F"
  have [simp]: "{\<Squnion>x \<sqinter> b |b . b \<in> Inf ` {f ` F |f. \<forall>Y\<in>F. f Y \<in> Y} } = {\<Squnion>x \<sqinter> (Inf (f ` F)) |f  . (\<forall>Y\<in>F. f Y \<in> Y)}"
    by auto
  define fa where "fa = (\<lambda> (b::'a) f Y . (if Y = x then b else f Y))"
  have "\<And>f b. \<forall>Y\<in>F. f Y \<in> Y \<Longrightarrow> b \<in> x \<Longrightarrow> insert b (f ` (F \<inter> {Y. Y \<noteq> x})) = insert (fa b f x) (fa b f ` F) \<and> fa b f x \<in> x \<and> (\<forall>Y\<in>F. fa b f Y \<in> Y)"
    by (auto simp add: fa_def)
  from this have B: "\<And>f b. \<forall>Y\<in>F. f Y \<in> Y \<Longrightarrow> b \<in> x \<Longrightarrow> fa b f ` ({x} \<union> F) \<in> {insert (f x) (f ` F) |f. f x \<in> x \<and> (\<forall>Y\<in>F. f Y \<in> Y)}"
    by blast
  have [simp]: "\<And>f b. \<forall>Y\<in>F. f Y \<in> Y \<Longrightarrow> b \<in> x \<Longrightarrow> b \<sqinter> (\<Sqinter>x\<in>F. f x)  \<le> \<Squnion>(Inf ` {insert (f x) (f ` F) |f. f x \<in> x \<and> (\<forall>Y\<in>F. f Y \<in> Y)})"
    using B apply (rule SUP_upper2)
    using \<open>x \<notin> F\<close> apply (simp_all add: fa_def Inf_union_distrib)
    apply (simp add: image_mono Inf_superset_mono inf.coboundedI2)
    done
  assume "\<Sqinter>(Sup ` F) \<le> \<Squnion>(Inf ` {f ` F |f. \<forall>Y\<in>F. f Y \<in> Y})"

  from this have "\<Squnion>x \<sqinter> \<Sqinter>(Sup ` F) \<le> \<Squnion>x \<sqinter> \<Squnion>(Inf ` {f ` F |f. \<forall>Y\<in>F. f Y \<in> Y})"
    using inf.coboundedI2 by auto
  also have "... = Sup {\<Squnion>x \<sqinter> (Inf (f ` F)) |f  .  (\<forall>Y\<in>F. f Y \<in> Y)}"
    by (simp add: finite_inf_Sup)

  also have "... = Sup {Sup {Inf (f ` F) \<sqinter> b | b . b \<in> x} |f  .  (\<forall>Y\<in>F. f Y \<in> Y)}"
    by (subst inf_commute) (simp add: finite_inf_Sup)

  also have "... \<le> \<Squnion>(Inf ` {insert (f x) (f ` F) |f. f x \<in> x \<and> (\<forall>Y\<in>F. f Y \<in> Y)})"
    apply (rule Sup_least, clarsimp)+
    apply (subst inf_commute, simp)
    done

  finally show "\<Squnion>x \<sqinter> \<Sqinter>(Sup ` F) \<le> \<Squnion>(Inf ` {insert (f x) (f ` F) |f. f x \<in> x \<and> (\<forall>Y\<in>F. f Y \<in> Y)})"
    by simp
qed

subclass complete_distrib_lattice
  by (standard, rule finite_Inf_Sup)
end

instantiation finite_3 :: finite_lattice
begin

definition "\<Sqinter>A = (if a\<^sub>1 \<in> A then a\<^sub>1 else if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>3)"
definition "\<Squnion>A = (if a\<^sub>3 \<in> A then a\<^sub>3 else if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>1)"
definition [simp]: "bot = a\<^sub>1"
definition [simp]: "top = a\<^sub>3"
definition [simp]: "inf = (min :: finite_3 \<Rightarrow> _)"
definition [simp]: "sup = (max :: finite_3 \<Rightarrow> _)"

instance
proof
qed (auto simp add: Inf_finite_3_def Sup_finite_3_def max_def min_def less_eq_finite_3_def less_finite_3_def split: finite_3.split)
end

instance finite_3 :: complete_lattice ..

instance finite_3 :: finite_distrib_lattice
proof 
qed (auto simp add: min_def max_def)

instance finite_3 :: complete_distrib_lattice ..

instance finite_3 :: complete_linorder ..

instantiation finite_3 :: "{field, idom_abs_sgn, idom_modulo}" begin
definition [simp]: "0 = a\<^sub>1"
definition [simp]: "1 = a\<^sub>2"
definition
  "x + y = (case (x, y) of
     (a\<^sub>1, a\<^sub>1) \<Rightarrow> a\<^sub>1 | (a\<^sub>2, a\<^sub>3) \<Rightarrow> a\<^sub>1 | (a\<^sub>3, a\<^sub>2) \<Rightarrow> a\<^sub>1
   | (a\<^sub>1, a\<^sub>2) \<Rightarrow> a\<^sub>2 | (a\<^sub>2, a\<^sub>1) \<Rightarrow> a\<^sub>2 | (a\<^sub>3, a\<^sub>3) \<Rightarrow> a\<^sub>2
   | _ \<Rightarrow> a\<^sub>3)"
definition "- x = (case x of a\<^sub>1 \<Rightarrow> a\<^sub>1 | a\<^sub>2 \<Rightarrow> a\<^sub>3 | a\<^sub>3 \<Rightarrow> a\<^sub>2)"
definition "x - y = x + (- y :: finite_3)"
definition "x * y = (case (x, y) of (a\<^sub>2, a\<^sub>2) \<Rightarrow> a\<^sub>2 | (a\<^sub>3, a\<^sub>3) \<Rightarrow> a\<^sub>2 | (a\<^sub>2, a\<^sub>3) \<Rightarrow> a\<^sub>3 | (a\<^sub>3, a\<^sub>2) \<Rightarrow> a\<^sub>3 | _ \<Rightarrow> a\<^sub>1)"
definition "inverse = (\<lambda>x :: finite_3. x)" 
definition "x div y = x * inverse (y :: finite_3)"
definition "x mod y = (case y of a\<^sub>1 \<Rightarrow> x | _ \<Rightarrow> a\<^sub>1)"
definition "abs = (\<lambda>x. case x of a\<^sub>3 \<Rightarrow> a\<^sub>2 | _ \<Rightarrow> x)"
definition "sgn = (\<lambda>x :: finite_3. x)"
instance
  by standard
    (subproofs
      \<open>simp_all add: plus_finite_3_def uminus_finite_3_def minus_finite_3_def
        times_finite_3_def
        inverse_finite_3_def divide_finite_3_def modulo_finite_3_def
        abs_finite_3_def sgn_finite_3_def
        less_finite_3_def
        split: finite_3.splits\<close>)
end

lemma two_finite_3 [simp]:
  "2 = a\<^sub>3"
  by (simp add: numeral.simps plus_finite_3_def)

lemma dvd_finite_3_unfold:
  "x dvd y \<longleftrightarrow> x = a\<^sub>2 \<or> x = a\<^sub>3 \<or> y = a\<^sub>1"
  by (cases x) (auto simp add: dvd_def times_finite_3_def split: finite_3.splits)

instantiation finite_3 :: "{normalization_semidom, unique_euclidean_semiring}" begin
definition [simp]: "normalize x = (case x of a\<^sub>3 \<Rightarrow> a\<^sub>2 | _ \<Rightarrow> x)"
definition [simp]: "unit_factor = (id :: finite_3 \<Rightarrow> _)"
definition [simp]: "euclidean_size x = (case x of a\<^sub>1 \<Rightarrow> 0 | _ \<Rightarrow> 1)"
definition [simp]: "division_segment (x :: finite_3) = 1"
instance
proof
  fix x :: finite_3
  assume "x \<noteq> 0"
  then show "is_unit (unit_factor x)"
    by (cases x) (simp_all add: dvd_finite_3_unfold)
qed
  (subproofs
    \<open>auto simp add: divide_finite_3_def times_finite_3_def
      dvd_finite_3_unfold inverse_finite_3_def plus_finite_3_def
      split: finite_3.splits\<close>)
end

hide_const (open) a\<^sub>1 a\<^sub>2 a\<^sub>3

datatype (plugins only: code "quickcheck" extraction) finite_4 =
  a\<^sub>1 | a\<^sub>2 | a\<^sub>3 | a\<^sub>4

notation (output) a\<^sub>1  (\<open>a\<^sub>1\<close>)
notation (output) a\<^sub>2  (\<open>a\<^sub>2\<close>)
notation (output) a\<^sub>3  (\<open>a\<^sub>3\<close>)
notation (output) a\<^sub>4  (\<open>a\<^sub>4\<close>)

lemma UNIV_finite_4:
  "UNIV = {a\<^sub>1, a\<^sub>2, a\<^sub>3, a\<^sub>4}"
  by (auto intro: finite_4.exhaust)

instantiation finite_4 :: enum
begin

definition
  "enum = [a\<^sub>1, a\<^sub>2, a\<^sub>3, a\<^sub>4]"

definition
  "enum_all P \<longleftrightarrow> P a\<^sub>1 \<and> P a\<^sub>2 \<and> P a\<^sub>3 \<and> P a\<^sub>4"

definition
  "enum_ex P \<longleftrightarrow> P a\<^sub>1 \<or> P a\<^sub>2 \<or> P a\<^sub>3 \<or> P a\<^sub>4"

instance proof
qed (simp_all only: enum_finite_4_def enum_all_finite_4_def enum_ex_finite_4_def UNIV_finite_4, simp_all)

end

instantiation finite_4 :: finite_distrib_lattice begin

text \<open>\<^term>\<open>a\<^sub>1\<close> $<$ \<^term>\<open>a\<^sub>2\<close>,\<^term>\<open>a\<^sub>3\<close> $<$ \<^term>\<open>a\<^sub>4\<close>,
  but \<^term>\<open>a\<^sub>2\<close> and \<^term>\<open>a\<^sub>3\<close> are incomparable.\<close>

definition
  "x < y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>1, a\<^sub>1) \<Rightarrow> False | (a\<^sub>1, _) \<Rightarrow> True
   |  (a\<^sub>2, a\<^sub>4) \<Rightarrow> True
   |  (a\<^sub>3, a\<^sub>4) \<Rightarrow> True  | _ \<Rightarrow> False)"

definition 
  "x \<le> y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>1, _) \<Rightarrow> True
   | (a\<^sub>2, a\<^sub>2) \<Rightarrow> True | (a\<^sub>2, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>3, a\<^sub>3) \<Rightarrow> True | (a\<^sub>3, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>4, a\<^sub>4) \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  "\<Sqinter>A = (if a\<^sub>1 \<in> A \<or> a\<^sub>2 \<in> A \<and> a\<^sub>3 \<in> A then a\<^sub>1 else if a\<^sub>2 \<in> A then a\<^sub>2 else if a\<^sub>3 \<in> A then a\<^sub>3 else a\<^sub>4)"
definition
  "\<Squnion>A = (if a\<^sub>4 \<in> A \<or> a\<^sub>2 \<in> A \<and> a\<^sub>3 \<in> A then a\<^sub>4 else if a\<^sub>2 \<in> A then a\<^sub>2 else if a\<^sub>3 \<in> A then a\<^sub>3 else a\<^sub>1)"
definition [simp]: "bot = a\<^sub>1"
definition [simp]: "top = a\<^sub>4"
definition
  "x \<sqinter> y = (case (x, y) of
     (a\<^sub>1, _) \<Rightarrow> a\<^sub>1 | (_, a\<^sub>1) \<Rightarrow> a\<^sub>1 | (a\<^sub>2, a\<^sub>3) \<Rightarrow> a\<^sub>1 | (a\<^sub>3, a\<^sub>2) \<Rightarrow> a\<^sub>1
   | (a\<^sub>2, _) \<Rightarrow> a\<^sub>2 | (_, a\<^sub>2) \<Rightarrow> a\<^sub>2
   | (a\<^sub>3, _) \<Rightarrow> a\<^sub>3 | (_, a\<^sub>3) \<Rightarrow> a\<^sub>3
   | _ \<Rightarrow> a\<^sub>4)"
definition
  "x \<squnion> y = (case (x, y) of
     (a\<^sub>4, _) \<Rightarrow> a\<^sub>4 | (_, a\<^sub>4) \<Rightarrow> a\<^sub>4 | (a\<^sub>2, a\<^sub>3) \<Rightarrow> a\<^sub>4 | (a\<^sub>3, a\<^sub>2) \<Rightarrow> a\<^sub>4
  | (a\<^sub>2, _) \<Rightarrow> a\<^sub>2 | (_, a\<^sub>2) \<Rightarrow> a\<^sub>2
  | (a\<^sub>3, _) \<Rightarrow> a\<^sub>3 | (_, a\<^sub>3) \<Rightarrow> a\<^sub>3
  | _ \<Rightarrow> a\<^sub>1)"

instance
  by standard
    (subproofs
      \<open>auto simp add: less_finite_4_def less_eq_finite_4_def Inf_finite_4_def Sup_finite_4_def 
        inf_finite_4_def sup_finite_4_def split: finite_4.splits\<close>)
end

instance finite_4 :: complete_lattice ..

instance finite_4 :: complete_distrib_lattice ..

instantiation finite_4 :: complete_boolean_algebra begin
definition "- x = (case x of a\<^sub>1 \<Rightarrow> a\<^sub>4 | a\<^sub>2 \<Rightarrow> a\<^sub>3 | a\<^sub>3 \<Rightarrow> a\<^sub>2 | a\<^sub>4 \<Rightarrow> a\<^sub>1)"
definition "x - y = x \<sqinter> - (y :: finite_4)"
instance
  by standard
    (subproofs
      \<open>simp_all add: inf_finite_4_def sup_finite_4_def uminus_finite_4_def minus_finite_4_def 
        split: finite_4.splits\<close>)
end

hide_const (open) a\<^sub>1 a\<^sub>2 a\<^sub>3 a\<^sub>4

datatype (plugins only: code "quickcheck" extraction) finite_5 =
  a\<^sub>1 | a\<^sub>2 | a\<^sub>3 | a\<^sub>4 | a\<^sub>5

notation (output) a\<^sub>1  (\<open>a\<^sub>1\<close>)
notation (output) a\<^sub>2  (\<open>a\<^sub>2\<close>)
notation (output) a\<^sub>3  (\<open>a\<^sub>3\<close>)
notation (output) a\<^sub>4  (\<open>a\<^sub>4\<close>)
notation (output) a\<^sub>5  (\<open>a\<^sub>5\<close>)

lemma UNIV_finite_5:
  "UNIV = {a\<^sub>1, a\<^sub>2, a\<^sub>3, a\<^sub>4, a\<^sub>5}"
  by (auto intro: finite_5.exhaust)

instantiation finite_5 :: enum
begin

definition
  "enum = [a\<^sub>1, a\<^sub>2, a\<^sub>3, a\<^sub>4, a\<^sub>5]"

definition
  "enum_all P \<longleftrightarrow> P a\<^sub>1 \<and> P a\<^sub>2 \<and> P a\<^sub>3 \<and> P a\<^sub>4 \<and> P a\<^sub>5"

definition
  "enum_ex P \<longleftrightarrow> P a\<^sub>1 \<or> P a\<^sub>2 \<or> P a\<^sub>3 \<or> P a\<^sub>4 \<or> P a\<^sub>5"

instance proof
qed (simp_all only: enum_finite_5_def enum_all_finite_5_def enum_ex_finite_5_def UNIV_finite_5, simp_all)

end

instantiation finite_5 :: finite_lattice
begin

text \<open>The non-distributive pentagon lattice $N_5$\<close>

definition
  "x < y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>1, a\<^sub>1) \<Rightarrow> False | (a\<^sub>1, _) \<Rightarrow> True
   | (a\<^sub>2, a\<^sub>3) \<Rightarrow> True  | (a\<^sub>2, a\<^sub>5) \<Rightarrow> True
   | (a\<^sub>3, a\<^sub>5) \<Rightarrow> True
   | (a\<^sub>4, a\<^sub>5) \<Rightarrow> True  | _ \<Rightarrow> False)"

definition
  "x \<le> y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>1, _) \<Rightarrow> True
   | (a\<^sub>2, a\<^sub>2) \<Rightarrow> True | (a\<^sub>2, a\<^sub>3) \<Rightarrow> True | (a\<^sub>2, a\<^sub>5) \<Rightarrow> True
   | (a\<^sub>3, a\<^sub>3) \<Rightarrow> True | (a\<^sub>3, a\<^sub>5) \<Rightarrow> True
   | (a\<^sub>4, a\<^sub>4) \<Rightarrow> True | (a\<^sub>4, a\<^sub>5) \<Rightarrow> True
   | (a\<^sub>5, a\<^sub>5) \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  "\<Sqinter>A = 
  (if a\<^sub>1 \<in> A \<or> a\<^sub>4 \<in> A \<and> (a\<^sub>2 \<in> A \<or> a\<^sub>3 \<in> A) then a\<^sub>1
   else if a\<^sub>2 \<in> A then a\<^sub>2
   else if a\<^sub>3 \<in> A then a\<^sub>3
   else if a\<^sub>4 \<in> A then a\<^sub>4
   else a\<^sub>5)"
definition
  "\<Squnion>A = 
  (if a\<^sub>5 \<in> A \<or> a\<^sub>4 \<in> A \<and> (a\<^sub>2 \<in> A \<or> a\<^sub>3 \<in> A) then a\<^sub>5
   else if a\<^sub>3 \<in> A then a\<^sub>3
   else if a\<^sub>2 \<in> A then a\<^sub>2
   else if a\<^sub>4 \<in> A then a\<^sub>4
   else a\<^sub>1)"
definition [simp]: "bot = a\<^sub>1"
definition [simp]: "top = a\<^sub>5"
definition
  "x \<sqinter> y = (case (x, y) of
     (a\<^sub>1, _) \<Rightarrow> a\<^sub>1 | (_, a\<^sub>1) \<Rightarrow> a\<^sub>1 | (a\<^sub>2, a\<^sub>4) \<Rightarrow> a\<^sub>1 | (a\<^sub>4, a\<^sub>2) \<Rightarrow> a\<^sub>1 | (a\<^sub>3, a\<^sub>4) \<Rightarrow> a\<^sub>1 | (a\<^sub>4, a\<^sub>3) \<Rightarrow> a\<^sub>1
   | (a\<^sub>2, _) \<Rightarrow> a\<^sub>2 | (_, a\<^sub>2) \<Rightarrow> a\<^sub>2
   | (a\<^sub>3, _) \<Rightarrow> a\<^sub>3 | (_, a\<^sub>3) \<Rightarrow> a\<^sub>3
   | (a\<^sub>4, _) \<Rightarrow> a\<^sub>4 | (_, a\<^sub>4) \<Rightarrow> a\<^sub>4
   | _ \<Rightarrow> a\<^sub>5)"
definition
  "x \<squnion> y = (case (x, y) of
     (a\<^sub>5, _) \<Rightarrow> a\<^sub>5 | (_, a\<^sub>5) \<Rightarrow> a\<^sub>5 | (a\<^sub>2, a\<^sub>4) \<Rightarrow> a\<^sub>5 | (a\<^sub>4, a\<^sub>2) \<Rightarrow> a\<^sub>5 | (a\<^sub>3, a\<^sub>4) \<Rightarrow> a\<^sub>5 | (a\<^sub>4, a\<^sub>3) \<Rightarrow> a\<^sub>5
   | (a\<^sub>3, _) \<Rightarrow> a\<^sub>3 | (_, a\<^sub>3) \<Rightarrow> a\<^sub>3
   | (a\<^sub>2, _) \<Rightarrow> a\<^sub>2 | (_, a\<^sub>2) \<Rightarrow> a\<^sub>2
   | (a\<^sub>4, _) \<Rightarrow> a\<^sub>4 | (_, a\<^sub>4) \<Rightarrow> a\<^sub>4
   | _ \<Rightarrow> a\<^sub>1)"

instance
  by standard
    (subproofs
      \<open>auto simp add: less_eq_finite_5_def less_finite_5_def inf_finite_5_def sup_finite_5_def 
        Inf_finite_5_def Sup_finite_5_def split: finite_5.splits if_split_asm\<close>)
end


instance  finite_5 :: complete_lattice ..


hide_const (open) a\<^sub>1 a\<^sub>2 a\<^sub>3 a\<^sub>4 a\<^sub>5


subsection \<open>Closing up\<close>

hide_type (open) finite_1 finite_2 finite_3 finite_4 finite_5
hide_const (open) enum enum_all enum_ex all_n_lists ex_n_lists ntrancl

end
