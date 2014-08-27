(* Author: Florian Haftmann, TU Muenchen *)

header {* Finite types as explicit enumerations *}

theory Enum
imports Map
begin

subsection {* Class @{text enum} *}

class enum =
  fixes enum :: "'a list"
  fixes enum_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  fixes enum_ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  assumes UNIV_enum: "UNIV = set enum"
    and enum_distinct: "distinct enum"
  assumes enum_all_UNIV: "enum_all P \<longleftrightarrow> Ball UNIV P"
  assumes enum_ex_UNIV: "enum_ex P \<longleftrightarrow> Bex UNIV P" 
   -- {* tailored towards simple instantiation *}
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


subsection {* Implementations using @{class enum} *}

subsubsection {* Unbounded operations and quantifiers *}

lemma Collect_code [code]:
  "Collect P = set (filter P enum)"
  by (simp add: enum_UNIV)

lemma vimage_code [code]:
  "f -` B = set (filter (%x. f x : B) enum_class.enum)"
  unfolding vimage_def Collect_code ..

definition card_UNIV :: "'a itself \<Rightarrow> nat"
where
  [code del]: "card_UNIV TYPE('a) = card (UNIV :: 'a set)"

lemma [code]:
  "card_UNIV TYPE('a :: enum) = card (set (Enum.enum :: 'a list))"
  by (simp only: card_UNIV_def enum_UNIV)

lemma all_code [code]: "(\<forall>x. P x) \<longleftrightarrow> enum_all P"
  by simp

lemma exists_code [code]: "(\<exists>x. P x) \<longleftrightarrow> enum_ex P"
  by simp

lemma exists1_code [code]: "(\<exists>!x. P x) \<longleftrightarrow> list_ex1 P enum"
  by (auto simp add: list_ex1_iff enum_UNIV)


subsubsection {* An executable choice operator *}

definition
  [code del]: "enum_the = The"

lemma [code]:
  "The P = (case filter P enum of [x] => x | _ => enum_the P)"
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
        with `P x` in_enum[of x, unfolded enum_eq] `x \<noteq> a` show "False" by auto
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


subsubsection {* Equality and order on functions *}

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
  fixes f g :: "'a\<Colon>enum \<Rightarrow> 'b\<Colon>order"
  shows "f \<le> g \<longleftrightarrow> enum_all (\<lambda>x. f x \<le> g x)"
    and "f < g \<longleftrightarrow> f \<le> g \<and> enum_ex (\<lambda>x. f x \<noteq> g x)"
  by (simp_all add: fun_eq_iff le_fun_def order_less_le)


subsubsection {* Operations on relations *}

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


subsubsection {* Bounded accessible part *}

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
  assume "x : Wellfounded.acc r"
  then have "\<exists> n. x : bacc r n"
  proof (induct x arbitrary: rule: acc.induct)
    case (accI x)
    then have "\<forall>y. \<exists> n. (y, x) \<in> r --> y : bacc r n" by simp
    from choice[OF this] obtain n where n: "\<forall>y. (y, x) \<in> r \<longrightarrow> y \<in> bacc r (n y)" ..
    obtain n where "\<And>y. (y, x) : r \<Longrightarrow> y : bacc r n"
    proof
      fix y assume y: "(y, x) : r"
      with n have "y : bacc r (n y)" by auto
      moreover have "n y <= Max ((%(y, x). n y) ` r)"
        using y `finite r` by (auto intro!: Max_ge)
      note bacc_mono[OF this, of r]
      ultimately show "y : bacc r (Max ((%(y, x). n y) ` r))" by auto
    qed
    then show ?case
      by (auto simp add: Let_def intro!: exI[of _ "Suc n"])
  qed
  then show "x : (UN n. bacc r n)" by auto
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


subsection {* Default instances for @{class enum} *}

lemma map_of_zip_enum_is_Some:
  assumes "length ys = length (enum \<Colon> 'a\<Colon>enum list)"
  shows "\<exists>y. map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x = Some y"
proof -
  from assms have "x \<in> set (enum \<Colon> 'a\<Colon>enum list) \<longleftrightarrow>
    (\<exists>y. map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x = Some y)"
    by (auto intro!: map_of_zip_is_Some)
  then show ?thesis using enum_UNIV by auto
qed

lemma map_of_zip_enum_inject:
  fixes xs ys :: "'b\<Colon>enum list"
  assumes length: "length xs = length (enum \<Colon> 'a\<Colon>enum list)"
      "length ys = length (enum \<Colon> 'a\<Colon>enum list)"
    and map_of: "the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) xs) = the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys)"
  shows "xs = ys"
proof -
  have "map_of (zip (enum \<Colon> 'a list) xs) = map_of (zip (enum \<Colon> 'a list) ys)"
  proof
    fix x :: 'a
    from length map_of_zip_enum_is_Some obtain y1 y2
      where "map_of (zip (enum \<Colon> 'a list) xs) x = Some y1"
        and "map_of (zip (enum \<Colon> 'a list) ys) x = Some y2" by blast
    moreover from map_of
      have "the (map_of (zip (enum \<Colon> 'a\<Colon>enum list) xs) x) = the (map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x)"
      by (auto dest: fun_cong)
    ultimately show "map_of (zip (enum \<Colon> 'a\<Colon>enum list) xs) x = map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x"
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
  "enum = map (\<lambda>ys. the o map_of (zip (enum\<Colon>'a list) ys)) (List.n_lists (length (enum\<Colon>'a\<Colon>enum list)) enum)"

definition
  "enum_all P = all_n_lists (\<lambda>bs. P (the o map_of (zip enum bs))) (length (enum :: 'a list))"

definition
  "enum_ex P = ex_n_lists (\<lambda>bs. P (the o map_of (zip enum bs))) (length (enum :: 'a list))"

instance proof
  show "UNIV = set (enum \<Colon> ('a \<Rightarrow> 'b) list)"
  proof (rule UNIV_eq_I)
    fix f :: "'a \<Rightarrow> 'b"
    have "f = the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) (map f enum))"
      by (auto simp add: map_of_zip_map fun_eq_iff intro: in_enum)
    then show "f \<in> set enum"
      by (auto simp add: enum_fun_def set_n_lists intro: in_enum)
  qed
next
  from map_of_zip_enum_inject
  show "distinct (enum \<Colon> ('a \<Rightarrow> 'b) list)"
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
      have f: "f = the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) (map f enum))"
        by (auto simp add: map_of_zip_map fun_eq_iff intro: in_enum)
      from `enum_all P` have "P (the \<circ> map_of (zip enum (map f enum)))"
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
    have f: "f = the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) (map f enum))"
      by (auto simp add: map_of_zip_map fun_eq_iff intro: in_enum) 
    from `P f` this have "P (the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) (map f enum)))"
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

lemma enum_fun_code [code]: "enum = (let enum_a = (enum \<Colon> 'a\<Colon>{enum, equal} list)
  in map (\<lambda>ys. the o map_of (zip enum_a ys)) (List.n_lists (length enum_a) enum))"
  by (simp add: enum_fun_def Let_def)

lemma enum_all_fun_code [code]:
  "enum_all P = (let enum_a = (enum :: 'a::{enum, equal} list)
   in all_n_lists (\<lambda>bs. P (the o map_of (zip enum_a bs))) (length enum_a))"
  by (simp only: enum_all_fun_def Let_def)

lemma enum_ex_fun_code [code]:
  "enum_ex P = (let enum_a = (enum :: 'a::{enum, equal} list)
   in ex_n_lists (\<lambda>bs. P (the o map_of (zip enum_a bs))) (length enum_a))"
  by (simp only: enum_ex_fun_def Let_def)

instantiation set :: (enum) enum
begin

definition
  "enum = map set (sublists enum)"

definition
  "enum_all P \<longleftrightarrow> (\<forall>A\<in>set enum. P (A::'a set))"

definition
  "enum_ex P \<longleftrightarrow> (\<exists>A\<in>set enum. P (A::'a set))"

instance proof
qed (simp_all add: enum_set_def enum_all_set_def enum_ex_set_def sublists_powset distinct_set_sublists
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

 
instance by default
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


subsection {* Small finite types *}

text {* We define small finite types for the use in Quickcheck *}

datatype finite_1 = a\<^sub>1

notation (output) a\<^sub>1  ("a\<^sub>1")

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
apply (metis finite_1.exhaust)
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
by intro_classes(simp_all add: INF_def SUP_def)

instance finite_1 :: complete_linorder ..

lemma finite_1_eq: "x = a\<^sub>1"
by(cases x) simp

simproc_setup finite_1_eq ("x::finite_1") = {*
  fn _ => fn _ => fn ct => case term_of ct of
    Const (@{const_name a\<^sub>1}, _) => NONE
  | _ => SOME (mk_meta_eq @{thm finite_1_eq})
*}

instantiation finite_1 :: complete_boolean_algebra begin
definition [simp]: "op - = (\<lambda>_ _. a\<^sub>1)"
definition [simp]: "uminus = (\<lambda>_. a\<^sub>1)"
instance by intro_classes simp_all
end

instantiation finite_1 :: 
  "{linordered_ring_strict, linordered_comm_semiring_strict, ordered_comm_ring,
    ordered_cancel_comm_monoid_diff, comm_monoid_mult, ordered_ring_abs,
    one, Divides.div, sgn_if, inverse}"
begin
definition [simp]: "Groups.zero = a\<^sub>1"
definition [simp]: "Groups.one = a\<^sub>1"
definition [simp]: "op + = (\<lambda>_ _. a\<^sub>1)"
definition [simp]: "op * = (\<lambda>_ _. a\<^sub>1)"
definition [simp]: "op div = (\<lambda>_ _. a\<^sub>1)" 
definition [simp]: "op mod = (\<lambda>_ _. a\<^sub>1)" 
definition [simp]: "abs = (\<lambda>_. a\<^sub>1)"
definition [simp]: "sgn = (\<lambda>_. a\<^sub>1)"
definition [simp]: "inverse = (\<lambda>_. a\<^sub>1)"
definition [simp]: "op / = (\<lambda>_ _. a\<^sub>1)"

instance by intro_classes(simp_all add: less_finite_1_def)
end

declare [[simproc del: finite_1_eq]]
hide_const (open) a\<^sub>1

datatype finite_2 = a\<^sub>1 | a\<^sub>2

notation (output) a\<^sub>1  ("a\<^sub>1")
notation (output) a\<^sub>2  ("a\<^sub>2")

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
    by(case_tac [!] x)(auto simp add: less_eq_finite_2_def less_finite_2_def Inf_finite_2_def Sup_finite_2_def)
qed(auto simp add: less_eq_finite_2_def less_finite_2_def inf_finite_2_def sup_finite_2_def Inf_finite_2_def Sup_finite_2_def)
end

instance finite_2 :: complete_distrib_lattice
by(intro_classes)(auto simp add: INF_def SUP_def sup_finite_2_def inf_finite_2_def Inf_finite_2_def Sup_finite_2_def)

instance finite_2 :: complete_linorder ..

instantiation finite_2 :: "{field_inverse_zero, abs_if, ring_div, semiring_div_parity, sgn_if}" begin
definition [simp]: "0 = a\<^sub>1"
definition [simp]: "1 = a\<^sub>2"
definition "x + y = (case (x, y) of (a\<^sub>1, a\<^sub>1) \<Rightarrow> a\<^sub>1 | (a\<^sub>2, a\<^sub>2) \<Rightarrow> a\<^sub>1 | _ \<Rightarrow> a\<^sub>2)"
definition "uminus = (\<lambda>x :: finite_2. x)"
definition "op - = (op + :: finite_2 \<Rightarrow> _)"
definition "x * y = (case (x, y) of (a\<^sub>2, a\<^sub>2) \<Rightarrow> a\<^sub>2 | _ \<Rightarrow> a\<^sub>1)"
definition "inverse = (\<lambda>x :: finite_2. x)"
definition "op / = (op * :: finite_2 \<Rightarrow> _)"
definition "abs = (\<lambda>x :: finite_2. x)"
definition "op div = (op / :: finite_2 \<Rightarrow> _)"
definition "x mod y = (case (x, y) of (a\<^sub>2, a\<^sub>1) \<Rightarrow> a\<^sub>2 | _ \<Rightarrow> a\<^sub>1)"
definition "sgn = (\<lambda>x :: finite_2. x)"
instance
by intro_classes
  (simp_all add: plus_finite_2_def uminus_finite_2_def minus_finite_2_def times_finite_2_def
       inverse_finite_2_def divide_finite_2_def abs_finite_2_def div_finite_2_def mod_finite_2_def sgn_finite_2_def
     split: finite_2.splits)
end

hide_const (open) a\<^sub>1 a\<^sub>2

datatype finite_3 = a\<^sub>1 | a\<^sub>2 | a\<^sub>3

notation (output) a\<^sub>1  ("a\<^sub>1")
notation (output) a\<^sub>2  ("a\<^sub>2")
notation (output) a\<^sub>3  ("a\<^sub>3")

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

instantiation finite_3 :: complete_lattice
begin

definition "\<Sqinter>A = (if a\<^sub>1 \<in> A then a\<^sub>1 else if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>3)"
definition "\<Squnion>A = (if a\<^sub>3 \<in> A then a\<^sub>3 else if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>1)"
definition [simp]: "bot = a\<^sub>1"
definition [simp]: "top = a\<^sub>3"
definition [simp]: "inf = (min :: finite_3 \<Rightarrow> _)"
definition [simp]: "sup = (max :: finite_3 \<Rightarrow> _)"

instance
proof
  fix x :: finite_3 and A
  assume "x \<in> A"
  then show "\<Sqinter>A \<le> x" "x \<le> \<Squnion>A"
    by(case_tac [!] x)(auto simp add: Inf_finite_3_def Sup_finite_3_def less_eq_finite_3_def less_finite_3_def)
next
  fix A and z :: finite_3
  assume "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  then show "z \<le> \<Sqinter>A"
    by(cases z)(auto simp add: Inf_finite_3_def less_eq_finite_3_def less_finite_3_def)
next
  fix A and z :: finite_3
  assume *: "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  show "\<Squnion>A \<le> z"
    by(auto simp add: Sup_finite_3_def less_eq_finite_3_def less_finite_3_def dest: *)
qed(auto simp add: Inf_finite_3_def Sup_finite_3_def)
end

instance finite_3 :: complete_distrib_lattice
proof
  fix a :: finite_3 and B
  show "a \<squnion> \<Sqinter>B = (\<Sqinter>b\<in>B. a \<squnion> b)"
  proof(cases a "\<Sqinter>B" rule: finite_3.exhaust[case_product finite_3.exhaust])
    case a\<^sub>2_a\<^sub>3
    then have "\<And>x. x \<in> B \<Longrightarrow> x = a\<^sub>3"
      by(case_tac x)(auto simp add: Inf_finite_3_def split: split_if_asm)
    then show ?thesis using a\<^sub>2_a\<^sub>3
      by(auto simp add: INF_def Inf_finite_3_def max_def less_eq_finite_3_def less_finite_3_def split: split_if_asm)
  qed(auto simp add: INF_def Inf_finite_3_def max_def less_finite_3_def less_eq_finite_3_def split: split_if_asm)
  show "a \<sqinter> \<Squnion>B = (\<Squnion>b\<in>B. a \<sqinter> b)"
    by(cases a "\<Squnion>B" rule: finite_3.exhaust[case_product finite_3.exhaust])
      (auto simp add: SUP_def Sup_finite_3_def min_def less_finite_3_def less_eq_finite_3_def split: split_if_asm)
qed

instance finite_3 :: complete_linorder ..

instantiation finite_3 :: "{field_inverse_zero, abs_if, ring_div, semiring_div, sgn_if}" begin
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
definition "x / y = x * inverse (y :: finite_3)"
definition "abs = (\<lambda>x :: finite_3. x)"
definition "op div = (op / :: finite_3 \<Rightarrow> _)"
definition "x mod y = (case (x, y) of (a\<^sub>2, a\<^sub>1) \<Rightarrow> a\<^sub>2 | (a\<^sub>3, a\<^sub>1) \<Rightarrow> a\<^sub>3 | _ \<Rightarrow> a\<^sub>1)"
definition "sgn = (\<lambda>x. case x of a\<^sub>1 \<Rightarrow> a\<^sub>1 | _ \<Rightarrow> a\<^sub>2)"
instance
by intro_classes
  (simp_all add: plus_finite_3_def uminus_finite_3_def minus_finite_3_def times_finite_3_def
       inverse_finite_3_def divide_finite_3_def abs_finite_3_def div_finite_3_def mod_finite_3_def sgn_finite_3_def
       less_finite_3_def
     split: finite_3.splits)
end

hide_const (open) a\<^sub>1 a\<^sub>2 a\<^sub>3

datatype finite_4 = a\<^sub>1 | a\<^sub>2 | a\<^sub>3 | a\<^sub>4

notation (output) a\<^sub>1  ("a\<^sub>1")
notation (output) a\<^sub>2  ("a\<^sub>2")
notation (output) a\<^sub>3  ("a\<^sub>3")
notation (output) a\<^sub>4  ("a\<^sub>4")

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

instantiation finite_4 :: complete_lattice begin

text {* @{term a\<^sub>1} $<$ @{term a\<^sub>2},@{term a\<^sub>3} $<$ @{term a\<^sub>4},
  but @{term a\<^sub>2} and @{term a\<^sub>3} are incomparable. *}

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
proof
  fix A and z :: finite_4
  assume *: "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  show "\<Squnion>A \<le> z"
    by(auto simp add: Sup_finite_4_def less_eq_finite_4_def dest!: * split: finite_4.splits)
next
  fix A and z :: finite_4
  assume *: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  show "z \<le> \<Sqinter>A"
    by(auto simp add: Inf_finite_4_def less_eq_finite_4_def dest!: * split: finite_4.splits)
qed(auto simp add: less_finite_4_def less_eq_finite_4_def Inf_finite_4_def Sup_finite_4_def inf_finite_4_def sup_finite_4_def split: finite_4.splits)

end

instance finite_4 :: complete_distrib_lattice
proof
  fix a :: finite_4 and B
  show "a \<squnion> \<Sqinter>B = (\<Sqinter>b\<in>B. a \<squnion> b)"
    by(cases a "\<Sqinter>B" rule: finite_4.exhaust[case_product finite_4.exhaust])
      (auto simp add: sup_finite_4_def Inf_finite_4_def INF_def split: finite_4.splits split_if_asm)
  show "a \<sqinter> \<Squnion>B = (\<Squnion>b\<in>B. a \<sqinter> b)"
    by(cases a "\<Squnion>B" rule: finite_4.exhaust[case_product finite_4.exhaust])
      (auto simp add: inf_finite_4_def Sup_finite_4_def SUP_def split: finite_4.splits split_if_asm)
qed

instantiation finite_4 :: complete_boolean_algebra begin
definition "- x = (case x of a\<^sub>1 \<Rightarrow> a\<^sub>4 | a\<^sub>2 \<Rightarrow> a\<^sub>3 | a\<^sub>3 \<Rightarrow> a\<^sub>2 | a\<^sub>4 \<Rightarrow> a\<^sub>1)"
definition "x - y = x \<sqinter> - (y :: finite_4)"
instance
by intro_classes
  (simp_all add: inf_finite_4_def sup_finite_4_def uminus_finite_4_def minus_finite_4_def split: finite_4.splits)
end

hide_const (open) a\<^sub>1 a\<^sub>2 a\<^sub>3 a\<^sub>4


datatype finite_5 = a\<^sub>1 | a\<^sub>2 | a\<^sub>3 | a\<^sub>4 | a\<^sub>5

notation (output) a\<^sub>1  ("a\<^sub>1")
notation (output) a\<^sub>2  ("a\<^sub>2")
notation (output) a\<^sub>3  ("a\<^sub>3")
notation (output) a\<^sub>4  ("a\<^sub>4")
notation (output) a\<^sub>5  ("a\<^sub>5")

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

instantiation finite_5 :: complete_lattice
begin

text {* The non-distributive pentagon lattice $N_5$ *}

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
proof intro_classes
  fix A and z :: finite_5
  assume *: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  show "z \<le> \<Sqinter>A"
    by(auto simp add: less_eq_finite_5_def Inf_finite_5_def split: finite_5.splits split_if_asm dest!: *)
next
  fix A and z :: finite_5
  assume *: "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  show "\<Squnion>A \<le> z"
    by(auto simp add: less_eq_finite_5_def Sup_finite_5_def split: finite_5.splits split_if_asm dest!: *)
qed(auto simp add: less_eq_finite_5_def less_finite_5_def inf_finite_5_def sup_finite_5_def Inf_finite_5_def Sup_finite_5_def split: finite_5.splits split_if_asm)

end

hide_const (open) a\<^sub>1 a\<^sub>2 a\<^sub>3 a\<^sub>4 a\<^sub>5


subsection {* Closing up *}

hide_type (open) finite_1 finite_2 finite_3 finite_4 finite_5
hide_const (open) enum enum_all enum_ex all_n_lists ex_n_lists ntrancl

end
