(*  Title:      HOL/Library/Enum.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Finite types as explicit enumerations *}

theory Enum
imports Main
begin

subsection {* Class @{text enum} *}

class enum = finite + -- FIXME
  fixes enum :: "'a list"
  assumes enum_all: "set enum = UNIV"
begin

lemma in_enum [intro]: "x \<in> set enum"
  unfolding enum_all by auto

lemma enum_eq_I:
  assumes "\<And>x. x \<in> set xs"
  shows "set enum = set xs"
proof -
  from assms UNIV_eq_I have "UNIV = set xs" by auto
  with enum_all show ?thesis by simp
qed

end


subsection {* Equality and order on functions *}

declare eq_fun [code func del] order_fun [code func del]

instance "fun" :: (enum, eq) eq ..

lemma eq_fun [code func]:
  fixes f g :: "'a\<Colon>enum \<Rightarrow> 'b\<Colon>eq"
  shows "f = g \<longleftrightarrow> (\<forall>x \<in> set enum. f x = g x)"
  by (simp add: enum_all expand_fun_eq)

lemma order_fun [code func]:
  fixes f g :: "'a\<Colon>enum \<Rightarrow> 'b\<Colon>order"
  shows "f \<le> g \<longleftrightarrow> (\<forall>x \<in> set enum. f x \<le> g x)"
    and "f < g \<longleftrightarrow> f \<le> g \<and> (\<exists>x \<in> set enum. f x \<noteq> g x)"
  by (simp_all add: enum_all expand_fun_eq le_fun_def less_fun_def order_less_le)


subsection {* Default instances *}

instantiation unit :: enum
begin

definition
  "enum = [()]"

instance by default
  (simp add: enum_unit_def UNIV_unit)

end

instantiation bool :: enum
begin

definition
  "enum = [False, True]"

instance by default
  (simp add: enum_bool_def UNIV_bool)

end

primrec product :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "product [] _ = []"
  | "product (x#xs) ys = map (Pair x) ys @ product xs ys"

lemma product_list_set:
  "set (product xs ys) = set xs \<times> set ys"
  by (induct xs) auto

instantiation * :: (enum, enum) enum
begin

definition
  "enum = product enum enum"

instance by default
  (simp add: enum_prod_def product_list_set enum_all)

end

instantiation "+" :: (enum, enum) enum
begin

definition
  "enum = map Inl enum @ map Inr enum"

instance by default
  (auto simp add: enum_all enum_sum_def, case_tac x, auto)

end

primrec sublists :: "'a list \<Rightarrow> 'a list list" where
  "sublists [] = [[]]"
  | "sublists (x#xs) = (let xss = sublists xs in map (Cons x) xss @ xss)"

lemma sublists_powset:
  "set (map set (sublists xs)) = Pow (set xs)"
proof -
  have aux: "\<And>x A. set ` Cons x ` A = insert x ` set ` A"
    by (auto simp add: image_def)
  show ?thesis
    by (induct xs)
     (simp_all add: aux Let_def Pow_insert Un_commute)
qed

instantiation set :: (enum) enum
begin

definition
  "enum = map set (sublists enum)"

instance by default
  (simp add: enum_set_def sublists_powset enum_all del: set_map)

end

instantiation nibble :: enum
begin

definition
  "enum = [Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF]"

instance by default
  (simp add: enum_nibble_def UNIV_nibble)

end

instantiation char :: enum
begin

definition
  "enum = map (split Char) (product enum enum)"

instance by default
  (auto intro: char.exhaust simp add: enum_char_def product_list_set enum_all full_SetCompr_eq [symmetric])

end

(*instantiation "fun" :: (enum, enum) enum
begin


definition
  "enum 

lemma inj_graph: "inj (%f. {(x, y). y = f x})"
  by (rule inj_onI, auto simp add: expand_set_eq expand_fun_eq)

instance "fun" :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a => 'b) set)"
  proof (rule finite_imageD)
    let ?graph = "%f::'a => 'b. {(x, y). y = f x}"
    show "finite (range ?graph)" by (rule finite)
    show "inj ?graph" by (rule inj_graph)
  qed
qed*)

end