(*  Title:      HOL/Library/Enum.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Finite types as explicit enumerations *}

theory Enum
imports Plain "~~/src/HOL/Map"
begin

subsection {* Class @{text enum} *}

class enum =
  fixes enum :: "'a list"
  assumes UNIV_enum [code]: "UNIV = set enum"
    and enum_distinct: "distinct enum"
begin

subclass finite proof
qed (simp add: UNIV_enum)

lemma enum_all: "set enum = UNIV" unfolding UNIV_enum ..

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

instantiation "fun" :: (enum, eq) eq
begin

definition
  "eq_class.eq f g \<longleftrightarrow> (\<forall>x \<in> set enum. f x = g x)"

instance by default
  (simp_all add: eq_fun_def enum_all expand_fun_eq)

end

lemma order_fun [code]:
  fixes f g :: "'a\<Colon>enum \<Rightarrow> 'b\<Colon>order"
  shows "f \<le> g \<longleftrightarrow> list_all (\<lambda>x. f x \<le> g x) enum"
    and "f < g \<longleftrightarrow> f \<le> g \<and> \<not> list_all (\<lambda>x. f x = g x) enum"
  by (simp_all add: list_all_iff enum_all expand_fun_eq le_fun_def order_less_le)


subsection {* Quantifiers *}

lemma all_code [code]: "(\<forall>x. P x) \<longleftrightarrow> list_all P enum"
  by (simp add: list_all_iff enum_all)

lemma exists_code [code]: "(\<exists>x. P x) \<longleftrightarrow> \<not> list_all (Not o P) enum"
  by (simp add: list_all_iff enum_all)


subsection {* Default instances *}

primrec n_lists :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "n_lists 0 xs = [[]]"
  | "n_lists (Suc n) xs = concat (map (\<lambda>ys. map (\<lambda>y. y # ys) xs) (n_lists n xs))"

lemma n_lists_Nil [simp]: "n_lists n [] = (if n = 0 then [[]] else [])"
  by (induct n) simp_all

lemma length_n_lists: "length (n_lists n xs) = length xs ^ n"
  by (induct n) (auto simp add: length_concat map_compose [symmetric] o_def listsum_triv)

lemma length_n_lists_elem: "ys \<in> set (n_lists n xs) \<Longrightarrow> length ys = n"
  by (induct n arbitrary: ys) auto

lemma set_n_lists: "set (n_lists n xs) = {ys. length ys = n \<and> set ys \<subseteq> set xs}"
proof (rule set_ext)
  fix ys :: "'a list"
  show "ys \<in> set (n_lists n xs) \<longleftrightarrow> ys \<in> {ys. length ys = n \<and> set ys \<subseteq> set xs}"
  proof -
    have "ys \<in> set (n_lists n xs) \<Longrightarrow> length ys = n"
      by (induct n arbitrary: ys) auto
    moreover have "\<And>x. ys \<in> set (n_lists n xs) \<Longrightarrow> x \<in> set ys \<Longrightarrow> x \<in> set xs"
      by (induct n arbitrary: ys) auto
    moreover have "set ys \<subseteq> set xs \<Longrightarrow> ys \<in> set (n_lists (length ys) xs)"
      by (induct ys) auto
    ultimately show ?thesis by auto
  qed
qed

lemma distinct_n_lists:
  assumes "distinct xs"
  shows "distinct (n_lists n xs)"
proof (rule card_distinct)
  from assms have card_length: "card (set xs) = length xs" by (rule distinct_card)
  have "card (set (n_lists n xs)) = card (set xs) ^ n"
  proof (induct n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    moreover have "card (\<Union>ys\<in>set (n_lists n xs). (\<lambda>y. y # ys) ` set xs)
      = (\<Sum>ys\<in>set (n_lists n xs). card ((\<lambda>y. y # ys) ` set xs))"
      by (rule card_UN_disjoint) auto
    moreover have "\<And>ys. card ((\<lambda>y. y # ys) ` set xs) = card (set xs)"
      by (rule card_image) (simp add: inj_on_def)
    ultimately show ?case by auto
  qed
  also have "\<dots> = length xs ^ n" by (simp add: card_length)
  finally show "card (set (n_lists n xs)) = length (n_lists n xs)"
    by (simp add: length_n_lists)
qed

lemma map_of_zip_map:
  fixes f :: "'a\<Colon>enum \<Rightarrow> 'b\<Colon>enum"
  shows "map_of (zip xs (map f xs)) = (\<lambda>x. if x \<in> set xs then Some (f x) else None)"
  by (induct xs) (simp_all add: expand_fun_eq)

lemma map_of_zip_enum_is_Some:
  assumes "length ys = length (enum \<Colon> 'a\<Colon>enum list)"
  shows "\<exists>y. map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x = Some y"
proof -
  from assms have "x \<in> set (enum \<Colon> 'a\<Colon>enum list) \<longleftrightarrow>
    (\<exists>y. map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x = Some y)"
    by (auto intro!: map_of_zip_is_Some)
  then show ?thesis using enum_all by auto
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
    moreover from map_of have "the (map_of (zip (enum \<Colon> 'a\<Colon>enum list) xs) x) = the (map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x)"
      by (auto dest: fun_cong)
    ultimately show "map_of (zip (enum \<Colon> 'a\<Colon>enum list) xs) x = map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x"
      by simp
  qed
  with length enum_distinct show "xs = ys" by (rule map_of_zip_inject)
qed

instantiation "fun" :: (enum, enum) enum
begin

definition
  [code del]: "enum = map (\<lambda>ys. the o map_of (zip (enum\<Colon>'a list) ys)) (n_lists (length (enum\<Colon>'a\<Colon>enum list)) enum)"

instance proof
  show "UNIV = set (enum \<Colon> ('a \<Rightarrow> 'b) list)"
  proof (rule UNIV_eq_I)
    fix f :: "'a \<Rightarrow> 'b"
    have "f = the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) (map f enum))"
      by (auto simp add: map_of_zip_map expand_fun_eq)
    then show "f \<in> set enum"
      by (auto simp add: enum_fun_def set_n_lists)
  qed
next
  from map_of_zip_enum_inject
  show "distinct (enum \<Colon> ('a \<Rightarrow> 'b) list)"
    by (auto intro!: inj_onI simp add: enum_fun_def
      distinct_map distinct_n_lists enum_distinct set_n_lists enum_all)
qed

end

lemma enum_fun_code [code]: "enum = (let enum_a = (enum \<Colon> 'a\<Colon>{enum, eq} list)
  in map (\<lambda>ys. the o map_of (zip enum_a ys)) (n_lists (length enum_a) enum))"
  by (simp add: enum_fun_def Let_def)

instantiation unit :: enum
begin

definition
  "enum = [()]"

instance by default
  (simp_all add: enum_unit_def UNIV_unit)

end

instantiation bool :: enum
begin

definition
  "enum = [False, True]"

instance by default
  (simp_all add: enum_bool_def UNIV_bool)

end

primrec product :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "product [] _ = []"
  | "product (x#xs) ys = map (Pair x) ys @ product xs ys"

lemma product_list_set:
  "set (product xs ys) = set xs \<times> set ys"
  by (induct xs) auto

lemma distinct_product:
  assumes "distinct xs" and "distinct ys"
  shows "distinct (product xs ys)"
  using assms by (induct xs)
    (auto intro: inj_onI simp add: product_list_set distinct_map)

instantiation * :: (enum, enum) enum
begin

definition
  "enum = product enum enum"

instance by default
  (simp_all add: enum_prod_def product_list_set distinct_product enum_all enum_distinct)

end

instantiation "+" :: (enum, enum) enum
begin

definition
  "enum = map Inl enum @ map Inr enum"

instance by default
  (auto simp add: enum_all enum_sum_def, case_tac x, auto intro: inj_onI simp add: distinct_map enum_distinct)

end

primrec sublists :: "'a list \<Rightarrow> 'a list list" where
  "sublists [] = [[]]"
  | "sublists (x#xs) = (let xss = sublists xs in map (Cons x) xss @ xss)"

lemma length_sublists:
  "length (sublists xs) = Suc (Suc (0\<Colon>nat)) ^ length xs"
  by (induct xs) (simp_all add: Let_def)

lemma sublists_powset:
  "set ` set (sublists xs) = Pow (set xs)"
proof -
  have aux: "\<And>x A. set ` Cons x ` A = insert x ` set ` A"
    by (auto simp add: image_def)
  have "set (map set (sublists xs)) = Pow (set xs)"
    by (induct xs)
      (simp_all add: aux Let_def Pow_insert Un_commute)
  then show ?thesis by simp
qed

lemma distinct_set_sublists:
  assumes "distinct xs"
  shows "distinct (map set (sublists xs))"
proof (rule card_distinct)
  have "finite (set xs)" by rule
  then have "card (Pow (set xs)) = Suc (Suc 0) ^ card (set xs)" by (rule card_Pow)
  with assms distinct_card [of xs]
    have "card (Pow (set xs)) = Suc (Suc 0) ^ length xs" by simp
  then show "card (set (map set (sublists xs))) = length (map set (sublists xs))"
    by (simp add: sublists_powset length_sublists)
qed

instantiation nibble :: enum
begin

definition
  "enum = [Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF]"

instance by default
  (simp_all add: enum_nibble_def UNIV_nibble)

end

instantiation char :: enum
begin

definition
  [code del]: "enum = map (split Char) (product enum enum)"

lemma enum_char [code]:
  "enum = [Char Nibble0 Nibble0, Char Nibble0 Nibble1, Char Nibble0 Nibble2,
  Char Nibble0 Nibble3, Char Nibble0 Nibble4, Char Nibble0 Nibble5,
  Char Nibble0 Nibble6, Char Nibble0 Nibble7, Char Nibble0 Nibble8,
  Char Nibble0 Nibble9, Char Nibble0 NibbleA, Char Nibble0 NibbleB,
  Char Nibble0 NibbleC, Char Nibble0 NibbleD, Char Nibble0 NibbleE,
  Char Nibble0 NibbleF, Char Nibble1 Nibble0, Char Nibble1 Nibble1,
  Char Nibble1 Nibble2, Char Nibble1 Nibble3, Char Nibble1 Nibble4,
  Char Nibble1 Nibble5, Char Nibble1 Nibble6, Char Nibble1 Nibble7,
  Char Nibble1 Nibble8, Char Nibble1 Nibble9, Char Nibble1 NibbleA,
  Char Nibble1 NibbleB, Char Nibble1 NibbleC, Char Nibble1 NibbleD,
  Char Nibble1 NibbleE, Char Nibble1 NibbleF, CHR '' '', CHR ''!'',
  Char Nibble2 Nibble2, CHR ''#'', CHR ''$'', CHR ''%'', CHR ''&'',
  Char Nibble2 Nibble7, CHR ''('', CHR '')'', CHR ''*'', CHR ''+'', CHR '','',
  CHR ''-'', CHR ''.'', CHR ''/'', CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'',
  CHR ''4'', CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9'', CHR '':'',
  CHR '';'', CHR ''<'', CHR ''='', CHR ''>'', CHR ''?'', CHR ''@'', CHR ''A'',
  CHR ''B'', CHR ''C'', CHR ''D'', CHR ''E'', CHR ''F'', CHR ''G'', CHR ''H'',
  CHR ''I'', CHR ''J'', CHR ''K'', CHR ''L'', CHR ''M'', CHR ''N'', CHR ''O'',
  CHR ''P'', CHR ''Q'', CHR ''R'', CHR ''S'', CHR ''T'', CHR ''U'', CHR ''V'',
  CHR ''W'', CHR ''X'', CHR ''Y'', CHR ''Z'', CHR ''['', Char Nibble5 NibbleC,
  CHR '']'', CHR ''^'', CHR ''_'', Char Nibble6 Nibble0, CHR ''a'', CHR ''b'',
  CHR ''c'', CHR ''d'', CHR ''e'', CHR ''f'', CHR ''g'', CHR ''h'', CHR ''i'',
  CHR ''j'', CHR ''k'', CHR ''l'', CHR ''m'', CHR ''n'', CHR ''o'', CHR ''p'',
  CHR ''q'', CHR ''r'', CHR ''s'', CHR ''t'', CHR ''u'', CHR ''v'', CHR ''w'',
  CHR ''x'', CHR ''y'', CHR ''z'', CHR ''{'', CHR ''|'', CHR ''}'', CHR ''~'',
  Char Nibble7 NibbleF, Char Nibble8 Nibble0, Char Nibble8 Nibble1,
  Char Nibble8 Nibble2, Char Nibble8 Nibble3, Char Nibble8 Nibble4,
  Char Nibble8 Nibble5, Char Nibble8 Nibble6, Char Nibble8 Nibble7,
  Char Nibble8 Nibble8, Char Nibble8 Nibble9, Char Nibble8 NibbleA,
  Char Nibble8 NibbleB, Char Nibble8 NibbleC, Char Nibble8 NibbleD,
  Char Nibble8 NibbleE, Char Nibble8 NibbleF, Char Nibble9 Nibble0,
  Char Nibble9 Nibble1, Char Nibble9 Nibble2, Char Nibble9 Nibble3,
  Char Nibble9 Nibble4, Char Nibble9 Nibble5, Char Nibble9 Nibble6,
  Char Nibble9 Nibble7, Char Nibble9 Nibble8, Char Nibble9 Nibble9,
  Char Nibble9 NibbleA, Char Nibble9 NibbleB, Char Nibble9 NibbleC,
  Char Nibble9 NibbleD, Char Nibble9 NibbleE, Char Nibble9 NibbleF,
  Char NibbleA Nibble0, Char NibbleA Nibble1, Char NibbleA Nibble2,
  Char NibbleA Nibble3, Char NibbleA Nibble4, Char NibbleA Nibble5,
  Char NibbleA Nibble6, Char NibbleA Nibble7, Char NibbleA Nibble8,
  Char NibbleA Nibble9, Char NibbleA NibbleA, Char NibbleA NibbleB,
  Char NibbleA NibbleC, Char NibbleA NibbleD, Char NibbleA NibbleE,
  Char NibbleA NibbleF, Char NibbleB Nibble0, Char NibbleB Nibble1,
  Char NibbleB Nibble2, Char NibbleB Nibble3, Char NibbleB Nibble4,
  Char NibbleB Nibble5, Char NibbleB Nibble6, Char NibbleB Nibble7,
  Char NibbleB Nibble8, Char NibbleB Nibble9, Char NibbleB NibbleA,
  Char NibbleB NibbleB, Char NibbleB NibbleC, Char NibbleB NibbleD,
  Char NibbleB NibbleE, Char NibbleB NibbleF, Char NibbleC Nibble0,
  Char NibbleC Nibble1, Char NibbleC Nibble2, Char NibbleC Nibble3,
  Char NibbleC Nibble4, Char NibbleC Nibble5, Char NibbleC Nibble6,
  Char NibbleC Nibble7, Char NibbleC Nibble8, Char NibbleC Nibble9,
  Char NibbleC NibbleA, Char NibbleC NibbleB, Char NibbleC NibbleC,
  Char NibbleC NibbleD, Char NibbleC NibbleE, Char NibbleC NibbleF,
  Char NibbleD Nibble0, Char NibbleD Nibble1, Char NibbleD Nibble2,
  Char NibbleD Nibble3, Char NibbleD Nibble4, Char NibbleD Nibble5,
  Char NibbleD Nibble6, Char NibbleD Nibble7, Char NibbleD Nibble8,
  Char NibbleD Nibble9, Char NibbleD NibbleA, Char NibbleD NibbleB,
  Char NibbleD NibbleC, Char NibbleD NibbleD, Char NibbleD NibbleE,
  Char NibbleD NibbleF, Char NibbleE Nibble0, Char NibbleE Nibble1,
  Char NibbleE Nibble2, Char NibbleE Nibble3, Char NibbleE Nibble4,
  Char NibbleE Nibble5, Char NibbleE Nibble6, Char NibbleE Nibble7,
  Char NibbleE Nibble8, Char NibbleE Nibble9, Char NibbleE NibbleA,
  Char NibbleE NibbleB, Char NibbleE NibbleC, Char NibbleE NibbleD,
  Char NibbleE NibbleE, Char NibbleE NibbleF, Char NibbleF Nibble0,
  Char NibbleF Nibble1, Char NibbleF Nibble2, Char NibbleF Nibble3,
  Char NibbleF Nibble4, Char NibbleF Nibble5, Char NibbleF Nibble6,
  Char NibbleF Nibble7, Char NibbleF Nibble8, Char NibbleF Nibble9,
  Char NibbleF NibbleA, Char NibbleF NibbleB, Char NibbleF NibbleC,
  Char NibbleF NibbleD, Char NibbleF NibbleE, Char NibbleF NibbleF]"
  unfolding enum_char_def enum_nibble_def by simp

instance by default
  (auto intro: char.exhaust injI simp add: enum_char_def product_list_set enum_all full_SetCompr_eq [symmetric]
    distinct_map distinct_product enum_distinct)

end

instantiation option :: (enum) enum
begin

definition
  "enum = None # map Some enum"

instance by default
  (auto simp add: enum_all enum_option_def, case_tac x, auto intro: inj_onI simp add: distinct_map enum_distinct)

end

end
