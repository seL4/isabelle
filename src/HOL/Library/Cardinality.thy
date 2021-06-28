(*  Title:      HOL/Library/Cardinality.thy
    Author:     Brian Huffman, Andreas Lochbihler
*)

section \<open>Cardinality of types\<close>

theory Cardinality
imports Phantom_Type
begin

subsection \<open>Preliminary lemmas\<close>
(* These should be moved elsewhere *)

lemma (in type_definition) univ:
  "UNIV = Abs ` A"
proof
  show "Abs ` A \<subseteq> UNIV" by (rule subset_UNIV)
  show "UNIV \<subseteq> Abs ` A"
  proof
    fix x :: 'b
    have "x = Abs (Rep x)" by (rule Rep_inverse [symmetric])
    moreover have "Rep x \<in> A" by (rule Rep)
    ultimately show "x \<in> Abs ` A" by (rule image_eqI)
  qed
qed

lemma (in type_definition) card: "card (UNIV :: 'b set) = card A"
  by (simp add: univ card_image inj_on_def Abs_inject)


subsection \<open>Cardinalities of types\<close>

syntax "_type_card" :: "type => nat" ("(1CARD/(1'(_')))")

translations "CARD('t)" => "CONST card (CONST UNIV :: 't set)"

print_translation \<open>
  let
    fun card_univ_tr' ctxt [Const (\<^const_syntax>\<open>UNIV\<close>, Type (_, [T]))] =
      Syntax.const \<^syntax_const>\<open>_type_card\<close> $ Syntax_Phases.term_of_typ ctxt T
  in [(\<^const_syntax>\<open>card\<close>, card_univ_tr')] end
\<close>

lemma card_prod [simp]: "CARD('a \<times> 'b) = CARD('a) * CARD('b)"
  unfolding UNIV_Times_UNIV [symmetric] by (simp only: card_cartesian_product)

lemma card_UNIV_sum: "CARD('a + 'b) = (if CARD('a) \<noteq> 0 \<and> CARD('b) \<noteq> 0 then CARD('a) + CARD('b) else 0)"
unfolding UNIV_Plus_UNIV[symmetric]
by(auto simp add: card_eq_0_iff card_Plus simp del: UNIV_Plus_UNIV)

lemma card_sum [simp]: "CARD('a + 'b) = CARD('a::finite) + CARD('b::finite)"
by(simp add: card_UNIV_sum)

lemma card_UNIV_option: "CARD('a option) = (if CARD('a) = 0 then 0 else CARD('a) + 1)"
proof -
  have "(None :: 'a option) \<notin> range Some" by clarsimp
  thus ?thesis
    by (simp add: UNIV_option_conv card_eq_0_iff finite_range_Some card_image)
qed

lemma card_option [simp]: "CARD('a option) = Suc CARD('a::finite)"
by(simp add: card_UNIV_option)

lemma card_UNIV_set: "CARD('a set) = (if CARD('a) = 0 then 0 else 2 ^ CARD('a))"
by(simp add: card_eq_0_iff card_Pow flip: Pow_UNIV)

lemma card_set [simp]: "CARD('a set) = 2 ^ CARD('a::finite)"
by(simp add: card_UNIV_set)

lemma card_nat [simp]: "CARD(nat) = 0"
  by (simp add: card_eq_0_iff)

lemma card_fun: "CARD('a \<Rightarrow> 'b) = (if CARD('a) \<noteq> 0 \<and> CARD('b) \<noteq> 0 \<or> CARD('b) = 1 then CARD('b) ^ CARD('a) else 0)"
proof -
  {  assume "0 < CARD('a)" and "0 < CARD('b)"
    hence fina: "finite (UNIV :: 'a set)" and finb: "finite (UNIV :: 'b set)"
      by(simp_all only: card_ge_0_finite)
    from finite_distinct_list[OF finb] obtain bs 
      where bs: "set bs = (UNIV :: 'b set)" and distb: "distinct bs" by blast
    from finite_distinct_list[OF fina] obtain as
      where as: "set as = (UNIV :: 'a set)" and dista: "distinct as" by blast
    have cb: "CARD('b) = length bs"
      unfolding bs[symmetric] distinct_card[OF distb] ..
    have ca: "CARD('a) = length as"
      unfolding as[symmetric] distinct_card[OF dista] ..
    let ?xs = "map (\<lambda>ys. the \<circ> map_of (zip as ys)) (List.n_lists (length as) bs)"
    have "UNIV = set ?xs"
    proof(rule UNIV_eq_I)
      fix f :: "'a \<Rightarrow> 'b"
      from as have "f = the \<circ> map_of (zip as (map f as))"
        by(auto simp add: map_of_zip_map)
      thus "f \<in> set ?xs" using bs by(auto simp add: set_n_lists)
    qed
    moreover have "distinct ?xs" unfolding distinct_map
    proof(intro conjI distinct_n_lists distb inj_onI)
      fix xs ys :: "'b list"
      assume xs: "xs \<in> set (List.n_lists (length as) bs)"
        and ys: "ys \<in> set (List.n_lists (length as) bs)"
        and eq: "the \<circ> map_of (zip as xs) = the \<circ> map_of (zip as ys)"
      from xs ys have [simp]: "length xs = length as" "length ys = length as"
        by(simp_all add: length_n_lists_elem)
      have "map_of (zip as xs) = map_of (zip as ys)"
      proof
        fix x
        from as bs have "\<exists>y. map_of (zip as xs) x = Some y" "\<exists>y. map_of (zip as ys) x = Some y"
          by(simp_all add: map_of_zip_is_Some[symmetric])
        with eq show "map_of (zip as xs) x = map_of (zip as ys) x"
          by(auto dest: fun_cong[where x=x])
      qed
      with dista show "xs = ys" by(simp add: map_of_zip_inject)
    qed
    hence "card (set ?xs) = length ?xs" by(simp only: distinct_card)
    moreover have "length ?xs = length bs ^ length as" by(simp add: length_n_lists)
    ultimately have "CARD('a \<Rightarrow> 'b) = CARD('b) ^ CARD('a)" using cb ca by simp }
  moreover {
    assume cb: "CARD('b) = 1"
    then obtain b where b: "UNIV = {b :: 'b}" by(auto simp add: card_Suc_eq)
    have eq: "UNIV = {\<lambda>x :: 'a. b ::'b}"
    proof(rule UNIV_eq_I)
      fix x :: "'a \<Rightarrow> 'b"
      { fix y
        have "x y \<in> UNIV" ..
        hence "x y = b" unfolding b by simp }
      thus "x \<in> {\<lambda>x. b}" by(auto)
    qed
    have "CARD('a \<Rightarrow> 'b) = 1" unfolding eq by simp }
  ultimately show ?thesis
    by(auto simp del: One_nat_def)(auto simp add: card_eq_0_iff dest: finite_fun_UNIVD2 finite_fun_UNIVD1)
qed

corollary finite_UNIV_fun:
  "finite (UNIV :: ('a \<Rightarrow> 'b) set) \<longleftrightarrow>
   finite (UNIV :: 'a set) \<and> finite (UNIV :: 'b set) \<or> CARD('b) = 1"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "?lhs \<longleftrightarrow> CARD('a \<Rightarrow> 'b) > 0" by(simp add: card_gt_0_iff)
  also have "\<dots> \<longleftrightarrow> CARD('a) > 0 \<and> CARD('b) > 0 \<or> CARD('b) = 1"
    by(simp add: card_fun)
  also have "\<dots> = ?rhs" by(simp add: card_gt_0_iff)
  finally show ?thesis .
qed

lemma card_literal: "CARD(String.literal) = 0"
by(simp add: card_eq_0_iff infinite_literal)

subsection \<open>Classes with at least 1 and 2\<close>

text \<open>Class finite already captures "at least 1"\<close>

lemma zero_less_card_finite [simp]: "0 < CARD('a::finite)"
  unfolding neq0_conv [symmetric] by simp

lemma one_le_card_finite [simp]: "Suc 0 \<le> CARD('a::finite)"
  by (simp add: less_Suc_eq_le [symmetric])


class CARD_1 =
  assumes CARD_1: "CARD ('a) = 1"
begin

subclass finite
proof
  from CARD_1 show "finite (UNIV :: 'a set)"
    using finite_UNIV_fun by fastforce
qed

end

text \<open>Class for cardinality "at least 2"\<close>

class card2 = finite + 
  assumes two_le_card: "2 \<le> CARD('a)"

lemma one_less_card: "Suc 0 < CARD('a::card2)"
  using two_le_card [where 'a='a] by simp

lemma one_less_int_card: "1 < int CARD('a::card2)"
  using one_less_card [where 'a='a] by simp


subsection \<open>A type class for deciding finiteness of types\<close>

type_synonym 'a finite_UNIV = "('a, bool) phantom"

class finite_UNIV = 
  fixes finite_UNIV :: "('a, bool) phantom"
  assumes finite_UNIV: "finite_UNIV = Phantom('a) (finite (UNIV :: 'a set))"

lemma finite_UNIV_code [code_unfold]:
  "finite (UNIV :: 'a :: finite_UNIV set)
  \<longleftrightarrow> of_phantom (finite_UNIV :: 'a finite_UNIV)"
by(simp add: finite_UNIV)

subsection \<open>A type class for computing the cardinality of types\<close>

definition is_list_UNIV :: "'a list \<Rightarrow> bool"
where "is_list_UNIV xs = (let c = CARD('a) in if c = 0 then False else size (remdups xs) = c)"

lemma is_list_UNIV_iff: "is_list_UNIV xs \<longleftrightarrow> set xs = UNIV"
by(auto simp add: is_list_UNIV_def Let_def card_eq_0_iff List.card_set[symmetric] 
   dest: subst[where P="finite", OF _ finite_set] card_eq_UNIV_imp_eq_UNIV)

type_synonym 'a card_UNIV = "('a, nat) phantom"

class card_UNIV = finite_UNIV +
  fixes card_UNIV :: "'a card_UNIV"
  assumes card_UNIV: "card_UNIV = Phantom('a) CARD('a)"

subsection \<open>Instantiations for \<open>card_UNIV\<close>\<close>

instantiation nat :: card_UNIV begin
definition "finite_UNIV = Phantom(nat) False"
definition "card_UNIV = Phantom(nat) 0"
instance by intro_classes (simp_all add: finite_UNIV_nat_def card_UNIV_nat_def)
end

instantiation int :: card_UNIV begin
definition "finite_UNIV = Phantom(int) False"
definition "card_UNIV = Phantom(int) 0"
instance by intro_classes (simp_all add: card_UNIV_int_def finite_UNIV_int_def)
end

instantiation natural :: card_UNIV begin
definition "finite_UNIV = Phantom(natural) False"
definition "card_UNIV = Phantom(natural) 0"
instance
  by standard
    (auto simp add: finite_UNIV_natural_def card_UNIV_natural_def card_eq_0_iff
      type_definition.univ [OF type_definition_natural] natural_eq_iff
      dest!: finite_imageD intro: inj_onI)
end

instantiation integer :: card_UNIV begin
definition "finite_UNIV = Phantom(integer) False"
definition "card_UNIV = Phantom(integer) 0"
instance
  by standard
    (auto simp add: finite_UNIV_integer_def card_UNIV_integer_def card_eq_0_iff
      type_definition.univ [OF type_definition_integer]
      dest!: finite_imageD intro: inj_onI)
end

instantiation list :: (type) card_UNIV begin
definition "finite_UNIV = Phantom('a list) False"
definition "card_UNIV = Phantom('a list) 0"
instance by intro_classes (simp_all add: card_UNIV_list_def finite_UNIV_list_def infinite_UNIV_listI)
end

instantiation unit :: card_UNIV begin
definition "finite_UNIV = Phantom(unit) True"
definition "card_UNIV = Phantom(unit) 1"
instance by intro_classes (simp_all add: card_UNIV_unit_def finite_UNIV_unit_def)
end

instantiation bool :: card_UNIV begin
definition "finite_UNIV = Phantom(bool) True"
definition "card_UNIV = Phantom(bool) 2"
instance by(intro_classes)(simp_all add: card_UNIV_bool_def finite_UNIV_bool_def)
end

instantiation char :: card_UNIV begin
definition "finite_UNIV = Phantom(char) True"
definition "card_UNIV = Phantom(char) 256"
instance by intro_classes (simp_all add: card_UNIV_char_def card_UNIV_char finite_UNIV_char_def)
end

instantiation prod :: (finite_UNIV, finite_UNIV) finite_UNIV begin
definition "finite_UNIV = Phantom('a \<times> 'b) 
  (of_phantom (finite_UNIV :: 'a finite_UNIV) \<and> of_phantom (finite_UNIV :: 'b finite_UNIV))"
instance by intro_classes (simp add: finite_UNIV_prod_def finite_UNIV finite_prod)
end

instantiation prod :: (card_UNIV, card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a \<times> 'b) 
  (of_phantom (card_UNIV :: 'a card_UNIV) * of_phantom (card_UNIV :: 'b card_UNIV))"
instance by intro_classes (simp add: card_UNIV_prod_def card_UNIV)
end

instantiation sum :: (finite_UNIV, finite_UNIV) finite_UNIV begin
definition "finite_UNIV = Phantom('a + 'b)
  (of_phantom (finite_UNIV :: 'a finite_UNIV) \<and> of_phantom (finite_UNIV :: 'b finite_UNIV))"
instance
  by intro_classes (simp add: finite_UNIV_sum_def finite_UNIV)
end

instantiation sum :: (card_UNIV, card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a + 'b)
  (let ca = of_phantom (card_UNIV :: 'a card_UNIV); 
       cb = of_phantom (card_UNIV :: 'b card_UNIV)
   in if ca \<noteq> 0 \<and> cb \<noteq> 0 then ca + cb else 0)"
instance by intro_classes (auto simp add: card_UNIV_sum_def card_UNIV card_UNIV_sum)
end

instantiation "fun" :: (finite_UNIV, card_UNIV) finite_UNIV begin
definition "finite_UNIV = Phantom('a \<Rightarrow> 'b)
  (let cb = of_phantom (card_UNIV :: 'b card_UNIV)
   in cb = 1 \<or> of_phantom (finite_UNIV :: 'a finite_UNIV) \<and> cb \<noteq> 0)"
instance
  by intro_classes (auto simp add: finite_UNIV_fun_def Let_def card_UNIV finite_UNIV finite_UNIV_fun card_gt_0_iff)
end

instantiation "fun" :: (card_UNIV, card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a \<Rightarrow> 'b)
  (let ca = of_phantom (card_UNIV :: 'a card_UNIV);
       cb = of_phantom (card_UNIV :: 'b card_UNIV)
   in if ca \<noteq> 0 \<and> cb \<noteq> 0 \<or> cb = 1 then cb ^ ca else 0)"
instance by intro_classes (simp add: card_UNIV_fun_def card_UNIV Let_def card_fun)
end

instantiation option :: (finite_UNIV) finite_UNIV begin
definition "finite_UNIV = Phantom('a option) (of_phantom (finite_UNIV :: 'a finite_UNIV))"
instance by intro_classes (simp add: finite_UNIV_option_def finite_UNIV)
end

instantiation option :: (card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a option)
  (let c = of_phantom (card_UNIV :: 'a card_UNIV) in if c \<noteq> 0 then Suc c else 0)"
instance by intro_classes (simp add: card_UNIV_option_def card_UNIV card_UNIV_option)
end

instantiation String.literal :: card_UNIV begin
definition "finite_UNIV = Phantom(String.literal) False"
definition "card_UNIV = Phantom(String.literal) 0"
instance
  by intro_classes (simp_all add: card_UNIV_literal_def finite_UNIV_literal_def infinite_literal card_literal)
end

instantiation set :: (finite_UNIV) finite_UNIV begin
definition "finite_UNIV = Phantom('a set) (of_phantom (finite_UNIV :: 'a finite_UNIV))"
instance by intro_classes (simp add: finite_UNIV_set_def finite_UNIV Finite_Set.finite_set)
end

instantiation set :: (card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a set)
  (let c = of_phantom (card_UNIV :: 'a card_UNIV) in if c = 0 then 0 else 2 ^ c)"
instance by intro_classes (simp add: card_UNIV_set_def card_UNIV_set card_UNIV)
end

lemma UNIV_finite_1: "UNIV = set [finite_1.a\<^sub>1]"
by(auto intro: finite_1.exhaust)

lemma UNIV_finite_2: "UNIV = set [finite_2.a\<^sub>1, finite_2.a\<^sub>2]"
by(auto intro: finite_2.exhaust)

lemma UNIV_finite_3: "UNIV = set [finite_3.a\<^sub>1, finite_3.a\<^sub>2, finite_3.a\<^sub>3]"
by(auto intro: finite_3.exhaust)

lemma UNIV_finite_4: "UNIV = set [finite_4.a\<^sub>1, finite_4.a\<^sub>2, finite_4.a\<^sub>3, finite_4.a\<^sub>4]"
by(auto intro: finite_4.exhaust)

lemma UNIV_finite_5:
  "UNIV = set [finite_5.a\<^sub>1, finite_5.a\<^sub>2, finite_5.a\<^sub>3, finite_5.a\<^sub>4, finite_5.a\<^sub>5]"
by(auto intro: finite_5.exhaust)

instantiation Enum.finite_1 :: card_UNIV begin
definition "finite_UNIV = Phantom(Enum.finite_1) True"
definition "card_UNIV = Phantom(Enum.finite_1) 1"
instance
  by intro_classes (simp_all add: UNIV_finite_1 card_UNIV_finite_1_def finite_UNIV_finite_1_def)
end

instantiation Enum.finite_2 :: card_UNIV begin
definition "finite_UNIV = Phantom(Enum.finite_2) True"
definition "card_UNIV = Phantom(Enum.finite_2) 2"
instance
  by intro_classes (simp_all add: UNIV_finite_2 card_UNIV_finite_2_def finite_UNIV_finite_2_def)
end

instantiation Enum.finite_3 :: card_UNIV begin
definition "finite_UNIV = Phantom(Enum.finite_3) True"
definition "card_UNIV = Phantom(Enum.finite_3) 3"
instance
  by intro_classes (simp_all add: UNIV_finite_3 card_UNIV_finite_3_def finite_UNIV_finite_3_def)
end

instantiation Enum.finite_4 :: card_UNIV begin
definition "finite_UNIV = Phantom(Enum.finite_4) True"
definition "card_UNIV = Phantom(Enum.finite_4) 4"
instance
  by intro_classes (simp_all add: UNIV_finite_4 card_UNIV_finite_4_def finite_UNIV_finite_4_def)
end

instantiation Enum.finite_5 :: card_UNIV begin
definition "finite_UNIV = Phantom(Enum.finite_5) True"
definition "card_UNIV = Phantom(Enum.finite_5) 5"
instance
  by intro_classes (simp_all add: UNIV_finite_5 card_UNIV_finite_5_def finite_UNIV_finite_5_def)
end

end
