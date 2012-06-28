(*  Title:      HOL/Library/Cardinality.thy
    Author:     Brian Huffman, Andreas Lochbihler
*)

header {* Cardinality of types *}

theory Cardinality
imports Phantom_Type
begin

subsection {* Preliminary lemmas *}
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

lemma finite_range_Some: "finite (range (Some :: 'a \<Rightarrow> 'a option)) = finite (UNIV :: 'a set)"
by(auto dest: finite_imageD intro: inj_Some)


subsection {* Cardinalities of types *}

syntax "_type_card" :: "type => nat" ("(1CARD/(1'(_')))")

translations "CARD('t)" => "CONST card (CONST UNIV \<Colon> 't set)"

typed_print_translation (advanced) {*
  let
    fun card_univ_tr' ctxt _ [Const (@{const_syntax UNIV}, Type (_, [T, _]))] =
      Syntax.const @{syntax_const "_type_card"} $ Syntax_Phases.term_of_typ ctxt T;
  in [(@{const_syntax card}, card_univ_tr')] end
*}

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
    by(simp add: UNIV_option_conv card_eq_0_iff finite_range_Some card_insert_disjoint card_image)
qed

lemma card_option [simp]: "CARD('a option) = Suc CARD('a::finite)"
by(simp add: card_UNIV_option)

lemma card_UNIV_set: "CARD('a set) = (if CARD('a) = 0 then 0 else 2 ^ CARD('a))"
by(simp add: Pow_UNIV[symmetric] card_eq_0_iff card_Pow del: Pow_UNIV)

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
    let ?xs = "map (\<lambda>ys. the o map_of (zip as ys)) (Enum.n_lists (length as) bs)"
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
      assume xs: "xs \<in> set (Enum.n_lists (length as) bs)"
        and ys: "ys \<in> set (Enum.n_lists (length as) bs)"
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

lemma card_nibble: "CARD(nibble) = 16"
unfolding UNIV_nibble by simp

lemma card_UNIV_char: "CARD(char) = 256"
proof -
  have "inj (\<lambda>(x, y). Char x y)" by(auto intro: injI)
  thus ?thesis unfolding UNIV_char by(simp add: card_image card_nibble)
qed

lemma card_literal: "CARD(String.literal) = 0"
proof -
  have "inj STR" by(auto intro: injI)
  thus ?thesis by(simp add: type_definition.univ[OF type_definition_literal] card_image infinite_UNIV_listI)
qed

subsection {* Classes with at least 1 and 2  *}

text {* Class finite already captures "at least 1" *}

lemma zero_less_card_finite [simp]: "0 < CARD('a::finite)"
  unfolding neq0_conv [symmetric] by simp

lemma one_le_card_finite [simp]: "Suc 0 \<le> CARD('a::finite)"
  by (simp add: less_Suc_eq_le [symmetric])

text {* Class for cardinality "at least 2" *}

class card2 = finite + 
  assumes two_le_card: "2 \<le> CARD('a)"

lemma one_less_card: "Suc 0 < CARD('a::card2)"
  using two_le_card [where 'a='a] by simp

lemma one_less_int_card: "1 < int CARD('a::card2)"
  using one_less_card [where 'a='a] by simp

subsection {* A type class for computing the cardinality of types *}

definition is_list_UNIV :: "'a list \<Rightarrow> bool"
where [code del]: "is_list_UNIV xs = (let c = CARD('a) in if c = 0 then False else size (remdups xs) = c)"

lemma is_list_UNIV_iff: "is_list_UNIV xs \<longleftrightarrow> set xs = UNIV"
by(auto simp add: is_list_UNIV_def Let_def card_eq_0_iff List.card_set[symmetric] 
   dest: subst[where P="finite", OF _ finite_set] card_eq_UNIV_imp_eq_UNIV)

type_synonym 'a card_UNIV = "('a, nat) phantom"

class card_UNIV = 
  fixes card_UNIV :: "'a card_UNIV"
  assumes card_UNIV: "card_UNIV = Phantom('a) CARD('a)"

lemma card_UNIV_code [code_unfold]: 
  "CARD('a :: card_UNIV) = of_phantom (card_UNIV :: 'a card_UNIV)"
by(simp add: card_UNIV)

lemma is_list_UNIV_code [code]:
  "is_list_UNIV (xs :: 'a list) = 
  (let c = CARD('a :: card_UNIV) in if c = 0 then False else size (remdups xs) = c)"
by(rule is_list_UNIV_def)

lemma finite_UNIV_conv_card_UNIV [code_unfold]:
  "finite (UNIV :: 'a :: card_UNIV set) \<longleftrightarrow> 
  of_phantom (card_UNIV :: 'a card_UNIV) > 0"
by(simp add: card_UNIV card_gt_0_iff)

subsection {* Instantiations for @{text "card_UNIV"} *}

instantiation nat :: card_UNIV begin
definition "card_UNIV = Phantom(nat) 0"
instance by intro_classes (simp add: card_UNIV_nat_def)
end

instantiation int :: card_UNIV begin
definition "card_UNIV = Phantom(int) 0"
instance by intro_classes (simp add: card_UNIV_int_def infinite_UNIV_int)
end

instantiation code_numeral :: card_UNIV begin
definition "card_UNIV = Phantom(code_numeral) 0"
instance 
  by(intro_classes)(auto simp add: card_UNIV_code_numeral_def type_definition.univ[OF type_definition_code_numeral] card_eq_0_iff dest!: finite_imageD intro: inj_onI)
end

instantiation list :: (type) card_UNIV begin
definition "card_UNIV = Phantom('a list) 0"
instance by intro_classes (simp add: card_UNIV_list_def infinite_UNIV_listI)
end

instantiation unit :: card_UNIV begin
definition "card_UNIV = Phantom(unit) 1"
instance by intro_classes (simp add: card_UNIV_unit_def card_UNIV_unit)
end

instantiation bool :: card_UNIV begin
definition "card_UNIV = Phantom(bool) 2"
instance by(intro_classes)(simp add: card_UNIV_bool_def card_UNIV_bool)
end

instantiation nibble :: card_UNIV begin
definition "card_UNIV = Phantom(nibble) 16"
instance by(intro_classes)(simp add: card_UNIV_nibble_def card_nibble)
end

instantiation char :: card_UNIV begin
definition "card_UNIV = Phantom(char) 256"
instance by intro_classes (simp add: card_UNIV_char_def card_UNIV_char)
end

instantiation prod :: (card_UNIV, card_UNIV) card_UNIV begin
definition "card_UNIV = 
  Phantom('a \<times> 'b) (of_phantom (card_UNIV :: 'a card_UNIV) * of_phantom (card_UNIV :: 'b card_UNIV))"
instance by intro_classes (simp add: card_UNIV_prod_def card_UNIV)
end

instantiation sum :: (card_UNIV, card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a + 'b)
  (let ca = of_phantom (card_UNIV :: 'a card_UNIV); 
       cb = of_phantom (card_UNIV :: 'b card_UNIV)
   in if ca \<noteq> 0 \<and> cb \<noteq> 0 then ca + cb else 0)"
instance by intro_classes (auto simp add: card_UNIV_sum_def card_UNIV card_UNIV_sum)
end

instantiation "fun" :: (card_UNIV, card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a \<Rightarrow> 'b)
  (let ca = of_phantom (card_UNIV :: 'a card_UNIV);
       cb = of_phantom (card_UNIV :: 'b card_UNIV)
   in if ca \<noteq> 0 \<and> cb \<noteq> 0 \<or> cb = 1 then cb ^ ca else 0)"
instance by intro_classes (simp add: card_UNIV_fun_def card_UNIV Let_def card_fun)
end

instantiation option :: (card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a option)
  (let c = of_phantom (card_UNIV :: 'a card_UNIV) in if c \<noteq> 0 then Suc c else 0)"
instance by intro_classes (simp add: card_UNIV_option_def card_UNIV card_UNIV_option)
end

instantiation String.literal :: card_UNIV begin
definition "card_UNIV = Phantom(String.literal) 0"
instance by intro_classes (simp add: card_UNIV_literal_def card_literal)
end

instantiation set :: (card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a set)
  (let c = of_phantom (card_UNIV :: 'a card_UNIV) in if c = 0 then 0 else 2 ^ c)"
instance by intro_classes (simp add: card_UNIV_set_def card_UNIV_set card_UNIV)
end


lemma UNIV_finite_1: "UNIV = set [finite_1.a\<^isub>1]"
by(auto intro: finite_1.exhaust)

lemma UNIV_finite_2: "UNIV = set [finite_2.a\<^isub>1, finite_2.a\<^isub>2]"
by(auto intro: finite_2.exhaust)

lemma UNIV_finite_3: "UNIV = set [finite_3.a\<^isub>1, finite_3.a\<^isub>2, finite_3.a\<^isub>3]"
by(auto intro: finite_3.exhaust)

lemma UNIV_finite_4: "UNIV = set [finite_4.a\<^isub>1, finite_4.a\<^isub>2, finite_4.a\<^isub>3, finite_4.a\<^isub>4]"
by(auto intro: finite_4.exhaust)

lemma UNIV_finite_5:
  "UNIV = set [finite_5.a\<^isub>1, finite_5.a\<^isub>2, finite_5.a\<^isub>3, finite_5.a\<^isub>4, finite_5.a\<^isub>5]"
by(auto intro: finite_5.exhaust)

instantiation Enum.finite_1 :: card_UNIV begin
definition "card_UNIV = Phantom(Enum.finite_1) 1"
instance by intro_classes (simp add: UNIV_finite_1 card_UNIV_finite_1_def)
end

instantiation Enum.finite_2 :: card_UNIV begin
definition "card_UNIV = Phantom(Enum.finite_2) 2"
instance by intro_classes (simp add: UNIV_finite_2 card_UNIV_finite_2_def)
end

instantiation Enum.finite_3 :: card_UNIV begin
definition "card_UNIV = Phantom(Enum.finite_3) 3"
instance by intro_classes (simp add: UNIV_finite_3 card_UNIV_finite_3_def)
end

instantiation Enum.finite_4 :: card_UNIV begin
definition "card_UNIV = Phantom(Enum.finite_4) 4"
instance by intro_classes (simp add: UNIV_finite_4 card_UNIV_finite_4_def)
end

instantiation Enum.finite_5 :: card_UNIV begin
definition "card_UNIV = Phantom(Enum.finite_5) 5"
instance by intro_classes (simp add: UNIV_finite_5 card_UNIV_finite_5_def)
end

subsection {* Code setup for sets *}

lemma card_Compl:
  "finite A \<Longrightarrow> card (- A) = card (UNIV :: 'a set) - card (A :: 'a set)"
by (metis Compl_eq_Diff_UNIV card_Diff_subset top_greatest)

context fixes xs :: "'a :: card_UNIV list"
begin

definition card' :: "'a set \<Rightarrow> nat" 
where [simp, code del, code_abbrev]: "card' = card"

lemma card'_code [code]:
  "card' (set xs) = length (remdups xs)"
  "card' (List.coset xs) = of_phantom (card_UNIV :: 'a card_UNIV) - length (remdups xs)"
by(simp_all add: List.card_set card_Compl card_UNIV)

lemma card'_UNIV [code_unfold]: 
  "card' (UNIV :: 'a :: card_UNIV set) = of_phantom (card_UNIV :: 'a card_UNIV)"
by(simp add: card_UNIV)

definition finite' :: "'a set \<Rightarrow> bool"
where [simp, code del, code_abbrev]: "finite' = finite"

lemma finite'_code [code]:
  "finite' (set xs) \<longleftrightarrow> True"
  "finite' (List.coset xs) \<longleftrightarrow> CARD('a) > 0"
by(simp_all add: card_gt_0_iff)

definition subset' :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where [simp, code del, code_abbrev]: "subset' = op \<subseteq>"

lemma subset'_code [code]:
  "subset' A (List.coset ys) \<longleftrightarrow> (\<forall>y \<in> set ys. y \<notin> A)"
  "subset' (set ys) B \<longleftrightarrow> (\<forall>y \<in> set ys. y \<in> B)"
  "subset' (List.coset xs) (set ys) \<longleftrightarrow> (let n = CARD('a) in n > 0 \<and> card(set (xs @ ys)) = n)"
by(auto simp add: Let_def card_gt_0_iff dest: card_eq_UNIV_imp_eq_UNIV intro: arg_cong[where f=card])
  (metis finite_compl finite_set rev_finite_subset)

definition eq_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where [simp, code del, code_abbrev]: "eq_set = op ="

lemma eq_set_code [code]:
  fixes ys
  defines "rhs \<equiv> 
  let n = CARD('a)
  in if n = 0 then False else 
        let xs' = remdups xs; ys' = remdups ys 
        in length xs' + length ys' = n \<and> (\<forall>x \<in> set xs'. x \<notin> set ys') \<and> (\<forall>y \<in> set ys'. y \<notin> set xs')"
  shows "eq_set (List.coset xs) (set ys) \<longleftrightarrow> rhs" (is ?thesis1)
  and "eq_set (set ys) (List.coset xs) \<longleftrightarrow> rhs" (is ?thesis2)
  and "eq_set (set xs) (set ys) \<longleftrightarrow> (\<forall>x \<in> set xs. x \<in> set ys) \<and> (\<forall>y \<in> set ys. y \<in> set xs)" (is ?thesis3)
  and "eq_set (List.coset xs) (List.coset ys) \<longleftrightarrow> (\<forall>x \<in> set xs. x \<in> set ys) \<and> (\<forall>y \<in> set ys. y \<in> set xs)" (is ?thesis4)
proof -
  show ?thesis1 (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs thus ?rhs
      by(auto simp add: rhs_def Let_def List.card_set[symmetric] card_Un_Int[where A="set xs" and B="- set xs"] card_UNIV Compl_partition card_gt_0_iff dest: sym)(metis finite_compl finite_set)
  next
    assume ?rhs
    moreover have "\<lbrakk> \<forall>y\<in>set xs. y \<notin> set ys; \<forall>x\<in>set ys. x \<notin> set xs \<rbrakk> \<Longrightarrow> set xs \<inter> set ys = {}" by blast
    ultimately show ?lhs
      by(auto simp add: rhs_def Let_def List.card_set[symmetric] card_UNIV card_gt_0_iff card_Un_Int[where A="set xs" and B="set ys"] dest: card_eq_UNIV_imp_eq_UNIV split: split_if_asm)
  qed
  thus ?thesis2 unfolding eq_set_def by blast
  show ?thesis3 ?thesis4 unfolding eq_set_def List.coset_def by blast+
qed

end

notepad begin (* test code setup *)
have "List.coset [True] = set [False] \<and> List.coset [] \<subseteq> List.set [True, False] \<and> finite (List.coset [True])"
  by eval
end

hide_const (open) card' finite' subset' eq_set

end
