(*  Title:      HOL/Library/Numeral_Type.thy
    Author:     Brian Huffman
*)

section \<open>Numeral Syntax for Types\<close>

theory Numeral_Type
imports Cardinality
begin

subsection \<open>Numeral Types\<close>

typedef num0 = "UNIV :: nat set" ..
typedef num1 = "UNIV :: unit set" ..

typedef 'a bit0 = "{0 ..< 2 * int CARD('a::finite)}"
proof
  show "0 \<in> {0 ..< 2 * int CARD('a)}"
    by simp
qed

typedef 'a bit1 = "{0 ..< 1 + 2 * int CARD('a::finite)}"
proof
  show "0 \<in> {0 ..< 1 + 2 * int CARD('a)}"
    by simp
qed

lemma card_num0 [simp]: "CARD (num0) = 0"
  unfolding type_definition.card [OF type_definition_num0]
  by simp

lemma infinite_num0: "\<not> finite (UNIV :: num0 set)"
  using card_num0[unfolded card_eq_0_iff]
  by simp

lemma card_num1 [simp]: "CARD(num1) = 1"
  unfolding type_definition.card [OF type_definition_num1]
  by (simp only: card_UNIV_unit)

lemma card_bit0 [simp]: "CARD('a bit0) = 2 * CARD('a::finite)"
  unfolding type_definition.card [OF type_definition_bit0]
  by simp

lemma card_bit1 [simp]: "CARD('a bit1) = Suc (2 * CARD('a::finite))"
  unfolding type_definition.card [OF type_definition_bit1]
  by simp

subsection \<open>@{typ num1}\<close>

instance num1 :: finite
proof
  show "finite (UNIV::num1 set)"
    unfolding type_definition.univ [OF type_definition_num1]
    using finite by (rule finite_imageI)
qed

instantiation num1 :: CARD_1
begin

instance
proof
  show "CARD(num1) = 1" by auto
qed

end

lemma num1_eq_iff: "(x::num1) = (y::num1) \<longleftrightarrow> True"
  by (induct x, induct y) simp

instantiation num1 :: "{comm_ring,comm_monoid_mult,numeral}"
begin

instance
  by standard (simp_all add: num1_eq_iff)

end

lemma num1_eqI:
  fixes a::num1 shows "a = b"
by(simp add: num1_eq_iff)

lemma num1_eq1 [simp]:
  fixes a::num1 shows "a = 1"
  by (rule num1_eqI)

lemma forall_1[simp]: "(\<forall>i::num1. P i) \<longleftrightarrow> P 1"
  by (metis (full_types) num1_eq_iff)

lemma ex_1[simp]: "(\<exists>x::num1. P x) \<longleftrightarrow> P 1"
  by auto (metis (full_types) num1_eq_iff)

instantiation num1 :: linorder begin
definition "a < b \<longleftrightarrow> Rep_num1 a < Rep_num1 b"
definition "a \<le> b \<longleftrightarrow> Rep_num1 a \<le> Rep_num1 b"
instance
  by intro_classes (auto simp: less_eq_num1_def less_num1_def intro: num1_eqI)
end

instance num1 :: wellorder
  by intro_classes (auto simp: less_eq_num1_def less_num1_def)


instance bit0 :: (finite) card2
proof
  show "finite (UNIV::'a bit0 set)"
    unfolding type_definition.univ [OF type_definition_bit0]
    by simp
  show "2 \<le> CARD('a bit0)"
    by simp
qed

instance bit1 :: (finite) card2
proof
  show "finite (UNIV::'a bit1 set)"
    unfolding type_definition.univ [OF type_definition_bit1]
    by simp
  show "2 \<le> CARD('a bit1)"
    by simp
qed

subsection \<open>Locales for for modular arithmetic subtypes\<close>

locale mod_type =
  fixes n :: int
  and Rep :: "'a::{zero,one,plus,times,uminus,minus} \<Rightarrow> int"
  and Abs :: "int \<Rightarrow> 'a::{zero,one,plus,times,uminus,minus}"
  assumes type: "type_definition Rep Abs {0..<n}"
  and size1: "1 < n"
  and zero_def: "0 = Abs 0"
  and one_def:  "1 = Abs 1"
  and add_def:  "x + y = Abs ((Rep x + Rep y) mod n)"
  and mult_def: "x * y = Abs ((Rep x * Rep y) mod n)"
  and diff_def: "x - y = Abs ((Rep x - Rep y) mod n)"
  and minus_def: "- x = Abs ((- Rep x) mod n)"
begin

lemma size0: "0 < n"
using size1 by simp

lemmas definitions =
  zero_def one_def add_def mult_def minus_def diff_def

lemma Rep_less_n: "Rep x < n"
by (rule type_definition.Rep [OF type, simplified, THEN conjunct2])

lemma Rep_le_n: "Rep x \<le> n"
by (rule Rep_less_n [THEN order_less_imp_le])

lemma Rep_inject_sym: "x = y \<longleftrightarrow> Rep x = Rep y"
by (rule type_definition.Rep_inject [OF type, symmetric])

lemma Rep_inverse: "Abs (Rep x) = x"
by (rule type_definition.Rep_inverse [OF type])

lemma Abs_inverse: "m \<in> {0..<n} \<Longrightarrow> Rep (Abs m) = m"
by (rule type_definition.Abs_inverse [OF type])

lemma Rep_Abs_mod: "Rep (Abs (m mod n)) = m mod n"
by (simp add: Abs_inverse pos_mod_conj [OF size0])

lemma Rep_Abs_0: "Rep (Abs 0) = 0"
by (simp add: Abs_inverse size0)

lemma Rep_0: "Rep 0 = 0"
by (simp add: zero_def Rep_Abs_0)

lemma Rep_Abs_1: "Rep (Abs 1) = 1"
by (simp add: Abs_inverse size1)

lemma Rep_1: "Rep 1 = 1"
by (simp add: one_def Rep_Abs_1)

lemma Rep_mod: "Rep x mod n = Rep x"
apply (rule_tac x=x in type_definition.Abs_cases [OF type])
apply (simp add: type_definition.Abs_inverse [OF type])
done

lemmas Rep_simps =
  Rep_inject_sym Rep_inverse Rep_Abs_mod Rep_mod Rep_Abs_0 Rep_Abs_1

lemma comm_ring_1: "OFCLASS('a, comm_ring_1_class)"
apply (intro_classes, unfold definitions)
apply (simp_all add: Rep_simps mod_simps field_simps)
done

end

locale mod_ring = mod_type n Rep Abs
  for n :: int
  and Rep :: "'a::{comm_ring_1} \<Rightarrow> int"
  and Abs :: "int \<Rightarrow> 'a::{comm_ring_1}"
begin

lemma of_nat_eq: "of_nat k = Abs (int k mod n)"
apply (induct k)
apply (simp add: zero_def)
apply (simp add: Rep_simps add_def one_def mod_simps ac_simps)
done

lemma of_int_eq: "of_int z = Abs (z mod n)"
apply (cases z rule: int_diff_cases)
apply (simp add: Rep_simps of_nat_eq diff_def mod_simps)
done

lemma Rep_numeral:
  "Rep (numeral w) = numeral w mod n"
using of_int_eq [of "numeral w"]
by (simp add: Rep_inject_sym Rep_Abs_mod)

lemma iszero_numeral:
  "iszero (numeral w::'a) \<longleftrightarrow> numeral w mod n = 0"
by (simp add: Rep_inject_sym Rep_numeral Rep_0 iszero_def)

lemma cases:
  assumes 1: "\<And>z. \<lbrakk>(x::'a) = of_int z; 0 \<le> z; z < n\<rbrakk> \<Longrightarrow> P"
  shows "P"
apply (cases x rule: type_definition.Abs_cases [OF type])
apply (rule_tac z="y" in 1)
apply (simp_all add: of_int_eq)
done

lemma induct:
  "(\<And>z. \<lbrakk>0 \<le> z; z < n\<rbrakk> \<Longrightarrow> P (of_int z)) \<Longrightarrow> P (x::'a)"
by (cases x rule: cases) simp

lemma UNIV_eq: "(UNIV :: 'a set) = Abs ` {0..<n}"
  using type type_definition.univ by blast

lemma CARD_eq: "CARD('a) = nat n"
proof -
  have "CARD('a) = card (Abs ` {0..<n})"
    by (simp add: UNIV_eq)
  also have "inj_on Abs {0..<n}"
    by (metis Abs_inverse inj_onI)
  hence "card (Abs ` {0..<n}) = nat n"
    using size1 by (subst card_image) auto
  finally show ?thesis .
qed

lemma CHAR_eq [simp]: "CHAR('a) = CARD('a)"
proof (rule CHAR_eqI)
  show "of_nat (CARD('a)) = (0 :: 'a)"
    by (simp add: CARD_eq of_nat_eq zero_def)
next
  fix n assume "of_nat n = (0 :: 'a)"
  thus "CARD('a) dvd n"
    by (metis CARD_eq Rep_0 Rep_Abs_mod Rep_le_n mod_0_imp_dvd nat_dvd_iff of_nat_eq)
qed

end


subsection \<open>Ring class instances\<close>

text \<open>
  Unfortunately \<open>ring_1\<close> instance is not possible for
  \<^typ>\<open>num1\<close>, since 0 and 1 are not distinct.
\<close>

instantiation
  bit0 and bit1 :: (finite) "{zero,one,plus,times,uminus,minus}"
begin

definition Abs_bit0' :: "int \<Rightarrow> 'a bit0" where
  "Abs_bit0' x = Abs_bit0 (x mod int CARD('a bit0))"

definition Abs_bit1' :: "int \<Rightarrow> 'a bit1" where
  "Abs_bit1' x = Abs_bit1 (x mod int CARD('a bit1))"

definition "0 = Abs_bit0 0"
definition "1 = Abs_bit0 1"
definition "x + y = Abs_bit0' (Rep_bit0 x + Rep_bit0 y)"
definition "x * y = Abs_bit0' (Rep_bit0 x * Rep_bit0 y)"
definition "x - y = Abs_bit0' (Rep_bit0 x - Rep_bit0 y)"
definition "- x = Abs_bit0' (- Rep_bit0 x)"

definition "0 = Abs_bit1 0"
definition "1 = Abs_bit1 1"
definition "x + y = Abs_bit1' (Rep_bit1 x + Rep_bit1 y)"
definition "x * y = Abs_bit1' (Rep_bit1 x * Rep_bit1 y)"
definition "x - y = Abs_bit1' (Rep_bit1 x - Rep_bit1 y)"
definition "- x = Abs_bit1' (- Rep_bit1 x)"

instance ..

end

interpretation bit0:
  mod_type "int CARD('a::finite bit0)"
           "Rep_bit0 :: 'a::finite bit0 \<Rightarrow> int"
           "Abs_bit0 :: int \<Rightarrow> 'a::finite bit0"
apply (rule mod_type.intro)
apply (simp add: type_definition_bit0)
apply (rule one_less_int_card)
apply (rule zero_bit0_def)
apply (rule one_bit0_def)
apply (rule plus_bit0_def [unfolded Abs_bit0'_def])
apply (rule times_bit0_def [unfolded Abs_bit0'_def])
apply (rule minus_bit0_def [unfolded Abs_bit0'_def])
apply (rule uminus_bit0_def [unfolded Abs_bit0'_def])
done

interpretation bit1:
  mod_type "int CARD('a::finite bit1)"
           "Rep_bit1 :: 'a::finite bit1 \<Rightarrow> int"
           "Abs_bit1 :: int \<Rightarrow> 'a::finite bit1"
apply (rule mod_type.intro)
apply (simp add: type_definition_bit1)
apply (rule one_less_int_card)
apply (rule zero_bit1_def)
apply (rule one_bit1_def)
apply (rule plus_bit1_def [unfolded Abs_bit1'_def])
apply (rule times_bit1_def [unfolded Abs_bit1'_def])
apply (rule minus_bit1_def [unfolded Abs_bit1'_def])
apply (rule uminus_bit1_def [unfolded Abs_bit1'_def])
done

instance bit0 :: (finite) comm_ring_1
  by (rule bit0.comm_ring_1)

instance bit1 :: (finite) comm_ring_1
  by (rule bit1.comm_ring_1)

interpretation bit0:
  mod_ring "int CARD('a::finite bit0)"
           "Rep_bit0 :: 'a::finite bit0 \<Rightarrow> int"
           "Abs_bit0 :: int \<Rightarrow> 'a::finite bit0"
  ..

interpretation bit1:
  mod_ring "int CARD('a::finite bit1)"
           "Rep_bit1 :: 'a::finite bit1 \<Rightarrow> int"
           "Abs_bit1 :: int \<Rightarrow> 'a::finite bit1"
  ..

text \<open>Set up cases, induction, and arithmetic\<close>

lemmas bit0_cases [case_names of_int, cases type: bit0] = bit0.cases
lemmas bit1_cases [case_names of_int, cases type: bit1] = bit1.cases

lemmas bit0_induct [case_names of_int, induct type: bit0] = bit0.induct
lemmas bit1_induct [case_names of_int, induct type: bit1] = bit1.induct

lemmas bit0_iszero_numeral [simp] = bit0.iszero_numeral
lemmas bit1_iszero_numeral [simp] = bit1.iszero_numeral

lemmas [simp] = eq_numeral_iff_iszero [where 'a="'a bit0"] for dummy :: "'a::finite"
lemmas [simp] = eq_numeral_iff_iszero [where 'a="'a bit1"] for dummy :: "'a::finite"

subsection \<open>Order instances\<close>

instantiation bit0 and bit1 :: (finite) linorder begin
definition "a < b \<longleftrightarrow> Rep_bit0 a < Rep_bit0 b"
definition "a \<le> b \<longleftrightarrow> Rep_bit0 a \<le> Rep_bit0 b"
definition "a < b \<longleftrightarrow> Rep_bit1 a < Rep_bit1 b"
definition "a \<le> b \<longleftrightarrow> Rep_bit1 a \<le> Rep_bit1 b"

instance
  by(intro_classes)
    (auto simp add: less_eq_bit0_def less_bit0_def less_eq_bit1_def less_bit1_def Rep_bit0_inject Rep_bit1_inject)
end

lemma (in preorder) tranclp_less: "(<) \<^sup>+\<^sup>+ = (<)"
by(auto simp add: fun_eq_iff intro: less_trans elim: tranclp.induct)

instance bit0 and bit1 :: (finite) wellorder
proof -
  have "wf {(x :: 'a bit0, y). x < y}"
    by(auto simp add: trancl_def tranclp_less intro!: finite_acyclic_wf acyclicI)
  thus "OFCLASS('a bit0, wellorder_class)"
    by(rule wf_wellorderI) intro_classes
next
  have "wf {(x :: 'a bit1, y). x < y}"
    by(auto simp add: trancl_def tranclp_less intro!: finite_acyclic_wf acyclicI)
  thus "OFCLASS('a bit1, wellorder_class)"
    by(rule wf_wellorderI) intro_classes
qed

subsection \<open>Code setup and type classes for code generation\<close>

text \<open>Code setup for \<^typ>\<open>num0\<close> and \<^typ>\<open>num1\<close>\<close>

definition Num0 :: num0 where "Num0 = Abs_num0 0"
code_datatype Num0

instantiation num0 :: equal begin
definition equal_num0 :: "num0 \<Rightarrow> num0 \<Rightarrow> bool"
  where "equal_num0 = (=)"
instance by intro_classes (simp add: equal_num0_def)
end

lemma equal_num0_code [code]:
  "equal_class.equal Num0 Num0 = True"
by(rule equal_refl)

code_datatype "1 :: num1"

instantiation num1 :: equal begin
definition equal_num1 :: "num1 \<Rightarrow> num1 \<Rightarrow> bool"
  where "equal_num1 = (=)"
instance by intro_classes (simp add: equal_num1_def)
end

lemma equal_num1_code [code]:
  "equal_class.equal (1 :: num1) 1 = True"
by(rule equal_refl)

instantiation num1 :: enum begin
definition "enum_class.enum = [1 :: num1]"
definition "enum_class.enum_all P = P (1 :: num1)"
definition "enum_class.enum_ex P = P (1 :: num1)"
instance
  by intro_classes
     (auto simp add: enum_num1_def enum_all_num1_def enum_ex_num1_def num1_eq_iff Ball_def)
end

instantiation num0 and num1 :: card_UNIV begin
definition "finite_UNIV = Phantom(num0) False"
definition "card_UNIV = Phantom(num0) 0"
definition "finite_UNIV = Phantom(num1) True"
definition "card_UNIV = Phantom(num1) 1"
instance
  by intro_classes
     (simp_all add: finite_UNIV_num0_def card_UNIV_num0_def infinite_num0 finite_UNIV_num1_def card_UNIV_num1_def)
end


text \<open>Code setup for \<^typ>\<open>'a bit0\<close> and \<^typ>\<open>'a bit1\<close>\<close>

declare
  bit0.Rep_inverse[code abstype]
  bit0.Rep_0[code abstract]
  bit0.Rep_1[code abstract]

lemma Abs_bit0'_code [code abstract]:
  "Rep_bit0 (Abs_bit0' x :: 'a :: finite bit0) = x mod int (CARD('a bit0))"
by(auto simp add: Abs_bit0'_def intro!: Abs_bit0_inverse)

lemma inj_on_Abs_bit0:
  "inj_on (Abs_bit0 :: int \<Rightarrow> 'a bit0) {0..<2 * int CARD('a :: finite)}"
by(auto intro: inj_onI simp add: Abs_bit0_inject)

declare
  bit1.Rep_inverse[code abstype]
  bit1.Rep_0[code abstract]
  bit1.Rep_1[code abstract]

lemma Abs_bit1'_code [code abstract]:
  "Rep_bit1 (Abs_bit1' x :: 'a :: finite bit1) = x mod int (CARD('a bit1))"
  by(auto simp add: Abs_bit1'_def intro!: Abs_bit1_inverse)

lemma inj_on_Abs_bit1:
  "inj_on (Abs_bit1 :: int \<Rightarrow> 'a bit1) {0..<1 + 2 * int CARD('a :: finite)}"
by(auto intro: inj_onI simp add: Abs_bit1_inject)

instantiation bit0 and bit1 :: (finite) equal begin

definition "equal_class.equal x y \<longleftrightarrow> Rep_bit0 x = Rep_bit0 y"
definition "equal_class.equal x y \<longleftrightarrow> Rep_bit1 x = Rep_bit1 y"

instance
  by intro_classes (simp_all add: equal_bit0_def equal_bit1_def Rep_bit0_inject Rep_bit1_inject)

end

instantiation bit0 :: (finite) enum begin
definition "(enum_class.enum :: 'a bit0 list) = map (Abs_bit0' \<circ> int) (upt 0 (CARD('a bit0)))"
definition "enum_class.enum_all P = (\<forall>b :: 'a bit0 \<in> set enum_class.enum. P b)"
definition "enum_class.enum_ex P = (\<exists>b :: 'a bit0 \<in> set enum_class.enum. P b)"

instance proof
  show "distinct (enum_class.enum :: 'a bit0 list)"
    by (simp add: enum_bit0_def distinct_map inj_on_def Abs_bit0'_def Abs_bit0_inject)

  let ?Abs = "Abs_bit0 :: _ \<Rightarrow> 'a bit0"
  interpret type_definition Rep_bit0 ?Abs "{0..<2 * int CARD('a)}"
    by (fact type_definition_bit0)
  have "UNIV = ?Abs ` {0..<2 * int CARD('a)}"
    by (simp add: Abs_image)
  also have "\<dots> = ?Abs ` (int ` {0..<2 * CARD('a)})"
    by (simp add: image_int_atLeastLessThan)
  also have "\<dots> = (?Abs \<circ> int) ` {0..<2 * CARD('a)}"
    by (simp add: image_image cong: image_cong)
  also have "\<dots> = set enum_class.enum"
    by (simp add: enum_bit0_def Abs_bit0'_def cong: image_cong_simp)
  finally show univ_eq: "(UNIV :: 'a bit0 set) = set enum_class.enum" .

  fix P :: "'a bit0 \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P"
    by(simp_all add: enum_all_bit0_def enum_ex_bit0_def univ_eq)
qed

end

instantiation bit1 :: (finite) enum begin
definition "(enum_class.enum :: 'a bit1 list) = map (Abs_bit1' \<circ> int) (upt 0 (CARD('a bit1)))"
definition "enum_class.enum_all P = (\<forall>b :: 'a bit1 \<in> set enum_class.enum. P b)"
definition "enum_class.enum_ex P = (\<exists>b :: 'a bit1 \<in> set enum_class.enum. P b)"

instance
proof(intro_classes)
  show "distinct (enum_class.enum :: 'a bit1 list)"
    by(simp only: Abs_bit1'_def zmod_int[symmetric] enum_bit1_def distinct_map Suc_eq_plus1 card_bit1 o_apply inj_on_def)
      (clarsimp simp add: Abs_bit1_inject)

  let ?Abs = "Abs_bit1 :: _ \<Rightarrow> 'a bit1"
  interpret type_definition Rep_bit1 ?Abs "{0..<1 + 2 * int CARD('a)}"
    by (fact type_definition_bit1)
  have "UNIV = ?Abs ` {0..<1 + 2 * int CARD('a)}"
    by (simp add: Abs_image)
  also have "\<dots> = ?Abs ` (int ` {0..<1 + 2 * CARD('a)})"
    by (simp add: image_int_atLeastLessThan)
  also have "\<dots> = (?Abs \<circ> int) ` {0..<1 + 2 * CARD('a)}"
    by (simp add: image_image cong: image_cong)
  finally show univ_eq: "(UNIV :: 'a bit1 set) = set enum_class.enum"
    by (simp only: enum_bit1_def set_map set_upt) (simp add: Abs_bit1'_def cong: image_cong_simp)

  fix P :: "'a bit1 \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P"
    by(simp_all add: enum_all_bit1_def enum_ex_bit1_def univ_eq)
qed

end

instantiation bit0 and bit1 :: (finite) finite_UNIV begin
definition "finite_UNIV = Phantom('a bit0) True"
definition "finite_UNIV = Phantom('a bit1) True"
instance by intro_classes (simp_all add: finite_UNIV_bit0_def finite_UNIV_bit1_def)
end

instantiation bit0 and bit1 :: ("{finite,card_UNIV}") card_UNIV begin
definition "card_UNIV = Phantom('a bit0) (2 * of_phantom (card_UNIV :: 'a card_UNIV))"
definition "card_UNIV = Phantom('a bit1) (1 + 2 * of_phantom (card_UNIV :: 'a card_UNIV))"
instance by intro_classes (simp_all add: card_UNIV_bit0_def card_UNIV_bit1_def card_UNIV)
end

subsection \<open>Syntax\<close>

syntax
  "_NumeralType" :: "num_token => type"  ("_")
  "_NumeralType0" :: type ("0")
  "_NumeralType1" :: type ("1")

translations
  (type) "1" == (type) "num1"
  (type) "0" == (type) "num0"

parse_translation \<open>
  let
    fun mk_bintype n =
      let
        fun mk_bit 0 = Syntax.const \<^type_syntax>\<open>bit0\<close>
          | mk_bit 1 = Syntax.const \<^type_syntax>\<open>bit1\<close>;
        fun bin_of n =
          if n = 1 then Syntax.const \<^type_syntax>\<open>num1\<close>
          else if n = 0 then Syntax.const \<^type_syntax>\<open>num0\<close>
          else if n = ~1 then raise TERM ("negative type numeral", [])
          else
            let val (q, r) = Integer.div_mod n 2;
            in mk_bit r $ bin_of q end;
      in bin_of n end;

    fun numeral_tr [Free (str, _)] = mk_bintype (the (Int.fromString str))
      | numeral_tr ts = raise TERM ("numeral_tr", ts);

  in [(\<^syntax_const>\<open>_NumeralType\<close>, K numeral_tr)] end
\<close>

print_translation \<open>
  let
    fun int_of [] = 0
      | int_of (b :: bs) = b + 2 * int_of bs;

    fun bin_of (Const (\<^type_syntax>\<open>num0\<close>, _)) = []
      | bin_of (Const (\<^type_syntax>\<open>num1\<close>, _)) = [1]
      | bin_of (Const (\<^type_syntax>\<open>bit0\<close>, _) $ bs) = 0 :: bin_of bs
      | bin_of (Const (\<^type_syntax>\<open>bit1\<close>, _) $ bs) = 1 :: bin_of bs
      | bin_of t = raise TERM ("bin_of", [t]);

    fun bit_tr' b [t] =
          let
            val rev_digs = b :: bin_of t handle TERM _ => raise Match
            val i = int_of rev_digs;
            val num = string_of_int (abs i);
          in
            Syntax.const \<^syntax_const>\<open>_NumeralType\<close> $ Syntax.free num
          end
      | bit_tr' b _ = raise Match;
  in
   [(\<^type_syntax>\<open>bit0\<close>, K (bit_tr' 0)),
    (\<^type_syntax>\<open>bit1\<close>, K (bit_tr' 1))]
  end
\<close>

subsection \<open>Examples\<close>

lemma "CARD(0) = 0" by simp
lemma "CARD(17) = 17" by simp
lemma "CHAR(23) = 23" by simp
lemma "8 * 11 ^ 3 - 6 = (2::5)" by simp

end
