(*  Title:      HOL/Library/Numeral_Type.thy
    Author:     Brian Huffman
*)

header {* Numeral Syntax for Types *}

theory Numeral_Type
imports Cardinality
begin

subsection {* Numeral Types *}

typedef (open) num0 = "UNIV :: nat set" ..
typedef (open) num1 = "UNIV :: unit set" ..

typedef (open) 'a bit0 = "{0 ..< 2 * int CARD('a::finite)}"
proof
  show "0 \<in> {0 ..< 2 * int CARD('a)}"
    by simp
qed

typedef (open) 'a bit1 = "{0 ..< 1 + 2 * int CARD('a::finite)}"
proof
  show "0 \<in> {0 ..< 1 + 2 * int CARD('a)}"
    by simp
qed

lemma card_num0 [simp]: "CARD (num0) = 0"
  unfolding type_definition.card [OF type_definition_num0]
  by simp

lemma card_num1 [simp]: "CARD(num1) = 1"
  unfolding type_definition.card [OF type_definition_num1]
  by (simp only: card_unit)

lemma card_bit0 [simp]: "CARD('a bit0) = 2 * CARD('a::finite)"
  unfolding type_definition.card [OF type_definition_bit0]
  by simp

lemma card_bit1 [simp]: "CARD('a bit1) = Suc (2 * CARD('a::finite))"
  unfolding type_definition.card [OF type_definition_bit1]
  by simp

instance num1 :: finite
proof
  show "finite (UNIV::num1 set)"
    unfolding type_definition.univ [OF type_definition_num1]
    using finite by (rule finite_imageI)
qed

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


subsection {* Locales for for modular arithmetic subtypes *}

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
apply (simp add: mod_pos_pos_trivial)
done

lemmas Rep_simps =
  Rep_inject_sym Rep_inverse Rep_Abs_mod Rep_mod Rep_Abs_0 Rep_Abs_1

lemma comm_ring_1: "OFCLASS('a, comm_ring_1_class)"
apply (intro_classes, unfold definitions)
apply (simp_all add: Rep_simps zmod_simps field_simps)
done

end

locale mod_ring = mod_type n Rep Abs
  for n :: int
  and Rep :: "'a::{number_ring} \<Rightarrow> int"
  and Abs :: "int \<Rightarrow> 'a::{number_ring}"
begin

lemma of_nat_eq: "of_nat k = Abs (int k mod n)"
apply (induct k)
apply (simp add: zero_def)
apply (simp add: Rep_simps add_def one_def zmod_simps add_ac)
done

lemma of_int_eq: "of_int z = Abs (z mod n)"
apply (cases z rule: int_diff_cases)
apply (simp add: Rep_simps of_nat_eq diff_def zmod_simps)
done

lemma Rep_number_of:
  "Rep (number_of w) = number_of w mod n"
by (simp add: number_of_eq of_int_eq Rep_Abs_mod)

lemma iszero_number_of:
  "iszero (number_of w::'a) \<longleftrightarrow> number_of w mod n = 0"
by (simp add: Rep_simps number_of_eq of_int_eq iszero_def zero_def)

lemma cases:
  assumes 1: "\<And>z. \<lbrakk>(x::'a) = of_int z; 0 \<le> z; z < n\<rbrakk> \<Longrightarrow> P"
  shows "P"
apply (cases x rule: type_definition.Abs_cases [OF type])
apply (rule_tac z="y" in 1)
apply (simp_all add: of_int_eq mod_pos_pos_trivial)
done

lemma induct:
  "(\<And>z. \<lbrakk>0 \<le> z; z < n\<rbrakk> \<Longrightarrow> P (of_int z)) \<Longrightarrow> P (x::'a)"
by (cases x rule: cases) simp

end


subsection {* Number ring instances *}

text {*
  Unfortunately a number ring instance is not possible for
  @{typ num1}, since 0 and 1 are not distinct.
*}

instantiation num1 :: "{comm_ring,comm_monoid_mult,number}"
begin

lemma num1_eq_iff: "(x::num1) = (y::num1) \<longleftrightarrow> True"
  by (induct x, induct y) simp

instance proof
qed (simp_all add: num1_eq_iff)

end

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
apply (simp add: int_mult type_definition_bit0)
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
apply (simp add: int_mult type_definition_bit1)
apply (rule one_less_int_card)
apply (rule zero_bit1_def)
apply (rule one_bit1_def)
apply (rule plus_bit1_def [unfolded Abs_bit1'_def])
apply (rule times_bit1_def [unfolded Abs_bit1'_def])
apply (rule minus_bit1_def [unfolded Abs_bit1'_def])
apply (rule uminus_bit1_def [unfolded Abs_bit1'_def])
done

instance bit0 :: (finite) comm_ring_1
  by (rule bit0.comm_ring_1)+

instance bit1 :: (finite) comm_ring_1
  by (rule bit1.comm_ring_1)+

instantiation bit0 and bit1 :: (finite) number_ring
begin

definition "(number_of w :: _ bit0) = of_int w"

definition "(number_of w :: _ bit1) = of_int w"

instance proof
qed (rule number_of_bit0_def number_of_bit1_def)+

end

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

text {* Set up cases, induction, and arithmetic *}

lemmas bit0_cases [case_names of_int, cases type: bit0] = bit0.cases
lemmas bit1_cases [case_names of_int, cases type: bit1] = bit1.cases

lemmas bit0_induct [case_names of_int, induct type: bit0] = bit0.induct
lemmas bit1_induct [case_names of_int, induct type: bit1] = bit1.induct

lemmas bit0_iszero_number_of [simp] = bit0.iszero_number_of
lemmas bit1_iszero_number_of [simp] = bit1.iszero_number_of


subsection {* Syntax *}

syntax
  "_NumeralType" :: "num_token => type"  ("_")
  "_NumeralType0" :: type ("0")
  "_NumeralType1" :: type ("1")

translations
  (type) "1" == (type) "num1"
  (type) "0" == (type) "num0"

parse_translation {*
let
  fun mk_bintype n =
    let
      fun mk_bit 0 = Syntax.const @{type_syntax bit0}
        | mk_bit 1 = Syntax.const @{type_syntax bit1};
      fun bin_of n =
        if n = 1 then Syntax.const @{type_syntax num1}
        else if n = 0 then Syntax.const @{type_syntax num0}
        else if n = ~1 then raise TERM ("negative type numeral", [])
        else
          let val (q, r) = Integer.div_mod n 2;
          in mk_bit r $ bin_of q end;
    in bin_of n end;

  fun numeral_tr [Free (str, _)] = mk_bintype (the (Int.fromString str))
    | numeral_tr ts = raise TERM ("numeral_tr", ts);

in [(@{syntax_const "_NumeralType"}, numeral_tr)] end;
*}

print_translation {*
let
  fun int_of [] = 0
    | int_of (b :: bs) = b + 2 * int_of bs;

  fun bin_of (Const (@{type_syntax num0}, _)) = []
    | bin_of (Const (@{type_syntax num1}, _)) = [1]
    | bin_of (Const (@{type_syntax bit0}, _) $ bs) = 0 :: bin_of bs
    | bin_of (Const (@{type_syntax bit1}, _) $ bs) = 1 :: bin_of bs
    | bin_of t = raise TERM ("bin_of", [t]);

  fun bit_tr' b [t] =
        let
          val rev_digs = b :: bin_of t handle TERM _ => raise Match
          val i = int_of rev_digs;
          val num = string_of_int (abs i);
        in
          Syntax.const @{syntax_const "_NumeralType"} $ Syntax.free num
        end
    | bit_tr' b _ = raise Match;
in [(@{type_syntax bit0}, bit_tr' 0), (@{type_syntax bit1}, bit_tr' 1)] end;
*}

subsection {* Examples *}

lemma "CARD(0) = 0" by simp
lemma "CARD(17) = 17" by simp
lemma "8 * 11 ^ 3 - 6 = (2::5)" by simp

end
