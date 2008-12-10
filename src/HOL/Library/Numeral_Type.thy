(*
  ID:     $Id$
  Author: Brian Huffman

  Numeral Syntax for Types
*)

header "Numeral Syntax for Types"

theory Numeral_Type
imports Plain "~~/src/HOL/Presburger"
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


subsection {* Cardinalities of types *}

syntax "_type_card" :: "type => nat" ("(1CARD/(1'(_')))")

translations "CARD(t)" => "CONST card (CONST UNIV \<Colon> t set)"

typed_print_translation {*
let
  fun card_univ_tr' show_sorts _ [Const (@{const_name UNIV}, Type(_,[T,_]))] =
    Syntax.const "_type_card" $ Syntax.term_of_typ show_sorts T;
in [(@{const_syntax card}, card_univ_tr')]
end
*}

lemma card_unit: "CARD(unit) = 1"
  unfolding UNIV_unit by simp

lemma card_bool: "CARD(bool) = 2"
  unfolding UNIV_bool by simp

lemma card_prod: "CARD('a::finite \<times> 'b::finite) = CARD('a) * CARD('b)"
  unfolding UNIV_Times_UNIV [symmetric] by (simp only: card_cartesian_product)

lemma card_sum: "CARD('a::finite + 'b::finite) = CARD('a) + CARD('b)"
  unfolding UNIV_Plus_UNIV [symmetric] by (simp only: finite card_Plus)

lemma card_option: "CARD('a::finite option) = Suc CARD('a)"
  unfolding insert_None_conv_UNIV [symmetric]
  apply (subgoal_tac "(None::'a option) \<notin> range Some")
  apply (simp add: finite card_image)
  apply fast
  done

lemma card_set: "CARD('a::finite set) = 2 ^ CARD('a)"
  unfolding Pow_UNIV [symmetric]
  by (simp only: card_Pow finite numeral_2_eq_2)


subsection {* Numeral Types *}

typedef (open) num0 = "UNIV :: nat set" ..
typedef (open) num1 = "UNIV :: unit set" ..
typedef (open) 'a bit0 = "UNIV :: (bool * 'a) set" ..
typedef (open) 'a bit1 = "UNIV :: (bool * 'a) option set" ..

instance num1 :: finite
proof
  show "finite (UNIV::num1 set)"
    unfolding type_definition.univ [OF type_definition_num1]
    using finite by (rule finite_imageI)
qed

instance bit0 :: (finite) finite
proof
  show "finite (UNIV::'a bit0 set)"
    unfolding type_definition.univ [OF type_definition_bit0]
    using finite by (rule finite_imageI)
qed

instance bit1 :: (finite) finite
proof
  show "finite (UNIV::'a bit1 set)"
    unfolding type_definition.univ [OF type_definition_bit1]
    using finite by (rule finite_imageI)
qed

lemma card_num1: "CARD(num1) = 1"
  unfolding type_definition.card [OF type_definition_num1]
  by (simp only: card_unit)

lemma card_bit0: "CARD('a::finite bit0) = 2 * CARD('a)"
  unfolding type_definition.card [OF type_definition_bit0]
  by (simp only: card_prod card_bool)

lemma card_bit1: "CARD('a::finite bit1) = Suc (2 * CARD('a))"
  unfolding type_definition.card [OF type_definition_bit1]
  by (simp only: card_prod card_option card_bool)

lemma card_num0: "CARD (num0) = 0"
  by (simp add: infinite_UNIV_nat card_eq_0_iff type_definition.card [OF type_definition_num0])

lemmas card_univ_simps [simp] =
  card_unit
  card_bool
  card_prod
  card_sum
  card_option
  card_set
  card_num1
  card_bit0
  card_bit1
  card_num0


subsection {* Syntax *}

syntax
  "_NumeralType" :: "num_const => type"  ("_")
  "_NumeralType0" :: type ("0")
  "_NumeralType1" :: type ("1")

translations
  "_NumeralType1" == (type) "num1"
  "_NumeralType0" == (type) "num0"

parse_translation {*
let

val num1_const = Syntax.const "Numeral_Type.num1";
val num0_const = Syntax.const "Numeral_Type.num0";
val B0_const = Syntax.const "Numeral_Type.bit0";
val B1_const = Syntax.const "Numeral_Type.bit1";

fun mk_bintype n =
  let
    fun mk_bit n = if n = 0 then B0_const else B1_const;
    fun bin_of n =
      if n = 1 then num1_const
      else if n = 0 then num0_const
      else if n = ~1 then raise TERM ("negative type numeral", [])
      else
        let val (q, r) = Integer.div_mod n 2;
        in mk_bit r $ bin_of q end;
  in bin_of n end;

fun numeral_tr (*"_NumeralType"*) [Const (str, _)] =
      mk_bintype (valOf (Int.fromString str))
  | numeral_tr (*"_NumeralType"*) ts = raise TERM ("numeral_tr", ts);

in [("_NumeralType", numeral_tr)] end;
*}

print_translation {*
let
fun int_of [] = 0
  | int_of (b :: bs) = b + 2 * int_of bs;

fun bin_of (Const ("num0", _)) = []
  | bin_of (Const ("num1", _)) = [1]
  | bin_of (Const ("bit0", _) $ bs) = 0 :: bin_of bs
  | bin_of (Const ("bit1", _) $ bs) = 1 :: bin_of bs
  | bin_of t = raise TERM("bin_of", [t]);

fun bit_tr' b [t] =
  let
    val rev_digs = b :: bin_of t handle TERM _ => raise Match
    val i = int_of rev_digs;
    val num = string_of_int (abs i);
  in
    Syntax.const "_NumeralType" $ Syntax.free num
  end
  | bit_tr' b _ = raise Match;

in [("bit0", bit_tr' 0), ("bit1", bit_tr' 1)] end;
*}


subsection {* Classes with at least 1 and 2  *}

text {* Class finite already captures "at least 1" *}

lemma zero_less_card_finite [simp]:
  "0 < CARD('a::finite)"
proof (cases "CARD('a::finite) = 0")
  case False thus ?thesis by (simp del: card_0_eq)
next
  case True
  thus ?thesis by (simp add: finite)
qed

lemma one_le_card_finite [simp]:
  "Suc 0 <= CARD('a::finite)"
  by (simp add: less_Suc_eq_le [symmetric] zero_less_card_finite)


text {* Class for cardinality "at least 2" *}

class card2 = finite + 
  assumes two_le_card: "2 <= CARD('a)"

lemma one_less_card: "Suc 0 < CARD('a::card2)"
  using two_le_card [where 'a='a] by simp

instance bit0 :: (finite) card2
  by intro_classes (simp add: one_le_card_finite)

instance bit1 :: (finite) card2
  by intro_classes (simp add: one_le_card_finite)

subsection {* Examples *}

lemma "CARD(0) = 0" by simp
lemma "CARD(17) = 17" by simp

end
