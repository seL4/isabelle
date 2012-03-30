(*  Title:      HOL/Library/Cardinality.thy
    Author:     Brian Huffman
*)

header {* Cardinality of types *}

theory Cardinality
imports "~~/src/HOL/Main"
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

translations "CARD('t)" => "CONST card (CONST UNIV \<Colon> 't set)"

typed_print_translation (advanced) {*
  let
    fun card_univ_tr' ctxt _ [Const (@{const_syntax UNIV}, Type (_, [T, _]))] =
      Syntax.const @{syntax_const "_type_card"} $ Syntax_Phases.term_of_typ ctxt T;
  in [(@{const_syntax card}, card_univ_tr')] end
*}

lemma card_unit [simp]: "CARD(unit) = 1"
  unfolding UNIV_unit by simp

lemma card_prod [simp]: "CARD('a \<times> 'b) = CARD('a::finite) * CARD('b::finite)"
  unfolding UNIV_Times_UNIV [symmetric] by (simp only: card_cartesian_product)

lemma card_sum [simp]: "CARD('a + 'b) = CARD('a::finite) + CARD('b::finite)"
  unfolding UNIV_Plus_UNIV [symmetric] by (simp only: finite card_Plus)

lemma card_option [simp]: "CARD('a option) = Suc CARD('a::finite)"
  unfolding UNIV_option_conv
  apply (subgoal_tac "(None::'a option) \<notin> range Some")
  apply (simp add: card_image)
  apply fast
  done

lemma card_set [simp]: "CARD('a set) = 2 ^ CARD('a::finite)"
  unfolding Pow_UNIV [symmetric]
  by (simp only: card_Pow finite)

lemma card_nat [simp]: "CARD(nat) = 0"
  by (simp add: card_eq_0_iff)


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

end
