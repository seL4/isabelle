(*  Title:      HOL/Library/Phantom_Type.thy
    Author:     Andreas Lochbihler
*)

header {* A generic phantom type *}

theory Phantom_Type imports "~~/src/HOL/Main" begin

datatype ('a, 'b) phantom = phantom 'b

primrec of_phantom :: "('a, 'b) phantom \<Rightarrow> 'b" 
where "of_phantom (phantom x) = x"

lemma of_phantom_phantom [simp]: "phantom (of_phantom x) = x"
by(cases x) simp

lemma type_definition_phantom': "type_definition of_phantom phantom UNIV"
by(unfold_locales) simp_all

setup_lifting (no_code) type_definition_phantom'

lemma phantom_comp_of_phantom [simp]: "phantom \<circ> of_phantom = id"
  and of_phantom_comp_phantom [simp]: "of_phantom \<circ> phantom = id"
by(simp_all add: o_def id_def)

syntax "_Phantom" :: "type \<Rightarrow> logic" ("(1Phantom/(1'(_')))")
translations
  "Phantom('t)" => "CONST phantom :: _ \<Rightarrow> ('t, _) phantom"

typed_print_translation (advanced) {*
let
  fun phantom_tr' ctxt 
      (Type (@{type_name fun}, [_, Type (@{type_name phantom}, [T, _])])) ts =
    Term.list_comb (Syntax.const @{syntax_const "_Phantom"} $ Syntax_Phases.term_of_typ ctxt T, ts)
  | phantom_tr' _ _ _ = raise Match;
in [(@{const_syntax phantom}, phantom_tr')] end
*}

end
