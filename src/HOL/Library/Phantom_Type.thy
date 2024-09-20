(*  Title:      HOL/Library/Phantom_Type.thy
    Author:     Andreas Lochbihler
*)

section \<open>A generic phantom type\<close>

theory Phantom_Type
imports Main
begin

datatype ('a, 'b) phantom = phantom (of_phantom: 'b)

lemma type_definition_phantom': "type_definition of_phantom phantom UNIV"
by(unfold_locales) simp_all

lemma phantom_comp_of_phantom [simp]: "phantom \<circ> of_phantom = id"
  and of_phantom_comp_phantom [simp]: "of_phantom \<circ> phantom = id"
by(simp_all add: o_def id_def)

syntax "_Phantom" :: "type \<Rightarrow> logic" (\<open>(1Phantom/(1'(_')))\<close>)
syntax_consts "_Phantom" == phantom
translations
  "Phantom('t)" => "CONST phantom :: _ \<Rightarrow> ('t, _) phantom"

typed_print_translation \<open>
  let
    fun phantom_tr' ctxt (Type (\<^type_name>\<open>fun\<close>, [_, Type (\<^type_name>\<open>phantom\<close>, [T, _])])) ts =
          list_comb
            (Syntax.const \<^syntax_const>\<open>_Phantom\<close> $ Syntax_Phases.term_of_typ ctxt T, ts)
      | phantom_tr' _ _ _ = raise Match;
  in [(\<^const_syntax>\<open>phantom\<close>, phantom_tr')] end
\<close>

lemma of_phantom_inject [simp]:
  "of_phantom x = of_phantom y \<longleftrightarrow> x = y"
by(cases x y rule: phantom.exhaust[case_product phantom.exhaust]) simp

end
