(*  Title:      Option.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

Derived rules
*)
open Option;

qed_goal "not_None_eq" thy "(x ~= None) = (? y. x = Some y)"
	(K [option.induct_tac "x" 1, Auto_tac]);

section "case analysis in premises";

val optionE = prove_goal thy 
	"[| opt = None ==> P;  !!x. opt = Some x ==> P |] ==> P" (fn prems => [
	case_tac "opt = None" 1,
	 eresolve_tac prems 1,
	dtac (not_None_eq RS iffD1) 1,
	etac exE 1,
	eresolve_tac prems 1]);
fun optionE_tac s i = EVERY [
	res_inst_tac [("opt",s)] optionE i,
	 hyp_subst_tac (i+1),
	hyp_subst_tac i];

qed_goal "option_caseE" thy "[|case x of None => P | Some y => Q y; \
\                  [|x = None;   P  |] ==> R; \
\             !!y. [|x = Some y; Q y|] ==> R|] ==> R" (fn prems => [
	cut_facts_tac prems 1,
	res_inst_tac [("opt","x")] optionE 1,
	 forward_tac prems 1,
	  forward_tac prems 3, 
	   Auto_tac]);
fun option_case_tac i = EVERY [
	etac option_caseE i,
	 hyp_subst_tac (i+1),
	hyp_subst_tac i];


section "the";

qed_goalw "the_Some" thy [the_def]
	"the (Some x) = x" (K [Simp_tac 1]);
Addsimps [the_Some];


section "option_map";

qed_goalw "option_map_None" thy [option_map_def] 
	"option_map f None = None" (K [Simp_tac 1]);
qed_goalw "option_map_Some" thy [option_map_def] 
	"option_map f (Some x) = Some (f x)" (K [Simp_tac 1]);
Addsimps [option_map_None, option_map_Some];

val option_map_eq_Some = prove_goalw thy [option_map_def]
	"(option_map f xo = Some y) = (? z. xo = Some z & f z = y)" 
 (K [asm_full_simp_tac (simpset() addsplits [split_option_case]) 1]);
AddIffs[option_map_eq_Some];

section "o2s";

val elem_o2s = prove_goal thy "!!X. x : o2s xo = (xo = Some x)"
 (K [optionE_tac "xo" 1, Auto_tac]);
AddSDs [elem_o2s RS iffD1];
Addsimps [elem_o2s];

val o2s_empty_eq = prove_goal thy "(o2s xo = {}) = (xo = None)"
 (K [optionE_tac "xo" 1, Auto_tac]);
Addsimps [o2s_empty_eq];
