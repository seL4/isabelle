(*  Title:      Option.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

Derived rules
*)

Goal "(x ~= None) = (? y. x = Some y)";
by (induct_tac "x" 1);
by Auto_tac;
qed "not_None_eq";
AddIffs[not_None_eq];

Goal "(!y. x ~= Some y) = (x = None)";
by (induct_tac "x" 1);
by Auto_tac;
qed "not_Some_eq";
AddIffs[not_Some_eq];


section "case analysis in premises";

val prems = Goal
	"[| opt = None ==> P;  !!x. opt = Some x ==> P |] ==> P";
by (case_tac "opt = None" 1);
by (eresolve_tac prems 1);
by (dtac (not_None_eq RS iffD1) 1);
by (etac exE 1);
by (eresolve_tac prems 1);
qed "optionE";

val prems = Goal
     "[| case x of None => P | Some y => Q y; \
\        [| x = None;   P  |] ==> R; \
\        !!y. [|x = Some y; Q y|] ==> R|] ==> R";
by (cut_facts_tac prems 1);
by (res_inst_tac [("opt","x")] optionE 1);
by (forward_tac prems 1);
by (forward_tac prems 3);
by Auto_tac;
qed "option_caseE";


section "option_map";

Goalw [option_map_def] "option_map f None = None";
by (Simp_tac 1);
qed "option_map_None";

Goalw [option_map_def] "option_map f (Some x) = Some (f x)";
by (Simp_tac 1);
qed "option_map_Some";

Addsimps [option_map_None, option_map_Some];

Goalw [option_map_def]
    "(option_map f xo = Some y) = (? z. xo = Some z & f z = y)";
by (asm_full_simp_tac (simpset() addsplits [option.split]) 1);
qed "option_map_eq_Some";
AddIffs[option_map_eq_Some];

Goal 
"option_map f o sum_case g h = sum_case (option_map f o g) (option_map f o h)";
by (rtac ext 1);
by (simp_tac (simpset() addsplits [sum.split]) 1);
qed "option_map_o_sum_case";
Addsimps [option_map_o_sum_case];


section "o2s";

Goal "[| !x:o2s A. P x; A = Some x |] ==> P x";
by Auto_tac;
qed "ospec";
AddDs[ospec];

claset_ref() := claset() addSD2 ("ospec", ospec);


Goal "(x : o2s xo) = (xo = Some x)";
by (case_tac "xo" 1);
by Auto_tac;
qed "elem_o2s";
AddIffs [elem_o2s];

Goal "(o2s xo = {}) = (xo = None)";
by (case_tac "xo" 1);
by Auto_tac;
qed "o2s_empty_eq";

Addsimps [o2s_empty_eq];

