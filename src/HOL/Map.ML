(*  Title:      HOL/Map.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen

Map lemmas
*)

goalw thy [empty_def] "empty k = None";
by (Simp_tac 1);
qed "empty_def2";
Addsimps [empty_def2];

goalw thy [update_def] "(m[a|->b])x = (if x=a then Some b else m x)";
by (Simp_tac 1);
qed "update_def2";
Addsimps [update_def2];

qed_goal "update_same" thy "(t[k|->x]) k = Some x" 
	(K [Simp_tac 1]);
qed_goal "update_other" thy "!!X. l~=k ==> (t[k|->x]) l = t l"
	(K [Asm_simp_tac 1]);
qed_goal "update_triv" thy "!!X. t k = Some x ==> t[k|->x] = t"
	(K [rtac ext 1, Asm_simp_tac 1]);
(*Addsimps [update_same, update_other, update_triv];*)

section "option_map";

qed_goal "option_map_o_empty" thy 
         "option_map f o empty = empty" (K [rtac ext 1, Simp_tac 1]);

qed_goal "option_map_o_update" thy 
	 "option_map f o m[a|->b] = (option_map f o m)[a|->f b]" 
	(K [rtac ext 1, Simp_tac 1]);
Addsimps[option_map_o_empty, option_map_o_update];

section "++";

goalw thy [override_def] "m ++ empty = m";
by (Simp_tac 1);
qed "override_empty";
Addsimps [override_empty];

goalw thy [override_def] "empty ++ m = m";
by (Simp_tac 1);
by (rtac ext 1);
by (split_tac [split_option_case] 1);
by (Simp_tac 1);
qed "empty_override";
Addsimps [empty_override];

goalw thy [override_def]
 "((m ++ n) k = Some x) = (n k = Some x | n k = None & m k = Some x)";
by (simp_tac (simpset() addsplits [split_option_case]) 1);
qed_spec_mp "override_Some_iff";

bind_thm ("override_SomeD", standard(override_Some_iff RS iffD1));

goalw thy [override_def]
 "((m ++ n) k = None) = (n k = None & m k = None)";
by (simp_tac (simpset() addsplits [split_option_case]) 1);
qed "override_None";
AddIffs [override_None];

goalw thy [override_def] "map_of(xs@ys) = map_of ys ++ map_of xs";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (rtac ext 1);
by (asm_simp_tac (simpset() addsplits [split_option_case]) 1);
qed "map_of_append";
Addsimps [map_of_append];

goal thy "map_of xs k = Some y --> (k,y):set xs";
by (list.induct_tac "xs" 1);
by  (Simp_tac 1);
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "map_of_SomeD";

section "dom";

goalw thy [dom_def] "dom empty = {}";
by (Simp_tac 1);
qed "dom_empty";
Addsimps [dom_empty];

goalw thy [dom_def] "dom(m[a|->b]) = insert a (dom m)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "dom_update";
Addsimps [dom_update];

qed_goalw "finite_dom_map_of" Map.thy [dom_def] "finite (dom (map_of l))" (K[
	list.induct_tac "l" 1,
	 ALLGOALS Simp_tac,
	stac (insert_Collect RS sym) 1,
	Asm_simp_tac 1]);

goalw thy [dom_def] "dom(m++n) = dom n Un dom m";
by (Blast_tac 1);
qed "dom_override";
Addsimps [dom_override];

section "ran";

goalw thy [ran_def] "ran empty = {}";
by (Simp_tac 1);
qed "ran_empty";
Addsimps [ran_empty];

goalw thy [ran_def] "!!X. m a = None ==> ran(m[a|->b]) = insert b (ran m)";
by Auto_tac;
by (subgoal_tac "~(aa = a)" 1);
by Auto_tac;
qed "ran_update";
Addsimps [ran_update];
