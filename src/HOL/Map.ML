(*  Title:      HOL/Map.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen

Map lemmas
*)

section "empty";

Goalw [empty_def] "empty k = None";
by (Simp_tac 1);
qed "empty_def2";
Addsimps [empty_def2];


section "map_upd";

qed_goal "map_upd_triv" thy "!!X. t k = Some x ==> t(k|->x) = t"
	(K [rtac ext 1, Asm_simp_tac 1]);
(*Addsimps [map_upd_triv];*)


section "map_upds";

Goal "a ~: set as --> (!m bs. (m(a|->b)(as[|->]bs)) = (m(as[|->]bs)(a|->b)))";
by (induct_tac "as" 1);
by  (auto_tac (claset(), simpset() delsimps[fun_upd_apply]));
by (REPEAT(dtac spec 1));
by (rotate_tac ~1 1);
by (etac subst 1);
by (etac (fun_upd_twist RS subst) 1);
by (rtac refl 1);
qed_spec_mp "map_upds_twist";
Addsimps [map_upds_twist];


section "chg_map";

qed_goalw "chg_map_new" thy [chg_map_def]
	"!!s. m a = None   ==> chg_map f a m = m"          (K [Auto_tac]);
qed_goalw "chg_map_upd" thy [chg_map_def]
	"!!s. m a = Some b ==> chg_map f a m = m(a|->f b)" (K [Auto_tac]);
Addsimps[chg_map_new, chg_map_upd];


section "map_of";

Goal "map_of xs k = Some y --> (k,y):set xs";
by (induct_tac "xs" 1);
by  (Simp_tac 1);
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed_spec_mp "map_of_SomeD";

Goal "[| map_of xs k = Some z; P z |] ==> map_of [(k,z):xs . P z] k = Some z";
br mp 1;
ba  2;
by (etac thin_rl 1);
by (induct_tac "xs" 1);
by  Auto_tac;
qed "map_of_filter_in";


section "option_map related";

qed_goal "option_map_o_empty" thy 
         "option_map f o empty = empty" (K [rtac ext 1, Simp_tac 1]);

qed_goal "option_map_o_map_upd" thy 
	 "option_map f o m(a|->b) = (option_map f o m)(a|->f b)" 
	(K [rtac ext 1, Simp_tac 1]);
Addsimps[option_map_o_empty, option_map_o_map_upd];

section "++";

Goalw [override_def] "m ++ empty = m";
by (Simp_tac 1);
qed "override_empty";
Addsimps [override_empty];

Goalw [override_def] "empty ++ m = m";
by (Simp_tac 1);
by (rtac ext 1);
by (split_tac [option.split] 1);
by (Simp_tac 1);
qed "empty_override";
Addsimps [empty_override];

Goalw [override_def]
 "((m ++ n) k = Some x) = (n k = Some x | n k = None & m k = Some x)";
by (simp_tac (simpset() addsplits [option.split]) 1);
qed_spec_mp "override_Some_iff";

bind_thm ("override_SomeD", standard(override_Some_iff RS iffD1));
AddSDs[override_SomeD];

Goal "!!xx. n k = Some xx ==> (m ++ n) k = Some xx";
by (stac override_Some_iff 1);
by (Fast_tac 1);
qed "override_find_right";
Addsimps[override_find_right];

Goalw [override_def] "((m ++ n) k = None) = (n k = None & m k = None)";
by (simp_tac (simpset() addsplits [option.split]) 1);
qed "override_None";
AddIffs [override_None];

Goalw [override_def] "map_of ys ++ map_of xs = map_of (xs@ys)";
by (rtac sym 1);
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (rtac ext 1);
by (asm_simp_tac (simpset() addsplits [option.split]) 1);
qed "map_of_override";
Addsimps [map_of_override];


section "dom";

Goalw [dom_def] "dom empty = {}";
by (Simp_tac 1);
qed "dom_empty";
Addsimps [dom_empty];

Goalw [dom_def] "dom(m(a|->b)) = insert a (dom m)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "dom_map_upd";
Addsimps [dom_map_upd];

qed_goalw "finite_dom_map_of" Map.thy [dom_def] "finite (dom (map_of l))" (K[
	induct_tac "l" 1,
	 ALLGOALS Simp_tac,
	stac (insert_Collect RS sym) 1,
	Asm_full_simp_tac 1]);

Goalw [dom_def] "dom(m++n) = dom n Un dom m";
by (Simp_tac 1);
by (Blast_tac 1);
qed "dom_override";
Addsimps [dom_override];

section "ran";

Goalw [ran_def] "ran empty = {}";
by (Simp_tac 1);
qed "ran_empty";
Addsimps [ran_empty];

Goalw [ran_def] "m a = None ==> ran(m(a|->b)) = insert b (ran m)";
by Auto_tac;
by (subgoal_tac "~(aa = a)" 1);
by Auto_tac;
qed "ran_map_upd";
Addsimps [ran_map_upd];
