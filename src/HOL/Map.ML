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

Goal "sum_case empty empty = empty";
by (rtac ext 1);
by (simp_tac (simpset() addsplits [sum.split]) 1);
qed "sum_case_empty_empty";
Addsimps [sum_case_empty_empty];


section "map_upd";

Goal "t k = Some x ==> t(k|->x) = t";
by (rtac ext 1);
by (Asm_simp_tac 1);
qed "map_upd_triv";

Goal "t(k|->x) ~= empty";
by Safe_tac;
by (dres_inst_tac [("x","k")] fun_cong 1);
by (Full_simp_tac 1);
qed "map_upd_nonempty";
Addsimps[map_upd_nonempty];

Goalw [image_def] "finite (range f) ==> finite (range (f(a|->b)))";
by (full_simp_tac (simpset() addsimps [full_SetCompr_eq]) 1);
by (rtac finite_subset 1);
by (assume_tac 2);
by Auto_tac;
qed "finite_range_updI";


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

Goalw [chg_map_def] "m a = None   ==> chg_map f a m = m";
by Auto_tac;
qed "chg_map_new";

Goalw [chg_map_def] "m a = Some b ==> chg_map f a m = m(a|->f b)";
by Auto_tac;
qed "chg_map_upd";

Addsimps[chg_map_new, chg_map_upd];


section "map_of";

Goal "map_of xs k = Some y --> (k,y):set xs";
by (induct_tac "xs" 1);
by  Auto_tac;
qed_spec_mp "map_of_SomeD";

Goal "inj f ==> map_of t k = Some x --> \
\  map_of (map (split (%k. Pair (f k))) t) (f k) = Some x";
by (induct_tac "t" 1);
by  (auto_tac (claset(),simpset()addsimps[inj_eq]));
qed_spec_mp "map_of_mapk_SomeI";

Goal "(k, x) : set l --> (? x. map_of l k = Some x)";
by (induct_tac "l" 1);
by  Auto_tac;
qed_spec_mp "weak_map_of_SomeI";

Goal "[| map_of xs k = Some z; P z |] ==> map_of [(k,z):xs . P z] k = Some z";
by (rtac mp 1);
by (assume_tac 2);
by (etac thin_rl 1);
by (induct_tac "xs" 1);
by  Auto_tac;
qed "map_of_filter_in";

Goal "finite (range (map_of l))";
by (induct_tac "l" 1);
by  (ALLGOALS (simp_tac (simpset() addsimps [image_constant])));
by (rtac finite_subset 1);
by (assume_tac 2);
by Auto_tac;
qed "finite_range_map_of";


section "option_map related";

Goal "option_map f o empty = empty";
by (rtac ext 1);
by (Simp_tac 1);
qed "option_map_o_empty";

Goal "option_map f o m(a|->b) = (option_map f o m)(a|->f b)";
by (rtac ext 1);
by (Simp_tac 1);
qed "option_map_o_map_upd";

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

Goalw [override_def] "f ++ g(x|->y) = (f ++ g)(x|->y)";
by (rtac ext 1);
by Auto_tac;
qed "override_upd";
Addsimps[override_upd];

Goalw [override_def] "map_of ys ++ map_of xs = map_of (xs@ys)";
by (rtac sym 1);
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (rtac ext 1);
by (asm_simp_tac (simpset() addsplits [option.split]) 1);
qed "map_of_override";
Addsimps [map_of_override];

Delsimps[fun_upd_apply];
Goal "finite (range f) ==> finite (range (f ++ map_of l))";
by (induct_tac "l" 1);
by  Auto_tac;
by  (fold_goals_tac [empty_def]);
by  (Asm_simp_tac 1);
by (etac finite_range_updI 1);
qed "finite_range_map_of_override";
Addsimps [fun_upd_apply];


section "dom";

Goalw [dom_def] "m a = Some b ==> a : dom m";
by Auto_tac;
qed "domI";

Goalw [dom_def] "a : dom m ==> ? b. m a = Some b";
by Auto_tac;
qed "domD";
AddSDs [domD];

Goalw [dom_def] "dom empty = {}";
by (Simp_tac 1);
qed "dom_empty";
Addsimps [dom_empty];

Goalw [dom_def] "dom(m(a|->b)) = insert a (dom m)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "dom_map_upd";
Addsimps [dom_map_upd];

Goalw [dom_def] "finite (dom (map_of l))";
by (induct_tac "l" 1);
by (auto_tac (claset(), 
	      simpset() addsimps [insert_Collect RS sym]));
qed "finite_dom_map_of";

Goalw [dom_def] "dom(m++n) = dom n Un dom m";
by Auto_tac;
qed "dom_override";
Addsimps [dom_override];

section "ran";

Goalw [ran_def] "ran empty = {}";
by (Simp_tac 1);
qed "ran_empty";
Addsimps [ran_empty];

Goalw [ran_def] "ran (%u. None) = {}";
by Auto_tac;
qed "ran_empty'";
Addsimps[ran_empty'];

Goalw [ran_def] "m a = None ==> ran(m(a|->b)) = insert b (ran m)";
by Auto_tac;
by (subgoal_tac "~(aa = a)" 1);
by Auto_tac;
qed "ran_map_upd";
Addsimps [ran_map_upd];
