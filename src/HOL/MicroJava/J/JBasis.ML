(*  Title:      HOL/MicroJava/J/JBasis.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TU Muenchen
*)

val strip_tac1 = SELECT_GOAL (safe_tac (HOL_cs delrules [conjI, disjE, impCE]));

Goalw [image_def]
	"x \\<in> f``A ==> \\<exists>y. y \\<in> A \\<and>  x = f y";
by(Auto_tac);
qed "image_rev";

fun case_tac1 s i = EVERY [case_tac s i, rotate_tac ~1 i, rotate_tac ~1 (i+1)];

val select_split = prove_goalw Prod.thy [split_def] 
	"(SOME (x,y). P x y) = (SOME xy. P (fst xy) (snd xy))" (K [rtac refl 1]);
	 

val split_beta = prove_goal Prod.thy "(\\<lambda>(x,y). P x y) z = P (fst z) (snd z)"
	(fn _ => [stac surjective_pairing 1, stac split 1, rtac refl 1]);
val split_beta2 = prove_goal Prod.thy "(\\<lambda>(x,y). P x y) (w,z) = P w z"
	(fn _ => [Auto_tac]);
val splitE2 = prove_goal Prod.thy "[|Q (split P z); !!x y. [|z = (x, y); Q (P x y)|] ==> R|] ==> R" (fn prems => [
	REPEAT (resolve_tac (prems@[surjective_pairing]) 1),
	rtac (split_beta RS subst) 1,
	rtac (hd prems) 1]);
val splitE2' = prove_goal Prod.thy "[|((\\<lambda>(x,y). P x y) z) w; !!x y. [|z = (x, y); (P x y) w|] ==> R|] ==> R" (fn prems => [
	REPEAT (resolve_tac (prems@[surjective_pairing]) 1),
	res_inst_tac [("P1","P")] (split_beta RS subst) 1,
	rtac (hd prems) 1]);
	

fun pair_tac s = res_inst_tac [("p",s)] PairE THEN' hyp_subst_tac;

val BallE = prove_goal thy "[|Ball A P; x \\<notin> A ==> Q; P x ==> Q |] ==> Q"
	(fn prems => [rtac ballE 1, resolve_tac prems 1, 
			eresolve_tac prems 1, eresolve_tac prems 1]);

val set_cs2 = set_cs delrules [ballE] addSEs [BallE];

Addsimps [Let_def];

(* To HOL.ML *)

val ex1_some_eq_trivial = prove_goal HOL.thy "[| \\<exists>!x. P x; P y |] ==> Eps P = y" 
	(fn prems => [
	cut_facts_tac prems 1,
	rtac some_equality 1,
	 atac 1,
	etac ex1E 1,
	etac all_dupE 1,
	fast_tac HOL_cs 1]);


val ball_insert = prove_goalw equalities.thy [Ball_def]
	"Ball (insert x A) P = (P x \\<and> Ball A P)" (fn _ => [
	fast_tac set_cs 1]);

fun option_case_tac i = EVERY [
	etac option_caseE i,
	 rotate_tac ~2 (i+1), asm_full_simp_tac HOL_basic_ss (i+1), 
	 rotate_tac ~2  i   , asm_full_simp_tac HOL_basic_ss i];

val not_None_tac = EVERY' [dtac (not_None_eq RS iffD1),rotate_tac ~1,etac exE,
		rotate_tac ~1,asm_full_simp_tac 
	(simpset() delsimps [split_paired_All,split_paired_Ex])];

Goal "{y. x = Some y} \\<subseteq> {the x}";
by Auto_tac;
qed "some_subset_the";

fun ex_ftac thm = EVERY' [forward_tac [thm], REPEAT o (etac exE), rotate_tac ~1,
  asm_full_simp_tac (simpset() delsimps [split_paired_All,split_paired_Ex])];

val optionE = prove_goal thy 
       "[| opt = None ==> P;  !!x. opt = Some x ==> P |] ==> P" 
   (fn prems => [
	case_tac "opt = None" 1,
	 eresolve_tac prems 1,
	not_None_tac 1,
	eresolve_tac prems 1]);

fun option_case_tac2 s i = EVERY [
	 case_tac s i,
	 rotate_tac ~1 (i+1), asm_full_simp_tac HOL_basic_ss (i+1), 
	 rotate_tac ~1  i   , asm_full_simp_tac HOL_basic_ss i];

val option_map_SomeD = prove_goalw thy [option_map_def]
	"!!x. option_map f x = Some y ==> \\<exists>z. x = Some z \\<and> f z = y" (K [
	option_case_tac2 "x" 1,
	 Auto_tac]);


section "unique";

Goal "(x, y) : set l --> x : fst `` set l";
by (induct_tac "l" 1);
by  Auto_tac;
qed_spec_mp "fst_in_set_lemma";

Goalw [unique_def] "unique []";
by (Simp_tac 1);
qed "unique_Nil";

Goalw [unique_def] "unique ((x,y)#l) = (unique l \\<and> (!y. (x,y) ~: set l))";
by  (auto_tac (claset() addDs [fst_in_set_lemma],simpset()));
qed "unique_Cons";

Addsimps [unique_Nil,unique_Cons];

Goal "unique l' ==> unique l --> \
\ (!(x,y):set l. !(x',y'):set l'. x' ~= x) --> unique (l @ l')";
by (induct_tac "l" 1);
by  (auto_tac (claset() addDs [fst_in_set_lemma],simpset()));
qed_spec_mp "unique_append";

Goal "unique l --> inj f --> unique (map (%(k,x). (f k, g k x)) l)";
by (induct_tac "l" 1);
by  (auto_tac (claset() addDs [fst_in_set_lemma],simpset()addsimps[inj_eq]));
qed_spec_mp "unique_map_inj";

Goal "!!l. unique l ==> unique (map (split (\\<lambda>k. Pair (k, C))) l)";
by(etac unique_map_inj 1);
by(rtac injI 1);
by Auto_tac;
qed "unique_map_Pair";

Goal "[|M = N; !!x. x\\<in>N ==> f x = g x|] ==> f``M = g``N";
by(rtac set_ext 1);
by(simp_tac (simpset() addsimps image_def::premises()) 1);
qed "image_cong";

val split_Pair_eq = prove_goal Prod.thy 
"!!X. ((x, y), z) \\<in> split (\\<lambda>x. Pair (x, Y)) `` A ==> y = Y" (K [
	etac imageE 1,
	split_all_tac 1,
	auto_tac(claset_of Prod.thy,simpset_of Prod.thy)]);


(* More about Maps *)

val override_SomeD = prove_goalw thy [override_def] "(s ++ t) k = Some x ==> \
\ t k = Some x |  t k = None \\<and>  s k = Some x" (fn prems => [
	cut_facts_tac prems 1,
	case_tac "\\<exists>x. t k = Some x" 1,
	 etac exE 1,
	 rotate_tac ~1 1,
	 Asm_full_simp_tac 1,
	asm_full_simp_tac (HOL_ss addsimps [not_None_eq RS sym]) 1,
	 rotate_tac ~1 1,
	 Asm_full_simp_tac 1]);

Addsimps [fun_upd_same, fun_upd_other];

Goal "unique xys --> (map_of xys x = Some y) = ((x,y) \\<in> set xys)";
by(induct_tac "xys" 1);
 by(Simp_tac 1);
by(force_tac (claset(), simpset() addsimps [unique_Cons]) 1);
qed_spec_mp "unique_map_of_Some_conv";

val in_set_get = unique_map_of_Some_conv RS iffD2;
val get_in_set = unique_map_of_Some_conv RS iffD1;

Goal "(\\<forall>(x,y)\\<in>set l. P x y) --> (\\<forall>x. \\<forall>y. map_of l x = Some y --> P x y)";
by(induct_tac "l" 1);
by(ALLGOALS Simp_tac);
by Safe_tac;
by Auto_tac;
bind_thm("Ball_set_table",result() RS mp);

val table_mono = prove_goal thy 
"unique l' --> (\\<forall>xy. (xy)\\<in>set l --> (xy)\\<in>set l') -->\
\ (\\<forall>k y. map_of l k = Some y --> map_of l' k = Some y)" (fn _ => [
	induct_tac "l" 1,
	 Auto_tac,
 	 fast_tac (HOL_cs addSIs [in_set_get]) 1])
 RS mp RS mp RS spec RS spec RS mp;

val table_map_Some' = prove_goal thy "map_of t k = Some (k', x) --> \
\ map_of (map (\\<lambda>u. ((fst u, fst (snd u)), snd (snd u))) t) (k, k') = Some x" (K [
	induct_tac "t" 1,	
	 ALLGOALS Simp_tac,
	case_tac1 "k = fst a" 1,
	 Auto_tac]) RS mp;
val table_map_Some = prove_goal thy 
"map_of (map (\\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) --> \
\map_of t (k, k') = Some x" (K [
	induct_tac "t" 1,	
	Auto_tac]) RS mp;


val table_mapf_Some = prove_goal thy "!!f. \\<forall>x y. f x = f y --> x = y ==> \
\ map_of (map (\\<lambda>(k,x). (k,f x)) t) k = Some (f x) --> map_of t k = Some x" (K [
	induct_tac "t" 1,	
	Auto_tac]) RS mp;
val table_mapf_SomeD = prove_goal thy 
"map_of (map (\\<lambda>(k,x). (k, f x)) t) k = Some z --> (\\<exists>y. (k,y)\\<in>set t \\<and>  z = f y)"(K [
	induct_tac "t" 1,	
	Auto_tac]) RS mp;

val table_mapf_Some2 = prove_goal thy 
"!!k. map_of (map (\\<lambda>(k,x). (k,C,x)) t) k = Some (D,x) ==> C = D \\<and> map_of t k = Some x" (K [
	forward_tac [table_mapf_SomeD] 1,
	Auto_tac,
	rtac table_mapf_Some 1,
	 atac 2,
	Fast_tac 1]);

val finite_map_of = rewrite_rule [dom_def] finite_dom_map_of;

Goal
"map_of (map (\\<lambda>(a,b). (a,f b)) xs) x = option_map f (map_of xs x)";
by (induct_tac "xs" 1);
auto();
qed "map_of_map";


