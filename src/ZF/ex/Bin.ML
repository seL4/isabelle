(*  Title:      ZF/ex/Bin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Arithmetic on binary integers.
*)

Addsimps bin.case_eqns;

(*Perform induction on l, then prove the major premise using prems. *)
fun bin_ind_tac a prems i = 
    EVERY [res_inst_tac [("x",a)] bin.induct i,
           rename_last_tac a ["1"] (i+3),
           ares_tac prems i];


(** bin_rec -- by Vset recursion **)

Goal "bin_rec(Pls,a,b,h) = a";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac bin.con_defs);
by (simp_tac rank_ss 1);
qed "bin_rec_Pls";

Goal "bin_rec(Min,a,b,h) = b";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac bin.con_defs);
by (simp_tac rank_ss 1);
qed "bin_rec_Min";

Goal "bin_rec(Cons(w,x),a,b,h) = h(w, x, bin_rec(w,a,b,h))";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac bin.con_defs);
by (simp_tac rank_ss 1);
qed "bin_rec_Cons";

(*Type checking*)
val prems = goal Bin.thy
    "[| w: bin;    \
\       a: C(Pls);   b: C(Min);       \
\       !!w x r. [| w: bin; x: bool; r: C(w) |] ==> h(w,x,r): C(Cons(w,x))  \
\    |] ==> bin_rec(w,a,b,h) : C(w)";
by (bin_ind_tac "w" prems 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps (prems@[bin_rec_Pls, bin_rec_Min,
                                          bin_rec_Cons]))));
qed "bin_rec_type";

(** Versions for use with definitions **)

val [rew] = goal Bin.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(Pls) = a";
by (rewtac rew);
by (rtac bin_rec_Pls 1);
qed "def_bin_rec_Pls";

val [rew] = goal Bin.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(Min) = b";
by (rewtac rew);
by (rtac bin_rec_Min 1);
qed "def_bin_rec_Min";

val [rew] = goal Bin.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(Cons(w,x)) = h(w,x,j(w))";
by (rewtac rew);
by (rtac bin_rec_Cons 1);
qed "def_bin_rec_Cons";

fun bin_recs def = map standard
        ([def] RL [def_bin_rec_Pls, def_bin_rec_Min, def_bin_rec_Cons]);

Goalw [NCons_def] "NCons(Pls,0) = Pls";
by (Asm_simp_tac 1);
qed "NCons_Pls_0";

Goalw [NCons_def] "NCons(Pls,1) = Cons(Pls,1)";
by (Asm_simp_tac 1);
qed "NCons_Pls_1";

Goalw [NCons_def] "NCons(Min,0) = Cons(Min,0)";
by (Asm_simp_tac 1);
qed "NCons_Min_0";

Goalw [NCons_def] "NCons(Min,1) = Min";
by (Asm_simp_tac 1);
qed "NCons_Min_1";

Goalw [NCons_def]
    "NCons(Cons(w,x),b) = Cons(Cons(w,x),b)";
by (asm_simp_tac (simpset() addsimps bin.case_eqns) 1);
qed "NCons_Cons";

val NCons_simps = [NCons_Pls_0, NCons_Pls_1, 
                        NCons_Min_0, NCons_Min_1,
                        NCons_Cons];

(** Type checking **)

val bin_typechecks0 = bin_rec_type :: bin.intrs;

Goalw [integ_of_def] "w: bin ==> integ_of(w) : integ";
by (typechk_tac (bin_typechecks0@integ_typechecks@
                 nat_typechecks@[bool_into_nat]));
qed "integ_of_type";

Goalw [NCons_def] "[| w: bin; b: bool |] ==> NCons(w,b) : bin";
by (etac bin.elim 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps bin.case_eqns)));
by (typechk_tac (bin_typechecks0@bool_typechecks));
qed "NCons_type";

Goalw [bin_succ_def] "w: bin ==> bin_succ(w) : bin";
by (typechk_tac ([NCons_type]@bin_typechecks0@bool_typechecks));
qed "bin_succ_type";

Goalw [bin_pred_def] "w: bin ==> bin_pred(w) : bin";
by (typechk_tac ([NCons_type]@bin_typechecks0@bool_typechecks));
qed "bin_pred_type";

Goalw [bin_minus_def] "w: bin ==> bin_minus(w) : bin";
by (typechk_tac ([NCons_type,bin_pred_type]@
		 bin_typechecks0@bool_typechecks));
qed "bin_minus_type";

Goalw [bin_add_def]
    "[| v: bin; w: bin |] ==> bin_add(v,w) : bin";
by (typechk_tac ([NCons_type, bin_succ_type, bin_pred_type]@
                 bin_typechecks0@ bool_typechecks@ZF_typechecks));
qed "bin_add_type";

Goalw [bin_mult_def]
    "[| v: bin; w: bin |] ==> bin_mult(v,w) : bin";
by (typechk_tac ([NCons_type, bin_minus_type, bin_add_type]@
                 bin_typechecks0@ bool_typechecks));
qed "bin_mult_type";

val bin_typechecks = bin_typechecks0 @
    [integ_of_type, NCons_type, bin_succ_type, bin_pred_type, 
     bin_minus_type, bin_add_type, bin_mult_type];

Addsimps ([bool_1I, bool_0I,
	   bin_rec_Pls, bin_rec_Min, bin_rec_Cons] @ 
	  bin_recs integ_of_def @ bin_typechecks);

val typechecks = bin_typechecks @ integ_typechecks @ nat_typechecks @
                 [bool_subset_nat RS subsetD];

(**** The carry/borrow functions, bin_succ and bin_pred ****)

(** Lemmas **)

goal Integ.thy 
    "!!z v. [| z $+ v = z' $+ v';  \
\       z: integ; z': integ;  v: integ; v': integ;  w: integ |]   \
\    ==> z $+ (v $+ w) = z' $+ (v' $+ w)";
by (asm_simp_tac (simpset() addsimps ([zadd_assoc RS sym])) 1);
qed "zadd_assoc_cong";

goal Integ.thy 
    "!!z v w. [| z: integ;  v: integ;  w: integ |]   \
\    ==> z $+ (v $+ w) = v $+ (z $+ w)";
by (REPEAT (ares_tac [zadd_commute RS zadd_assoc_cong] 1));
qed "zadd_assoc_swap";

(*Pushes 'constants' of the form $#m to the right -- LOOPS if two!*)
bind_thm ("zadd_assoc_znat", (znat_type RS zadd_assoc_swap));


Addsimps (bin_recs bin_succ_def @ bin_recs bin_pred_def);


(*NCons preserves the integer value of its argument*)
Goal "[| w: bin; b: bool |] ==>     \
\         integ_of(NCons(w,b)) = integ_of(Cons(w,b))";
by (etac bin.elim 1);
by (asm_simp_tac (simpset() addsimps NCons_simps) 3);
by (ALLGOALS (etac boolE));
by (ALLGOALS (asm_simp_tac (simpset() addsimps (NCons_simps))));
qed "integ_of_NCons";

Addsimps [integ_of_NCons];

Goal "w: bin ==> integ_of(bin_succ(w)) = $#1 $+ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac)));
qed "integ_of_succ";

Goal "w: bin ==> integ_of(bin_pred(w)) = $~ ($#1) $+ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac)));
qed "integ_of_pred";

(*These two results replace the definitions of bin_succ and bin_pred*)


(*** bin_minus: (unary!) negation of binary integers ***)

Addsimps (bin_recs bin_minus_def @ [integ_of_succ, integ_of_pred]);

Goal "w: bin ==> integ_of(bin_minus(w)) = $~ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps (zadd_ac@[zminus_zadd_distrib]))));
qed "integ_of_minus";


(*** bin_add: binary addition ***)

Goalw [bin_add_def] "w: bin ==> bin_add(Pls,w) = w";
by (Asm_simp_tac 1);
qed "bin_add_Pls";

Goalw [bin_add_def] "w: bin ==> bin_add(Min,w) = bin_pred(w)";
by (Asm_simp_tac 1);
qed "bin_add_Min";

Goalw [bin_add_def] "bin_add(Cons(v,x),Pls) = Cons(v,x)";
by (Simp_tac 1);
qed "bin_add_Cons_Pls";

Goalw [bin_add_def] "bin_add(Cons(v,x),Min) = bin_pred(Cons(v,x))";
by (Simp_tac 1);
qed "bin_add_Cons_Min";

Goalw [bin_add_def]
    "[| w: bin;  y: bool |] ==> \
\           bin_add(Cons(v,x), Cons(w,y)) = \
\           NCons(bin_add(v, cond(x and y, bin_succ(w), w)), x xor y)";
by (Asm_simp_tac 1);
qed "bin_add_Cons_Cons";

Addsimps [bin_add_Pls, bin_add_Min, bin_add_Cons_Pls,
	  bin_add_Cons_Min, bin_add_Cons_Cons,
	  integ_of_succ, integ_of_pred];

Addsimps [bool_subset_nat RS subsetD];

Goal "v: bin ==> \
\         ALL w: bin. integ_of(bin_add(v,w)) = \
\                     integ_of(v) $+ integ_of(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (rtac ballI 1);
by (bin_ind_tac "wa" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac setloop (etac boolE))));
val integ_of_add_lemma = result();

bind_thm("integ_of_add", integ_of_add_lemma RS bspec);


(*** bin_add: binary multiplication ***)

Addsimps (bin_recs bin_mult_def @ 
	  [integ_of_minus, integ_of_add]);

val major::prems = goal Bin.thy
    "[| v: bin; w: bin |] ==>   \
\    integ_of(bin_mult(v,w)) = \
\    integ_of(v) $* integ_of(w)";
by (cut_facts_tac prems 1);
by (bin_ind_tac "v" [major] 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (etac boolE 1);
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib]) 2);
by (asm_simp_tac 
    (simpset() addsimps ([zadd_zmult_distrib, zmult_1] @ zadd_ac)) 1);
qed "integ_of_mult";

(**** Computations ****)

(** extra rules for bin_succ, bin_pred **)

val [bin_succ_Pls, bin_succ_Min, _] = bin_recs bin_succ_def;
val [bin_pred_Pls, bin_pred_Min, _] = bin_recs bin_pred_def;

Goal "bin_succ(Cons(w,1)) = Cons(bin_succ(w), 0)";
by (Simp_tac 1);
qed "bin_succ_Cons1";

Goal "bin_succ(Cons(w,0)) = NCons(w,1)";
by (Simp_tac 1);
qed "bin_succ_Cons0";

Goal "bin_pred(Cons(w,1)) = NCons(w,0)";
by (Simp_tac 1);
qed "bin_pred_Cons1";

Goal "bin_pred(Cons(w,0)) = Cons(bin_pred(w), 1)";
by (Simp_tac 1);
qed "bin_pred_Cons0";

(** extra rules for bin_minus **)

val [bin_minus_Pls, bin_minus_Min, _] = bin_recs bin_minus_def;

Goal "bin_minus(Cons(w,1)) = bin_pred(NCons(bin_minus(w), 0))";
by (Simp_tac 1);
qed "bin_minus_Cons1";

Goal "bin_minus(Cons(w,0)) = Cons(bin_minus(w), 0)";
by (Simp_tac 1);
qed "bin_minus_Cons0";

(** extra rules for bin_add **)

Goal "w: bin ==> bin_add(Cons(v,1), Cons(w,1)) = \
\                    NCons(bin_add(v, bin_succ(w)), 0)";
by (Asm_simp_tac 1);
qed "bin_add_Cons_Cons11";

Goal "w: bin ==> bin_add(Cons(v,1), Cons(w,0)) =  \
\                    NCons(bin_add(v,w), 1)";
by (Asm_simp_tac 1);
qed "bin_add_Cons_Cons10";

Goal "[| w: bin;  y: bool |] ==> \
\           bin_add(Cons(v,0), Cons(w,y)) = NCons(bin_add(v,w), y)";
by (Asm_simp_tac 1);
qed "bin_add_Cons_Cons0";

(** extra rules for bin_mult **)

val [bin_mult_Pls, bin_mult_Min, _] = bin_recs bin_mult_def;

Goal "bin_mult(Cons(v,1), w) = bin_add(NCons(bin_mult(v,w),0), w)";
by (Simp_tac 1);
qed "bin_mult_Cons1";

Goal "bin_mult(Cons(v,0), w) = NCons(bin_mult(v,w),0)";
by (Simp_tac 1);
qed "bin_mult_Cons0";


(*** The computation simpset ***)

val bin_comp_ss = simpset_of Integ.thy 
    addsimps [integ_of_add RS sym,   (*invoke bin_add*)
              integ_of_minus RS sym, (*invoke bin_minus*)
              integ_of_mult RS sym,  (*invoke bin_mult*)
              bin_succ_Pls, bin_succ_Min,
              bin_succ_Cons1, bin_succ_Cons0,
              bin_pred_Pls, bin_pred_Min,
              bin_pred_Cons1, bin_pred_Cons0,
              bin_minus_Pls, bin_minus_Min,
              bin_minus_Cons1, bin_minus_Cons0,
              bin_add_Pls, bin_add_Min, bin_add_Cons_Pls, 
              bin_add_Cons_Min, bin_add_Cons_Cons0, 
              bin_add_Cons_Cons10, bin_add_Cons_Cons11,
              bin_mult_Pls, bin_mult_Min,
              bin_mult_Cons1, bin_mult_Cons0] @
             NCons_simps
    setSolver (type_auto_tac ([bool_1I, bool_0I] @ bin_typechecks0));


(*** Examples of performing binary arithmetic by simplification ***)

set proof_timing;
(*All runtimes below are on a SPARCserver 10*)

Goal "#13  $+  #19 = #32";
by (simp_tac bin_comp_ss 1);    (*0.4 secs*)
result();

bin_add(binary_of_int 13, binary_of_int 19);

Goal "#1234  $+  #5678 = #6912";
by (simp_tac bin_comp_ss 1);    (*1.3 secs*)
result();

bin_add(binary_of_int 1234, binary_of_int 5678);

Goal "#1359  $+  #-2468 = #-1109";
by (simp_tac bin_comp_ss 1);    (*1.2 secs*)
result();

bin_add(binary_of_int 1359, binary_of_int ~2468);

Goal "#93746  $+  #-46375 = #47371";
by (simp_tac bin_comp_ss 1);    (*1.9 secs*)
result();

bin_add(binary_of_int 93746, binary_of_int ~46375);

Goal "$~ #65745 = #-65745";
by (simp_tac bin_comp_ss 1);    (*0.4 secs*)
result();

bin_minus(binary_of_int 65745);

(* negation of ~54321 *)
Goal "$~ #-54321 = #54321";
by (simp_tac bin_comp_ss 1);    (*0.5 secs*)
result();

bin_minus(binary_of_int ~54321);

Goal "#13  $*  #19 = #247";
by (simp_tac bin_comp_ss 1);    (*0.7 secs*)
result();

bin_mult(binary_of_int 13, binary_of_int 19);

Goal "#-84  $*  #51 = #-4284";
by (simp_tac bin_comp_ss 1);    (*1.3 secs*)
result();

bin_mult(binary_of_int ~84, binary_of_int 51);

(*The worst case for 8-bit operands *)
Goal "#255  $*  #255 = #65025";
by (simp_tac bin_comp_ss 1);    (*4.3 secs*)
result();

bin_mult(binary_of_int 255, binary_of_int 255);

Goal "#1359  $*  #-2468 = #-3354012";
by (simp_tac bin_comp_ss 1);    (*6.1 secs*)
result();

bin_mult(binary_of_int 1359, binary_of_int ~2468);
