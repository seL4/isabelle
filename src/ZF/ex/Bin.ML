(*  Title:      ZF/ex/Bin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

For Bin.thy.  Arithmetic on binary integers.
*)

open Bin;

Addsimps bin.case_eqns;

(*Perform induction on l, then prove the major premise using prems. *)
fun bin_ind_tac a prems i = 
    EVERY [res_inst_tac [("x",a)] bin.induct i,
           rename_last_tac a ["1"] (i+3),
           ares_tac prems i];


(** bin_rec -- by Vset recursion **)

goal Bin.thy "bin_rec(Plus,a,b,h) = a";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac bin.con_defs);
by (simp_tac rank_ss 1);
qed "bin_rec_Plus";

goal Bin.thy "bin_rec(Minus,a,b,h) = b";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac bin.con_defs);
by (simp_tac rank_ss 1);
qed "bin_rec_Minus";

goal Bin.thy "bin_rec(Bcons(w,x),a,b,h) = h(w, x, bin_rec(w,a,b,h))";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac bin.con_defs);
by (simp_tac rank_ss 1);
qed "bin_rec_Bcons";

(*Type checking*)
val prems = goal Bin.thy
    "[| w: bin;    \
\       a: C(Plus);   b: C(Minus);       \
\       !!w x r. [| w: bin; x: bool; r: C(w) |] ==> h(w,x,r): C(Bcons(w,x))  \
\    |] ==> bin_rec(w,a,b,h) : C(w)";
by (bin_ind_tac "w" prems 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps (prems@[bin_rec_Plus, bin_rec_Minus,
                                          bin_rec_Bcons]))));
qed "bin_rec_type";

(** Versions for use with definitions **)

val [rew] = goal Bin.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(Plus) = a";
by (rewtac rew);
by (rtac bin_rec_Plus 1);
qed "def_bin_rec_Plus";

val [rew] = goal Bin.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(Minus) = b";
by (rewtac rew);
by (rtac bin_rec_Minus 1);
qed "def_bin_rec_Minus";

val [rew] = goal Bin.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(Bcons(w,x)) = h(w,x,j(w))";
by (rewtac rew);
by (rtac bin_rec_Bcons 1);
qed "def_bin_rec_Bcons";

fun bin_recs def = map standard
        ([def] RL [def_bin_rec_Plus, def_bin_rec_Minus, def_bin_rec_Bcons]);

goalw Bin.thy [norm_Bcons_def] "norm_Bcons(Plus,0) = Plus";
by (Asm_simp_tac 1);
qed "norm_Bcons_Plus_0";

goalw Bin.thy [norm_Bcons_def] "norm_Bcons(Plus,1) = Bcons(Plus,1)";
by (Asm_simp_tac 1);
qed "norm_Bcons_Plus_1";

goalw Bin.thy [norm_Bcons_def] "norm_Bcons(Minus,0) = Bcons(Minus,0)";
by (Asm_simp_tac 1);
qed "norm_Bcons_Minus_0";

goalw Bin.thy [norm_Bcons_def] "norm_Bcons(Minus,1) = Minus";
by (Asm_simp_tac 1);
qed "norm_Bcons_Minus_1";

goalw Bin.thy [norm_Bcons_def]
    "norm_Bcons(Bcons(w,x),b) = Bcons(Bcons(w,x),b)";
by (asm_simp_tac (simpset() addsimps bin.case_eqns) 1);
qed "norm_Bcons_Bcons";

val norm_Bcons_simps = [norm_Bcons_Plus_0, norm_Bcons_Plus_1, 
                        norm_Bcons_Minus_0, norm_Bcons_Minus_1,
                        norm_Bcons_Bcons];

(** Type checking **)

val bin_typechecks0 = bin_rec_type :: bin.intrs;

goalw Bin.thy [integ_of_bin_def]
    "!!w. w: bin ==> integ_of_bin(w) : integ";
by (typechk_tac (bin_typechecks0@integ_typechecks@
                 nat_typechecks@[bool_into_nat]));
qed "integ_of_bin_type";

goalw Bin.thy [norm_Bcons_def]
    "!!w. [| w: bin; b: bool |] ==> norm_Bcons(w,b) : bin";
by (etac bin.elim 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps bin.case_eqns)));
by (typechk_tac (bin_typechecks0@bool_typechecks));
qed "norm_Bcons_type";

goalw Bin.thy [bin_succ_def]
    "!!w. w: bin ==> bin_succ(w) : bin";
by (typechk_tac ([norm_Bcons_type]@bin_typechecks0@bool_typechecks));
qed "bin_succ_type";

goalw Bin.thy [bin_pred_def]
    "!!w. w: bin ==> bin_pred(w) : bin";
by (typechk_tac ([norm_Bcons_type]@bin_typechecks0@bool_typechecks));
qed "bin_pred_type";

goalw Bin.thy [bin_minus_def]
    "!!w. w: bin ==> bin_minus(w) : bin";
by (typechk_tac ([bin_pred_type]@bin_typechecks0@bool_typechecks));
qed "bin_minus_type";

goalw Bin.thy [bin_add_def]
    "!!v w. [| v: bin; w: bin |] ==> bin_add(v,w) : bin";
by (typechk_tac ([norm_Bcons_type, bin_succ_type, bin_pred_type]@
                 bin_typechecks0@ bool_typechecks@ZF_typechecks));
qed "bin_add_type";

goalw Bin.thy [bin_mult_def]
    "!!v w. [| v: bin; w: bin |] ==> bin_mult(v,w) : bin";
by (typechk_tac ([norm_Bcons_type, bin_minus_type, bin_add_type]@
                 bin_typechecks0@ bool_typechecks));
qed "bin_mult_type";

val bin_typechecks = bin_typechecks0 @
    [integ_of_bin_type, norm_Bcons_type, bin_succ_type, bin_pred_type, 
     bin_minus_type, bin_add_type, bin_mult_type];

Addsimps ([bool_1I, bool_0I,
	   bin_rec_Plus, bin_rec_Minus, bin_rec_Bcons] @ 
	  bin_recs integ_of_bin_def @ bin_typechecks);

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


(*norm_Bcons preserves the integer value of its argument*)
goal Bin.thy
    "!!w. [| w: bin; b: bool |] ==>     \
\         integ_of_bin(norm_Bcons(w,b)) = integ_of_bin(Bcons(w,b))";
by (etac bin.elim 1);
by (asm_simp_tac (simpset() addsimps norm_Bcons_simps) 3);
by (ALLGOALS (etac boolE));
by (ALLGOALS (asm_simp_tac (simpset() addsimps (norm_Bcons_simps))));
qed "integ_of_bin_norm_Bcons";

goal Bin.thy
    "!!w. w: bin ==> integ_of_bin(bin_succ(w)) = $#1 $+ integ_of_bin(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps integ_of_bin_norm_Bcons::zadd_ac)));
qed "integ_of_bin_succ";

goal Bin.thy
    "!!w. w: bin ==> integ_of_bin(bin_pred(w)) = $~ ($#1) $+ integ_of_bin(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps integ_of_bin_norm_Bcons::zadd_ac)));
qed "integ_of_bin_pred";

(*These two results replace the definitions of bin_succ and bin_pred*)


(*** bin_minus: (unary!) negation of binary integers ***)

Addsimps (bin_recs bin_minus_def @
	  [integ_of_bin_succ, integ_of_bin_pred]);

goal Bin.thy
    "!!w. w: bin ==> integ_of_bin(bin_minus(w)) = $~ integ_of_bin(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (etac boolE 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps (zadd_ac@[zminus_zadd_distrib]))));
qed "integ_of_bin_minus";


(*** bin_add: binary addition ***)

goalw Bin.thy [bin_add_def] "!!w. w: bin ==> bin_add(Plus,w) = w";
by (Asm_simp_tac 1);
qed "bin_add_Plus";

goalw Bin.thy [bin_add_def] "!!w. w: bin ==> bin_add(Minus,w) = bin_pred(w)";
by (Asm_simp_tac 1);
qed "bin_add_Minus";

goalw Bin.thy [bin_add_def] "bin_add(Bcons(v,x),Plus) = Bcons(v,x)";
by (Simp_tac 1);
qed "bin_add_Bcons_Plus";

goalw Bin.thy [bin_add_def] "bin_add(Bcons(v,x),Minus) = bin_pred(Bcons(v,x))";
by (Simp_tac 1);
qed "bin_add_Bcons_Minus";

goalw Bin.thy [bin_add_def]
    "!!w y. [| w: bin;  y: bool |] ==> \
\           bin_add(Bcons(v,x), Bcons(w,y)) = \
\           norm_Bcons(bin_add(v, cond(x and y, bin_succ(w), w)), x xor y)";
by (Asm_simp_tac 1);
qed "bin_add_Bcons_Bcons";

Addsimps [bin_add_Plus, bin_add_Minus, bin_add_Bcons_Plus,
	  bin_add_Bcons_Minus, bin_add_Bcons_Bcons,
	  integ_of_bin_succ, integ_of_bin_pred,
	  integ_of_bin_norm_Bcons];

Addsimps [bool_subset_nat RS subsetD];

goal Bin.thy
    "!!v. v: bin ==> \
\         ALL w: bin. integ_of_bin(bin_add(v,w)) = \
\                     integ_of_bin(v) $+ integ_of_bin(w)";
by (etac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (rtac ballI 1);
by (bin_ind_tac "wa" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac setloop (etac boolE))));
val integ_of_bin_add_lemma = result();

bind_thm("integ_of_bin_add", integ_of_bin_add_lemma RS bspec);


(*** bin_add: binary multiplication ***)

Addsimps (bin_recs bin_mult_def @ 
	  [integ_of_bin_minus, integ_of_bin_add,
	   integ_of_bin_norm_Bcons]);

val major::prems = goal Bin.thy
    "[| v: bin; w: bin |] ==>   \
\    integ_of_bin(bin_mult(v,w)) = \
\    integ_of_bin(v) $* integ_of_bin(w)";
by (cut_facts_tac prems 1);
by (bin_ind_tac "v" [major] 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (etac boolE 1);
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib]) 2);
by (asm_simp_tac 
    (simpset() addsimps ([zadd_zmult_distrib, zmult_1] @ zadd_ac)) 1);
qed "integ_of_bin_mult";

(**** Computations ****)

(** extra rules for bin_succ, bin_pred **)

val [bin_succ_Plus, bin_succ_Minus, _] = bin_recs bin_succ_def;
val [bin_pred_Plus, bin_pred_Minus, _] = bin_recs bin_pred_def;

goal Bin.thy "bin_succ(Bcons(w,1)) = Bcons(bin_succ(w), 0)";
by (Simp_tac 1);
qed "bin_succ_Bcons1";

goal Bin.thy "bin_succ(Bcons(w,0)) = norm_Bcons(w,1)";
by (Simp_tac 1);
qed "bin_succ_Bcons0";

goal Bin.thy "bin_pred(Bcons(w,1)) = norm_Bcons(w,0)";
by (Simp_tac 1);
qed "bin_pred_Bcons1";

goal Bin.thy "bin_pred(Bcons(w,0)) = Bcons(bin_pred(w), 1)";
by (Simp_tac 1);
qed "bin_pred_Bcons0";

(** extra rules for bin_minus **)

val [bin_minus_Plus, bin_minus_Minus, _] = bin_recs bin_minus_def;

goal Bin.thy "bin_minus(Bcons(w,1)) = bin_pred(Bcons(bin_minus(w), 0))";
by (Simp_tac 1);
qed "bin_minus_Bcons1";

goal Bin.thy "bin_minus(Bcons(w,0)) = Bcons(bin_minus(w), 0)";
by (Simp_tac 1);
qed "bin_minus_Bcons0";

(** extra rules for bin_add **)

goal Bin.thy 
    "!!w. w: bin ==> bin_add(Bcons(v,1), Bcons(w,1)) = \
\                    norm_Bcons(bin_add(v, bin_succ(w)), 0)";
by (Asm_simp_tac 1);
qed "bin_add_Bcons_Bcons11";

goal Bin.thy 
    "!!w. w: bin ==> bin_add(Bcons(v,1), Bcons(w,0)) =  \
\                    norm_Bcons(bin_add(v,w), 1)";
by (Asm_simp_tac 1);
qed "bin_add_Bcons_Bcons10";

goal Bin.thy 
    "!!w y. [| w: bin;  y: bool |] ==> \
\           bin_add(Bcons(v,0), Bcons(w,y)) = norm_Bcons(bin_add(v,w), y)";
by (Asm_simp_tac 1);
qed "bin_add_Bcons_Bcons0";

(** extra rules for bin_mult **)

val [bin_mult_Plus, bin_mult_Minus, _] = bin_recs bin_mult_def;

goal Bin.thy
    "bin_mult(Bcons(v,1), w) = bin_add(norm_Bcons(bin_mult(v,w),0), w)";
by (Simp_tac 1);
qed "bin_mult_Bcons1";

goal Bin.thy "bin_mult(Bcons(v,0), w) = norm_Bcons(bin_mult(v,w),0)";
by (Simp_tac 1);
qed "bin_mult_Bcons0";


(*** The computation simpset ***)

val bin_comp_ss = simpset_of Integ.thy 
    addsimps [integ_of_bin_add RS sym,   (*invoke bin_add*)
              integ_of_bin_minus RS sym, (*invoke bin_minus*)
              integ_of_bin_mult RS sym,  (*invoke bin_mult*)
              bin_succ_Plus, bin_succ_Minus,
              bin_succ_Bcons1, bin_succ_Bcons0,
              bin_pred_Plus, bin_pred_Minus,
              bin_pred_Bcons1, bin_pred_Bcons0,
              bin_minus_Plus, bin_minus_Minus,
              bin_minus_Bcons1, bin_minus_Bcons0,
              bin_add_Plus, bin_add_Minus, bin_add_Bcons_Plus, 
              bin_add_Bcons_Minus, bin_add_Bcons_Bcons0, 
              bin_add_Bcons_Bcons10, bin_add_Bcons_Bcons11,
              bin_mult_Plus, bin_mult_Minus,
              bin_mult_Bcons1, bin_mult_Bcons0] @
             norm_Bcons_simps
    setSolver (type_auto_tac ([bool_1I, bool_0I] @ bin_typechecks0));


(*** Examples of performing binary arithmetic by simplification ***)

set proof_timing;
(*All runtimes below are on a SPARCserver 10*)

goal Bin.thy "#13  $+  #19 = #32";
by (simp_tac bin_comp_ss 1);    (*0.4 secs*)
result();

bin_add(binary_of_int 13, binary_of_int 19);

goal Bin.thy "#1234  $+  #5678 = #6912";
by (simp_tac bin_comp_ss 1);    (*1.3 secs*)
result();

bin_add(binary_of_int 1234, binary_of_int 5678);

goal Bin.thy "#1359  $+  #~2468 = #~1109";
by (simp_tac bin_comp_ss 1);    (*1.2 secs*)
result();

bin_add(binary_of_int 1359, binary_of_int ~2468);

goal Bin.thy "#93746  $+  #~46375 = #47371";
by (simp_tac bin_comp_ss 1);    (*1.9 secs*)
result();

bin_add(binary_of_int 93746, binary_of_int ~46375);

goal Bin.thy "$~ #65745 = #~65745";
by (simp_tac bin_comp_ss 1);    (*0.4 secs*)
result();

bin_minus(binary_of_int 65745);

(* negation of ~54321 *)
goal Bin.thy "$~ #~54321 = #54321";
by (simp_tac bin_comp_ss 1);    (*0.5 secs*)
result();

bin_minus(binary_of_int ~54321);

goal Bin.thy "#13  $*  #19 = #247";
by (simp_tac bin_comp_ss 1);    (*0.7 secs*)
result();

bin_mult(binary_of_int 13, binary_of_int 19);

goal Bin.thy "#~84  $*  #51 = #~4284";
by (simp_tac bin_comp_ss 1);    (*1.3 secs*)
result();

bin_mult(binary_of_int ~84, binary_of_int 51);

(*The worst case for 8-bit operands *)
goal Bin.thy "#255  $*  #255 = #65025";
by (simp_tac bin_comp_ss 1);    (*4.3 secs*)
result();

bin_mult(binary_of_int 255, binary_of_int 255);

goal Bin.thy "#1359  $*  #~2468 = #~3354012";
by (simp_tac bin_comp_ss 1);    (*6.1 secs*)
result();

bin_mult(binary_of_int 1359, binary_of_int ~2468);
