(*  Title: 	ZF/ex/bin.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For bin.thy.  Arithmetic on binary integers.
*)

open BinFn;


(** bin_rec -- by Vset recursion **)

goal BinFn.thy "bin_rec(Plus,a,b,h) = a";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac Bin.con_defs);
by (simp_tac rank_ss 1);
val bin_rec_Plus = result();

goal BinFn.thy "bin_rec(Minus,a,b,h) = b";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac Bin.con_defs);
by (simp_tac rank_ss 1);
val bin_rec_Minus = result();

goal BinFn.thy "bin_rec(w$$x,a,b,h) = h(w, x, bin_rec(w,a,b,h))";
by (rtac (bin_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac Bin.con_defs);
by (simp_tac rank_ss 1);
val bin_rec_Bcons = result();

(*Type checking*)
val prems = goal BinFn.thy
    "[| w: bin;    \
\       a: C(Plus);   b: C(Minus);       \
\       !!w x r. [| w: bin;  x: bool;  r: C(w) |] ==> h(w,x,r): C(w$$x)  \
\    |] ==> bin_rec(w,a,b,h) : C(w)";
by (bin_ind_tac "w" prems 1);
by (ALLGOALS 
    (asm_simp_tac (ZF_ss addsimps (prems@[bin_rec_Plus,bin_rec_Minus,
					 bin_rec_Bcons]))));
val bin_rec_type = result();

(** Versions for use with definitions **)

val [rew] = goal BinFn.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(Plus) = a";
by (rewtac rew);
by (rtac bin_rec_Plus 1);
val def_bin_rec_Plus = result();

val [rew] = goal BinFn.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(Minus) = b";
by (rewtac rew);
by (rtac bin_rec_Minus 1);
val def_bin_rec_Minus = result();

val [rew] = goal BinFn.thy
    "[| !!w. j(w)==bin_rec(w,a,b,h) |] ==> j(w$$x) = h(w,x,j(w))";
by (rewtac rew);
by (rtac bin_rec_Bcons 1);
val def_bin_rec_Bcons = result();

fun bin_recs def = map standard
	([def] RL [def_bin_rec_Plus, def_bin_rec_Minus, def_bin_rec_Bcons]);

(** Type checking **)

val bin_typechecks0 = bin_rec_type :: Bin.intrs;

goalw BinFn.thy [integ_of_bin_def]
    "!!w. w: bin ==> integ_of_bin(w) : integ";
by (typechk_tac (bin_typechecks0@integ_typechecks@
		 nat_typechecks@[bool_into_nat]));
val integ_of_bin_type = result();

goalw BinFn.thy [bin_succ_def]
    "!!w. w: bin ==> bin_succ(w) : bin";
by (typechk_tac (bin_typechecks0@bool_typechecks));
val bin_succ_type = result();

goalw BinFn.thy [bin_pred_def]
    "!!w. w: bin ==> bin_pred(w) : bin";
by (typechk_tac (bin_typechecks0@bool_typechecks));
val bin_pred_type = result();

goalw BinFn.thy [bin_minus_def]
    "!!w. w: bin ==> bin_minus(w) : bin";
by (typechk_tac ([bin_pred_type]@bin_typechecks0@bool_typechecks));
val bin_minus_type = result();

goalw BinFn.thy [bin_add_def]
    "!!v w. [| v: bin; w: bin |] ==> bin_add(v,w) : bin";
by (typechk_tac ([bin_succ_type,bin_pred_type]@bin_typechecks0@
		 bool_typechecks@ZF_typechecks));
val bin_add_type = result();

goalw BinFn.thy [bin_mult_def]
    "!!v w. [| v: bin; w: bin |] ==> bin_mult(v,w) : bin";
by (typechk_tac ([bin_minus_type,bin_add_type]@bin_typechecks0@
		 bool_typechecks));
val bin_mult_type = result();

val bin_typechecks = bin_typechecks0 @
    [integ_of_bin_type, bin_succ_type, bin_pred_type, 
     bin_minus_type, bin_add_type, bin_mult_type];

val bin_ss = integ_ss 
    addsimps([bool_1I, bool_0I,
	     bin_rec_Plus, bin_rec_Minus, bin_rec_Bcons] @ 
	     bin_recs integ_of_bin_def @ bool_rews @ bin_typechecks);

val typechecks = bin_typechecks @ integ_typechecks @ nat_typechecks @
                 [bool_subset_nat RS subsetD];

(**** The carry/borrow functions, bin_succ and bin_pred ****)

(** Lemmas **)

goal Integ.thy 
    "!!z v. [| z $+ v = z' $+ v';  \
\       z: integ; z': integ;  v: integ; v': integ;  w: integ |]   \
\    ==> z $+ (v $+ w) = z' $+ (v' $+ w)";
by (asm_simp_tac (integ_ss addsimps ([zadd_assoc RS sym])) 1);
val zadd_assoc_cong = result();

goal Integ.thy 
    "!!z v w. [| z: integ;  v: integ;  w: integ |]   \
\    ==> z $+ (v $+ w) = v $+ (z $+ w)";
by (REPEAT (ares_tac [zadd_commute RS zadd_assoc_cong] 1));
val zadd_assoc_swap = result();

val zadd_cong = 
    read_instantiate_sg (sign_of Integ.thy) [("t","op $+")] subst_context2;

val zadd_kill = (refl RS zadd_cong);
val zadd_assoc_swap_kill = zadd_kill RSN (4, zadd_assoc_swap RS trans);

(*Pushes 'constants' of the form $#m to the right -- LOOPS if two!*)
val zadd_assoc_znat = standard (znat_type RS zadd_assoc_swap);

goal Integ.thy 
    "!!z w. [| z: integ;  w: integ |]   \
\    ==> w $+ (z $+ (w $+ z)) = w $+ (w $+ (z $+ z))";
by (REPEAT (ares_tac [zadd_kill, zadd_assoc_swap] 1));
val zadd_swap_pairs = result();


val carry_ss = bin_ss addsimps 
               (bin_recs bin_succ_def @ bin_recs bin_pred_def);

goal BinFn.thy
    "!!w. w: bin ==> integ_of_bin(bin_succ(w)) = $#1 $+ integ_of_bin(w)";
by (etac Bin.induct 1);
by (simp_tac (carry_ss addsimps [zadd_0_right]) 1);
by (simp_tac (carry_ss addsimps [zadd_zminus_inverse]) 1);
by (etac boolE 1);
by (ALLGOALS (asm_simp_tac (carry_ss addsimps [zadd_assoc])));
by (REPEAT (ares_tac (zadd_swap_pairs::typechecks) 1));
val integ_of_bin_succ = result();

goal BinFn.thy
    "!!w. w: bin ==> integ_of_bin(bin_pred(w)) = $~ ($#1) $+ integ_of_bin(w)";
by (etac Bin.induct 1);
by (simp_tac (carry_ss addsimps [zadd_0_right]) 1);
by (simp_tac (carry_ss addsimps [zadd_zminus_inverse]) 1);
by (etac boolE 1);
by (ALLGOALS 
    (asm_simp_tac 
     (carry_ss addsimps [zadd_assoc RS sym,
			zadd_zminus_inverse, zadd_zminus_inverse2])));
by (REPEAT (ares_tac ([zadd_commute, zadd_cong, refl]@typechecks) 1));
val integ_of_bin_pred = result();

(*These two results replace the definitions of bin_succ and bin_pred*)


(*** bin_minus: (unary!) negation of binary integers ***)

val bin_minus_ss =
    bin_ss addsimps (bin_recs bin_minus_def @
		    [integ_of_bin_succ, integ_of_bin_pred]);

goal BinFn.thy
    "!!w. w: bin ==> integ_of_bin(bin_minus(w)) = $~ integ_of_bin(w)";
by (etac Bin.induct 1);
by (simp_tac (bin_minus_ss addsimps [zminus_0]) 1);
by (simp_tac (bin_minus_ss addsimps [zadd_0_right]) 1);
by (etac boolE 1);
by (ALLGOALS 
    (asm_simp_tac (bin_minus_ss addsimps [zminus_zadd_distrib, zadd_assoc])));
val integ_of_bin_minus = result();


(*** bin_add: binary addition ***)

goalw BinFn.thy [bin_add_def] "!!w. w: bin ==> bin_add(Plus,w) = w";
by (asm_simp_tac bin_ss 1);
val bin_add_Plus = result();

goalw BinFn.thy [bin_add_def] "!!w. w: bin ==> bin_add(Minus,w) = bin_pred(w)";
by (asm_simp_tac bin_ss 1);
val bin_add_Minus = result();

goalw BinFn.thy [bin_add_def] "bin_add(v$$x,Plus) = v$$x";
by (simp_tac bin_ss 1);
val bin_add_Bcons_Plus = result();

goalw BinFn.thy [bin_add_def] "bin_add(v$$x,Minus) = bin_pred(v$$x)";
by (simp_tac bin_ss 1);
val bin_add_Bcons_Minus = result();

goalw BinFn.thy [bin_add_def]
    "!!w y. [| w: bin;  y: bool |] ==> \
\           bin_add(v$$x, w$$y) = \
\           bin_add(v, cond(x and y, bin_succ(w), w)) $$ (x xor y)";
by (asm_simp_tac bin_ss 1);
val bin_add_Bcons_Bcons = result();

val bin_add_rews = [bin_add_Plus, bin_add_Minus, bin_add_Bcons_Plus,
		    bin_add_Bcons_Minus, bin_add_Bcons_Bcons,
		    integ_of_bin_succ, integ_of_bin_pred];

val bin_add_ss = bin_ss addsimps ([bool_subset_nat RS subsetD] @ bin_add_rews);

goal BinFn.thy
    "!!v. v: bin ==> \
\         ALL w: bin. integ_of_bin(bin_add(v,w)) = \
\                     integ_of_bin(v) $+ integ_of_bin(w)";
by (etac Bin.induct 1);
by (simp_tac bin_add_ss 1);
by (simp_tac bin_add_ss 1);
by (rtac ballI 1);
by (bin_ind_tac "wa" [] 1);
by (asm_simp_tac (bin_add_ss addsimps [zadd_0_right]) 1);
by (asm_simp_tac bin_add_ss 1);
by (REPEAT (ares_tac (zadd_commute::typechecks) 1));
by (etac boolE 1);
by (asm_simp_tac (bin_add_ss addsimps [zadd_assoc, zadd_swap_pairs]) 2);
by (REPEAT (ares_tac ([refl, zadd_kill, zadd_assoc_swap_kill]@typechecks) 2));
by (etac boolE 1);
by (ALLGOALS (asm_simp_tac (bin_add_ss addsimps [zadd_assoc,zadd_swap_pairs])));
by (REPEAT (ares_tac ([refl, zadd_kill, zadd_assoc_swap_kill RS sym]@
		      typechecks) 1));
val integ_of_bin_add_lemma = result();

val integ_of_bin_add = integ_of_bin_add_lemma RS bspec;


(*** bin_add: binary multiplication ***)

val bin_mult_ss =
    bin_ss addsimps (bin_recs bin_mult_def @ 
		       [integ_of_bin_minus, integ_of_bin_add]);


val major::prems = goal BinFn.thy
    "[| v: bin; w: bin |] ==>	\
\    integ_of_bin(bin_mult(v,w)) = \
\    integ_of_bin(v) $* integ_of_bin(w)";
by (cut_facts_tac prems 1);
by (bin_ind_tac "v" [major] 1);
by (asm_simp_tac (bin_mult_ss addsimps [zmult_0]) 1);
by (asm_simp_tac (bin_mult_ss addsimps [zmult_1,zmult_zminus]) 1);
by (etac boolE 1);
by (asm_simp_tac (bin_mult_ss addsimps [zadd_zmult_distrib]) 2);
by (asm_simp_tac 
    (bin_mult_ss addsimps [zadd_zmult_distrib, zmult_1, zadd_assoc]) 1);
by (REPEAT (ares_tac ([zadd_commute, zadd_assoc_swap_kill RS sym]@
		      typechecks) 1));
val integ_of_bin_mult = result();

(**** Computations ****)

(** extra rules for bin_succ, bin_pred **)

val [bin_succ_Plus, bin_succ_Minus, _] = bin_recs bin_succ_def;
val [bin_pred_Plus, bin_pred_Minus, _] = bin_recs bin_pred_def;

goal BinFn.thy "bin_succ(w$$1) = bin_succ(w) $$ 0";
by (simp_tac carry_ss 1);
val bin_succ_Bcons1 = result();

goal BinFn.thy "bin_succ(w$$0) = w$$1";
by (simp_tac carry_ss 1);
val bin_succ_Bcons0 = result();

goal BinFn.thy "bin_pred(w$$1) = w$$0";
by (simp_tac carry_ss 1);
val bin_pred_Bcons1 = result();

goal BinFn.thy "bin_pred(w$$0) = bin_pred(w) $$ 1";
by (simp_tac carry_ss 1);
val bin_pred_Bcons0 = result();

(** extra rules for bin_minus **)

val [bin_minus_Plus, bin_minus_Minus, _] = bin_recs bin_minus_def;

goal BinFn.thy "bin_minus(w$$1) = bin_pred(bin_minus(w) $$ 0)";
by (simp_tac bin_minus_ss 1);
val bin_minus_Bcons1 = result();

goal BinFn.thy "bin_minus(w$$0) = bin_minus(w) $$ 0";
by (simp_tac bin_minus_ss 1);
val bin_minus_Bcons0 = result();

(** extra rules for bin_add **)

goal BinFn.thy 
    "!!w. w: bin ==> bin_add(v$$1, w$$1) = bin_add(v, bin_succ(w)) $$ 0";
by (asm_simp_tac bin_add_ss 1);
val bin_add_Bcons_Bcons11 = result();

goal BinFn.thy 
    "!!w. w: bin ==> bin_add(v$$1, w$$0) = bin_add(v,w) $$ 1";
by (asm_simp_tac bin_add_ss 1);
val bin_add_Bcons_Bcons10 = result();

goal BinFn.thy 
    "!!w y.[| w: bin;  y: bool |] ==> bin_add(v$$0, w$$y) = bin_add(v,w) $$ y";
by (asm_simp_tac bin_add_ss 1);
val bin_add_Bcons_Bcons0 = result();

(** extra rules for bin_mult **)

val [bin_mult_Plus, bin_mult_Minus, _] = bin_recs bin_mult_def;

goal BinFn.thy "bin_mult(v$$1, w) = bin_add(bin_mult(v,w)$$0, w)";
by (simp_tac bin_mult_ss 1);
val bin_mult_Bcons1 = result();

goal BinFn.thy "bin_mult(v$$0, w) = bin_mult(v,w)$$0";
by (simp_tac bin_mult_ss 1);
val bin_mult_Bcons0 = result();


(*** The computation simpset ***)

val bin_comp_ss = integ_ss 
    addsimps [bin_succ_Plus, bin_succ_Minus,
	     bin_succ_Bcons1, bin_succ_Bcons0,
	     bin_pred_Plus, bin_pred_Minus,
	     bin_pred_Bcons1, bin_pred_Bcons0,
	     bin_minus_Plus, bin_minus_Minus,
	     bin_minus_Bcons1, bin_minus_Bcons0,
	     bin_add_Plus, bin_add_Minus, bin_add_Bcons_Plus, 
	     bin_add_Bcons_Minus, bin_add_Bcons_Bcons0, 
	     bin_add_Bcons_Bcons10, bin_add_Bcons_Bcons11,
	     bin_mult_Plus, bin_mult_Minus,
	     bin_mult_Bcons1, bin_mult_Bcons0]
    setsolver (type_auto_tac ([bool_1I, bool_0I] @ bin_typechecks0));

(*** Examples of performing binary arithmetic by simplification ***)

proof_timing := true;
(*All runtimes below are on a SPARCserver 10*)

(* 13+19 = 32 *)
goal BinFn.thy
    "bin_add(Plus$$1$$1$$0$$1, Plus$$1$$0$$0$$1$$1) = Plus$$1$$0$$0$$0$$0$$0";
by (simp_tac bin_comp_ss 1);	(*0.6 secs*)
result();

bin_add(binary_of_int 13, binary_of_int 19);

(* 1234+5678 = 6912 *)
goal BinFn.thy
    "bin_add(Plus$$1$$0$$0$$1$$1$$0$$1$$0$$0$$1$$0, \
\	     Plus$$1$$0$$1$$1$$0$$0$$0$$1$$0$$1$$1$$1$$0) = \
\    Plus$$1$$1$$0$$1$$1$$0$$0$$0$$0$$0$$0$$0$$0";
by (simp_tac bin_comp_ss 1);	(*2.6 secs*)
result();

bin_add(binary_of_int 1234, binary_of_int 5678);

(* 1359-2468 = ~1109 *)
goal BinFn.thy
    "bin_add(Plus$$1$$0$$1$$0$$1$$0$$0$$1$$1$$1$$1,		\
\	     Minus$$0$$1$$1$$0$$0$$1$$0$$1$$1$$1$$0$$0) = 	\
\    Minus$$1$$0$$1$$1$$1$$0$$1$$0$$1$$0$$1$$1";
by (simp_tac bin_comp_ss 1);	(*2.3 secs*)
result();

bin_add(binary_of_int 1359, binary_of_int ~2468);

(* 93746-46375 = 47371 *)
goal BinFn.thy
    "bin_add(Plus$$1$$0$$1$$1$$0$$1$$1$$1$$0$$0$$0$$1$$1$$0$$0$$1$$0, \
\	     Minus$$0$$1$$0$$0$$1$$0$$1$$0$$1$$1$$0$$1$$1$$0$$0$$1) = \
\    Plus$$0$$1$$0$$1$$1$$1$$0$$0$$1$$0$$0$$0$$0$$1$$0$$1$$1";
by (simp_tac bin_comp_ss 1);	(*3.9 secs*)
result();

bin_add(binary_of_int 93746, binary_of_int ~46375);

(* negation of 65745 *)
goal BinFn.thy
    "bin_minus(Plus$$1$$0$$0$$0$$0$$0$$0$$0$$0$$1$$1$$0$$1$$0$$0$$0$$1) = \
\    Minus$$0$$1$$1$$1$$1$$1$$1$$1$$1$$0$$0$$1$$0$$1$$1$$1$$1";
by (simp_tac bin_comp_ss 1);	(*0.6 secs*)
result();

bin_minus(binary_of_int 65745);

(* negation of ~54321 *)
goal BinFn.thy
    "bin_minus(Minus$$0$$0$$1$$0$$1$$0$$1$$1$$1$$1$$0$$0$$1$$1$$1$$1) = \
\    Plus$$0$$1$$1$$0$$1$$0$$1$$0$$0$$0$$0$$1$$1$$0$$0$$0$$1";
by (simp_tac bin_comp_ss 1);	(*0.7 secs*)
result();

bin_minus(binary_of_int ~54321);

(* 13*19 = 247 *)
goal BinFn.thy "bin_mult(Plus$$1$$1$$0$$1, Plus$$1$$0$$0$$1$$1) = \
\               Plus$$1$$1$$1$$1$$0$$1$$1$$1";
by (simp_tac bin_comp_ss 1);	(*1.5 secs*)
result();

bin_mult(binary_of_int 13, binary_of_int 19);

(* ~84 * 51 = ~4284 *)
goal BinFn.thy
    "bin_mult(Minus$$0$$1$$0$$1$$1$$0$$0, Plus$$1$$1$$0$$0$$1$$1) = \
\    Minus$$0$$1$$1$$1$$1$$0$$1$$0$$0$$0$$1$$0$$0";
by (simp_tac bin_comp_ss 1);	(*2.6 secs*)
result();

bin_mult(binary_of_int ~84, binary_of_int 51);

(* 255*255 = 65025;  the worst case for 8-bit operands *)
goal BinFn.thy
    "bin_mult(Plus$$1$$1$$1$$1$$1$$1$$1$$1, \
\             Plus$$1$$1$$1$$1$$1$$1$$1$$1) = \
\        Plus$$1$$1$$1$$1$$1$$1$$1$$0$$0$$0$$0$$0$$0$$0$$0$$1";
by (simp_tac bin_comp_ss 1);	(*9.8 secs*)
result();

bin_mult(binary_of_int 255, binary_of_int 255);

(* 1359 * ~2468 = ~3354012 *)
goal BinFn.thy
    "bin_mult(Plus$$1$$0$$1$$0$$1$$0$$0$$1$$1$$1$$1, 		\
\	      Minus$$0$$1$$1$$0$$0$$1$$0$$1$$1$$1$$0$$0) = 	\
\    Minus$$0$$0$$1$$1$$0$$0$$1$$1$$0$$1$$0$$0$$1$$0$$0$$1$$1$$0$$0$$1$$0$$0";
by (simp_tac bin_comp_ss 1);	(*13.7 secs*)
result();

bin_mult(binary_of_int 1359, binary_of_int ~2468);
