(*  Title: 	ZF/ex/integ.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For integ.thy.  The integers as equivalence classes over nat*nat.

Could also prove...
"znegative(z) ==> $# zmagnitude(z) = $~ z"
"~ znegative(z) ==> $# zmagnitude(z) = z"
$< is a linear ordering
$+ and $* are monotonic wrt $<
*)

open Integ;

val [add_cong] = mk_congs Arith.thy ["op #+"];

(*** Proving that intrel is an equivalence relation ***)

val prems = goal Arith.thy 
    "[| m #+ n = m' #+ n';  m: nat; m': nat |]   \
\    ==> m #+ (n #+ k) = m' #+ (n' #+ k)";
by (ASM_SIMP_TAC (arith_ss addrews ([add_assoc RS sym] @ prems)) 1);
val add_assoc_cong = result();

val prems = goal Arith.thy 
    "[| m: nat; n: nat |]   \
\    ==> m #+ (n #+ k) = n #+ (m #+ k)";
by (REPEAT (resolve_tac ([add_commute RS add_assoc_cong] @ prems) 1));
val add_assoc_swap = result();

val add_kill = (refl RS add_cong);
val add_assoc_swap_kill = add_kill RSN (3, add_assoc_swap RS trans);

(*By luck, requires no typing premises for y1, y2,y3*)
val eqa::eqb::prems = goal Arith.thy 
    "[| x1 #+ y2 = x2 #+ y1; x2 #+ y3 = x3 #+ y2;  \
\       x1: nat; x2: nat; x3: nat |]    ==>    x1 #+ y3 = x3 #+ y1";
by (res_inst_tac [("k","x2")] add_left_cancel 1);
by (resolve_tac prems 1);
by (rtac (add_assoc_swap RS trans) 1 THEN typechk_tac prems);
by (rtac (eqb RS ssubst) 1);
by (rtac (add_assoc_swap RS trans) 1 THEN typechk_tac prems);
by (rtac (eqa RS ssubst) 1);
by (rtac (add_assoc_swap) 1 THEN typechk_tac prems);
val integ_trans_lemma = result();

(** Natural deduction for intrel **)

val prems = goalw Integ.thy [intrel_def]
    "[| x1#+y2 = x2#+y1; x1: nat; y1: nat; x2: nat; y2: nat |] ==> \
\    <<x1,y1>,<x2,y2>>: intrel";
by (fast_tac (ZF_cs addIs prems) 1);
val intrelI = result();

(*intrelE is hard to derive because fast_tac tries hyp_subst_tac so soon*)
goalw Integ.thy [intrel_def]
  "p: intrel --> (EX x1 y1 x2 y2. \
\                  p = <<x1,y1>,<x2,y2>> & x1#+y2 = x2#+y1 & \
\                  x1: nat & y1: nat & x2: nat & y2: nat)";
by (fast_tac ZF_cs 1);
val intrelE_lemma = result();

val [major,minor] = goal Integ.thy
  "[| p: intrel;  \
\     !!x1 y1 x2 y2. [| p = <<x1,y1>,<x2,y2>>;  x1#+y2 = x2#+y1; \
\                       x1: nat; y1: nat; x2: nat; y2: nat |] ==> Q |] \
\  ==> Q";
by (cut_facts_tac [major RS (intrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
val intrelE = result();

val intrel_cs = ZF_cs addSIs [intrelI] addSEs [intrelE];

goal Integ.thy
    "<<x1,y1>,<x2,y2>>: intrel <-> \
\    x1#+y2 = x2#+y1 & x1: nat & y1: nat & x2: nat & y2: nat";
by (fast_tac intrel_cs 1);
val intrel_iff = result();

val prems = goalw Integ.thy [equiv_def] "equiv(nat*nat, intrel)";
by (safe_tac intrel_cs);
by (rewtac refl_def);
by (fast_tac intrel_cs 1);
by (rewtac sym_def);
by (fast_tac (intrel_cs addSEs [sym]) 1);
by (rewtac trans_def);
by (fast_tac (intrel_cs addSEs [integ_trans_lemma]) 1);
val equiv_intrel = result();


val integ_congs = mk_congs Integ.thy
  ["znat", "zminus", "znegative", "zmagnitude", "op $+", "op $-", "op $*"];

val intrel_ss0 = arith_ss addcongs integ_congs;

val intrel_ss = 
    intrel_ss0 addrews [equiv_intrel RS eq_equiv_class_iff, intrel_iff];

(*More than twice as fast as simplifying with intrel_ss*)
fun INTEG_SIMP_TAC ths = 
  let val ss = intrel_ss0 addrews ths 
  in fn i =>
       EVERY [ASM_SIMP_TAC ss i,
	      rtac (intrelI RS (equiv_intrel RS equiv_class_eq)) i,
	      typechk_tac (ZF_typechecks@nat_typechecks@arith_typechecks),
	      ASM_SIMP_TAC ss i]
  end;


(** znat: the injection from nat to integ **)

val prems = goalw Integ.thy [integ_def,quotient_def,znat_def]
    "m : nat ==> $#m : integ";
by (fast_tac (ZF_cs addSIs (nat_0I::prems)) 1);
val znat_type = result();

val [major,nnat] = goalw Integ.thy [znat_def]
    "[| $#m = $#n;  n: nat |] ==> m=n";
by (rtac (make_elim (major RS eq_equiv_class)) 1);
by (rtac equiv_intrel 1);
by (typechk_tac [nat_0I,nnat,SigmaI]);
by (safe_tac (intrel_cs addSEs [box_equals,add_0_right]));
val znat_inject = result();


(**** zminus: unary negation on integ ****)

goalw Integ.thy [congruent_def]
    "congruent(intrel, split(%x y. intrel``{<y,x>}))";
by (safe_tac intrel_cs);
by (ALLGOALS (ASM_SIMP_TAC intrel_ss));
by (etac (box_equals RS sym) 1);
by (REPEAT (ares_tac [add_commute] 1));
val zminus_congruent = result();

(*Resolve th against the corresponding facts for zminus*)
val zminus_ize = RSLIST [equiv_intrel, zminus_congruent];

val [prem] = goalw Integ.thy [integ_def,zminus_def]
    "z : integ ==> $~z : integ";
by (typechk_tac [split_type, SigmaI, prem, zminus_ize UN_equiv_class_type,
		 quotientI]);
val zminus_type = result();

val major::prems = goalw Integ.thy [integ_def,zminus_def]
    "[| $~z = $~w;  z: integ;  w: integ |] ==> z=w";
by (rtac (major RS zminus_ize UN_equiv_class_inject) 1);
by (REPEAT (ares_tac prems 1));
by (REPEAT (etac SigmaE 1));
by (etac rev_mp 1);
by (ASM_SIMP_TAC ZF_ss 1);
by (fast_tac (intrel_cs addSIs [SigmaI, equiv_intrel]
			addSEs [box_equals RS sym, add_commute,
			        make_elim eq_equiv_class]) 1);
val zminus_inject = result();

val prems = goalw Integ.thy [zminus_def]
    "[| x: nat;  y: nat |] ==> $~ (intrel``{<x,y>}) = intrel `` {<y,x>}";
by (ASM_SIMP_TAC 
    (ZF_ss addrews (prems@[zminus_ize UN_equiv_class, SigmaI])) 1);
val zminus = result();

goalw Integ.thy [integ_def] "!!z. z : integ ==> $~ ($~ z) = z";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (ASM_SIMP_TAC (ZF_ss addrews [zminus] addcongs integ_congs) 1);
val zminus_zminus = result();

goalw Integ.thy [integ_def, znat_def] "$~ ($#0) = $#0";
by (SIMP_TAC (arith_ss addrews [zminus]) 1);
val zminus_0 = result();


(**** znegative: the test for negative integers ****)

goalw Integ.thy [znegative_def, znat_def]
    "~ znegative($# n)";
by (safe_tac intrel_cs);
by (rtac (add_not_less_self RS notE) 1);
by (etac ssubst 3);
by (ASM_SIMP_TAC (arith_ss addrews [add_0_right]) 3);
by (REPEAT (assume_tac 1));
val not_znegative_znat = result();

val [nnat] = goalw Integ.thy [znegative_def, znat_def]
    "n: nat ==> znegative($~ $# succ(n))";
by (SIMP_TAC (intrel_ss addrews [zminus,nnat]) 1);
by (REPEAT 
    (resolve_tac [refl, exI, conjI, naturals_are_ordinals RS Ord_0_mem_succ,
		  refl RS intrelI RS imageI, consI1, nnat, nat_0I,
		  nat_succI] 1));
val znegative_zminus_znat = result();


(**** zmagnitude: magnitide of an integer, as a natural number ****)

goalw Integ.thy [congruent_def]
    "congruent(intrel, split(%x y. (y#-x) #+ (x#-y)))";
by (safe_tac intrel_cs);
by (ALLGOALS (ASM_SIMP_TAC intrel_ss));
by (etac rev_mp 1);
by (res_inst_tac [("m","x1"),("n","y1")] diff_induct 1);
by (REPEAT (assume_tac 1));
by (ASM_SIMP_TAC (arith_ss addrews [add_succ_right,succ_inject_iff]) 3);
by (ASM_SIMP_TAC
    (arith_ss addrews [diff_add_inverse,diff_add_0,add_0_right]) 2);
by (ASM_SIMP_TAC (arith_ss addrews [add_0_right]) 1);
by (rtac impI 1);
by (etac subst 1);
by (res_inst_tac [("m1","x")] (add_commute RS ssubst) 1);
by (REPEAT (assume_tac 1));
by (ASM_SIMP_TAC (arith_ss addrews [diff_add_inverse,diff_add_0]) 1);
val zmagnitude_congruent = result();

(*Resolve th against the corresponding facts for zmagnitude*)
val zmagnitude_ize = RSLIST [equiv_intrel, zmagnitude_congruent];

val [prem] = goalw Integ.thy [integ_def,zmagnitude_def]
    "z : integ ==> zmagnitude(z) : nat";
by (typechk_tac [split_type, prem, zmagnitude_ize UN_equiv_class_type,
		 add_type, diff_type]);
val zmagnitude_type = result();

val prems = goalw Integ.thy [zmagnitude_def]
    "[| x: nat;  y: nat |] ==> \
\    zmagnitude (intrel``{<x,y>}) = (y #- x) #+ (x #- y)";
by (ASM_SIMP_TAC 
    (ZF_ss addrews (prems@[zmagnitude_ize UN_equiv_class, SigmaI])) 1);
val zmagnitude = result();

val [nnat] = goalw Integ.thy [znat_def]
    "n: nat ==> zmagnitude($# n) = n";
by (SIMP_TAC (intrel_ss addrews [zmagnitude,nnat]) 1);
val zmagnitude_znat = result();

val [nnat] = goalw Integ.thy [znat_def]
    "n: nat ==> zmagnitude($~ $# n) = n";
by (SIMP_TAC (intrel_ss addrews [zmagnitude,zminus,nnat,add_0_right]) 1);
val zmagnitude_zminus_znat = result();


(**** zadd: addition on integ ****)

(** Congruence property for addition **)

goalw Integ.thy [congruent2_def]
    "congruent2(intrel, %p1 p2.                  \
\         split(%x1 y1. split(%x2 y2. intrel `` {<x1#+x2, y1#+y2>}, p2), p1))";
(*Proof via congruent2_commuteI seems longer*)
by (safe_tac intrel_cs);
by (INTEG_SIMP_TAC [add_assoc] 1);
(*The rest should be trivial, but rearranging terms is hard*)
by (res_inst_tac [("m1","x1a")] (add_assoc_swap RS ssubst) 1);
by (res_inst_tac [("m1","x2a")] (add_assoc_swap RS ssubst) 3);
by (typechk_tac [add_type]);
by (ASM_SIMP_TAC (arith_ss addrews [add_assoc RS sym]) 1);
val zadd_congruent2 = result();

(*Resolve th against the corresponding facts for zadd*)
val zadd_ize = RSLIST [equiv_intrel, zadd_congruent2];

val prems = goalw Integ.thy [integ_def,zadd_def]
    "[| z: integ;  w: integ |] ==> z $+ w : integ";
by (REPEAT (ares_tac (prems@[zadd_ize UN_equiv_class_type2,
			     split_type, add_type, quotientI, SigmaI]) 1));
val zadd_type = result();

val prems = goalw Integ.thy [zadd_def]
  "[| x1: nat; y1: nat;  x2: nat; y2: nat |] ==> \
\ (intrel``{<x1,y1>}) $+ (intrel``{<x2,y2>}) = intrel `` {<x1#+x2, y1#+y2>}";
by (ASM_SIMP_TAC (ZF_ss addrews 
		  (prems @ [zadd_ize UN_equiv_class2, SigmaI])) 1);
val zadd = result();

goalw Integ.thy [integ_def,znat_def] "!!z. z : integ ==> $#0 $+ z = z";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (ASM_SIMP_TAC (arith_ss addrews [zadd]) 1);
val zadd_0 = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> $~ (z $+ w) = $~ z $+ $~ w";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (ASM_SIMP_TAC (arith_ss addrews [zminus,zadd] addcongs integ_congs) 1);
val zminus_zadd_distrib = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> z $+ w = w $+ z";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (INTEG_SIMP_TAC [zadd] 1);
by (REPEAT (ares_tac [add_commute,add_cong] 1));
val zadd_commute = result();

goalw Integ.thy [integ_def]
    "!!z1 z2 z3. [| z1: integ;  z2: integ;  z3: integ |] ==> \
\                (z1 $+ z2) $+ z3 = z1 $+ (z2 $+ z3)";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
(*rewriting is much faster without intrel_iff, etc.*)
by (ASM_SIMP_TAC (intrel_ss0 addrews [zadd,add_assoc]) 1);
val zadd_assoc = result();

val prems = goalw Integ.thy [znat_def]
    "[| m: nat;  n: nat |] ==> $# (m #+ n) = ($#m) $+ ($#n)";
by (ASM_SIMP_TAC (arith_ss addrews (zadd::prems)) 1);
val znat_add = result();

goalw Integ.thy [integ_def,znat_def] "!!z. z : integ ==> z $+ ($~ z) = $#0";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (ASM_SIMP_TAC (intrel_ss addrews [zminus,zadd,add_0_right]) 1);
by (REPEAT (ares_tac [add_commute] 1));
val zadd_zminus_inverse = result();

val prems = goal Integ.thy 
    "z : integ ==> ($~ z) $+ z = $#0";
by (rtac (zadd_commute RS trans) 1);
by (REPEAT (resolve_tac (prems@[zminus_type, zadd_zminus_inverse]) 1));
val zadd_zminus_inverse2 = result();

val prems = goal Integ.thy "z:integ ==> z $+ $#0 = z";
by (rtac (zadd_commute RS trans) 1);
by (REPEAT (resolve_tac (prems@[znat_type,nat_0I,zadd_0]) 1));
val zadd_0_right = result();


(*Need properties of $- ???  Or use $- just as an abbreviation?
     [| m: nat;  n: nat;  m>=n |] ==> $# (m #- n) = ($#m) $- ($#n)
*)

(**** zmult: multiplication on integ ****)

(** Congruence property for multiplication **)

val prems = goalw Integ.thy [znat_def]
    "[| k: nat;  l: nat;  m: nat;  n: nat |] ==> 	\
\    (k #+ l) #+ (m #+ n) = (k #+ m) #+ (n #+ l)";
val add_commute' = read_instantiate [("m","l")] add_commute;
by (SIMP_TAC (arith_ss addrews ([add_commute',add_assoc]@prems)) 1);
val zmult_congruent_lemma = result();

goal Integ.thy 
    "congruent2(intrel, %p1 p2.  		\
\               split(%x1 y1. split(%x2 y2. 	\
\                   intrel``{<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}, p2), p1))";
by (rtac (equiv_intrel RS congruent2_commuteI) 1);
by (safe_tac intrel_cs);
by (ALLGOALS (INTEG_SIMP_TAC []));
(*Proof that zmult is congruent in one argument*)
by (rtac (zmult_congruent_lemma RS trans) 2);
by (rtac (zmult_congruent_lemma RS trans RS sym) 6);
by (typechk_tac [mult_type]);
by (ASM_SIMP_TAC (arith_ss addrews [add_mult_distrib_left RS sym]) 2);
(*Proof that zmult is commutative on representatives*)
by (rtac add_cong 1);
by (rtac (add_commute RS trans) 2);
by (REPEAT (ares_tac [mult_commute,add_type,mult_type,add_cong] 1));
val zmult_congruent2 = result();

(*Resolve th against the corresponding facts for zmult*)
val zmult_ize = RSLIST [equiv_intrel, zmult_congruent2];

val prems = goalw Integ.thy [integ_def,zmult_def]
    "[| z: integ;  w: integ |] ==> z $* w : integ";
by (REPEAT (ares_tac (prems@[zmult_ize UN_equiv_class_type2,
			     split_type, add_type, mult_type, 
			     quotientI, SigmaI]) 1));
val zmult_type = result();


val prems = goalw Integ.thy [zmult_def]
     "[| x1: nat; y1: nat;  x2: nat; y2: nat |] ==> 	\
\     (intrel``{<x1,y1>}) $* (intrel``{<x2,y2>}) = 	\
\     intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}";
by (ASM_SIMP_TAC (ZF_ss addrews 
		  (prems @ [zmult_ize UN_equiv_class2, SigmaI])) 1);
val zmult = result();

goalw Integ.thy [integ_def,znat_def] "!!z. z : integ ==> $#0 $* z = $#0";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (ASM_SIMP_TAC (arith_ss addrews [zmult]) 1);
val zmult_0 = result();

goalw Integ.thy [integ_def,znat_def,one_def]
    "!!z. z : integ ==> $#1 $* z = z";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (ASM_SIMP_TAC (arith_ss addrews [zmult,add_0_right]) 1);
val zmult_1 = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> ($~ z) $* w = $~ (z $* w)";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (INTEG_SIMP_TAC [zminus,zmult] 1);
by (REPEAT (ares_tac [mult_type,add_commute,add_cong] 1));
val zmult_zminus = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> ($~ z) $* ($~ w) = (z $* w)";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (INTEG_SIMP_TAC [zminus,zmult] 1);
by (REPEAT (ares_tac [mult_type,add_commute,add_cong] 1));
val zmult_zminus_zminus = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> z $* w = w $* z";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (INTEG_SIMP_TAC [zmult] 1);
by (res_inst_tac [("m1","xc #* y")] (add_commute RS ssubst) 1);
by (REPEAT (ares_tac [mult_type,mult_commute,add_cong] 1));
val zmult_commute = result();

goalw Integ.thy [integ_def]
    "!!z1 z2 z3. [| z1: integ;  z2: integ;  z3: integ |] ==> \
\                (z1 $* z2) $* z3 = z1 $* (z2 $* z3)";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (INTEG_SIMP_TAC [zmult, add_mult_distrib_left, 
		    add_mult_distrib, add_assoc, mult_assoc] 1);
(*takes 54 seconds due to wasteful type-checking*)
by (REPEAT (ares_tac [add_type, mult_type, add_commute, add_kill, 
		      add_assoc_swap_kill, add_assoc_swap_kill RS sym] 1));
val zmult_assoc = result();

goalw Integ.thy [integ_def]
    "!!z1 z2 z3. [| z1: integ;  z2: integ;  w: integ |] ==> \
\                (z1 $+ z2) $* w = (z1 $* w) $+ (z2 $* w)";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (INTEG_SIMP_TAC [zadd, zmult, add_mult_distrib, add_assoc] 1);
(*takes 30 seconds due to wasteful type-checking*)
by (REPEAT (ares_tac [add_type, mult_type, refl, add_commute, add_kill, 
		      add_assoc_swap_kill, add_assoc_swap_kill RS sym] 1));
val zadd_zmult_distrib = result();

val integ_typechecks =
    [znat_type, zminus_type, zmagnitude_type, zadd_type, zmult_type];

val integ_ss =
    arith_ss addcongs integ_congs
             addrews  ([zminus_zminus,zmagnitude_znat,zmagnitude_zminus_znat,
		        zadd_0] @ integ_typechecks);
