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

val add_cong = 
    read_instantiate_sg (sign_of Arith.thy) [("t","op #+")] subst_context2;


open Integ;

(*** Proving that intrel is an equivalence relation ***)

val add_kill = (refl RS add_cong);

val add_left_commute_kill = add_kill RSN (3, add_left_commute RS trans);

(*By luck, requires no typing premises for y1, y2,y3*)
val eqa::eqb::prems = goal Arith.thy 
    "[| x1 #+ y2 = x2 #+ y1; x2 #+ y3 = x3 #+ y2;  \
\       x1: nat; x2: nat; x3: nat |]    ==>    x1 #+ y3 = x3 #+ y1";
by (res_inst_tac [("k","x2")] add_left_cancel 1);
by (resolve_tac prems 2);
by (rtac (add_left_commute RS trans) 1 THEN typechk_tac prems);
by (rtac (eqb RS ssubst) 1);
by (rtac (add_left_commute RS trans) 1 THEN typechk_tac prems);
by (rtac (eqa RS ssubst) 1);
by (rtac (add_left_commute) 1 THEN typechk_tac prems);
val integ_trans_lemma = result();

(** Natural deduction for intrel **)

goalw Integ.thy [intrel_def]
    "<<x1,y1>,<x2,y2>>: intrel <-> \
\    x1: nat & y1: nat & x2: nat & y2: nat & x1#+y2 = x2#+y1";
by (fast_tac ZF_cs 1);
val intrel_iff = result();

goalw Integ.thy [intrel_def]
    "!!x1 x2. [| x1#+y2 = x2#+y1; x1: nat; y1: nat; x2: nat; y2: nat |] ==> \
\             <<x1,y1>,<x2,y2>>: intrel";
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

goalw Integ.thy [equiv_def, refl_def, sym_def, trans_def]
    "equiv(nat*nat, intrel)";
by (fast_tac (intrel_cs addSEs [sym, integ_trans_lemma]) 1);
val equiv_intrel = result();


val intrel_ss = 
    arith_ss addsimps [equiv_intrel RS eq_equiv_class_iff, intrel_iff,
		       add_0_right, add_succ_right]
             addcongs [conj_cong];

val eq_intrelD = equiv_intrel RSN (2,eq_equiv_class);

(** znat: the injection from nat to integ **)

goalw Integ.thy [integ_def,quotient_def,znat_def]
    "!!m. m : nat ==> $#m : integ";
by (fast_tac (ZF_cs addSIs [nat_0I]) 1);
val znat_type = result();

goalw Integ.thy [znat_def]
    "!!m n. [| $#m = $#n;  n: nat |] ==> m=n";
by (dtac eq_intrelD 1);
by (typechk_tac [nat_0I, SigmaI]);
by (asm_full_simp_tac intrel_ss 1);
val znat_inject = result();


(**** zminus: unary negation on integ ****)

goalw Integ.thy [congruent_def]
    "congruent(intrel, split(%x y. intrel``{<y,x>}))";
by (safe_tac intrel_cs);
by (asm_full_simp_tac (intrel_ss addsimps add_ac) 1);
val zminus_congruent = result();

(*Resolve th against the corresponding facts for zminus*)
val zminus_ize = RSLIST [equiv_intrel, zminus_congruent];

goalw Integ.thy [integ_def,zminus_def]
    "!!z. z : integ ==> $~z : integ";
by (typechk_tac [split_type, SigmaI, zminus_ize UN_equiv_class_type,
		 quotientI]);
val zminus_type = result();

goalw Integ.thy [integ_def,zminus_def]
    "!!z w. [| $~z = $~w;  z: integ;  w: integ |] ==> z=w";
by (etac (zminus_ize UN_equiv_class_inject) 1);
by (safe_tac intrel_cs);
(*The setloop is only needed because assumptions are in the wrong order!*)
by (asm_full_simp_tac (intrel_ss addsimps add_ac
		       setloop dtac eq_intrelD) 1);
val zminus_inject = result();

goalw Integ.thy [zminus_def]
    "!!x y.[| x: nat;  y: nat |] ==> $~ (intrel``{<x,y>}) = intrel `` {<y,x>}";
by (asm_simp_tac (ZF_ss addsimps [zminus_ize UN_equiv_class, SigmaI]) 1);
val zminus = result();

goalw Integ.thy [integ_def] "!!z. z : integ ==> $~ ($~ z) = z";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (asm_simp_tac (ZF_ss addsimps [zminus]) 1);
val zminus_zminus = result();

goalw Integ.thy [integ_def, znat_def] "$~ ($#0) = $#0";
by (simp_tac (arith_ss addsimps [zminus]) 1);
val zminus_0 = result();


(**** znegative: the test for negative integers ****)

goalw Integ.thy [znegative_def, znat_def]  "~ znegative($# n)";
by (asm_full_simp_tac (intrel_ss setloop K(safe_tac intrel_cs)) 1);
be rev_mp 1;
by (asm_simp_tac (arith_ss addsimps [add_le_self2 RS le_imp_not_lt]) 1);
val not_znegative_znat = result();

goalw Integ.thy [znegative_def, znat_def]
    "!!n. n: nat ==> znegative($~ $# succ(n))";
by (asm_simp_tac (intrel_ss addsimps [zminus]) 1);
by (REPEAT 
    (ares_tac [refl, exI, conjI, nat_0_le,
	       refl RS intrelI RS imageI, consI1, nat_0I, nat_succI] 1));
val znegative_zminus_znat = result();


(**** zmagnitude: magnitide of an integer, as a natural number ****)

goalw Integ.thy [congruent_def]
    "congruent(intrel, split(%x y. (y#-x) #+ (x#-y)))";
by (safe_tac intrel_cs);
by (ALLGOALS (asm_simp_tac intrel_ss));
by (etac rev_mp 1);
by (res_inst_tac [("m","x1"),("n","y1")] diff_induct 1 THEN 
    REPEAT (assume_tac 1));
by (asm_simp_tac (intrel_ss addsimps [succ_inject_iff]) 3);
by (asm_simp_tac  (*this one's very sensitive to order of rewrites*)
    (arith_ss addsimps [diff_add_inverse,diff_add_0,add_0_right]) 2);
by (asm_simp_tac intrel_ss 1);
by (rtac impI 1);
by (etac subst 1);
by (res_inst_tac [("m1","x")] (add_commute RS ssubst) 1 THEN
    REPEAT (assume_tac 1));
by (asm_simp_tac (arith_ss addsimps [diff_add_inverse, diff_add_0]) 1);
val zmagnitude_congruent = result();


(*Resolve th against the corresponding facts for zmagnitude*)
val zmagnitude_ize = RSLIST [equiv_intrel, zmagnitude_congruent];

goalw Integ.thy [integ_def,zmagnitude_def]
    "!!z. z : integ ==> zmagnitude(z) : nat";
by (typechk_tac [split_type, zmagnitude_ize UN_equiv_class_type,
		 add_type, diff_type]);
val zmagnitude_type = result();

goalw Integ.thy [zmagnitude_def]
    "!!x y. [| x: nat;  y: nat |] ==> \
\           zmagnitude (intrel``{<x,y>}) = (y #- x) #+ (x #- y)";
by (asm_simp_tac (ZF_ss addsimps [zmagnitude_ize UN_equiv_class, SigmaI]) 1);
val zmagnitude = result();

goalw Integ.thy [znat_def]
    "!!n. n: nat ==> zmagnitude($# n) = n";
by (asm_simp_tac (intrel_ss addsimps [zmagnitude]) 1);
val zmagnitude_znat = result();

goalw Integ.thy [znat_def]
    "!!n. n: nat ==> zmagnitude($~ $# n) = n";
by (asm_simp_tac (intrel_ss addsimps [zmagnitude, zminus]) 1);
val zmagnitude_zminus_znat = result();


(**** zadd: addition on integ ****)

(** Congruence property for addition **)

goalw Integ.thy [congruent2_def]
    "congruent2(intrel, %p1 p2.                  \
\         split(%x1 y1. split(%x2 y2. intrel `` {<x1#+x2, y1#+y2>}, p2), p1))";
(*Proof via congruent2_commuteI seems longer*)
by (safe_tac intrel_cs);
by (asm_simp_tac (intrel_ss addsimps [add_assoc]) 1);
(*The rest should be trivial, but rearranging terms is hard;
  add_ac does not help rewriting with the assumptions.*)
by (res_inst_tac [("m1","x1a")] (add_left_commute RS ssubst) 1);
by (res_inst_tac [("m1","x2a")] (add_left_commute RS ssubst) 3);
by (typechk_tac [add_type]);
by (asm_simp_tac (arith_ss addsimps [add_assoc RS sym]) 1);
val zadd_congruent2 = result();


(*Resolve th against the corresponding facts for zadd*)
val zadd_ize = RSLIST [equiv_intrel, zadd_congruent2];

goalw Integ.thy [integ_def,zadd_def]
    "!!z w. [| z: integ;  w: integ |] ==> z $+ w : integ";
by (REPEAT (ares_tac [zadd_ize UN_equiv_class_type2,
		      split_type, add_type, quotientI, SigmaI] 1));
val zadd_type = result();

goalw Integ.thy [zadd_def]
  "!!x1 y1. [| x1: nat; y1: nat;  x2: nat; y2: nat |] ==>	\
\           (intrel``{<x1,y1>}) $+ (intrel``{<x2,y2>}) =	\
\	    intrel `` {<x1#+x2, y1#+y2>}";
by (asm_simp_tac (ZF_ss addsimps [zadd_ize UN_equiv_class2, SigmaI]) 1);
val zadd = result();

goalw Integ.thy [integ_def,znat_def] "!!z. z : integ ==> $#0 $+ z = z";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (arith_ss addsimps [zadd]) 1);
val zadd_0 = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> $~ (z $+ w) = $~ z $+ $~ w";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (arith_ss addsimps [zminus,zadd]) 1);
val zminus_zadd_distrib = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> z $+ w = w $+ z";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (intrel_ss addsimps (add_ac @ [zadd])) 1);
val zadd_commute = result();

goalw Integ.thy [integ_def]
    "!!z1 z2 z3. [| z1: integ;  z2: integ;  z3: integ |] ==> \
\                (z1 $+ z2) $+ z3 = z1 $+ (z2 $+ z3)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
(*rewriting is much faster without intrel_iff, etc.*)
by (asm_simp_tac (arith_ss addsimps [zadd, add_assoc]) 1);
val zadd_assoc = result();

goalw Integ.thy [znat_def]
    "!!m n. [| m: nat;  n: nat |] ==> $# (m #+ n) = ($#m) $+ ($#n)";
by (asm_simp_tac (arith_ss addsimps [zadd]) 1);
val znat_add = result();

goalw Integ.thy [integ_def,znat_def] "!!z. z : integ ==> z $+ ($~ z) = $#0";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (intrel_ss addsimps [zminus, zadd, add_commute]) 1);
val zadd_zminus_inverse = result();

goal Integ.thy "!!z. z : integ ==> ($~ z) $+ z = $#0";
by (asm_simp_tac
    (ZF_ss addsimps [zadd_commute, zminus_type, zadd_zminus_inverse]) 1);
val zadd_zminus_inverse2 = result();

goal Integ.thy "!!z. z:integ ==> z $+ $#0 = z";
by (rtac (zadd_commute RS trans) 1);
by (REPEAT (ares_tac [znat_type, nat_0I, zadd_0] 1));
val zadd_0_right = result();


(*Need properties of $- ???  Or use $- just as an abbreviation?
     [| m: nat;  n: nat;  m>=n |] ==> $# (m #- n) = ($#m) $- ($#n)
*)

(**** zmult: multiplication on integ ****)

(** Congruence property for multiplication **)

goal Integ.thy 
    "congruent2(intrel, %p1 p2.  		\
\               split(%x1 y1. split(%x2 y2. 	\
\                   intrel``{<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}, p2), p1))";
by (rtac (equiv_intrel RS congruent2_commuteI) 1);
by (safe_tac intrel_cs);
by (ALLGOALS (asm_simp_tac intrel_ss));
(*Proof that zmult is congruent in one argument*)
by (asm_simp_tac 
    (arith_ss addsimps (add_ac @ [add_mult_distrib_left RS sym])) 2);
by (asm_simp_tac
    (arith_ss addsimps ([add_assoc RS sym, add_mult_distrib_left RS sym])) 2);
(*Proof that zmult is commutative on representatives*)
by (asm_simp_tac (arith_ss addsimps (mult_ac@add_ac)) 1);
val zmult_congruent2 = result();


(*Resolve th against the corresponding facts for zmult*)
val zmult_ize = RSLIST [equiv_intrel, zmult_congruent2];

goalw Integ.thy [integ_def,zmult_def]
    "!!z w. [| z: integ;  w: integ |] ==> z $* w : integ";
by (REPEAT (ares_tac [zmult_ize UN_equiv_class_type2,
		      split_type, add_type, mult_type, 
		      quotientI, SigmaI] 1));
val zmult_type = result();

goalw Integ.thy [zmult_def]
     "!!x1 x2. [| x1: nat; y1: nat;  x2: nat; y2: nat |] ==> 	\
\              (intrel``{<x1,y1>}) $* (intrel``{<x2,y2>}) = 	\
\              intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}";
by (asm_simp_tac (ZF_ss addsimps [zmult_ize UN_equiv_class2, SigmaI]) 1);
val zmult = result();

goalw Integ.thy [integ_def,znat_def] "!!z. z : integ ==> $#0 $* z = $#0";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (arith_ss addsimps [zmult]) 1);
val zmult_0 = result();

goalw Integ.thy [integ_def,znat_def]
    "!!z. z : integ ==> $#1 $* z = z";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (arith_ss addsimps [zmult, add_0_right]) 1);
val zmult_1 = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> ($~ z) $* w = $~ (z $* w)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (intrel_ss addsimps ([zminus, zmult] @ add_ac)) 1);
val zmult_zminus = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> ($~ z) $* ($~ w) = (z $* w)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (intrel_ss addsimps ([zminus, zmult] @ add_ac)) 1);
val zmult_zminus_zminus = result();

goalw Integ.thy [integ_def]
    "!!z w. [| z: integ;  w: integ |] ==> z $* w = w $* z";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (intrel_ss addsimps ([zmult] @ add_ac @ mult_ac)) 1);
val zmult_commute = result();

goalw Integ.thy [integ_def]
    "!!z1 z2 z3. [| z1: integ;  z2: integ;  z3: integ |] ==> \
\                (z1 $* z2) $* z3 = z1 $* (z2 $* z3)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac 
    (intrel_ss addsimps ([zmult, add_mult_distrib_left, 
			  add_mult_distrib] @ add_ac @ mult_ac)) 1);
val zmult_assoc = result();

goalw Integ.thy [integ_def]
    "!!z1 z2 z3. [| z1: integ;  z2: integ;  w: integ |] ==> \
\                (z1 $+ z2) $* w = (z1 $* w) $+ (z2 $* w)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac 
    (intrel_ss addsimps ([zadd, zmult, add_mult_distrib] @ 
			 add_ac @ mult_ac)) 1);
val zadd_zmult_distrib = result();

val integ_typechecks =
    [znat_type, zminus_type, zmagnitude_type, zadd_type, zmult_type];

val integ_ss =
    arith_ss addsimps ([zminus_zminus, zmagnitude_znat, 
			zmagnitude_zminus_znat, zadd_0] @ integ_typechecks);
