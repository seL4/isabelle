(*  Title:      ZF/ex/integ.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The integers as equivalence classes over nat*nat.

Could also prove...
"znegative(z) ==> $# zmagnitude(z) = $~ z"
"~ znegative(z) ==> $# zmagnitude(z) = z"
$< is a linear ordering
$+ and $* are monotonic wrt $<
*)

AddSEs [quotientE];

(*** Proving that intrel is an equivalence relation ***)

(*By luck, requires no typing premises for y1, y2,y3*)
val eqa::eqb::prems = goal Arith.thy 
    "[| x1 #+ y2 = x2 #+ y1; x2 #+ y3 = x3 #+ y2;  \
\       x1: nat; x2: nat; x3: nat |]    ==>    x1 #+ y3 = x3 #+ y1";
by (res_inst_tac [("k","x2")] add_left_cancel 1);
by (resolve_tac prems 2);
by (rtac (add_left_commute RS trans) 1 THEN typechk_tac prems);
by (stac eqb 1);
by (rtac (add_left_commute RS trans) 1 THEN typechk_tac prems);
by (stac eqa 1);
by (rtac (add_left_commute) 1 THEN typechk_tac prems);
qed "integ_trans_lemma";

(** Natural deduction for intrel **)

Goalw [intrel_def]
    "<<x1,y1>,<x2,y2>>: intrel <-> \
\    x1: nat & y1: nat & x2: nat & y2: nat & x1#+y2 = x2#+y1";
by (Fast_tac 1);
qed "intrel_iff";

Goalw [intrel_def]
    "[| x1#+y2 = x2#+y1; x1: nat; y1: nat; x2: nat; y2: nat |] ==> \
\             <<x1,y1>,<x2,y2>>: intrel";
by (fast_tac (claset() addIs prems) 1);
qed "intrelI";

(*intrelE is hard to derive because fast_tac tries hyp_subst_tac so soon*)
Goalw [intrel_def]
  "p: intrel --> (EX x1 y1 x2 y2. \
\                  p = <<x1,y1>,<x2,y2>> & x1#+y2 = x2#+y1 & \
\                  x1: nat & y1: nat & x2: nat & y2: nat)";
by (Fast_tac 1);
qed "intrelE_lemma";

val [major,minor] = goal Integ.thy
  "[| p: intrel;  \
\     !!x1 y1 x2 y2. [| p = <<x1,y1>,<x2,y2>>;  x1#+y2 = x2#+y1; \
\                       x1: nat; y1: nat; x2: nat; y2: nat |] ==> Q |] \
\  ==> Q";
by (cut_facts_tac [major RS (intrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "intrelE";

AddSIs [intrelI];
AddSEs [intrelE];

Goalw [equiv_def, refl_def, sym_def, trans_def]
    "equiv(nat*nat, intrel)";
by (fast_tac (claset() addSEs [sym, integ_trans_lemma]) 1);
qed "equiv_intrel";


Addsimps [equiv_intrel RS eq_equiv_class_iff, intrel_iff,
	  add_0_right, add_succ_right];
Addcongs [conj_cong];

val eq_intrelD = equiv_intrel RSN (2,eq_equiv_class);

(** znat: the injection from nat to integ **)

Goalw [integ_def,quotient_def,znat_def]
    "m : nat ==> $#m : integ";
by (fast_tac (claset() addSIs [nat_0I]) 1);
qed "znat_type";

Addsimps [znat_type];

Goalw [znat_def] "[| $#m = $#n;  m: nat |] ==> m=n";
by (dtac (sym RS eq_intrelD) 1);
by (typechk_tac [nat_0I, SigmaI]);
by (Asm_full_simp_tac 1);
qed "znat_inject";

AddSDs [znat_inject];

Goal "m: nat ==> ($# m = $# n) <-> (m = n)"; 
by (Blast_tac 1); 
qed "znat_znat_eq"; 
Addsimps [znat_znat_eq]; 

(**** zminus: unary negation on integ ****)

Goalw [congruent_def] "congruent(intrel, %<x,y>. intrel``{<y,x>})";
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps add_ac) 1);
qed "zminus_congruent";

(*Resolve th against the corresponding facts for zminus*)
val zminus_ize = RSLIST [equiv_intrel, zminus_congruent];

Goalw [integ_def,zminus_def] "z : integ ==> $~z : integ";
by (typechk_tac [split_type, SigmaI, zminus_ize UN_equiv_class_type,
                 quotientI]);
qed "zminus_type";

Goalw [integ_def,zminus_def] "[| $~z = $~w;  z: integ;  w: integ |] ==> z=w";
by (etac (zminus_ize UN_equiv_class_inject) 1);
by Safe_tac;
(*The setloop is only needed because assumptions are in the wrong order!*)
by (asm_full_simp_tac (simpset() addsimps add_ac
                       setloop dtac eq_intrelD) 1);
qed "zminus_inject";

Goalw [zminus_def]
    "[| x: nat;  y: nat |] ==> $~ (intrel``{<x,y>}) = intrel `` {<y,x>}";
by (asm_simp_tac (simpset() addsimps [zminus_ize UN_equiv_class, SigmaI]) 1);
qed "zminus";

Goalw [integ_def] "z : integ ==> $~ ($~ z) = z";
by (REPEAT (eresolve_tac [quotientE,SigmaE,ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zminus]) 1);
qed "zminus_zminus";

Goalw [integ_def, znat_def] "$~ ($#0) = $#0";
by (simp_tac (simpset() addsimps [zminus]) 1);
qed "zminus_0";

Addsimps [zminus_zminus, zminus_0];


(**** znegative: the test for negative integers ****)

(*No natural number is negative!*)
Goalw [znegative_def, znat_def]  "~ znegative($# n)";
by Safe_tac;
by (dres_inst_tac [("psi", "?lhs=?rhs")] asm_rl 1);
by (dres_inst_tac [("psi", "?lhs<?rhs")] asm_rl 1);
by (force_tac (claset(),
	       simpset() addsimps [add_le_self2 RS le_imp_not_lt]) 1);
qed "not_znegative_znat";

Addsimps [not_znegative_znat];
AddSEs   [not_znegative_znat RS notE];

Goalw [znegative_def, znat_def] "n: nat ==> znegative($~ $# succ(n))";
by (asm_simp_tac (simpset() addsimps [zminus]) 1);
by (blast_tac (claset() addIs [nat_0_le]) 1);
qed "znegative_zminus_znat";

Addsimps [znegative_zminus_znat];

Goalw [znegative_def, znat_def] "[| n: nat; ~ znegative($~ $# n) |] ==> n=0";
by (asm_full_simp_tac (simpset() addsimps [zminus, image_singleton_iff]) 1);
be natE 1;
by (dres_inst_tac [("x","0")] spec 2);
by Auto_tac;
qed "not_znegative_imp_zero";

(**** zmagnitude: magnitide of an integer, as a natural number ****)

Goalw [zmagnitude_def] "n: nat ==> zmagnitude($# n) = n";
by Auto_tac;
qed "zmagnitude_znat";

Goalw [zmagnitude_def] "n: nat ==> zmagnitude($~ $# n) = n";
by (auto_tac(claset() addDs [not_znegative_imp_zero], simpset()));
qed "zmagnitude_zminus_znat";

Addsimps [zmagnitude_znat, zmagnitude_zminus_znat];

Goalw [zmagnitude_def] "zmagnitude(z) : nat";
br theI2 1;
by Auto_tac;
qed "zmagnitude_type";

Goalw [integ_def, znegative_def, znat_def]
     "[| z: integ; ~ znegative(z) |] ==> EX n:nat. z = $# n"; 
by (auto_tac(claset() , simpset() addsimps [image_singleton_iff]));
by (rename_tac "i j" 1);
by (dres_inst_tac [("x", "i")] spec 1);
by (dres_inst_tac [("x", "j")] spec 1);
br bexI 1;
br (add_diff_inverse2 RS sym) 1;
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [nat_into_Ord, not_lt_iff_le]) 1);
qed "not_zneg_znat";

Goal "[| z: integ; ~ znegative(z) |] ==> $# (zmagnitude(z)) = z"; 
bd not_zneg_znat 1;
by Auto_tac;
qed "not_zneg_mag"; 

Addsimps [not_zneg_mag];


Goalw [integ_def, znegative_def, znat_def]
     "[| z: integ; znegative(z) |] ==> EX n:nat. z = $~ ($# succ(n))"; 
by (auto_tac(claset() addSDs [less_imp_Suc_add], 
	     simpset() addsimps [zminus, image_singleton_iff]));
by (rename_tac "m n j k" 1);
by (subgoal_tac "j #+ succ(m #+ k) = j #+ n" 1);
by (rotate_tac ~2 2);
by (asm_full_simp_tac (simpset() addsimps add_ac) 2);
by (blast_tac (claset() addSDs [add_left_cancel]) 1);
qed "zneg_znat";

Goal "[| z: integ; znegative(z) |] ==> $# (zmagnitude(z)) = $~ z"; 
bd zneg_znat 1;
by Auto_tac;
qed "zneg_mag"; 

Addsimps [zneg_mag];


(**** zadd: addition on integ ****)

(** Congruence property for addition **)

Goalw [congruent2_def]
    "congruent2(intrel, %z1 z2.                      \
\         let <x1,y1>=z1; <x2,y2>=z2                 \
\                           in intrel``{<x1#+x2, y1#+y2>})";
(*Proof via congruent2_commuteI seems longer*)
by Safe_tac;
by (asm_simp_tac (simpset() addsimps [add_assoc, Let_def]) 1);
(*The rest should be trivial, but rearranging terms is hard;
  add_ac does not help rewriting with the assumptions.*)
by (res_inst_tac [("m1","x1a")] (add_left_commute RS ssubst) 1);
by (res_inst_tac [("m1","x2a")] (add_left_commute RS ssubst) 3);
by (typechk_tac [add_type]);
by (asm_simp_tac (simpset() addsimps [add_assoc RS sym]) 1);
qed "zadd_congruent2";

(*Resolve th against the corresponding facts for zadd*)
val zadd_ize = RSLIST [equiv_intrel, zadd_congruent2];

Goalw [integ_def,zadd_def] "[| z: integ;  w: integ |] ==> z $+ w : integ";
by (rtac (zadd_ize UN_equiv_class_type2) 1);
by (simp_tac (simpset() addsimps [Let_def]) 3);
by (REPEAT (ares_tac [split_type, add_type, quotientI, SigmaI] 1));
qed "zadd_type";

Goalw [zadd_def]
  "[| x1: nat; y1: nat;  x2: nat; y2: nat |] ==>       \
\           (intrel``{<x1,y1>}) $+ (intrel``{<x2,y2>}) =        \
\           intrel `` {<x1#+x2, y1#+y2>}";
by (asm_simp_tac (simpset() addsimps [zadd_ize UN_equiv_class2, SigmaI]) 1);
by (simp_tac (simpset() addsimps [Let_def]) 1);
qed "zadd";

Goalw [integ_def,znat_def] "z : integ ==> $#0 $+ z = z";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zadd]) 1);
qed "zadd_0";

Goalw [integ_def] "[| z: integ;  w: integ |] ==> $~ (z $+ w) = $~ z $+ $~ w";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zminus,zadd]) 1);
qed "zminus_zadd_distrib";

Goalw [integ_def] "[| z: integ;  w: integ |] ==> z $+ w = w $+ z";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps add_ac @ [zadd]) 1);
qed "zadd_commute";

Goalw [integ_def]
    "[| z1: integ;  z2: integ;  z3: integ |]   \
\    ==> (z1 $+ z2) $+ z3 = z1 $+ (z2 $+ z3)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
(*rewriting is much faster without intrel_iff, etc.*)
by (asm_simp_tac (simpset() addsimps [zadd, add_assoc]) 1);
qed "zadd_assoc";

(*For AC rewriting*)
Goal "[| z1:integ;  z2:integ;  z3: integ |] ==> z1$+(z2$+z3) = z2$+(z1$+z3)";
by (asm_simp_tac (simpset() addsimps [zadd_assoc RS sym, zadd_commute]) 1);
qed "zadd_left_commute";

(*Integer addition is an AC operator*)
val zadd_ac = [zadd_assoc, zadd_commute, zadd_left_commute];

Goalw [znat_def]
    "[| m: nat;  n: nat |] ==> $# (m #+ n) = ($#m) $+ ($#n)";
by (asm_simp_tac (simpset() addsimps [zadd]) 1);
qed "znat_add";

Goalw [integ_def,znat_def] "z : integ ==> z $+ ($~ z) = $#0";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zminus, zadd, add_commute]) 1);
qed "zadd_zminus_inverse";

Goal "z : integ ==> ($~ z) $+ z = $#0";
by (asm_simp_tac
    (simpset() addsimps [zadd_commute, zminus_type, zadd_zminus_inverse]) 1);
qed "zadd_zminus_inverse2";

Goal "z:integ ==> z $+ $#0 = z";
by (rtac (zadd_commute RS trans) 1);
by (REPEAT (ares_tac [znat_type, nat_0I, zadd_0] 1));
qed "zadd_0_right";

Addsimps [zadd_0, zadd_0_right, zadd_zminus_inverse, zadd_zminus_inverse2];


(*Need properties of $- ???  Or use $- just as an abbreviation?
     [| m: nat;  n: nat;  m>=n |] ==> $# (m #- n) = ($#m) $- ($#n)
*)

(**** zmult: multiplication on integ ****)

(** Congruence property for multiplication **)

Goal "congruent2(intrel, %p1 p2.                 \
\               split(%x1 y1. split(%x2 y2.     \
\                   intrel``{<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}, p2), p1))";
by (rtac (equiv_intrel RS congruent2_commuteI) 1);
by Safe_tac;
by (ALLGOALS Asm_simp_tac);
(*Proof that zmult is congruent in one argument*)
by (asm_simp_tac 
    (simpset() addsimps add_ac @ [add_mult_distrib_left RS sym]) 2);
by (asm_simp_tac
    (simpset() addsimps [add_assoc RS sym, add_mult_distrib_left RS sym]) 2);
(*Proof that zmult is commutative on representatives*)
by (asm_simp_tac (simpset() addsimps mult_ac@add_ac) 1);
qed "zmult_congruent2";


(*Resolve th against the corresponding facts for zmult*)
val zmult_ize = RSLIST [equiv_intrel, zmult_congruent2];

Goalw [integ_def,zmult_def] "[| z: integ;  w: integ |] ==> z $* w : integ";
by (REPEAT (ares_tac [zmult_ize UN_equiv_class_type2,
                      split_type, add_type, mult_type, 
                      quotientI, SigmaI] 1));
qed "zmult_type";

Goalw [zmult_def]
     "[| x1: nat; y1: nat;  x2: nat; y2: nat |] ==>    \
\              (intrel``{<x1,y1>}) $* (intrel``{<x2,y2>}) =     \
\              intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}";
by (asm_simp_tac (simpset() addsimps [zmult_ize UN_equiv_class2, SigmaI]) 1);
qed "zmult";

Goalw [integ_def,znat_def] "z : integ ==> $#0 $* z = $#0";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zmult]) 1);
qed "zmult_0";

Goalw [integ_def,znat_def] "z : integ ==> $#1 $* z = z";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zmult, add_0_right]) 1);
qed "zmult_1";

Goalw [integ_def] "[| z: integ;  w: integ |] ==> ($~ z) $* w = $~ (z $* w)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zminus, zmult] @ add_ac) 1);
qed "zmult_zminus";

Addsimps [zmult_0, zmult_1, zmult_zminus];

Goalw [integ_def] "[| z: integ;  w: integ |] ==> ($~ z) $* ($~ w) = (z $* w)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zminus, zmult] @ add_ac) 1);
qed "zmult_zminus_zminus";

Goalw [integ_def] "[| z: integ;  w: integ |] ==> z $* w = w $* z";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zmult] @ add_ac @ mult_ac) 1);
qed "zmult_commute";

Goalw [integ_def]
    "[| z1: integ;  z2: integ;  z3: integ |]     \
\    ==> (z1 $* z2) $* z3 = z1 $* (z2 $* z3)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac 
    (simpset() addsimps [zmult, add_mult_distrib_left, 
                         add_mult_distrib] @ add_ac @ mult_ac) 1);
qed "zmult_assoc";

(*For AC rewriting*)
Goal "[| z1:integ;  z2:integ;  z3: integ |] ==> z1$*(z2$*z3) = z2$*(z1$*z3)";
by (asm_simp_tac (simpset() addsimps [zmult_assoc RS sym, zmult_commute]) 1);
qed "zmult_left_commute";

(*Integer multiplication is an AC operator*)
val zmult_ac = [zmult_assoc, zmult_commute, zmult_left_commute];

Goalw [integ_def]
    "[| z1: integ;  z2: integ;  w: integ |] ==> \
\                (z1 $+ z2) $* w = (z1 $* w) $+ (z2 $* w)";
by (REPEAT (eresolve_tac [quotientE, SigmaE, ssubst] 1));
by (asm_simp_tac (simpset() addsimps [zadd, zmult, add_mult_distrib]) 1);
by (asm_simp_tac (simpset() addsimps add_ac @ mult_ac) 1);
qed "zadd_zmult_distrib";

val integ_typechecks =
    [znat_type, zminus_type, zmagnitude_type, zadd_type, zmult_type];

Addsimps integ_typechecks;



