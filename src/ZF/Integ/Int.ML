(*  Title:      ZF/Integ/Int.ML
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

(** Natural deduction for intrel **)

Goalw [intrel_def]
    "<<x1,y1>,<x2,y2>>: intrel <-> \
\    x1: nat & y1: nat & x2: nat & y2: nat & x1#+y2 = x2#+y1";
by (Fast_tac 1);
qed "intrel_iff";

Goalw [intrel_def]
    "[| x1#+y2 = x2#+y1; x1: nat; y1: nat; x2: nat; y2: nat |]  \
\    ==> <<x1,y1>,<x2,y2>>: intrel";
by (fast_tac (claset() addIs prems) 1);
qed "intrelI";

(*intrelE is hard to derive because fast_tac tries hyp_subst_tac so soon*)
Goalw [intrel_def]
  "p: intrel --> (EX x1 y1 x2 y2. \
\                  p = <<x1,y1>,<x2,y2>> & x1#+y2 = x2#+y1 & \
\                  x1: nat & y1: nat & x2: nat & y2: nat)";
by (Fast_tac 1);
qed "intrelE_lemma";

val [major,minor] = goal thy
  "[| p: intrel;  \
\     !!x1 y1 x2 y2. [| p = <<x1,y1>,<x2,y2>>;  x1#+y2 = x2#+y1; \
\                       x1: nat; y1: nat; x2: nat; y2: nat |] ==> Q |] \
\  ==> Q";
by (cut_facts_tac [major RS (intrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "intrelE";

AddSIs [intrelI];
AddSEs [intrelE];

val eqa::eqb::prems = goal Arith.thy 
    "[| x1 #+ y2 = x2 #+ y1; x2 #+ y3 = x3 #+ y2 |] ==> x1 #+ y3 = x3 #+ y1";
by (res_inst_tac [("k","x2")] add_left_cancel 1);
by (rtac (add_left_commute RS trans) 1);
by Auto_tac;
by (stac eqb 1);
by (rtac (add_left_commute RS trans) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [eqa, add_left_commute])));
qed "int_trans_lemma";

Goalw [equiv_def, refl_def, sym_def, trans_def]
    "equiv(nat*nat, intrel)";
by (fast_tac (claset() addSEs [sym, int_trans_lemma]) 1);
qed "equiv_intrel";


Goalw [int_def] "[| m: nat; n: nat |] ==> intrel `` {<m,n>} : int";
by (blast_tac (claset() addIs [quotientI]) 1);
qed "image_intrel_int";


Addsimps [equiv_intrel RS eq_equiv_class_iff, intrel_iff,
	  add_0_right, add_succ_right];
Addcongs [conj_cong];

val eq_intrelD = equiv_intrel RSN (2,eq_equiv_class);

(** int_of: the injection from nat to int **)

Goalw [int_def,quotient_def,int_of_def]  "$#m : int";
by Auto_tac;
qed "int_of_type";

AddIffs [int_of_type];
AddTCs  [int_of_type];


Goalw [int_of_def] "($# m = $# n) <-> natify(m)=natify(n)"; 
by Auto_tac;  
qed "int_of_eq"; 
AddIffs [int_of_eq];

Goal "[| $#m = $#n;  m: nat;  n: nat |] ==> m=n";
by (dtac (int_of_eq RS iffD1) 1);
by Auto_tac;
qed "int_of_inject";


(** intify: coercion from anything to int **)

Goal "intify(x) : int";
by (simp_tac (simpset() addsimps [intify_def]) 1);
qed "intify_in_int";
AddIffs [intify_in_int];
AddTCs [intify_in_int];

Goal "n : int ==> intify(n) = n";
by (asm_simp_tac (simpset() addsimps [intify_def]) 1);
qed "intify_ident";
Addsimps [intify_ident];


(*** Collapsing rules: to remove intify from arithmetic expressions ***)

Goal "intify(intify(x)) = intify(x)";
by (Simp_tac 1);
qed "intify_idem";
Addsimps [intify_idem];

Goal "$# (natify(m)) = $# m";
by (simp_tac (simpset() addsimps [int_of_def]) 1);
qed "int_of_natify";

Goal "$~ (intify(m)) = $~ m";
by (simp_tac (simpset() addsimps [zminus_def]) 1);
qed "zminus_intify";

Addsimps [int_of_natify, zminus_intify];

(** Addition **)

Goal "intify(x) $+ y = x $+ y";
by (simp_tac (simpset() addsimps [zadd_def]) 1);
qed "zadd_intify1";

Goal "x $+ intify(y) = x $+ y";
by (simp_tac (simpset() addsimps [zadd_def]) 1);
qed "zadd_intify2";
Addsimps [zadd_intify1, zadd_intify2];

(** Multiplication **)

Goal "intify(x) $* y = x $* y";
by (simp_tac (simpset() addsimps [zmult_def]) 1);
qed "zmult_intify1";

Goal "x $* intify(y) = x $* y";
by (simp_tac (simpset() addsimps [zmult_def]) 1);
qed "zmult_intify2";
Addsimps [zmult_intify1, zmult_intify2];


(**** zminus: unary negation on int ****)

Goalw [congruent_def] "congruent(intrel, %<x,y>. intrel``{<y,x>})";
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps add_ac) 1);
qed "zminus_congruent";

val RSLIST = curry (op MRS);

(*Resolve th against the corresponding facts for zminus*)
val zminus_ize = RSLIST [equiv_intrel, zminus_congruent];

Goalw [int_def,raw_zminus_def] "z : int ==> raw_zminus(z) : int";
by (typecheck_tac (tcset() addTCs [zminus_ize UN_equiv_class_type]));
qed "raw_zminus_type";

Goalw [zminus_def] "$~z : int";
by (simp_tac (simpset() addsimps [zminus_def, raw_zminus_type]) 1);
qed "zminus_type";
AddIffs [zminus_type];
AddTCs [zminus_type];


Goalw [int_def,raw_zminus_def]
     "[| raw_zminus(z) = raw_zminus(w);  z: int;  w: int |] ==> z=w";
by (etac (zminus_ize UN_equiv_class_inject) 1);
by Safe_tac;
by (auto_tac (claset() addDs [eq_intrelD], simpset() addsimps add_ac));  
qed "raw_zminus_inject";

Goalw [zminus_def] "$~z = $~w ==> intify(z) = intify(w)";
by (blast_tac (claset() addSDs [raw_zminus_inject]) 1);
qed "zminus_inject_intify";

AddSDs [zminus_inject_intify];

Goal "[| $~z = $~w;  z: int;  w: int |] ==> z=w";
by Auto_tac;  
qed "zminus_inject";

Goalw [raw_zminus_def]
    "[| x: nat;  y: nat |] \
\    ==> raw_zminus(intrel``{<x,y>}) = intrel `` {<y,x>}";
by (asm_simp_tac (simpset() addsimps [zminus_ize UN_equiv_class, SigmaI]) 1);
qed "raw_zminus";

Goalw [zminus_def]
    "[| x: nat;  y: nat |] \
\    ==> $~ (intrel``{<x,y>}) = intrel `` {<y,x>}";
by (asm_simp_tac (simpset() addsimps [raw_zminus, image_intrel_int]) 1);
qed "zminus";

Goalw [int_def] "z : int ==> raw_zminus (raw_zminus(z)) = z";
by (auto_tac (claset(), simpset() addsimps [raw_zminus]));  
qed "raw_zminus_zminus";

Goal "$~ ($~ z) = intify(z)";
by (simp_tac (simpset() addsimps [zminus_def, raw_zminus_type, 
	                          raw_zminus_zminus]) 1);
qed "zminus_zminus_intify"; 

Goalw [int_of_def] "$~ ($#0) = $#0";
by (simp_tac (simpset() addsimps [zminus]) 1);
qed "zminus_0";

Addsimps [zminus_zminus_intify, zminus_0];

Goal "z : int ==> $~ ($~ z) = z";
by (Asm_simp_tac 1);
qed "zminus_zminus";


(**** znegative: the test for negative integers ****)

(*No natural number is negative!*)
Goalw [znegative_def, int_of_def]  "~ znegative($# n)";
by Safe_tac;
by (dres_inst_tac [("psi", "?lhs=?rhs")] asm_rl 1);
by (dres_inst_tac [("psi", "?lhs<?rhs")] asm_rl 1);
by (force_tac (claset(),
	       simpset() addsimps [add_le_self2 RS le_imp_not_lt]) 1);
qed "not_znegative_int_of";

Addsimps [not_znegative_int_of];
AddSEs   [not_znegative_int_of RS notE];

Goalw [znegative_def, int_of_def] "znegative($~ $# succ(n))";
by (asm_simp_tac (simpset() addsimps [zminus]) 1);
by (blast_tac (claset() addIs [nat_0_le]) 1);
qed "znegative_zminus_int_of";

Addsimps [znegative_zminus_int_of];

Goalw [znegative_def, int_of_def] "~ znegative($~ $# n) ==> natify(n)=0";
by (asm_full_simp_tac (simpset() addsimps [zminus, image_singleton_iff]) 1);
by (dres_inst_tac [("x","0")] spec 1);
by (auto_tac(claset(), 
             simpset() addsimps [nat_into_Ord RS Ord_0_lt_iff RS iff_sym]));
qed "not_znegative_imp_zero";

(**** zmagnitude: magnitide of an integer, as a natural number ****)

Goalw [zmagnitude_def] "zmagnitude($# n) = natify(n)";
by (auto_tac (claset(), simpset() addsimps [int_of_eq]));  
qed "zmagnitude_int_of";

Goal "natify(x)=n ==> $#x = $# n";
by (dtac sym 1);
by (asm_simp_tac (simpset() addsimps [int_of_eq]) 1);
qed "natify_int_of_eq";

Goalw [zmagnitude_def] "zmagnitude($~ $# n) = natify(n)";
by (rtac the_equality 1);
by (auto_tac((claset() addSDs [not_znegative_imp_zero, natify_int_of_eq], 
              simpset())
             delIffs [int_of_eq]));
by Auto_tac;  
qed "zmagnitude_zminus_int_of";

Addsimps [zmagnitude_int_of, zmagnitude_zminus_int_of];

Goalw [zmagnitude_def] "zmagnitude(z) : nat";
by (rtac theI2 1);
by Auto_tac;
qed "zmagnitude_type";
AddTCs [zmagnitude_type];

Goalw [int_def, znegative_def, int_of_def]
     "[| z: int; ~ znegative(z) |] ==> EX n:nat. z = $# n"; 
by (auto_tac(claset() , simpset() addsimps [image_singleton_iff]));
by (rename_tac "i j" 1);
by (dres_inst_tac [("x", "i")] spec 1);
by (dres_inst_tac [("x", "j")] spec 1);
by (rtac bexI 1);
by (rtac (add_diff_inverse2 RS sym) 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [not_lt_iff_le]) 1);
qed "not_zneg_int_of";

Goal "[| z: int; ~ znegative(z) |] ==> $# (zmagnitude(z)) = z"; 
by (dtac not_zneg_int_of 1);
by Auto_tac;
qed "not_zneg_mag"; 

Addsimps [not_zneg_mag];


Goalw [int_def, znegative_def, int_of_def]
     "[| z: int; znegative(z) |] ==> EX n:nat. z = $~ ($# succ(n))"; 
by (auto_tac(claset() addSDs [less_imp_Suc_add], 
	     simpset() addsimps [zminus, image_singleton_iff]));
by (rename_tac "m n j k" 1);
by (subgoal_tac "j #+ succ(m #+ k) = j #+ n" 1);
by (rotate_tac ~2 2);
by (asm_full_simp_tac (simpset() addsimps add_ac) 2);
by (blast_tac (claset() addSDs [add_left_cancel]) 1);
qed "zneg_int_of";

Goal "[| z: int; znegative(z) |] ==> $# (zmagnitude(z)) = $~ z"; 
by (dtac zneg_int_of 1);
by Auto_tac;
qed "zneg_mag"; 

Addsimps [zneg_mag];


(**** zadd: addition on int ****)

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
by (res_inst_tac [("m1","x2a")] (add_left_commute RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [add_assoc RS sym]) 1);
qed "zadd_congruent2";

(*Resolve th against the corresponding facts for zadd*)
val zadd_ize = RSLIST [equiv_intrel, zadd_congruent2];

Goalw [int_def,raw_zadd_def] "[| z: int;  w: int |] ==> raw_zadd(z,w) : int";
by (rtac (zadd_ize UN_equiv_class_type2) 1);
by (simp_tac (simpset() addsimps [Let_def]) 3);
by (REPEAT (assume_tac 1));
qed "raw_zadd_type";

Goal "z $+ w : int";
by (simp_tac (simpset() addsimps [zadd_def, raw_zadd_type]) 1);
qed "zadd_type";
AddIffs [zadd_type];  AddTCs [zadd_type];

Goalw [raw_zadd_def]
  "[| x1: nat; y1: nat;  x2: nat; y2: nat |]              \
\  ==> raw_zadd (intrel``{<x1,y1>}, intrel``{<x2,y2>}) =  \
\      intrel `` {<x1#+x2, y1#+y2>}";
by (asm_simp_tac (simpset() addsimps [zadd_ize UN_equiv_class2, SigmaI]) 1);
by (simp_tac (simpset() addsimps [Let_def]) 1);
qed "raw_zadd";

Goalw [zadd_def]
  "[| x1: nat; y1: nat;  x2: nat; y2: nat |]         \
\  ==> (intrel``{<x1,y1>}) $+ (intrel``{<x2,y2>}) =  \
\      intrel `` {<x1#+x2, y1#+y2>}";
by (asm_simp_tac (simpset() addsimps [raw_zadd, image_intrel_int]) 1);
qed "zadd";

Goalw [int_def,int_of_def] "z : int ==> raw_zadd ($#0,z) = z";
by (auto_tac (claset(), simpset() addsimps [raw_zadd]));  
qed "raw_zadd_0";

Goal "$#0 $+ z = intify(z)";
by (asm_simp_tac (simpset() addsimps [zadd_def, raw_zadd_0]) 1);
qed "zadd_0_intify";
Addsimps [zadd_0_intify];

Goal "z: int ==> $#0 $+ z = z";
by (Asm_simp_tac 1);
qed "zadd_0";

Goalw [int_def]
     "[| z: int;  w: int |] ==> $~ raw_zadd(z,w) = raw_zadd($~ z, $~ w)";
by (auto_tac (claset(), simpset() addsimps [zminus,raw_zadd]));  
qed "raw_zminus_zadd_distrib";

Goal "$~ (z $+ w) = $~ z $+ $~ w";
by (simp_tac (simpset() addsimps [zadd_def, raw_zminus_zadd_distrib]) 1);
qed "zminus_zadd_distrib";

Goalw [int_def] "[| z: int;  w: int |] ==> raw_zadd(z,w) = raw_zadd(w,z)";
by (auto_tac (claset(), simpset() addsimps raw_zadd::add_ac));  
qed "raw_zadd_commute";

Goal "z $+ w = w $+ z";
by (simp_tac (simpset() addsimps [zadd_def, raw_zadd_commute]) 1);
qed "zadd_commute";

Goalw [int_def]
    "[| z1: int;  z2: int;  z3: int |]   \
\    ==> raw_zadd (raw_zadd(z1,z2),z3) = raw_zadd(z1,raw_zadd(z2,z3))";
by (auto_tac (claset(), simpset() addsimps [raw_zadd, add_assoc]));  
qed "raw_zadd_assoc";

Goal "(z1 $+ z2) $+ z3 = z1 $+ (z2 $+ z3)";
by (simp_tac (simpset() addsimps [zadd_def, raw_zadd_type, raw_zadd_assoc]) 1);
qed "zadd_assoc";

(*For AC rewriting*)
Goal "z1$+(z2$+z3) = z2$+(z1$+z3)";
by (asm_simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
by (asm_simp_tac (simpset() addsimps [zadd_commute]) 1);
qed "zadd_left_commute";

(*Integer addition is an AC operator*)
val zadd_ac = [zadd_assoc, zadd_commute, zadd_left_commute];

Goalw [int_of_def] "$# (m #+ n) = ($#m) $+ ($#n)";
by (asm_simp_tac (simpset() addsimps [zadd]) 1);
qed "int_of_add";

Goalw [int_def,int_of_def] "z : int ==> raw_zadd (z, $~ z) = $#0";
by (auto_tac (claset(), simpset() addsimps [zminus, raw_zadd, add_commute]));  
qed "raw_zadd_zminus_inverse";

Goal "z $+ ($~ z) = $#0";
by (simp_tac (simpset() addsimps [zadd_def]) 1);
by (stac (zminus_intify RS sym) 1);
by (rtac (intify_in_int RS raw_zadd_zminus_inverse) 1); 
qed "zadd_zminus_inverse";

Goal "($~ z) $+ z = $#0";
by (simp_tac (simpset() addsimps [zadd_commute, zadd_zminus_inverse]) 1);
qed "zadd_zminus_inverse2";

Goal "z $+ $#0 = intify(z)";
by (rtac ([zadd_commute, zadd_0_intify] MRS trans) 1);
qed "zadd_0_right_intify";
Addsimps [zadd_0_right_intify];

Goal "z:int ==> z $+ $#0 = z";
by (Asm_simp_tac 1);
qed "zadd_0_right";

Addsimps [zadd_zminus_inverse, zadd_zminus_inverse2];


(*Need properties of $- ???  Or use $- just as an abbreviation?
     [| m: nat;  n: nat;  n le m |] ==> $# (m #- n) = ($#m) $- ($#n)
*)

(**** zmult: multiplication on int ****)

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

Goalw [int_def,raw_zmult_def] "[| z: int;  w: int |] ==> raw_zmult(z,w) : int";
by (REPEAT (ares_tac [zmult_ize UN_equiv_class_type2,
                      split_type, add_type, mult_type, 
                      quotientI, SigmaI] 1));
qed "raw_zmult_type";

Goal "z $* w : int";
by (simp_tac (simpset() addsimps [zmult_def, raw_zmult_type]) 1);
qed "zmult_type";
AddIffs [zmult_type];  AddTCs [zmult_type];

Goalw [raw_zmult_def]
     "[| x1: nat; y1: nat;  x2: nat; y2: nat |]    \
\     ==> raw_zmult(intrel``{<x1,y1>}, intrel``{<x2,y2>}) =     \
\         intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}";
by (asm_simp_tac (simpset() addsimps [zmult_ize UN_equiv_class2, SigmaI]) 1);
qed "raw_zmult";

Goalw [zmult_def]
     "[| x1: nat; y1: nat;  x2: nat; y2: nat |]    \
\     ==> (intrel``{<x1,y1>}) $* (intrel``{<x2,y2>}) =     \
\         intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}";
by (asm_simp_tac (simpset() addsimps [raw_zmult, image_intrel_int]) 1);
qed "zmult";

Goalw [int_def,int_of_def] "z : int ==> raw_zmult ($#0,z) = $#0";
by (auto_tac (claset(), simpset() addsimps [raw_zmult]));  
qed "raw_zmult_0";

Goal "$#0 $* z = $#0";
by (simp_tac (simpset() addsimps [zmult_def, raw_zmult_0]) 1);
qed "zmult_0";
Addsimps [zmult_0];

Goalw [int_def,int_of_def] "z : int ==> raw_zmult ($#1,z) = z";
by (auto_tac (claset(), simpset() addsimps [raw_zmult]));  
qed "raw_zmult_1";

Goal "$#1 $* z = intify(z)";
by (simp_tac (simpset() addsimps [zmult_def, raw_zmult_1]) 1);
qed "zmult_1_intify";
Addsimps [zmult_1_intify];

Goal "z : int ==> $#1 $* z = z";
by (Asm_simp_tac 1);
qed "zmult_1";

Goalw [int_def] "[| z: int;  w: int |] ==> raw_zmult(z,w) = raw_zmult(w,z)";
by (auto_tac (claset(), simpset() addsimps [raw_zmult] @ add_ac @ mult_ac));  
qed "raw_zmult_commute";

Goal "z $* w = w $* z";
by (simp_tac (simpset() addsimps [zmult_def, raw_zmult_commute]) 1);
qed "zmult_commute";

Goalw [int_def]
     "[| z: int;  w: int |] ==> raw_zmult($~ z, w) = $~ raw_zmult(z, w)";
by (auto_tac (claset(), simpset() addsimps [zminus, raw_zmult] @ add_ac));  
qed "raw_zmult_zminus";

Goal "($~ z) $* w = $~ (z $* w)";
by (simp_tac (simpset() addsimps [zmult_def, raw_zmult_zminus]) 1);
by (stac (zminus_intify RS sym) 1 THEN rtac raw_zmult_zminus 1); 
by Auto_tac;  
qed "zmult_zminus";
Addsimps [zmult_zminus];

Goal "($~ z) $* ($~ w) = (z $* w)";
by (stac zmult_zminus 1);
by (stac zmult_commute 1 THEN stac zmult_zminus 1);
by (simp_tac (simpset() addsimps [zmult_commute])1);
qed "zmult_zminus_zminus";

Goalw [int_def]
    "[| z1: int;  z2: int;  z3: int |]   \
\    ==> raw_zmult (raw_zmult(z1,z2),z3) = raw_zmult(z1,raw_zmult(z2,z3))";
by (auto_tac (claset(), 
  simpset() addsimps [raw_zmult, add_mult_distrib_left] @ add_ac @ mult_ac));  
qed "raw_zmult_assoc";

Goal "(z1 $* z2) $* z3 = z1 $* (z2 $* z3)";
by (simp_tac (simpset() addsimps [zmult_def, raw_zmult_type, 
                                  raw_zmult_assoc]) 1);
qed "zmult_assoc";

(*For AC rewriting*)
Goal "z1$*(z2$*z3) = z2$*(z1$*z3)";
by (asm_simp_tac (simpset() addsimps [zmult_assoc RS sym]) 1);
by (asm_simp_tac (simpset() addsimps [zmult_commute]) 1);
qed "zmult_left_commute";

(*Integer multiplication is an AC operator*)
val zmult_ac = [zmult_assoc, zmult_commute, zmult_left_commute];

Goalw [int_def]
    "[| z1: int;  z2: int;  w: int |]  \
\    ==> raw_zmult(raw_zadd(z1,z2), w) = \
\        raw_zadd (raw_zmult(z1,w), raw_zmult(z2,w))";
by (auto_tac (claset(), 
              simpset() addsimps [raw_zadd, raw_zmult, add_mult_distrib_left] @ 
                                 add_ac @ mult_ac));  
qed "raw_zadd_zmult_distrib";

Goal "(z1 $+ z2) $* w = (z1 $* w) $+ (z2 $* w)";
by (simp_tac (simpset() addsimps [zmult_def, zadd_def, raw_zadd_type, 
     	                          raw_zmult_type, raw_zadd_zmult_distrib]) 1);
qed "zadd_zmult_distrib";

Goal "w $* (z1 $+ z2) = (w $* z1) $+ (w $* z2)";
by (simp_tac (simpset() addsimps [inst "z" "w" zmult_commute,
                                  zadd_zmult_distrib]) 1);
qed "zadd_zmult_distrib_left";

val int_typechecks =
    [int_of_type, zminus_type, zmagnitude_type, zadd_type, zmult_type];


