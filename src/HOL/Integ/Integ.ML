(*  Title:      Integ.ML
    ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The integers as equivalence classes over nat*nat.

Could also prove...
"znegative(z) ==> $# zmagnitude(z) = $~ z"
"~ znegative(z) ==> $# zmagnitude(z) = z"
< is a linear ordering
+ and * are monotonic wrt <
*)

open Integ;

Delrules [equalityI];


(*** Proving that intrel is an equivalence relation ***)

val eqa::eqb::prems = goal Arith.thy 
    "[| (x1::nat) + y2 = x2 + y1; x2 + y3 = x3 + y2 |] ==> \
\       x1 + y3 = x3 + y1";
by (res_inst_tac [("k1","x2")] (add_left_cancel RS iffD1) 1);
by (rtac (add_left_commute RS trans) 1);
by (stac eqb 1);
by (rtac (add_left_commute RS trans) 1);
by (stac eqa 1);
by (rtac (add_left_commute) 1);
qed "integ_trans_lemma";

(** Natural deduction for intrel **)

val prems = goalw Integ.thy [intrel_def]
    "[| x1+y2 = x2+y1|] ==> \
\    ((x1,y1),(x2,y2)): intrel";
by (fast_tac (claset() addIs prems) 1);
qed "intrelI";

(*intrelE is hard to derive because fast_tac tries hyp_subst_tac so soon*)
goalw Integ.thy [intrel_def]
  "p: intrel --> (EX x1 y1 x2 y2. \
\                  p = ((x1,y1),(x2,y2)) & x1+y2 = x2+y1)";
by (Fast_tac 1);
qed "intrelE_lemma";

val [major,minor] = goal Integ.thy
  "[| p: intrel;  \
\     !!x1 y1 x2 y2. [| p = ((x1,y1),(x2,y2));  x1+y2 = x2+y1|] ==> Q |] \
\  ==> Q";
by (cut_facts_tac [major RS (intrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "intrelE";

AddSIs [intrelI];
AddSEs [intrelE];

goal Integ.thy "((x1,y1),(x2,y2)): intrel = (x1+y2 = x2+y1)";
by (Fast_tac 1);
qed "intrel_iff";

goal Integ.thy "(x,x): intrel";
by (stac surjective_pairing 1 THEN rtac (refl RS intrelI) 1);
qed "intrel_refl";

goalw Integ.thy [equiv_def, refl_def, sym_def, trans_def]
    "equiv {x::(nat*nat).True} intrel";
by (fast_tac (claset() addSIs [intrel_refl] 
                        addSEs [sym, integ_trans_lemma]) 1);
qed "equiv_intrel";

val equiv_intrel_iff =
    [TrueI, TrueI] MRS 
    ([CollectI, CollectI] MRS 
    (equiv_intrel RS eq_equiv_class_iff));

goalw Integ.thy  [Integ_def,intrel_def,quotient_def] "intrel^^{(x,y)}:Integ";
by (Fast_tac 1);
qed "intrel_in_integ";

goal Integ.thy "inj_onto Abs_Integ Integ";
by (rtac inj_onto_inverseI 1);
by (etac Abs_Integ_inverse 1);
qed "inj_onto_Abs_Integ";

Addsimps [equiv_intrel_iff, inj_onto_Abs_Integ RS inj_onto_iff,
          intrel_iff, intrel_in_integ, Abs_Integ_inverse];

goal Integ.thy "inj(Rep_Integ)";
by (rtac inj_inverseI 1);
by (rtac Rep_Integ_inverse 1);
qed "inj_Rep_Integ";




(** znat: the injection from nat to Integ **)

goal Integ.thy "inj(znat)";
by (rtac injI 1);
by (rewtac znat_def);
by (dtac (inj_onto_Abs_Integ RS inj_ontoD) 1);
by (REPEAT (rtac intrel_in_integ 1));
by (dtac eq_equiv_class 1);
by (rtac equiv_intrel 1);
by (Fast_tac 1);
by Safe_tac;
by (Asm_full_simp_tac 1);
qed "inj_znat";


(**** zminus: unary negation on Integ ****)

goalw Integ.thy [congruent_def]
  "congruent intrel (%p. split (%x y. intrel^^{(y,x)}) p)";
by Safe_tac;
by (asm_simp_tac (simpset() addsimps add_ac) 1);
qed "zminus_congruent";


(*Resolve th against the corresponding facts for zminus*)
val zminus_ize = RSLIST [equiv_intrel, zminus_congruent];

goalw Integ.thy [zminus_def]
      "$~ Abs_Integ(intrel^^{(x,y)}) = Abs_Integ(intrel ^^ {(y,x)})";
by (res_inst_tac [("f","Abs_Integ")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [intrel_in_integ RS Abs_Integ_inverse,zminus_ize UN_equiv_class]) 1);
qed "zminus";

(*by lcp*)
val [prem] = goal Integ.thy
    "(!!x y. z = Abs_Integ(intrel^^{(x,y)}) ==> P) ==> P";
by (res_inst_tac [("x1","z")] 
    (rewrite_rule [Integ_def] Rep_Integ RS quotientE) 1);
by (dres_inst_tac [("f","Abs_Integ")] arg_cong 1);
by (res_inst_tac [("p","x")] PairE 1);
by (rtac prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_Integ_inverse]) 1);
qed "eq_Abs_Integ";

goal Integ.thy "$~ ($~ z) = z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zminus]) 1);
qed "zminus_zminus";

goal Integ.thy "inj(zminus)";
by (rtac injI 1);
by (dres_inst_tac [("f","zminus")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [zminus_zminus]) 1);
qed "inj_zminus";

goalw Integ.thy [znat_def] "$~ ($#0) = $#0";
by (simp_tac (simpset() addsimps [zminus]) 1);
qed "zminus_0";


(**** znegative: the test for negative integers ****)


goalw Integ.thy [znegative_def, znat_def]
    "~ znegative($# n)";
by (Simp_tac 1);
by Safe_tac;
qed "not_znegative_znat";

goalw Integ.thy [znegative_def, znat_def] "znegative($~ $# Suc(n))";
by (simp_tac (simpset() addsimps [zminus]) 1);
qed "znegative_zminus_znat";


(**** zmagnitude: magnitide of an integer, as a natural number ****)

goal Arith.thy "!!n::nat. n - Suc(n+m)=0";
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_Suc_add_0";

goal Arith.thy "Suc((n::nat)+m)-n=Suc(m)";
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_Suc_add_inverse";

goalw Integ.thy [congruent_def]
    "congruent intrel (split (%x y. intrel^^{((y-x) + (x-(y::nat)),0)}))";
by Safe_tac;
by (Asm_simp_tac 1);
by (etac rev_mp 1);
by (res_inst_tac [("m","x1"),("n","y1")] diff_induct 1);
by (asm_simp_tac (simpset() addsimps [inj_Suc RS inj_eq]) 3);
by (asm_simp_tac (simpset() addsimps [diff_add_inverse,diff_add_0]) 2);
by (Asm_simp_tac 1);
by (rtac impI 1);
by (etac subst 1);
by (res_inst_tac [("m1","x")] (add_commute RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [diff_add_inverse,diff_add_0]) 1);
qed "zmagnitude_congruent";

(*Resolve th against the corresponding facts for zmagnitude*)
val zmagnitude_ize = RSLIST [equiv_intrel, zmagnitude_congruent];


goalw Integ.thy [zmagnitude_def]
    "zmagnitude (Abs_Integ(intrel^^{(x,y)})) = \
\    Abs_Integ(intrel^^{((y - x) + (x - y),0)})";
by (res_inst_tac [("f","Abs_Integ")] arg_cong 1);
by (asm_simp_tac (simpset() addsimps [zmagnitude_ize UN_equiv_class]) 1);
qed "zmagnitude";

goalw Integ.thy [znat_def] "zmagnitude($# n) = $#n";
by (asm_simp_tac (simpset() addsimps [zmagnitude]) 1);
qed "zmagnitude_znat";

goalw Integ.thy [znat_def] "zmagnitude($~ $# n) = $#n";
by (asm_simp_tac (simpset() addsimps [zmagnitude, zminus]) 1);
qed "zmagnitude_zminus_znat";


(**** zadd: addition on Integ ****)

(** Congruence property for addition **)

goalw Integ.thy [congruent2_def]
    "congruent2 intrel (%p1 p2.                  \
\         split (%x1 y1. split (%x2 y2. intrel^^{(x1+x2, y1+y2)}) p2) p1)";
(*Proof via congruent2_commuteI seems longer*)
by Safe_tac;
by (asm_simp_tac (simpset() addsimps [add_assoc]) 1);
(*The rest should be trivial, but rearranging terms is hard*)
by (res_inst_tac [("x1","x1a")] (add_left_commute RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [add_assoc RS sym]) 1);
qed "zadd_congruent2";

(*Resolve th against the corresponding facts for zadd*)
val zadd_ize = RSLIST [equiv_intrel, zadd_congruent2];

goalw Integ.thy [zadd_def]
  "Abs_Integ(intrel^^{(x1,y1)}) + Abs_Integ(intrel^^{(x2,y2)}) = \
\  Abs_Integ(intrel^^{(x1+x2, y1+y2)})";
by (asm_simp_tac
    (simpset() addsimps [zadd_ize UN_equiv_class2]) 1);
qed "zadd";

goalw Integ.thy [znat_def] "$#0 + z = z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zadd]) 1);
qed "zadd_0";

goal Integ.thy "$~ (z + w) = $~ z + $~ w";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zminus,zadd]) 1);
qed "zminus_zadd_distrib";

goal Integ.thy "(z::int) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps (add_ac @ [zadd])) 1);
qed "zadd_commute";

goal Integ.thy "((z1::int) + z2) + z3 = z1 + (z2 + z3)";
by (res_inst_tac [("z","z1")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z2")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z3")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zadd, add_assoc]) 1);
qed "zadd_assoc";

(*For AC rewriting*)
goal Integ.thy "(x::int)+(y+z)=y+(x+z)";
by (rtac (zadd_commute RS trans) 1);
by (rtac (zadd_assoc RS trans) 1);
by (rtac (zadd_commute RS arg_cong) 1);
qed "zadd_left_commute";

(*Integer addition is an AC operator*)
val zadd_ac = [zadd_assoc,zadd_commute,zadd_left_commute];

goalw Integ.thy [znat_def] "$# (m + n) = ($#m) + ($#n)";
by (asm_simp_tac (simpset() addsimps [zadd]) 1);
qed "znat_add";

goalw Integ.thy [znat_def] "z + ($~ z) = $#0";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zminus, zadd, add_commute]) 1);
qed "zadd_zminus_inverse";

goal Integ.thy "($~ z) + z = $#0";
by (rtac (zadd_commute RS trans) 1);
by (rtac zadd_zminus_inverse 1);
qed "zadd_zminus_inverse2";

goal Integ.thy "z + $#0 = z";
by (rtac (zadd_commute RS trans) 1);
by (rtac zadd_0 1);
qed "zadd_0_right";


(** Lemmas **)

qed_goal "zadd_assoc_cong" Integ.thy
    "!!z. (z::int) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
 (fn _ => [(asm_simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1)]);

qed_goal "zadd_assoc_swap" Integ.thy "(z::int) + (v + w) = v + (z + w)"
 (fn _ => [(REPEAT (ares_tac [zadd_commute RS zadd_assoc_cong] 1))]);


(*Need properties of subtraction?  Or use $- just as an abbreviation!*)

(**** zmult: multiplication on Integ ****)

(** Congruence property for multiplication **)

goal Integ.thy "((k::nat) + l) + (m + n) = (k + m) + (n + l)";
by (simp_tac (simpset() addsimps add_ac) 1);
qed "zmult_congruent_lemma";

goal Integ.thy 
    "congruent2 intrel (%p1 p2.                 \
\               split (%x1 y1. split (%x2 y2.   \
\                   intrel^^{(x1*x2 + y1*y2, x1*y2 + y1*x2)}) p2) p1)";
by (rtac (equiv_intrel RS congruent2_commuteI) 1);
by Safe_tac;
by (rewtac split_def);
by (simp_tac (simpset() addsimps add_ac@mult_ac) 1);
by (asm_simp_tac (simpset() delsimps [equiv_intrel_iff]
                           addsimps add_ac@mult_ac) 1);
by (rtac (intrelI RS(equiv_intrel RS equiv_class_eq)) 1);
by (rtac (zmult_congruent_lemma RS trans) 1);
by (rtac (zmult_congruent_lemma RS trans RS sym) 1);
by (rtac (zmult_congruent_lemma RS trans RS sym) 1);
by (rtac (zmult_congruent_lemma RS trans RS sym) 1);
by (asm_simp_tac (simpset() addsimps [add_mult_distrib RS sym]) 1);
by (asm_simp_tac (simpset() addsimps add_ac@mult_ac) 1);
qed "zmult_congruent2";

(*Resolve th against the corresponding facts for zmult*)
val zmult_ize = RSLIST [equiv_intrel, zmult_congruent2];

goalw Integ.thy [zmult_def]
   "Abs_Integ((intrel^^{(x1,y1)})) * Abs_Integ((intrel^^{(x2,y2)})) =   \
\   Abs_Integ(intrel ^^ {(x1*x2 + y1*y2, x1*y2 + y1*x2)})";
by (simp_tac (simpset() addsimps [zmult_ize UN_equiv_class2]) 1);
qed "zmult";

goalw Integ.thy [znat_def] "$#0 * z = $#0";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zmult]) 1);
qed "zmult_0";

goalw Integ.thy [znat_def] "$#Suc(0) * z = z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps [zmult]) 1);
qed "zmult_1";

goal Integ.thy "($~ z) * w = $~ (z * w)";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps ([zminus, zmult] @ add_ac)) 1);
qed "zmult_zminus";


goal Integ.thy "($~ z) * ($~ w) = (z * w)";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps ([zminus, zmult] @ add_ac)) 1);
qed "zmult_zminus_zminus";

goal Integ.thy "(z::int) * w = w * z";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps ([zmult] @ add_ac @ mult_ac)) 1);
qed "zmult_commute";

goal Integ.thy "z * $# 0 = $#0";
by (rtac ([zmult_commute, zmult_0] MRS trans) 1);
qed "zmult_0_right";

goal Integ.thy "z * $#Suc(0) = z";
by (rtac ([zmult_commute, zmult_1] MRS trans) 1);
qed "zmult_1_right";

goal Integ.thy "((z1::int) * z2) * z3 = z1 * (z2 * z3)";
by (res_inst_tac [("z","z1")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z2")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z3")] eq_Abs_Integ 1);
by (asm_simp_tac (simpset() addsimps ([add_mult_distrib2,zmult] @ 
                                     add_ac @ mult_ac)) 1);
qed "zmult_assoc";

(*For AC rewriting*)
qed_goal "zmult_left_commute" Integ.thy
    "(z1::int)*(z2*z3) = z2*(z1*z3)"
 (fn _ => [rtac (zmult_commute RS trans) 1, rtac (zmult_assoc RS trans) 1,
           rtac (zmult_commute RS arg_cong) 1]);

(*Integer multiplication is an AC operator*)
val zmult_ac = [zmult_assoc, zmult_commute, zmult_left_commute];

goal Integ.thy "((z1::int) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_Integ 1);
by (res_inst_tac [("z","z2")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_simp_tac 
    (simpset() addsimps ([add_mult_distrib2, zadd, zmult] @ 
                        add_ac @ mult_ac)) 1);
qed "zadd_zmult_distrib";

val zmult_commute'= read_instantiate [("z","w")] zmult_commute;

goal Integ.thy "w * ($~ z) = $~ (w * z)";
by (simp_tac (simpset() addsimps [zmult_commute', zmult_zminus]) 1);
qed "zmult_zminus_right";

goal Integ.thy "(w::int) * (z1 + z2) = (w * z1) + (w * z2)";
by (simp_tac (simpset() addsimps [zmult_commute',zadd_zmult_distrib]) 1);
qed "zadd_zmult_distrib2";

val zadd_simps = 
    [zadd_0, zadd_0_right, zadd_zminus_inverse, zadd_zminus_inverse2];

val zminus_simps = [zminus_zminus, zminus_0, zminus_zadd_distrib];

val zmult_simps = [zmult_0, zmult_1, zmult_0_right, zmult_1_right, 
                   zmult_zminus, zmult_zminus_right];

Addsimps (zadd_simps @ zminus_simps @ zmult_simps @ 
          [zmagnitude_znat, zmagnitude_zminus_znat]);


(**** Additional Theorems (by Mattolini; proofs mainly by lcp) ****)

(* Some Theorems about zsuc and zpred *)
goalw Integ.thy [zsuc_def] "$#(Suc(n)) = zsuc($# n)";
by (simp_tac (simpset() addsimps [znat_add RS sym]) 1);
qed "znat_Suc";

goalw Integ.thy [zpred_def,zsuc_def,zdiff_def] "$~ zsuc(z) = zpred($~ z)";
by (Simp_tac 1);
qed "zminus_zsuc";

goalw Integ.thy [zpred_def,zsuc_def,zdiff_def] "$~ zpred(z) = zsuc($~ z)";
by (Simp_tac 1);
qed "zminus_zpred";

goalw Integ.thy [zsuc_def,zpred_def,zdiff_def]
   "zpred(zsuc(z)) = z";
by (simp_tac (simpset() addsimps [zadd_assoc]) 1);
qed "zpred_zsuc";

goalw Integ.thy [zsuc_def,zpred_def,zdiff_def]
   "zsuc(zpred(z)) = z";
by (simp_tac (simpset() addsimps [zadd_assoc]) 1);
qed "zsuc_zpred";

goal Integ.thy "(zpred(z)=w) = (z=zsuc(w))";
by Safe_tac;
by (rtac (zsuc_zpred RS sym) 1);
by (rtac zpred_zsuc 1);
qed "zpred_to_zsuc";

goal Integ.thy "(zsuc(z)=w)=(z=zpred(w))";
by Safe_tac;
by (rtac (zpred_zsuc RS sym) 1);
by (rtac zsuc_zpred 1);
qed "zsuc_to_zpred";

goal Integ.thy "($~ z = w) = (z = $~ w)";
by Safe_tac;
by (rtac (zminus_zminus RS sym) 1);
by (rtac zminus_zminus 1);
qed "zminus_exchange";

goal Integ.thy"(zsuc(z)=zsuc(w)) = (z=w)";
by Safe_tac;
by (dres_inst_tac [("f","zpred")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [zpred_zsuc]) 1);
qed "bijective_zsuc";

goal Integ.thy"(zpred(z)=zpred(w)) = (z=w)";
by Safe_tac;
by (dres_inst_tac [("f","zsuc")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [zsuc_zpred]) 1);
qed "bijective_zpred";

(* Additional Theorems about zadd *)

goalw Integ.thy [zsuc_def] "zsuc(z) + w = zsuc(z+w)";
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "zadd_zsuc";

goalw Integ.thy [zsuc_def] "w + zsuc(z) = zsuc(w+z)";
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "zadd_zsuc_right";

goalw Integ.thy [zpred_def,zdiff_def] "zpred(z) + w = zpred(z+w)";
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "zadd_zpred";

goalw Integ.thy [zpred_def,zdiff_def] "w + zpred(z) = zpred(w+z)";
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "zadd_zpred_right";


(* Additional Theorems about zmult *)

goalw Integ.thy [zsuc_def] "zsuc(w) * z = z + w * z";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib, zadd_commute]) 1);
qed "zmult_zsuc";

goalw Integ.thy [zsuc_def] "z * zsuc(w) = z + w * z";
by (simp_tac 
    (simpset() addsimps [zadd_zmult_distrib2, zadd_commute, zmult_commute]) 1);
qed "zmult_zsuc_right";

goalw Integ.thy [zpred_def, zdiff_def] "zpred(w) * z = w * z - z";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib]) 1);
qed "zmult_zpred";

goalw Integ.thy [zpred_def, zdiff_def] "z * zpred(w) = w * z - z";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib2, zmult_commute]) 1);
qed "zmult_zpred_right";

(* Further Theorems about zsuc and zpred *)
goal Integ.thy "$#Suc(m) ~= $#0";
by (simp_tac (simpset() addsimps [inj_znat RS inj_eq]) 1);
qed "znat_Suc_not_znat_Zero";

bind_thm ("znat_Zero_not_znat_Suc", (znat_Suc_not_znat_Zero RS not_sym));


goalw Integ.thy [zsuc_def,znat_def] "w ~= zsuc(w)";
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by (asm_full_simp_tac (simpset() addsimps [zadd]) 1);
qed "n_not_zsuc_n";

val zsuc_n_not_n = n_not_zsuc_n RS not_sym;

goal Integ.thy "w ~= zpred(w)";
by Safe_tac;
by (dres_inst_tac [("x","w"),("f","zsuc")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [zsuc_zpred,zsuc_n_not_n]) 1);
qed "n_not_zpred_n";

val zpred_n_not_n = n_not_zpred_n RS not_sym;


(* Theorems about less and less_equal *)

goalw Integ.thy [zless_def, znegative_def, zdiff_def, znat_def] 
    "!!w. w<z ==> ? n. z = w + $#(Suc(n))";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [zadd, zminus]) 1);
by (safe_tac (claset() addSDs [less_eq_Suc_add]));
by (res_inst_tac [("x","k")] exI 1);
by (asm_full_simp_tac (simpset() addsimps add_ac) 1);
qed "zless_eq_zadd_Suc";

goalw Integ.thy [zless_def, znegative_def, zdiff_def, znat_def] 
    "z < z + $#(Suc(n))";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (Clarify_tac 1);
by (simp_tac (simpset() addsimps [zadd, zminus]) 1);
qed "zless_zadd_Suc";

goal Integ.thy "!!z1 z2 z3. [| z1<z2; z2<z3 |] ==> z1 < (z3::int)";
by (safe_tac (claset() addSDs [zless_eq_zadd_Suc]));
by (simp_tac 
    (simpset() addsimps [zadd_assoc, zless_zadd_Suc, znat_add RS sym]) 1);
qed "zless_trans";

goalw Integ.thy [zsuc_def] "z<zsuc(z)";
by (rtac zless_zadd_Suc 1);
qed "zlessI";

val zless_zsucI = zlessI RSN (2,zless_trans);

goal Integ.thy "!!z w::int. z<w ==> ~w<z";
by (safe_tac (claset() addSDs [zless_eq_zadd_Suc]));
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps ([znat_def, zadd])) 1);
qed "zless_not_sym";

(* [| n<m; m<n |] ==> R *)
bind_thm ("zless_asym", (zless_not_sym RS notE));

goal Integ.thy "!!z::int. ~ z<z";
by (resolve_tac [zless_asym RS notI] 1);
by (REPEAT (assume_tac 1));
qed "zless_not_refl";

(* z<z ==> R *)
bind_thm ("zless_irrefl", (zless_not_refl RS notE));

goal Integ.thy "!!w. z<w ==> w ~= (z::int)";
by (fast_tac (claset() addEs [zless_irrefl]) 1);
qed "zless_not_refl2";


(*"Less than" is a linear ordering*)
goalw Integ.thy [zless_def, znegative_def, zdiff_def] 
    "z<w | z=w | w<(z::int)";
by (res_inst_tac [("z","z")] eq_Abs_Integ 1);
by (res_inst_tac [("z","w")] eq_Abs_Integ 1);
by Safe_tac;
by (asm_full_simp_tac
    (simpset() addsimps [zadd, zminus, Image_iff, Bex_def]) 1);
by (res_inst_tac [("m1", "x+ya"), ("n1", "xa+y")] (less_linear RS disjE) 1);
by (REPEAT (fast_tac (claset() addss (simpset() addsimps add_ac)) 1));
qed "zless_linear";


(*** Properties of <= ***)

goalw Integ.thy  [zless_def, znegative_def, zdiff_def, znat_def]
    "($#m < $#n) = (m<n)";
by (simp_tac
    (simpset() addsimps [zadd, zminus, Image_iff, Bex_def]) 1);
by (fast_tac (claset() addIs [add_commute] addSEs [less_add_eq_less]) 1);
qed "zless_eq_less";

goalw Integ.thy [zle_def, le_def] "($#m <= $#n) = (m<=n)";
by (simp_tac (simpset() addsimps [zless_eq_less]) 1);
qed "zle_eq_le";

goalw Integ.thy [zle_def] "!!w. ~(w<z) ==> z<=(w::int)";
by (assume_tac 1);
qed "zleI";

goalw Integ.thy [zle_def] "!!w. z<=w ==> ~(w<(z::int))";
by (assume_tac 1);
qed "zleD";

val zleE = make_elim zleD;

goalw Integ.thy [zle_def] "!!z. ~ z <= w ==> w<(z::int)";
by (Fast_tac 1);
qed "not_zleE";

goalw Integ.thy [zle_def] "!!z. z < w ==> z <= (w::int)";
by (fast_tac (claset() addEs [zless_asym]) 1);
qed "zless_imp_zle";

goalw Integ.thy [zle_def] "!!z. z <= w ==> z < w | z=(w::int)";
by (cut_facts_tac [zless_linear] 1);
by (fast_tac (claset() addEs [zless_irrefl,zless_asym]) 1);
qed "zle_imp_zless_or_eq";

goalw Integ.thy [zle_def] "!!z. z<w | z=w ==> z <=(w::int)";
by (cut_facts_tac [zless_linear] 1);
by (fast_tac (claset() addEs [zless_irrefl,zless_asym]) 1);
qed "zless_or_eq_imp_zle";

goal Integ.thy "(x <= (y::int)) = (x < y | x=y)";
by (REPEAT(ares_tac [iffI, zless_or_eq_imp_zle, zle_imp_zless_or_eq] 1));
qed "zle_eq_zless_or_eq";

goal Integ.thy "w <= (w::int)";
by (simp_tac (simpset() addsimps [zle_eq_zless_or_eq]) 1);
qed "zle_refl";

val prems = goal Integ.thy "!!i. [| i <= j; j < k |] ==> i < (k::int)";
by (dtac zle_imp_zless_or_eq 1);
by (fast_tac (claset() addIs [zless_trans]) 1);
qed "zle_zless_trans";

goal Integ.thy "!!i. [| i <= j; j <= k |] ==> i <= (k::int)";
by (EVERY1 [dtac zle_imp_zless_or_eq, dtac zle_imp_zless_or_eq,
            rtac zless_or_eq_imp_zle, fast_tac (claset() addIs [zless_trans])]);
qed "zle_trans";

goal Integ.thy "!!z. [| z <= w; w <= z |] ==> z = (w::int)";
by (EVERY1 [dtac zle_imp_zless_or_eq, dtac zle_imp_zless_or_eq,
            fast_tac (claset() addEs [zless_irrefl,zless_asym])]);
qed "zle_anti_sym";


goal Integ.thy "!!w w' z::int. z + w' = z + w ==> w' = w";
by (dres_inst_tac [("f", "%x. x + $~z")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps zadd_ac) 1);
qed "zadd_left_cancel";


(*** Monotonicity results ***)

goal Integ.thy "!!v w z::int. v < w ==> v + z < w + z";
by (safe_tac (claset() addSDs [zless_eq_zadd_Suc]));
by (simp_tac (simpset() addsimps zadd_ac) 1);
by (simp_tac (simpset() addsimps [zadd_assoc RS sym, zless_zadd_Suc]) 1);
qed "zadd_zless_mono1";

goal Integ.thy "!!v w z::int. (v+z < w+z) = (v < w)";
by (safe_tac (claset() addSEs [zadd_zless_mono1]));
by (dres_inst_tac [("z", "$~z")] zadd_zless_mono1 1);
by (asm_full_simp_tac (simpset() addsimps [zadd_assoc]) 1);
qed "zadd_left_cancel_zless";

goal Integ.thy "!!v w z::int. (v+z <= w+z) = (v <= w)";
by (asm_full_simp_tac
    (simpset() addsimps [zle_def, zadd_left_cancel_zless]) 1);
qed "zadd_left_cancel_zle";

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("zadd_zle_mono1", zadd_left_cancel_zle RS iffD2);


goal Integ.thy "!!z' z::int. [| w'<=w; z'<=z |] ==> w' + z' <= w + z";
by (etac (zadd_zle_mono1 RS zle_trans) 1);
by (simp_tac (simpset() addsimps [zadd_commute]) 1);
(*w moves to the end because it is free while z', z are bound*)
by (etac zadd_zle_mono1 1);
qed "zadd_zle_mono";

goal Integ.thy "!!w z::int. z<=$#0 ==> w+z <= w";
by (dres_inst_tac [("z", "w")] zadd_zle_mono1 1);
by (asm_full_simp_tac (simpset() addsimps [zadd_commute]) 1);
qed "zadd_zle_self";


(**** Comparisons: lemmas and proofs by Norbert Voelker ****)

(** One auxiliary theorem...**)

goal HOL.thy "(x = False) = (~ x)";
  by (fast_tac HOL_cs 1);
qed "eq_False_conv";

(** Additional theorems for Integ.thy **) 

Addsimps [zless_eq_less, zle_eq_le,
	  znegative_zminus_znat, not_znegative_znat]; 

goal Integ.thy "!! x. (x::int) = y ==> x <= y"; 
  by (etac subst 1); by (rtac zle_refl 1); 
qed "zequalD1"; 

goal Integ.thy "($~ x < $~ y) = (y < x)";
  by (rewrite_goals_tac [zless_def,zdiff_def]); 
  by (simp_tac (simpset() addsimps zadd_ac ) 1); 
qed "zminus_zless_zminus"; 

goal Integ.thy "($~ x <= $~ y) = (y <= x)";
  by (simp_tac (HOL_ss addsimps[zle_def, zminus_zless_zminus]) 1); 
qed "zminus_zle_zminus"; 

goal Integ.thy "(x < $~ y) = (y < $~ x)";
  by (rewrite_goals_tac [zless_def,zdiff_def]); 
  by (simp_tac (simpset() addsimps zadd_ac ) 1); 
qed "zless_zminus"; 

goal Integ.thy "($~ x < y) = ($~ y < x)";
  by (rewrite_goals_tac [zless_def,zdiff_def]); 
  by (simp_tac (simpset() addsimps zadd_ac ) 1); 
qed "zminus_zless"; 

goal Integ.thy "(x <= $~ y) = (y <=  $~ x)";
  by (simp_tac (HOL_ss addsimps[zle_def, zminus_zless]) 1); 
qed "zle_zminus"; 

goal Integ.thy "($~ x <= y) = ($~ y <=  x)";
  by (simp_tac (HOL_ss addsimps[zle_def, zless_zminus]) 1); 
qed "zminus_zle"; 

goal Integ.thy " $#0 < $# Suc n"; 
  by (rtac (zero_less_Suc RS (zless_eq_less RS iffD2)) 1); 
qed "zero_zless_Suc_pos"; 

goal Integ.thy "($# n= $# m) = (n = m)"; 
  by (fast_tac (HOL_cs addSEs[inj_znat RS injD]) 1); 
qed "znat_znat_eq"; 
AddIffs[znat_znat_eq]; 

goal Integ.thy "$~ $# Suc n < $#0";
  by (stac (zminus_0 RS sym) 1); 
  by (rtac (zminus_zless_zminus RS iffD2) 1); 
  by (rtac (zero_less_Suc RS (zless_eq_less RS iffD2)) 1); 
qed "negative_zless_0"; 
Addsimps [zero_zless_Suc_pos, negative_zless_0]; 

goal Integ.thy "$~ $#  n <= $#0";
  by (rtac zless_or_eq_imp_zle 1); 
  by (nat_ind_tac "n" 1); 
  by (ALLGOALS Asm_simp_tac); 
qed "negative_zle_0"; 
Addsimps[negative_zle_0]; 

goal Integ.thy "~($#0 <= $~ $# Suc n)";
  by (stac zle_zminus 1);
  by (Simp_tac 1);
qed "not_zle_0_negative"; 
Addsimps[not_zle_0_negative]; 

goal Integ.thy "($# n <= $~ $# m) = (n = 0 & m = 0)"; 
  by (safe_tac HOL_cs); 
  by (Simp_tac 3); 
  by (dtac (zle_zminus RS iffD1) 2); 
  by (ALLGOALS(dtac (negative_zle_0 RSN(2,zle_trans)))); 
  by (ALLGOALS Asm_full_simp_tac); 
qed "znat_zle_znegative"; 

goal Integ.thy "~($# n < $~ $# Suc m)";
  by (rtac notI 1); by (forward_tac [zless_imp_zle] 1); 
  by (dtac (znat_zle_znegative RS iffD1) 1); 
  by (safe_tac HOL_cs); 
  by (dtac (zless_zminus RS iffD1) 1); 
  by (Asm_full_simp_tac 1);
qed "not_znat_zless_negative"; 

goal Integ.thy "($~ $# n = $# m) = (n = 0 & m = 0)"; 
  by (rtac iffI 1);
  by (rtac  (znat_zle_znegative RS iffD1) 1); 
  by (dtac sym 1); 
  by (ALLGOALS Asm_simp_tac); 
qed "negative_eq_positive"; 

Addsimps [zminus_zless_zminus, zminus_zle_zminus, 
	  negative_eq_positive, not_znat_zless_negative]; 

goalw Integ.thy [zdiff_def,zless_def] "!! x. znegative x = (x < $# 0)";
  by Auto_tac; 
qed "znegative_less_0"; 

goalw Integ.thy [zdiff_def,zless_def] "!! x. (~znegative x) = ($# 0 <= x)";
  by (stac znegative_less_0 1); 
  by (safe_tac (HOL_cs addSDs[zleD,not_zleE,zleI]) ); 
qed "not_znegative_ge_0"; 

goal Integ.thy "!! x. znegative x ==> ? n. x = $~ $# Suc n"; 
  by (dtac (znegative_less_0 RS iffD1 RS zless_eq_zadd_Suc) 1); 
  by (etac exE 1); 
  by (rtac exI 1);
  by (dres_inst_tac [("f","(% z. z + $~ $# Suc n )")] arg_cong 1); 
  by (auto_tac(claset(), simpset() addsimps [zadd_assoc])); 
qed "znegativeD"; 

goal Integ.thy "!! x. ~znegative x ==> ? n. x = $# n"; 
  by (dtac (not_znegative_ge_0 RS iffD1) 1); 
  by (dtac zle_imp_zless_or_eq 1); 
  by (etac disjE 1); 
  by (dtac zless_eq_zadd_Suc 1); 
  by Auto_tac; 
qed "not_znegativeD"; 

(* a case theorem distinguishing positive and negative int *)  

val prems = goal Integ.thy 
    "[|!! n. P ($# n); !! n. P ($~ $# Suc n) |] ==> P z"; 
  by (cut_inst_tac [("P","znegative z")] excluded_middle 1); 
  by (fast_tac (HOL_cs addSDs[znegativeD,not_znegativeD] addSIs prems) 1); 
qed "int_cases"; 

fun int_case_tac x = res_inst_tac [("z",x)] int_cases; 

