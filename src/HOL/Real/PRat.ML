(*  Title       : PRat.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The positive rationals
*) 

open PRat;

Delrules [equalityI];

(*** Many theorems similar to those in Integ.thy ***)
(*** Proving that ratrel is an equivalence relation ***)

Goal
    "[| (x1::pnat) * y2 = x2 * y1; x2 * y3 = x3 * y2 |] \
\            ==> x1 * y3 = x3 * y1";        
by (res_inst_tac [("k1","y2")] (pnat_mult_cancel1 RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps [pnat_mult_assoc RS sym]));
by (auto_tac (claset(),simpset() addsimps [pnat_mult_commute]));
by (dres_inst_tac [("s","x2 * y3")] sym 1);
by (asm_simp_tac (simpset() addsimps [pnat_mult_left_commute,
    pnat_mult_commute]) 1);
qed "prat_trans_lemma";

(** Natural deduction for ratrel **)

Goalw [ratrel_def]
    "(((x1,y1),(x2,y2)): ratrel) = (x1 * y2 = x2 * y1)";
by (Fast_tac 1);
qed "ratrel_iff";

Goalw [ratrel_def]
    "[| x1 * y2 = x2 * y1 |] ==> ((x1,y1),(x2,y2)): ratrel";
by (Fast_tac  1);
qed "ratrelI";

Goalw [ratrel_def]
  "p: ratrel --> (EX x1 y1 x2 y2. \
\                  p = ((x1,y1),(x2,y2)) & x1 *y2 = x2 *y1)";
by (Fast_tac 1);
qed "ratrelE_lemma";

val [major,minor] = goal thy
  "[| p: ratrel;  \
\     !!x1 y1 x2 y2. [| p = ((x1,y1),(x2,y2));  x1*y2 = x2*y1 \
\                    |] ==> Q |] ==> Q";
by (cut_facts_tac [major RS (ratrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "ratrelE";

AddSIs [ratrelI];
AddSEs [ratrelE];

Goal "(x,x): ratrel";
by (stac surjective_pairing 1 THEN rtac (refl RS ratrelI) 1);
qed "ratrel_refl";

Goalw [equiv_def, refl_def, sym_def, trans_def]
    "equiv {x::(pnat*pnat).True} ratrel";
by (fast_tac (claset() addSIs [ratrel_refl] 
                      addSEs [sym, prat_trans_lemma]) 1);
qed "equiv_ratrel";

val equiv_ratrel_iff =
    [TrueI, TrueI] MRS 
    ([CollectI, CollectI] MRS 
    (equiv_ratrel RS eq_equiv_class_iff));

Goalw  [prat_def,ratrel_def,quotient_def] "ratrel^^{(x,y)}:prat";
by (Blast_tac 1);
qed "ratrel_in_prat";

Goal "inj_on Abs_prat prat";
by (rtac inj_on_inverseI 1);
by (etac Abs_prat_inverse 1);
qed "inj_on_Abs_prat";

Addsimps [equiv_ratrel_iff,inj_on_Abs_prat RS inj_on_iff,
          ratrel_iff, ratrel_in_prat, Abs_prat_inverse];

Addsimps [equiv_ratrel RS eq_equiv_class_iff];
val eq_ratrelD = equiv_ratrel RSN (2,eq_equiv_class);

Goal "inj(Rep_prat)";
by (rtac inj_inverseI 1);
by (rtac Rep_prat_inverse 1);
qed "inj_Rep_prat";

(** prat_of_pnat: the injection from pnat to prat **)
Goal "inj(prat_of_pnat)";
by (rtac injI 1);
by (rewtac prat_of_pnat_def);
by (dtac (inj_on_Abs_prat RS inj_onD) 1);
by (REPEAT (rtac ratrel_in_prat 1));
by (dtac eq_equiv_class 1);
by (rtac equiv_ratrel 1);
by (Fast_tac 1);
by Safe_tac;
by (Asm_full_simp_tac 1);
qed "inj_prat_of_pnat";

val [prem] = goal thy
    "(!!x y. z = Abs_prat(ratrel^^{(x,y)}) ==> P) ==> P";
by (res_inst_tac [("x1","z")] 
    (rewrite_rule [prat_def] Rep_prat RS quotientE) 1);
by (dres_inst_tac [("f","Abs_prat")] arg_cong 1);
by (res_inst_tac [("p","x")] PairE 1);
by (rtac prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_prat_inverse]) 1);
qed "eq_Abs_prat";

(**** qinv: inverse on prat ****)

Goalw [congruent_def]
  "congruent ratrel (%p. split (%x y. ratrel^^{(y,x)}) p)";
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [pnat_mult_commute]) 1);
qed "qinv_congruent";

(*Resolve th against the corresponding facts for qinv*)
val qinv_ize = RSLIST [equiv_ratrel, qinv_congruent];

Goalw [qinv_def]
      "qinv (Abs_prat(ratrel^^{(x,y)})) = Abs_prat(ratrel ^^ {(y,x)})";
by (res_inst_tac [("f","Abs_prat")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [ratrel_in_prat RS Abs_prat_inverse,qinv_ize UN_equiv_class]) 1);
qed "qinv";

Goal "qinv (qinv z) = z";
by (res_inst_tac [("z","z")] eq_Abs_prat 1);
by (asm_simp_tac (simpset() addsimps [qinv]) 1);
qed "qinv_qinv";

Goal "inj(qinv)";
by (rtac injI 1);
by (dres_inst_tac [("f","qinv")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [qinv_qinv]) 1);
qed "inj_qinv";

Goalw [prat_of_pnat_def] 
      "qinv(prat_of_pnat  (Abs_pnat 1)) = prat_of_pnat (Abs_pnat 1)";
by (simp_tac (simpset() addsimps [qinv]) 1);
qed "qinv_1";

Goal "!!(x1::pnat). [| x1 * y2 = x2 * y1 |] ==> \
\     (x * y1 + x1 * ya) * (ya * y2) = (x * y2 + x2 * ya) * (ya * y1)";
by (auto_tac (claset() addSIs [pnat_same_multI2],
       simpset() addsimps [pnat_add_mult_distrib,
       pnat_mult_assoc]));
by (res_inst_tac [("n1","y2")] (pnat_mult_commute RS subst) 1);
by (auto_tac (claset() addIs [pnat_add_left_cancel RS iffD2],simpset() addsimps pnat_mult_ac));
by (res_inst_tac [("y1","x1")] (pnat_mult_left_commute RS subst) 1);
by (res_inst_tac [("y1","x1")] (pnat_mult_left_commute RS ssubst) 1);
by (auto_tac (claset(),simpset() addsimps [pnat_mult_assoc RS sym]));
qed "prat_add_congruent2_lemma";

Goal 
    "congruent2 ratrel (%p1 p2.                  \
\         split (%x1 y1. split (%x2 y2. ratrel^^{(x1*y2 + x2*y1, y1*y2)}) p2) p1)";
by (rtac (equiv_ratrel RS congruent2_commuteI) 1);
by Safe_tac;
by (rewtac split_def);
by (asm_simp_tac (simpset() addsimps [pnat_mult_commute,pnat_add_commute]) 1);
by (auto_tac (claset(),simpset() addsimps [prat_add_congruent2_lemma]));
qed "prat_add_congruent2";

(*Resolve th against the corresponding facts for prat_add*)
val prat_add_ize = RSLIST [equiv_ratrel, prat_add_congruent2];

Goalw [prat_add_def]
   "Abs_prat((ratrel^^{(x1,y1)})) + Abs_prat((ratrel^^{(x2,y2)})) =   \
\   Abs_prat(ratrel ^^ {(x1*y2 + x2*y1, y1*y2)})";
by (simp_tac (simpset() addsimps [prat_add_ize UN_equiv_class2]) 1);
qed "prat_add";

Goal "(z::prat) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_prat 1);
by (res_inst_tac [("z","w")] eq_Abs_prat 1);
by (asm_simp_tac
    (simpset() addsimps [prat_add] @ pnat_add_ac @ pnat_mult_ac) 1);
qed "prat_add_commute";

Goal "((z1::prat) + z2) + z3 = z1 + (z2 + z3)";
by (res_inst_tac [("z","z1")] eq_Abs_prat 1);
by (res_inst_tac [("z","z2")] eq_Abs_prat 1);
by (res_inst_tac [("z","z3")] eq_Abs_prat 1);
by (asm_simp_tac (simpset() addsimps [pnat_add_mult_distrib2,prat_add] @ 
                                     pnat_add_ac @ pnat_mult_ac) 1);
qed "prat_add_assoc";

qed_goal "prat_add_left_commute" thy
    "(z1::prat) + (z2 + z3) = z2 + (z1 + z3)"
 (fn _ => [rtac (prat_add_commute RS trans) 1, rtac (prat_add_assoc RS trans) 1,
           rtac (prat_add_commute RS arg_cong) 1]);

(* Positive Rational addition is an AC operator *)
val prat_add_ac = [prat_add_assoc, prat_add_commute, prat_add_left_commute];


(*** Congruence property for multiplication ***)

Goalw [congruent2_def]
    "congruent2 ratrel (%p1 p2.                  \
\         split (%x1 y1. split (%x2 y2. ratrel^^{(x1*x2, y1*y2)}) p2) p1)";

(*Proof via congruent2_commuteI seems longer*)
by Safe_tac;
by (asm_simp_tac (simpset() addsimps [pnat_mult_assoc]) 1);
(*The rest should be trivial, but rearranging terms is hard*)
by (res_inst_tac [("x1","x1a")] (pnat_mult_left_commute RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [pnat_mult_assoc RS sym]) 1);
by (asm_simp_tac (simpset() addsimps pnat_mult_ac) 1);
qed "pnat_mult_congruent2";

(*Resolve th against the corresponding facts for pnat_mult*)
val prat_mult_ize = RSLIST [equiv_ratrel, pnat_mult_congruent2];

Goalw [prat_mult_def]
  "Abs_prat(ratrel^^{(x1,y1)}) * Abs_prat(ratrel^^{(x2,y2)}) = \
\  Abs_prat(ratrel^^{(x1*x2, y1*y2)})";
by (asm_simp_tac
    (simpset() addsimps [prat_mult_ize UN_equiv_class2]) 1);
qed "prat_mult";

Goal "(z::prat) * w = w * z";
by (res_inst_tac [("z","z")] eq_Abs_prat 1);
by (res_inst_tac [("z","w")] eq_Abs_prat 1);
by (asm_simp_tac (simpset() addsimps pnat_mult_ac @ [prat_mult]) 1);
qed "prat_mult_commute";

Goal "((z1::prat) * z2) * z3 = z1 * (z2 * z3)";
by (res_inst_tac [("z","z1")] eq_Abs_prat 1);
by (res_inst_tac [("z","z2")] eq_Abs_prat 1);
by (res_inst_tac [("z","z3")] eq_Abs_prat 1);
by (asm_simp_tac (simpset() addsimps [prat_mult, pnat_mult_assoc]) 1);
qed "prat_mult_assoc";

(*For AC rewriting*)
Goal "(x::prat)*(y*z)=y*(x*z)";
by (rtac (prat_mult_commute RS trans) 1);
by (rtac (prat_mult_assoc RS trans) 1);
by (rtac (prat_mult_commute RS arg_cong) 1);
qed "prat_mult_left_commute";

(*Positive Rational multiplication is an AC operator*)
val prat_mult_ac = [prat_mult_assoc,
                    prat_mult_commute,prat_mult_left_commute];

Goalw [prat_of_pnat_def] 
      "(prat_of_pnat (Abs_pnat 1)) * z = z";
by (res_inst_tac [("z","z")] eq_Abs_prat 1);
by (asm_full_simp_tac (simpset() addsimps 
   [prat_mult] @ pnat_mult_ac) 1);
qed "prat_mult_1";

Goalw [prat_of_pnat_def] 
      "z * (prat_of_pnat (Abs_pnat 1)) = z";
by (res_inst_tac [("z","z")] eq_Abs_prat 1);
by (asm_full_simp_tac (simpset() addsimps 
    [prat_mult] @ pnat_mult_ac) 1);
qed "prat_mult_1_right";

Goalw [prat_of_pnat_def] 
      "prat_of_pnat ((z1::pnat) + z2) = \
\      prat_of_pnat z1 + prat_of_pnat z2";
by (asm_simp_tac (simpset() addsimps [prat_add,
       pnat_add_mult_distrib,pnat_mult_1]) 1);
qed "prat_of_pnat_add";

Goalw [prat_of_pnat_def] 
      "prat_of_pnat ((z1::pnat) * z2) = \
\      prat_of_pnat z1 * prat_of_pnat z2";
by (asm_simp_tac (simpset() addsimps [prat_mult,
                              pnat_mult_1]) 1);
qed "prat_of_pnat_mult";

(*** prat_mult and qinv ***)

Goalw [prat_def,prat_of_pnat_def] 
      "qinv (q) * q = prat_of_pnat (Abs_pnat 1)";
by (res_inst_tac [("z","q")] eq_Abs_prat 1);
by (asm_full_simp_tac (simpset() addsimps [qinv,
        prat_mult,pnat_mult_1,pnat_mult_1_left,
                        pnat_mult_commute]) 1);
qed "prat_mult_qinv";

Goal "q * qinv (q) = prat_of_pnat (Abs_pnat 1)";
by (rtac (prat_mult_commute RS subst) 1);
by (simp_tac (simpset() addsimps [prat_mult_qinv]) 1);
qed "prat_mult_qinv_right";

Goal "? y. (x::prat) * y = prat_of_pnat (Abs_pnat 1)";
by (fast_tac (claset() addIs [prat_mult_qinv_right]) 1);
qed "prat_qinv_ex";

Goal "?! y. (x::prat) * y = prat_of_pnat (Abs_pnat 1)";
by (auto_tac (claset() addIs [prat_mult_qinv_right],simpset()));
by (dres_inst_tac [("f","%x. ya*x")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [prat_mult_assoc RS sym]) 1);
by (asm_full_simp_tac (simpset() addsimps [prat_mult_commute,
    prat_mult_1,prat_mult_1_right]) 1);
qed "prat_qinv_ex1";

Goal "?! y. y * (x::prat) = prat_of_pnat (Abs_pnat 1)";
by (auto_tac (claset() addIs [prat_mult_qinv],simpset()));
by (dres_inst_tac [("f","%x. x*ya")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [prat_mult_assoc]) 1);
by (asm_full_simp_tac (simpset() addsimps [prat_mult_commute,
    prat_mult_1,prat_mult_1_right]) 1);
qed "prat_qinv_left_ex1";

Goal "x * y = prat_of_pnat (Abs_pnat 1) ==> x = qinv y";
by (cut_inst_tac [("q","y")] prat_mult_qinv 1);
by (res_inst_tac [("x1","y")] (prat_qinv_left_ex1 RS ex1E) 1);
by (Blast_tac 1);
qed "prat_mult_inv_qinv";

Goal "? y. x = qinv y";
by (cut_inst_tac [("x","x")] prat_qinv_ex 1);
by (etac exE 1 THEN dtac prat_mult_inv_qinv 1);
by (Fast_tac 1);
qed "prat_as_inverse_ex";

Goal "qinv(x*y) = qinv(x)*qinv(y)";
by (res_inst_tac [("z","x")] eq_Abs_prat 1);
by (res_inst_tac [("z","y")] eq_Abs_prat 1);
by (auto_tac (claset(),simpset() addsimps [qinv,prat_mult]));
qed "qinv_mult_eq";

(** Lemmas **)

qed_goal "prat_add_assoc_cong" thy
    "!!z. (z::prat) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
 (fn _ => [(asm_simp_tac (simpset() addsimps [prat_add_assoc RS sym]) 1)]);

qed_goal "prat_add_assoc_swap" thy "(z::prat) + (v + w) = v + (z + w)"
 (fn _ => [(REPEAT (ares_tac [prat_add_commute RS prat_add_assoc_cong] 1))]);

Goal "((z1::prat) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_prat 1);
by (res_inst_tac [("z","z2")] eq_Abs_prat 1);
by (res_inst_tac [("z","w")] eq_Abs_prat 1);
by (asm_simp_tac 
    (simpset() addsimps [pnat_add_mult_distrib2, prat_add, prat_mult] @ 
                        pnat_add_ac @ pnat_mult_ac) 1);
qed "prat_add_mult_distrib";

val prat_mult_commute'= read_instantiate [("z","w")] prat_mult_commute;

Goal "(w::prat) * (z1 + z2) = (w * z1) + (w * z2)";
by (simp_tac (simpset() addsimps [prat_mult_commute',prat_add_mult_distrib]) 1);
qed "prat_add_mult_distrib2";

val prat_mult_simps = [prat_mult_1, prat_mult_1_right, 
                       prat_mult_qinv, prat_mult_qinv_right];
Addsimps prat_mult_simps;

      (*** theorems for ordering ***)
(* prove introduction and elimination rules for prat_less *)

Goalw [prat_less_def]
    "Q1 < (Q2::prat) = (EX Q3. Q1 + Q3 = Q2)";
by (Fast_tac 1);
qed "prat_less_iff";

Goalw [prat_less_def]
      "!!(Q1::prat). Q1 + Q3 = Q2 ==> Q1 < Q2";
by (Fast_tac  1);
qed "prat_lessI";

(* ordering on positive fractions in terms of existence of sum *)
Goalw [prat_less_def]
      "Q1 < (Q2::prat) --> (EX Q3. Q1 + Q3 = Q2)";
by (Fast_tac 1);
qed "prat_lessE_lemma";

Goal "!!P. [| Q1 < (Q2::prat); \
\             !! (Q3::prat). Q1 + Q3 = Q2 ==> P |] \
\          ==> P";
by (dtac (prat_lessE_lemma RS mp) 1);
by Auto_tac;
qed "prat_lessE";

(* qless is a strong order i.e nonreflexive and transitive *)
Goal "!!(q1::prat). [| q1 < q2; q2 < q3 |] ==> q1 < q3";
by (REPEAT(dtac (prat_lessE_lemma RS mp) 1));
by (REPEAT(etac exE 1));
by (hyp_subst_tac 1);
by (res_inst_tac [("Q3.0","Q3 + Q3a")] prat_lessI 1);
by (auto_tac (claset(),simpset() addsimps [prat_add_assoc]));
qed "prat_less_trans";

Goal "~q < (q::prat)";
by (EVERY1[rtac notI, dtac (prat_lessE_lemma RS mp)]);
by (res_inst_tac [("z","q")] eq_Abs_prat 1);
by (res_inst_tac [("z","Q3")] eq_Abs_prat 1);
by (etac exE 1 THEN res_inst_tac [("z","Q3a")] eq_Abs_prat 1);
by (REPEAT(hyp_subst_tac 1));
by (asm_full_simp_tac (simpset() addsimps [prat_add,
    pnat_no_add_ident,pnat_add_mult_distrib2] @ pnat_mult_ac) 1);
qed "prat_less_not_refl";

(*** y < y ==> P ***)
bind_thm("prat_less_irrefl",prat_less_not_refl RS notE);

Goal "!! (q1::prat). q1 < q2 ==> ~ q2 < q1";
by (rtac notI 1);
by (dtac prat_less_trans 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [prat_less_not_refl]) 1);
qed "prat_less_not_sym";

(* [| x < y;  ~P ==> y < x |] ==> P *)
bind_thm ("prat_less_asym", prat_less_not_sym RS swap);

(* half of positive fraction exists- Gleason p. 120- Proposition 9-2.6(i)*)
Goal "!(q::prat). ? x. x + x = q";
by (rtac allI 1);
by (res_inst_tac [("z","q")] eq_Abs_prat 1);
by (res_inst_tac [("x","Abs_prat (ratrel ^^ {(x, y+y)})")] exI 1);
by (auto_tac (claset(),simpset() addsimps 
              [prat_add,pnat_mult_assoc RS sym,pnat_add_mult_distrib,
               pnat_add_mult_distrib2]));
qed "lemma_prat_dense";

Goal "? (x::prat). x + x = q";
by (res_inst_tac [("z","q")] eq_Abs_prat 1);
by (res_inst_tac [("x","Abs_prat (ratrel ^^ {(x, y+y)})")] exI 1);
by (auto_tac (claset(),simpset() addsimps 
              [prat_add,pnat_mult_assoc RS sym,pnat_add_mult_distrib,
               pnat_add_mult_distrib2]));
qed "prat_lemma_dense";

(* there exists a number between any two positive fractions *)
(* Gleason p. 120- Proposition 9-2.6(iv) *)
Goalw [prat_less_def] 
      "!! (q1::prat). q1 < q2 ==> ? x. q1 < x & x < q2";
by (auto_tac (claset() addIs [lemma_prat_dense],simpset()));
by (res_inst_tac [("x","T")] (lemma_prat_dense RS allE) 1);
by (etac exE 1);
by (res_inst_tac [("x","q1 + x")] exI 1);
by (auto_tac (claset() addIs [prat_lemma_dense],
    simpset() addsimps [prat_add_assoc]));
qed "prat_dense";

(* ordering of addition for positive fractions *)
Goalw [prat_less_def] 
      "!!(q1::prat). q1 < q2 ==> q1 + x < q2 + x";
by (Step_tac 1);
by (res_inst_tac [("x","T")] exI 1);
by (auto_tac (claset(),simpset() addsimps prat_add_ac));
qed "prat_add_less2_mono1";

Goal  
      "!!(q1::prat). q1 < q2 ==> x + q1 < x + q2";
by (auto_tac (claset() addIs [prat_add_less2_mono1],
    simpset() addsimps [prat_add_commute]));
qed "prat_add_less2_mono2";

(* ordering of multiplication for positive fractions *)
Goalw [prat_less_def] 
      "!!(q1::prat). q1 < q2 ==> q1 * x < q2 * x";
by (Step_tac 1);
by (res_inst_tac [("x","T*x")] exI 1);
by (auto_tac (claset(),simpset() addsimps [prat_add_mult_distrib]));
qed "prat_mult_less2_mono1";

Goal "!!(q1::prat). q1 < q2  ==> x * q1 < x * q2";
by (auto_tac (claset() addDs [prat_mult_less2_mono1],
    simpset() addsimps [prat_mult_commute]));
qed "prat_mult_left_less2_mono1";

(* there is no smallest positive fraction *)
Goalw [prat_less_def] "? (x::prat). x < y";
by (cut_facts_tac [lemma_prat_dense] 1);
by (Fast_tac 1);
qed "qless_Ex";

(* lemma for proving $< is linear *)
Goalw [prat_def,prat_less_def] 
      "ratrel ^^ {(x, y * ya)} : {p::(pnat*pnat).True}/ratrel";
by (asm_full_simp_tac (simpset() addsimps [ratrel_def,quotient_def]) 1);
by (Blast_tac 1);
qed "lemma_prat_less_linear";

(* linearity of < -- Gleason p. 120 - Proposition 9-2.6 *)
(*** FIXME Proof long ***)
Goalw [prat_less_def] 
      "(q1::prat) < q2 | q1 = q2 | q2 < q1";
by (res_inst_tac [("z","q1")] eq_Abs_prat 1);
by (res_inst_tac [("z","q2")] eq_Abs_prat 1);
by (Step_tac 1 THEN REPEAT(dtac (not_ex RS iffD1) 1) 
               THEN Auto_tac);
by (cut_inst_tac  [("z1.0","x*ya"),
   ("z2.0","xa*y")] pnat_linear_Ex_eq 1);
by (EVERY1[etac disjE,etac exE]);
by (eres_inst_tac 
    [("x","Abs_prat(ratrel^^{(xb,ya*y)})")] allE 1);
by (asm_full_simp_tac 
    (simpset() addsimps [prat_add, pnat_mult_assoc 
     RS sym,pnat_add_mult_distrib RS sym]) 1);
by (EVERY1[asm_full_simp_tac (simpset() addsimps pnat_mult_ac),
    etac disjE, assume_tac, etac exE]);
by (thin_tac "!T. Abs_prat (ratrel ^^ {(x, y)}) + T ~= \
\     Abs_prat (ratrel ^^ {(xa, ya)})" 1);
by (eres_inst_tac [("x","Abs_prat(ratrel^^{(xb,y*ya)})")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [prat_add,
      pnat_mult_assoc RS sym,pnat_add_mult_distrib RS sym]) 1);
by (asm_full_simp_tac (simpset() addsimps pnat_mult_ac) 1);
qed "prat_linear";

Goal
    "!!(q1::prat). [| q1 < q2 ==> P;  q1 = q2 ==> P; \
\          q2 < q1 ==> P |] ==> P";
by (cut_inst_tac [("q1.0","q1"),("q2.0","q2")] prat_linear 1);
by Auto_tac;
qed "prat_linear_less2";

(* Gleason p. 120 -- 9-2.6 (iv) *)
Goal 
 "!!(q1::prat). [| q1 < q2; qinv(q1) = qinv(q2) |] ==> P";
by (cut_inst_tac [("x","qinv (q2)"),("q1.0","q1"),
   ("q2.0","q2")] prat_mult_less2_mono1 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1 THEN dtac sym 1);
by (auto_tac (claset(),simpset() addsimps [prat_less_not_refl]));
qed "lemma1_qinv_prat_less";

Goal 
 "!!(q1::prat). [| q1 < q2; qinv(q1) < qinv(q2) |] ==> P";
by (cut_inst_tac [("x","qinv (q2)"),("q1.0","q1"),
   ("q2.0","q2")] prat_mult_less2_mono1 1);
by (assume_tac 1);
by (cut_inst_tac [("x","q1"),("q1.0","qinv (q1)"),
   ("q2.0","qinv (q2)")] prat_mult_left_less2_mono1 1);
by Auto_tac;
by (dres_inst_tac [("q2.0","prat_of_pnat (Abs_pnat 1)")] prat_less_trans 1);
by (auto_tac (claset(),simpset() addsimps 
    [prat_less_not_refl]));
qed "lemma2_qinv_prat_less";

Goal 
      "!!(q1::prat). q1 < q2  ==> qinv (q2) < qinv (q1)";
by (res_inst_tac [("q2.0","qinv q1"),
         ("q1.0","qinv q2")] prat_linear_less2 1);
by (auto_tac (claset() addEs [lemma1_qinv_prat_less,
                 lemma2_qinv_prat_less],simpset()));
qed "qinv_prat_less";

Goal "!!(q1::prat). q1 < prat_of_pnat (Abs_pnat 1) \
\     ==> prat_of_pnat (Abs_pnat 1) < qinv(q1)";
by (dtac qinv_prat_less 1);
by (full_simp_tac (simpset() addsimps [qinv_1]) 1);
qed "prat_qinv_gt_1";

Goalw [pnat_one_def] 
     "!!(q1::prat). q1 < prat_of_pnat 1p \
\     ==> prat_of_pnat 1p < qinv(q1)";
by (etac prat_qinv_gt_1 1);
qed "prat_qinv_is_gt_1";

Goalw [prat_less_def] 
      "prat_of_pnat (Abs_pnat 1) < prat_of_pnat (Abs_pnat 1) \
\                   + prat_of_pnat (Abs_pnat 1)";
by (Fast_tac 1); 
qed "prat_less_1_2";

Goal "qinv(prat_of_pnat (Abs_pnat 1) + \
\     prat_of_pnat (Abs_pnat 1)) < prat_of_pnat (Abs_pnat 1)";
by (cut_facts_tac [prat_less_1_2 RS qinv_prat_less] 1);
by (asm_full_simp_tac (simpset() addsimps [qinv_1]) 1);
qed "prat_less_qinv_2_1";

Goal "!!(x::prat). x < y ==> x*qinv(y) < prat_of_pnat (Abs_pnat 1)";
by (dres_inst_tac [("x","qinv(y)")] prat_mult_less2_mono1 1);
by (Asm_full_simp_tac 1);
qed "prat_mult_qinv_less_1";

Goal "(x::prat) < x + x";
by (cut_inst_tac [("x","x")] 
    (prat_less_1_2 RS prat_mult_left_less2_mono1) 1);
by (asm_full_simp_tac (simpset() addsimps 
    [prat_add_mult_distrib2]) 1);
qed "prat_self_less_add_self";

Goalw [prat_less_def] "(x::prat) < y + x";
by (res_inst_tac [("x","y")] exI 1);
by (simp_tac (simpset() addsimps [prat_add_commute]) 1);
qed "prat_self_less_add_right";

Goal "(x::prat) < x + y";
by (rtac (prat_add_commute RS subst) 1);
by (simp_tac (simpset() addsimps [prat_self_less_add_right]) 1);
qed "prat_self_less_add_left";

Goalw [prat_less_def] "prat_of_pnat 1p < y ==> (x::prat) < x * y";
by (auto_tac (claset(),simpset() addsimps [pnat_one_def,
    prat_add_mult_distrib2]));
qed "prat_self_less_mult_right";

(*** Properties of <= ***)

Goalw [prat_le_def] "~(w < z) ==> z <= (w::prat)";
by (assume_tac 1);
qed "prat_leI";

Goalw [prat_le_def] "z<=w ==> ~(w<(z::prat))";
by (assume_tac 1);
qed "prat_leD";

val prat_leE = make_elim prat_leD;

Goal "(~(w < z)) = (z <= (w::prat))";
by (fast_tac (claset() addSIs [prat_leI,prat_leD]) 1);
qed "prat_less_le_iff";

Goalw [prat_le_def] "~ z <= w ==> w<(z::prat)";
by (Fast_tac 1);
qed "not_prat_leE";

Goalw [prat_le_def] "z < w ==> z <= (w::prat)";
by (fast_tac (claset() addEs [prat_less_asym]) 1);
qed "prat_less_imp_le";

Goalw [prat_le_def] "!!(x::prat). x <= y ==> x < y | x = y";
by (cut_facts_tac [prat_linear] 1);
by (fast_tac (claset() addEs [prat_less_irrefl,prat_less_asym]) 1);
qed "prat_le_imp_less_or_eq";

Goalw [prat_le_def] "z<w | z=w ==> z <=(w::prat)";
by (cut_facts_tac [prat_linear] 1);
by (fast_tac (claset() addEs [prat_less_irrefl,prat_less_asym]) 1);
qed "prat_less_or_eq_imp_le";

Goal "(x <= (y::prat)) = (x < y | x=y)";
by (REPEAT(ares_tac [iffI, prat_less_or_eq_imp_le, prat_le_imp_less_or_eq] 1));
qed "prat_le_eq_less_or_eq";

Goal "w <= (w::prat)";
by (simp_tac (simpset() addsimps [prat_le_eq_less_or_eq]) 1);
qed "prat_le_refl";

val prems = goal thy "!!i. [| i <= j; j < k |] ==> i < (k::prat)";
by (dtac prat_le_imp_less_or_eq 1);
by (fast_tac (claset() addIs [prat_less_trans]) 1);
qed "prat_le_less_trans";

Goal "!! (i::prat). [| i < j; j <= k |] ==> i < k";
by (dtac prat_le_imp_less_or_eq 1);
by (fast_tac (claset() addIs [prat_less_trans]) 1);
qed "prat_less_le_trans";

Goal "[| i <= j; j <= k |] ==> i <= (k::prat)";
by (EVERY1 [dtac prat_le_imp_less_or_eq, dtac prat_le_imp_less_or_eq,
            rtac prat_less_or_eq_imp_le, fast_tac (claset() addIs [prat_less_trans])]);
qed "prat_le_trans";

Goal "[| z <= w; w <= z |] ==> z = (w::prat)";
by (EVERY1 [dtac prat_le_imp_less_or_eq, dtac prat_le_imp_less_or_eq,
            fast_tac (claset() addEs [prat_less_irrefl,prat_less_asym])]);
qed "prat_le_anti_sym";

Goal "[| ~ y < x; y ~= x |] ==> x < (y::prat)";
by (rtac not_prat_leE 1);
by (fast_tac (claset() addDs [prat_le_imp_less_or_eq]) 1);
qed "not_less_not_eq_prat_less";

Goalw [prat_less_def] 
      "[| x1 < y1; x2 < y2 |] ==> x1 + x2 < y1 + (y2::prat)";
by (REPEAT(etac exE 1));
by (res_inst_tac [("x","T+Ta")] exI 1);
by (auto_tac (claset(),simpset() addsimps prat_add_ac));
qed "prat_add_less_mono";

Goalw [prat_less_def] 
      "[| x1 < y1; x2 < y2 |] ==> x1 * x2 < y1 * (y2::prat)";
by (REPEAT(etac exE 1));
by (res_inst_tac [("x","T*Ta+T*x2+x1*Ta")] exI 1);
by (auto_tac (claset(),simpset() addsimps prat_add_ac @ 
    [prat_add_mult_distrib,prat_add_mult_distrib2]));
qed "prat_mult_less_mono";

(* more prat_le *)
Goal "!!(q1::prat). q1 <= q2  ==> x * q1 <= x * q2";
by (dtac prat_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [prat_le_refl,
    prat_less_imp_le,prat_mult_left_less2_mono1],simpset()));
qed "prat_mult_left_le2_mono1";

Goal "!!(q1::prat). q1 <= q2  ==> q1 * x <= q2 * x";
by (auto_tac (claset() addDs [prat_mult_left_le2_mono1],
    simpset() addsimps [prat_mult_commute]));
qed "prat_mult_le2_mono1";

Goal 
      "!!(q1::prat). q1 <= q2  ==> qinv (q2) <= qinv (q1)";
by (dtac prat_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [prat_le_refl,
    prat_less_imp_le,qinv_prat_less],simpset()));
qed "qinv_prat_le";

Goal "!!(q1::prat). q1 <= q2  ==> x + q1 <= x + q2";
by (dtac prat_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [prat_le_refl,
    prat_less_imp_le,prat_add_less2_mono1],
    simpset() addsimps [prat_add_commute]));
qed "prat_add_left_le2_mono1";

Goal "!!(q1::prat). q1 <= q2  ==> q1 + x <= q2 + x";
by (auto_tac (claset() addDs [prat_add_left_le2_mono1],
    simpset() addsimps [prat_add_commute]));
qed "prat_add_le2_mono1";

Goal "!!k l::prat. [|i<=j;  k<=l |] ==> i + k <= j + l";
by (etac (prat_add_le2_mono1 RS prat_le_trans) 1);
by (simp_tac (simpset() addsimps [prat_add_commute]) 1);
(*j moves to the end because it is free while k, l are bound*)
by (etac prat_add_le2_mono1 1);
qed "prat_add_le_mono";

Goal "!!(x::prat). x + y < z + y ==> x < z";
by (rtac ccontr 1);
by (etac (prat_leI RS prat_le_imp_less_or_eq RS disjE) 1);
by (dres_inst_tac [("x","y"),("q1.0","z")] prat_add_less2_mono1 1);
by (auto_tac (claset() addIs [prat_less_asym],
    simpset() addsimps [prat_less_not_refl]));
qed "prat_add_right_less_cancel";

Goal "!!(x::prat). y + x < y + z ==> x < z";
by (res_inst_tac [("y","y")] prat_add_right_less_cancel 1);
by (asm_full_simp_tac (simpset() addsimps [prat_add_commute]) 1);
qed "prat_add_left_less_cancel";

(*** lemmas required for lemma_gleason9_34 in PReal : w*y > y/z ***)
Goalw [prat_of_pnat_def] 
      "Abs_prat(ratrel^^{(x,y)}) = (prat_of_pnat x)*qinv(prat_of_pnat y)";
by (auto_tac (claset(),simpset() addsimps [prat_mult,qinv,pnat_mult_1_left,
    pnat_mult_1]));
qed "Abs_prat_mult_qinv";

Goal "Abs_prat(ratrel^^{(x,y)}) <= Abs_prat(ratrel^^{(x,Abs_pnat 1)})";
by (simp_tac (simpset() addsimps [Abs_prat_mult_qinv]) 1);
by (rtac prat_mult_left_le2_mono1 1);
by (rtac qinv_prat_le 1);
by (pnat_ind_tac "y" 1);
by (dres_inst_tac [("x","prat_of_pnat (Abs_pnat 1)")] prat_add_le2_mono1 2);
by (cut_facts_tac [prat_less_1_2 RS prat_less_imp_le] 2);
by (auto_tac (claset() addIs [prat_le_trans],
    simpset() addsimps [prat_le_refl,
    pSuc_is_plus_one,pnat_one_def,prat_of_pnat_add]));
qed "lemma_Abs_prat_le1";

Goal "Abs_prat(ratrel^^{(x,Abs_pnat 1)}) <= Abs_prat(ratrel^^{(x*y,Abs_pnat 1)})";
by (simp_tac (simpset() addsimps [Abs_prat_mult_qinv]) 1);
by (rtac prat_mult_le2_mono1 1);
by (pnat_ind_tac "y" 1);
by (dres_inst_tac [("x","prat_of_pnat x")] prat_add_le2_mono1 2);
by (cut_inst_tac [("z","prat_of_pnat x")] (prat_self_less_add_self 
    RS prat_less_imp_le) 2);
by (auto_tac (claset() addIs [prat_le_trans],
    simpset() addsimps [prat_le_refl,
    pSuc_is_plus_one,pnat_one_def,prat_add_mult_distrib2,
    prat_of_pnat_add,prat_of_pnat_mult]));
qed "lemma_Abs_prat_le2";

Goal "Abs_prat(ratrel^^{(x,z)}) <= Abs_prat(ratrel^^{(x*y,Abs_pnat 1)})";
by (fast_tac (claset() addIs [prat_le_trans,
    lemma_Abs_prat_le1,lemma_Abs_prat_le2]) 1);
qed "lemma_Abs_prat_le3";

Goal "Abs_prat(ratrel^^{(x*y,Abs_pnat 1)}) * Abs_prat(ratrel^^{(w,x)}) = \
\         Abs_prat(ratrel^^{(w*y,Abs_pnat 1)})";
by (full_simp_tac (simpset() addsimps [prat_mult,
    pnat_mult_1,pnat_mult_1_left] @ pnat_mult_ac) 1);
qed "pre_lemma_gleason9_34";

Goal "Abs_prat(ratrel^^{(y*x,Abs_pnat 1*y)}) = \
\         Abs_prat(ratrel^^{(x,Abs_pnat 1)})";
by (auto_tac (claset(),simpset() addsimps 
    [pnat_mult_1,pnat_mult_1_left] @ pnat_mult_ac));
qed "pre_lemma_gleason9_34b";

Goal "(prat_of_pnat n < prat_of_pnat m) = (n < m)";
by (auto_tac (claset(),simpset() addsimps [prat_less_def,
    pnat_less_iff,prat_of_pnat_add]));
by (res_inst_tac [("z","T")] eq_Abs_prat 1);
by (auto_tac (claset() addDs [pnat_eq_lessI],
    simpset() addsimps [prat_add,pnat_mult_1,
    pnat_mult_1_left,prat_of_pnat_def,pnat_less_iff RS sym]));
qed "prat_of_pnat_less_iff";

Addsimps [prat_of_pnat_less_iff];

(*------------------------------------------------------------------*)

(*** prove witness that will be required to prove non-emptiness ***)
(*** of preal type as defined using Dedekind Sections in PReal  ***)
(*** Show that exists positive real `one' ***)

Goal "? q. q: {x::prat. x < prat_of_pnat (Abs_pnat 1)}";
by (fast_tac (claset() addIs [prat_less_qinv_2_1]) 1);
qed "lemma_prat_less_1_memEx";

Goal "{x::prat. x < prat_of_pnat (Abs_pnat 1)} ~= {}";
by (rtac notI 1);
by (cut_facts_tac [lemma_prat_less_1_memEx] 1);
by (Asm_full_simp_tac 1);
qed "lemma_prat_less_1_set_non_empty";

Goalw [psubset_def] "{} < {x::prat. x < prat_of_pnat (Abs_pnat 1)}";
by (asm_full_simp_tac (simpset() addsimps 
         [lemma_prat_less_1_set_non_empty RS not_sym]) 1);
qed "empty_set_psubset_lemma_prat_less_1_set";

(*** exists rational not in set --- prat_of_pnat (Abs_pnat 1) itself ***)
Goal "? q. q ~: {x::prat. x < prat_of_pnat (Abs_pnat 1)}";
by (res_inst_tac [("x","prat_of_pnat (Abs_pnat 1)")] exI 1);
by (auto_tac (claset(),simpset() addsimps [prat_less_not_refl]));
qed "lemma_prat_less_1_not_memEx";

Goal "{x::prat. x < prat_of_pnat (Abs_pnat 1)} ~= {q::prat. True}";
by (rtac notI 1);
by (cut_facts_tac [lemma_prat_less_1_not_memEx] 1);
by (Asm_full_simp_tac 1);
qed "lemma_prat_less_1_set_not_rat_set";

Goalw [psubset_def,subset_def] 
      "{x::prat. x < prat_of_pnat (Abs_pnat 1)} < {q::prat. True}";
by (asm_full_simp_tac (simpset() addsimps 
      [lemma_prat_less_1_set_not_rat_set,
       lemma_prat_less_1_not_memEx]) 1);
qed "lemma_prat_less_1_set_psubset_rat_set";

(*** prove non_emptiness of type ***)
Goal "{x::prat. x < prat_of_pnat (Abs_pnat 1)} : {A. {} < A & \
\               A < {q::prat. True} & \
\               (!y: A. ((!z. z < y --> z: A) & \
\               (? u: A. y < u)))}";
by (auto_tac (claset() addDs [prat_less_trans],
    simpset() addsimps [empty_set_psubset_lemma_prat_less_1_set,
                       lemma_prat_less_1_set_psubset_rat_set]));
by (dtac prat_dense 1);
by (Fast_tac 1);
qed "preal_1";






