(*  Title       : PReal.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The positive reals as Dedekind sections of positive
                  rationals. Fundamentals of Abstract Analysis 
                  [Gleason- p. 121] provides some of the definitions.
*)

claset_ref() := claset() delWrapper "bspec";

Goal "inj_on Abs_preal preal";
by (rtac inj_on_inverseI 1);
by (etac Abs_preal_inverse 1);
qed "inj_on_Abs_preal";

Addsimps [inj_on_Abs_preal RS inj_on_iff];

Goal "inj(Rep_preal)";
by (rtac inj_inverseI 1);
by (rtac Rep_preal_inverse 1);
qed "inj_Rep_preal";

Goalw [preal_def] "{} ~: preal";
by (Fast_tac 1);
qed "empty_not_mem_preal";

(* {} : preal ==> P *)
bind_thm ("empty_not_mem_prealE", empty_not_mem_preal RS notE);

Addsimps [empty_not_mem_preal];

Goalw [preal_def] "{x::prat. x < prat_of_pnat (Abs_pnat 1)} : preal";
by (rtac preal_1 1);
qed "one_set_mem_preal";

Addsimps [one_set_mem_preal];

Goalw [preal_def] "x : preal ==> {} < x";
by (Fast_tac 1);
qed "preal_psubset_empty";

Goal "{} < Rep_preal x";
by (rtac (Rep_preal RS preal_psubset_empty) 1);
qed "Rep_preal_psubset_empty";

Goal "? x. x: Rep_preal X";
by (cut_inst_tac [("x","X")]  Rep_preal_psubset_empty 1);
by (auto_tac (claset() addIs [(equals0I RS sym)],
              simpset() addsimps [psubset_def]));
qed "mem_Rep_preal_Ex";

Goalw [preal_def] 
      "[| {} < A; A < UNIV; \
\              (!y: A. ((!z. z < y --> z: A) & \
\                        (? u: A. y < u))) |] ==> A : preal";
by (Fast_tac 1);
qed "prealI1";
    
Goalw [preal_def] 
      "[| {} < A; A < UNIV; \
\              !y: A. (!z. z < y --> z: A); \
\              !y: A. (? u: A. y < u) |] ==> A : preal";
by (Best_tac 1);
qed "prealI2";

Goalw [preal_def] 
      "A : preal ==> {} < A & A < UNIV & \
\                         (!y: A. ((!z. z < y --> z: A) & \
\                                  (? u: A. y < u)))";
by (Fast_tac 1);
qed "prealE_lemma";


AddSIs [prealI1,prealI2];

Addsimps [Abs_preal_inverse];


Goalw [preal_def] "A : preal ==> {} < A";
by (Fast_tac 1);
qed "prealE_lemma1";

Goalw [preal_def] "A : preal ==> A < UNIV";
by (Fast_tac 1);
qed "prealE_lemma2";

Goalw [preal_def] "A : preal ==> !y: A. (!z. z < y --> z: A)";
by (Fast_tac 1);
qed "prealE_lemma3";

Goal "[| A : preal; y: A |] ==> (!z. z < y --> z: A)";
by (fast_tac (claset() addSDs [prealE_lemma3]) 1);
qed "prealE_lemma3a";

Goal "[| A : preal; y: A; z < y |] ==> z: A";
by (fast_tac (claset() addSDs [prealE_lemma3a]) 1);
qed "prealE_lemma3b";

Goalw [preal_def] "A : preal ==> !y: A. (? u: A. y < u)";
by (Fast_tac 1);
qed "prealE_lemma4";

Goal "[| A : preal; y: A |] ==> ? u: A. y < u";
by (fast_tac (claset() addSDs [prealE_lemma4]) 1);
qed "prealE_lemma4a";

Goal "? x. x~: Rep_preal X";
by (cut_inst_tac [("x","X")] Rep_preal 1);
by (dtac prealE_lemma2 1);
by (rtac ccontr 1);
by (auto_tac (claset(),simpset() addsimps [psubset_def]));
by (blast_tac (claset() addIs [set_ext] addEs [swap]) 1);
qed "not_mem_Rep_preal_Ex";

(** preal_of_prat: the injection from prat to preal **)
(** A few lemmas **)

Goal "{xa::prat. xa < y} : preal";
by (cut_facts_tac [qless_Ex] 1);
by (auto_tac (claset() addIs[prat_less_trans]
                       addSEs [equalityCE, prat_less_irrefl], 
	      simpset()));
by (blast_tac (claset() addDs [prat_dense]) 1);
qed "lemma_prat_less_set_mem_preal";

Goal "!!(x::prat). {xa. xa < x} = {x. x < y} ==> x = y";
by (cut_inst_tac [("q1.0","x"),("q2.0","y")] prat_linear 1);
by Auto_tac;
by (dtac prat_dense 2 THEN etac exE 2);
by (dtac prat_dense 1 THEN etac exE 1);
by (auto_tac (claset() addDs [prat_less_not_sym] addSEs [equalityCE],
              simpset()));
qed "lemma_prat_set_eq";

Goal "inj(preal_of_prat)";
by (rtac injI 1);
by (rewtac preal_of_prat_def);
by (dtac (inj_on_Abs_preal RS inj_onD) 1);
by (rtac lemma_prat_less_set_mem_preal 1);
by (rtac lemma_prat_less_set_mem_preal 1);
by (etac lemma_prat_set_eq 1);
qed "inj_preal_of_prat";

      (*** theorems for ordering ***)
(* prove introduction and elimination rules for preal_less *)

(* A positive fraction not in a positive real is an upper bound *)
(* Gleason p. 122 - Remark (1)                                  *)

Goal "x ~: Rep_preal(R) ==> !y: Rep_preal(R). y < x";
by (cut_inst_tac [("x1","R")] (Rep_preal RS prealE_lemma) 1);
by (auto_tac (claset() addIs [not_less_not_eq_prat_less],simpset()));
qed "not_in_preal_ub";

(* preal_less is a strong order i.e nonreflexive and transitive *)

Goalw [preal_less_def] "~ (x::preal) < x";
by (simp_tac (simpset() addsimps [psubset_def]) 1);
qed "preal_less_not_refl";

(*** y < y ==> P ***)
bind_thm("preal_less_irrefl",preal_less_not_refl RS notE);

Goal "!!(x::preal). x < y ==> x ~= y";
by (auto_tac (claset(),simpset() addsimps [preal_less_not_refl]));
qed "preal_not_refl2";

Goalw  [preal_less_def] "!!(x::preal). [| x < y; y < z |] ==> x < z";
by (auto_tac (claset() addDs [subsetD,equalityI],
              simpset() addsimps [psubset_def]));
qed "preal_less_trans";

Goal "!! (q1::preal). q1 < q2 ==> ~ q2 < q1";
by (rtac notI 1);
by (dtac preal_less_trans 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [preal_less_not_refl]) 1);
qed "preal_less_not_sym";

(* [| x < y;  ~P ==> y < x |] ==> P *)
bind_thm ("preal_less_asym", preal_less_not_sym RS swap);

Goalw [preal_less_def] 
      "(r1::preal) < r2 | r1 = r2 | r2 < r1";
by (auto_tac (claset() addSDs [inj_Rep_preal RS injD],
              simpset() addsimps [psubset_def]));
by (rtac prealE_lemma3b 1 THEN rtac Rep_preal 1);
by (assume_tac 1);
by (fast_tac (claset() addDs [not_in_preal_ub]) 1);
qed "preal_linear";

Goal "!!(r1::preal). [| r1 < r2 ==> P;  r1 = r2 ==> P; \
\                       r2 < r1 ==> P |] ==> P";
by (cut_inst_tac [("r1.0","r1"),("r2.0","r2")] preal_linear 1);
by Auto_tac;
qed "preal_linear_less2";

  (*** Properties of addition ***)

Goalw [preal_add_def] "(x::preal) + y = y + x";
by (res_inst_tac [("f","Abs_preal")] arg_cong 1);
by (rtac set_ext 1);
by (blast_tac (claset() addIs [prat_add_commute RS subst]) 1);
qed "preal_add_commute";

(** addition of two positive reals gives a positive real **)
(** lemmas for proving positive reals addition set in preal **)

(** Part 1 of Dedekind sections def **)
Goal "{} < {w. ? x: Rep_preal R. ? y:Rep_preal S. w = x + y}";
by (cut_facts_tac [mem_Rep_preal_Ex,mem_Rep_preal_Ex] 1);
by (auto_tac (claset() addSIs [psubsetI] addEs [equalityCE],simpset()));
qed "preal_add_set_not_empty";

(** Part 2 of Dedekind sections def **)
Goal "? q. q  ~: {w. ? x: Rep_preal R. ? y:Rep_preal S. w = x + y}";
by (cut_inst_tac [("X","R")] not_mem_Rep_preal_Ex 1);
by (cut_inst_tac [("X","S")] not_mem_Rep_preal_Ex 1);
by (REPEAT(etac exE 1));
by (REPEAT(dtac not_in_preal_ub 1));
by (res_inst_tac [("x","x+xa")] exI 1);
by (Auto_tac THEN (REPEAT(etac ballE 1)) THEN Auto_tac);
by (dtac prat_add_less_mono 1);
by (auto_tac (claset(),simpset() addsimps [prat_less_not_refl]));
qed "preal_not_mem_add_set_Ex";

Goal "{w. ? x: Rep_preal R. ? y:Rep_preal S. w = x + y} < UNIV";
by (auto_tac (claset() addSIs [psubsetI],simpset()));
by (cut_inst_tac [("R","R"),("S","S")] preal_not_mem_add_set_Ex 1);
by (etac exE 1);
by (eres_inst_tac [("c","q")] equalityCE 1);
by Auto_tac;
qed "preal_add_set_not_prat_set";

(** Part 3 of Dedekind sections def **)
Goal "!y: {w. ? x: Rep_preal R. ? y: Rep_preal S. w = x + y}. \
\         !z. z < y --> z : {w. ? x:Rep_preal R. ? y:Rep_preal S. w = x + y}";
by Auto_tac;
by (ftac prat_mult_qinv_less_1 1);
by (forw_inst_tac [("x","x"),("q2.0","prat_of_pnat (Abs_pnat 1)")] 
    prat_mult_less2_mono1 1);
by (forw_inst_tac [("x","ya"),("q2.0","prat_of_pnat (Abs_pnat 1)")] 
    prat_mult_less2_mono1 1);
by (Asm_full_simp_tac 1);
by (REPEAT(dtac (Rep_preal RS prealE_lemma3a) 1));
by (REPEAT(etac allE 1));
by Auto_tac;
by (REPEAT(rtac bexI 1));
by (auto_tac (claset(),simpset() addsimps [prat_add_mult_distrib2 
     RS sym,prat_add_assoc RS sym,prat_mult_assoc]));
qed "preal_add_set_lemma3";

Goal "!y: {w. ? x: Rep_preal R. ? y: Rep_preal S. w = x + y}. \
\         ? u: {w. ? x: Rep_preal R. ? y: Rep_preal S. w = x + y}. y < u";
by Auto_tac;
by (dtac (Rep_preal RS prealE_lemma4a) 1);
by (auto_tac (claset() addIs [prat_add_less2_mono1],simpset()));
qed "preal_add_set_lemma4";

Goal "{w. ? x: Rep_preal R. ? y: Rep_preal S. w = x + y} : preal";
by (rtac prealI2 1);
by (rtac preal_add_set_not_empty 1);
by (rtac preal_add_set_not_prat_set 1);
by (rtac preal_add_set_lemma3 1);
by (rtac preal_add_set_lemma4 1);
qed "preal_mem_add_set";

Goalw [preal_add_def] "((x::preal) + y) + z = x + (y + z)";
by (res_inst_tac [("f","Abs_preal")] arg_cong 1);
by (rtac set_ext 1);
by (rtac (preal_mem_add_set RS Abs_preal_inverse RS ssubst) 1);
by (rtac (preal_mem_add_set RS Abs_preal_inverse RS ssubst) 1);
by (auto_tac (claset(),simpset() addsimps prat_add_ac));
by (rtac bexI 1);
by (auto_tac (claset() addSIs [exI],simpset() addsimps prat_add_ac));
qed "preal_add_assoc";

qed_goal "preal_add_left_commute" thy
    "(z1::preal) + (z2 + z3) = z2 + (z1 + z3)"
 (fn _ => [rtac (preal_add_commute RS trans) 1, rtac (preal_add_assoc RS trans) 1,
           rtac (preal_add_commute RS arg_cong) 1]);

(* Positive Reals addition is an AC operator *)
val preal_add_ac = [preal_add_assoc, preal_add_commute, preal_add_left_commute];

  (*** Properties of multiplication ***)

(** Proofs essentially same as for addition **)

Goalw [preal_mult_def] "(x::preal) * y = y * x";
by (res_inst_tac [("f","Abs_preal")] arg_cong 1);
by (rtac set_ext 1);
by (blast_tac (claset() addIs [prat_mult_commute RS subst]) 1);
qed "preal_mult_commute";

(** multiplication of two positive reals gives a positive real **)
(** lemmas for proving positive reals multiplication set in preal **)

(** Part 1 of Dedekind sections def **)
Goal "{} < {w. ? x: Rep_preal R. ? y:Rep_preal S. w = x * y}";
by (cut_facts_tac [mem_Rep_preal_Ex,mem_Rep_preal_Ex] 1);
by (auto_tac (claset() addSIs [psubsetI] addEs [equalityCE],simpset()));
qed "preal_mult_set_not_empty";

(** Part 2 of Dedekind sections def **)
Goal "? q. q  ~: {w. ? x: Rep_preal R. ? y:Rep_preal S. w = x * y}";
by (cut_inst_tac [("X","R")] not_mem_Rep_preal_Ex 1);
by (cut_inst_tac [("X","S")] not_mem_Rep_preal_Ex 1);
by (REPEAT(etac exE 1));
by (REPEAT(dtac not_in_preal_ub 1));
by (res_inst_tac [("x","x*xa")] exI 1);
by (Auto_tac  THEN (REPEAT(etac ballE 1)) THEN Auto_tac );
by (dtac prat_mult_less_mono 1);
by (auto_tac (claset(),simpset() addsimps [prat_less_not_refl]));
qed "preal_not_mem_mult_set_Ex";

Goal "{w. ? x: Rep_preal R. ? y:Rep_preal S. w = x * y} < UNIV";
by (auto_tac (claset() addSIs [psubsetI],simpset()));
by (cut_inst_tac [("R","R"),("S","S")] preal_not_mem_mult_set_Ex 1);
by (etac exE 1);
by (eres_inst_tac [("c","q")] equalityCE 1);
by Auto_tac;
qed "preal_mult_set_not_prat_set";

(** Part 3 of Dedekind sections def **)
Goal "!y: {w. ? x: Rep_preal R. ? y: Rep_preal S. w = x * y}. \
\         !z. z < y --> z : {w. ? x:Rep_preal R. ? y:Rep_preal S. w = x * y}";
by Auto_tac;
by (forw_inst_tac [("x","qinv(ya)"),("q1.0","z")] 
    prat_mult_left_less2_mono1 1);
by (asm_full_simp_tac (simpset() addsimps prat_mult_ac) 1);
by (dtac (Rep_preal RS prealE_lemma3a) 1);
by (etac allE 1);
by (REPEAT(rtac bexI 1));
by (auto_tac (claset(),simpset() addsimps [prat_mult_assoc]));
qed "preal_mult_set_lemma3";

Goal "!y: {w. ? x: Rep_preal R. ? y: Rep_preal S. w = x * y}. \
\         ? u: {w. ? x: Rep_preal R. ? y: Rep_preal S. w = x * y}. y < u";
by Auto_tac;
by (dtac (Rep_preal RS prealE_lemma4a) 1);
by (auto_tac (claset() addIs [prat_mult_less2_mono1],simpset()));
qed "preal_mult_set_lemma4";

Goal "{w. ? x: Rep_preal R. ? y: Rep_preal S. w = x * y} : preal";
by (rtac prealI2 1);
by (rtac preal_mult_set_not_empty 1);
by (rtac preal_mult_set_not_prat_set 1);
by (rtac preal_mult_set_lemma3 1);
by (rtac preal_mult_set_lemma4 1);
qed "preal_mem_mult_set";

Goalw [preal_mult_def] "((x::preal) * y) * z = x * (y * z)";
by (res_inst_tac [("f","Abs_preal")] arg_cong 1);
by (rtac set_ext 1);
by (rtac (preal_mem_mult_set RS Abs_preal_inverse RS ssubst) 1);
by (rtac (preal_mem_mult_set RS Abs_preal_inverse RS ssubst) 1);
by (auto_tac (claset(),simpset() addsimps prat_mult_ac));
by (rtac bexI 1);
by (auto_tac (claset() addSIs [exI],simpset() addsimps prat_mult_ac));
qed "preal_mult_assoc";

qed_goal "preal_mult_left_commute" thy
    "(z1::preal) * (z2 * z3) = z2 * (z1 * z3)"
 (fn _ => [rtac (preal_mult_commute RS trans) 1, 
           rtac (preal_mult_assoc RS trans) 1,
           rtac (preal_mult_commute RS arg_cong) 1]);

(* Positive Reals multiplication is an AC operator *)
val preal_mult_ac = [preal_mult_assoc, 
                     preal_mult_commute, 
                     preal_mult_left_commute];

(* Positive Real 1 is the multiplicative identity element *) 
(* long *)
Goalw [preal_of_prat_def,preal_mult_def] 
      "(preal_of_prat (prat_of_pnat (Abs_pnat 1))) * z = z";
by (rtac (Rep_preal_inverse RS subst) 1);
by (res_inst_tac [("f","Abs_preal")] arg_cong 1);
by (rtac (one_set_mem_preal RS Abs_preal_inverse RS ssubst) 1);
by (rtac set_ext 1);
by (auto_tac(claset(),simpset() addsimps [Rep_preal_inverse]));
by (EVERY1[dtac (Rep_preal RS prealE_lemma4a),etac bexE]);
by (dtac prat_mult_less_mono 1);
by (auto_tac (claset() addDs [Rep_preal RS prealE_lemma3a],simpset()));
by (EVERY1[forward_tac [Rep_preal RS prealE_lemma4a],etac bexE]);
by (forw_inst_tac [("x","qinv(u)"),("q1.0","x")] 
    prat_mult_less2_mono1 1);
by (rtac exI 1 THEN Auto_tac THEN res_inst_tac [("x","u")] bexI 1);
by (auto_tac (claset(),simpset() addsimps [prat_mult_assoc]));
qed "preal_mult_1";

Goal "z * (preal_of_prat (prat_of_pnat (Abs_pnat 1))) = z";
by (rtac (preal_mult_commute RS subst) 1);
by (rtac preal_mult_1 1);
qed "preal_mult_1_right";

(** Lemmas **)

qed_goal "preal_add_assoc_cong" thy
    "!!z. (z::preal) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
 (fn _ => [(asm_simp_tac (simpset() addsimps [preal_add_assoc RS sym]) 1)]);

qed_goal "preal_add_assoc_swap" thy "(z::preal) + (v + w) = v + (z + w)"
 (fn _ => [(REPEAT (ares_tac [preal_add_commute RS preal_add_assoc_cong] 1))]);

(** Distribution of multiplication across addition **)
(** lemmas for the proof **)

 (** lemmas **)
Goalw [preal_add_def] 
      "z: Rep_preal(R+S) ==> \
\           ? x: Rep_preal(R). ? y: Rep_preal(S). z = x + y";
by (dtac (preal_mem_add_set RS Abs_preal_inverse RS subst) 1);
by (Fast_tac 1);
qed "mem_Rep_preal_addD";

Goalw [preal_add_def] 
      "? x: Rep_preal(R). ? y: Rep_preal(S). z = x + y \
\      ==> z: Rep_preal(R+S)";
by (rtac (preal_mem_add_set RS Abs_preal_inverse RS ssubst) 1);
by (Fast_tac 1);
qed "mem_Rep_preal_addI";

Goal " z: Rep_preal(R+S) = (? x: Rep_preal(R). \
\                                 ? y: Rep_preal(S). z = x + y)";
by (fast_tac (claset() addSIs [mem_Rep_preal_addD,mem_Rep_preal_addI]) 1);
qed "mem_Rep_preal_add_iff";

Goalw [preal_mult_def] 
      "z: Rep_preal(R*S) ==> \
\           ? x: Rep_preal(R). ? y: Rep_preal(S). z = x * y";
by (dtac (preal_mem_mult_set RS Abs_preal_inverse RS subst) 1);
by (Fast_tac 1);
qed "mem_Rep_preal_multD";

Goalw [preal_mult_def] 
      "? x: Rep_preal(R). ? y: Rep_preal(S). z = x * y \
\      ==> z: Rep_preal(R*S)";
by (rtac (preal_mem_mult_set RS Abs_preal_inverse RS ssubst) 1);
by (Fast_tac 1);
qed "mem_Rep_preal_multI";

Goal " z: Rep_preal(R*S) = (? x: Rep_preal(R). \
\                                 ? y: Rep_preal(S). z = x * y)";
by (fast_tac (claset() addSIs [mem_Rep_preal_multD,mem_Rep_preal_multI]) 1);
qed "mem_Rep_preal_mult_iff";

(** More lemmas for preal_add_mult_distrib2 **)
goal PRat.thy "!!(a1::prat). a1 < a2 ==> a1 * b + a2 * c < a2 * (b + c)";
by (auto_tac (claset() addSIs [prat_add_less2_mono1,prat_mult_less2_mono1],
              simpset() addsimps [prat_add_mult_distrib2]));
qed "lemma_prat_add_mult_mono";

Goal "[| xb: Rep_preal z1; xc: Rep_preal z2; ya: \
\                  Rep_preal w; yb: Rep_preal w |] ==> \
\                  xb * ya + xc * yb: Rep_preal (z1 * w + z2 * w)";
by (fast_tac (claset() addIs [mem_Rep_preal_addI,mem_Rep_preal_multI]) 1);
qed "lemma_add_mult_mem_Rep_preal";

Goal "[| xb: Rep_preal z1; xc: Rep_preal z2; ya: \
\                  Rep_preal w; yb: Rep_preal w |] ==> \
\                  yb*(xb + xc): Rep_preal (w*(z1 + z2))";
by (fast_tac (claset() addIs [mem_Rep_preal_addI,mem_Rep_preal_multI]) 1);
qed "lemma_add_mult_mem_Rep_preal1";

Goal "x: Rep_preal (w * z1 + w * z2) ==> \
\              x: Rep_preal (w * (z1 + z2))";
by (auto_tac (claset() addSDs [mem_Rep_preal_addD,mem_Rep_preal_multD],
              simpset()));
by (forw_inst_tac [("ya","xa"),("yb","xb"),("xb","ya"),("xc","yb")] 
                                   lemma_add_mult_mem_Rep_preal1 1);
by Auto_tac;
by (res_inst_tac [("q1.0","xa"),("q2.0","xb")] prat_linear_less2 1);
by (dres_inst_tac [("b","ya"),("c","yb")] lemma_prat_add_mult_mono 1);
by (rtac (Rep_preal RS prealE_lemma3b) 1);
by (auto_tac (claset(),simpset() addsimps [prat_add_mult_distrib2]));
by (dres_inst_tac [("ya","xb"),("yb","xa"),("xc","ya"),("xb","yb")] 
                                   lemma_add_mult_mem_Rep_preal1 1);
by Auto_tac;
by (dres_inst_tac [("b","yb"),("c","ya")] lemma_prat_add_mult_mono 1);
by (rtac (Rep_preal RS prealE_lemma3b) 1);
by (thin_tac "xb * ya + xb * yb  : Rep_preal (w * (z1 + z2))" 1);
by (auto_tac (claset(),simpset() addsimps [prat_add_mult_distrib,
              prat_add_commute] @ preal_add_ac ));
qed "lemma_preal_add_mult_distrib";

Goal "x: Rep_preal (w * (z1 + z2)) ==> \
\              x: Rep_preal (w * z1 + w * z2)";
by (auto_tac (claset() addSDs [mem_Rep_preal_addD,mem_Rep_preal_multD]
              addSIs [bexI,mem_Rep_preal_addI,mem_Rep_preal_multI],
              simpset() addsimps [prat_add_mult_distrib2]));
qed "lemma_preal_add_mult_distrib2";

Goal "(w * ((z1::preal) + z2)) = (w * z1) + (w * z2)";
by (rtac (inj_Rep_preal RS injD) 1);
by (rtac set_ext 1);
by (fast_tac (claset() addIs [lemma_preal_add_mult_distrib,
                       lemma_preal_add_mult_distrib2]) 1);
qed "preal_add_mult_distrib2";

Goal "(((z1::preal) + z2) * w) = (z1 * w) + (z2 * w)";
by (simp_tac (simpset() addsimps [preal_mult_commute,
                       preal_add_mult_distrib2]) 1);
qed "preal_add_mult_distrib";

(*** Prove existence of inverse ***)
(*** Inverse is a positive real ***)

Goal "? y. qinv(y) ~:  Rep_preal X";
by (cut_inst_tac [("X","X")] not_mem_Rep_preal_Ex 1);
by (etac exE 1 THEN cut_inst_tac [("x","x")] prat_as_inverse_ex 1);
by Auto_tac;
qed "qinv_not_mem_Rep_preal_Ex";

Goal "? q. q: {x. ? y. x < y & qinv y ~:  Rep_preal A}";
by (cut_inst_tac [("X","A")] qinv_not_mem_Rep_preal_Ex 1);
by Auto_tac;
by (cut_inst_tac [("y","y")] qless_Ex 1);
by (Fast_tac 1);
qed "lemma_preal_mem_inv_set_ex";

(** Part 1 of Dedekind sections def **)
Goal "{} < {x. ? y. x < y & qinv y ~:  Rep_preal A}";
by (cut_facts_tac [lemma_preal_mem_inv_set_ex] 1);
by (auto_tac (claset() addSIs [psubsetI] addEs [equalityCE],simpset()));
qed "preal_inv_set_not_empty";

(** Part 2 of Dedekind sections def **)
Goal "? y. qinv(y) :  Rep_preal X";
by (cut_inst_tac [("X","X")] mem_Rep_preal_Ex 1);
by (etac exE 1 THEN cut_inst_tac [("x","x")] prat_as_inverse_ex 1);
by Auto_tac;
qed "qinv_mem_Rep_preal_Ex";

Goal "? x. x ~: {x. ? y. x < y & qinv y ~:  Rep_preal A}";
by (rtac ccontr 1);
by (cut_inst_tac [("X","A")] qinv_mem_Rep_preal_Ex 1);
by Auto_tac;
by (EVERY1[etac allE, etac exE, etac conjE]);
by (dtac qinv_prat_less 1 THEN dtac not_in_preal_ub 1);
by (eres_inst_tac [("x","qinv y")] ballE 1);
by (dtac prat_less_trans 1);
by (auto_tac (claset(),simpset() addsimps [prat_less_not_refl]));
qed "preal_not_mem_inv_set_Ex";

Goal "{x. ? y. x < y & qinv y ~:  Rep_preal A} < UNIV";
by (auto_tac (claset() addSIs [psubsetI],simpset()));
by (cut_inst_tac [("A","A")]  preal_not_mem_inv_set_Ex 1);
by (etac exE 1);
by (eres_inst_tac [("c","x")] equalityCE 1);
by Auto_tac;
qed "preal_inv_set_not_prat_set";

(** Part 3 of Dedekind sections def **)
Goal "! y: {x. ? y. x < y & qinv y ~: Rep_preal A}. \
 \      !z. z < y --> z : {x. ? y. x < y & qinv y ~: Rep_preal A}";
by Auto_tac;
by (res_inst_tac [("x","ya")] exI 1);
by (auto_tac (claset() addIs [prat_less_trans],simpset()));
qed "preal_inv_set_lemma3";

Goal "! y: {x. ? y. x < y & qinv y ~: Rep_preal A}. \
\       Bex {x. ? y. x < y & qinv y ~: Rep_preal A} (op < y)";
by (blast_tac (claset() addDs [prat_dense]) 1);
qed "preal_inv_set_lemma4";

Goal "{x. ? y. x < y & qinv(y) ~: Rep_preal(A)} : preal";
by (rtac prealI2 1);
by (rtac preal_inv_set_not_empty 1);
by (rtac preal_inv_set_not_prat_set 1);
by (rtac preal_inv_set_lemma3 1);
by (rtac preal_inv_set_lemma4 1);
qed "preal_mem_inv_set";

(*more lemmas for inverse *)
Goal "x: Rep_preal(pinv(A)*A) ==> \
\     x: Rep_preal(preal_of_prat (prat_of_pnat (Abs_pnat 1)))";
by (auto_tac (claset() addSDs [mem_Rep_preal_multD],
              simpset() addsimps [pinv_def,preal_of_prat_def] ));
by (dtac (preal_mem_inv_set RS Abs_preal_inverse RS subst) 1);
by (auto_tac (claset() addSDs [not_in_preal_ub],simpset()));
by (dtac prat_mult_less_mono 1 THEN Blast_tac 1);
by (auto_tac (claset(),simpset()));
qed "preal_mem_mult_invD";

(*** Gleason's Lemma 9-3.4 p 122 ***)
Goal "! xa : Rep_preal(A). xa + x : Rep_preal(A) ==> \
\            ? xb : Rep_preal(A). xb + (prat_of_pnat p)*x : Rep_preal(A)";
by (cut_facts_tac [mem_Rep_preal_Ex] 1);
by (res_inst_tac [("n","p")] pnat_induct 1);
by (auto_tac (claset(),simpset() addsimps [pnat_one_def,
    pSuc_is_plus_one,prat_add_mult_distrib,
   prat_of_pnat_add,prat_add_assoc RS sym]));
qed "lemma1_gleason9_34";

Goal "Abs_prat (ratrel ^^ {(y, z)}) < xb + \
\         Abs_prat (ratrel ^^ {(x*y, Abs_pnat 1)})*Abs_prat (ratrel ^^ {(w, x)})";
by (res_inst_tac [("j","Abs_prat (ratrel ^^ {(x * y, Abs_pnat 1)}) *\
\                   Abs_prat (ratrel ^^ {(w, x)})")] prat_le_less_trans 1);
by (rtac prat_self_less_add_right 2);
by (auto_tac (claset() addIs [lemma_Abs_prat_le3],
    simpset() addsimps [prat_mult,pre_lemma_gleason9_34b,pnat_mult_assoc]));
qed "lemma1b_gleason9_34";

Goal "! xa : Rep_preal(A). xa + x : Rep_preal(A) ==> False";
by (cut_inst_tac [("X","A")] not_mem_Rep_preal_Ex 1);
by (etac exE 1);
by (dtac not_in_preal_ub 1);
by (res_inst_tac [("z","x")] eq_Abs_prat 1);
by (res_inst_tac [("z","xa")] eq_Abs_prat 1);
by (dres_inst_tac [("p","y*xb")] lemma1_gleason9_34 1);
by (etac bexE 1);
by (cut_inst_tac [("x","y"),("y","xb"),("w","xaa"),
    ("z","ya"),("xb","xba")] lemma1b_gleason9_34 1);
by (dres_inst_tac [("x","xba + prat_of_pnat (y * xb) * x")]  bspec 1);
by (auto_tac (claset() addIs [prat_less_asym],
    simpset() addsimps [prat_of_pnat_def]));
qed "lemma_gleason9_34a";

Goal "? r: Rep_preal(R). r + x ~: Rep_preal(R)";
by (rtac ccontr 1);
by (blast_tac (claset() addIs [lemma_gleason9_34a]) 1);
qed "lemma_gleason9_34";

(*** Gleason's Lemma 9-3.6  ***)
(*  lemmas for Gleason 9-3.6  *)
(*                            *) 
(******************************)

Goal "r + r*qinv(xa)*Q3 = r*qinv(xa)*(xa + Q3)";
by (full_simp_tac (simpset() addsimps [prat_add_mult_distrib2,
    prat_mult_assoc]) 1);
qed "lemma1_gleason9_36";

Goal "r*qinv(xa)*(xa*x) = r*x";
by (full_simp_tac (simpset() addsimps prat_mult_ac) 1);
qed "lemma2_gleason9_36";
(******)

(*** FIXME: long! ***)
Goal "prat_of_pnat 1p < x ==> ? r: Rep_preal(A). r*x ~: Rep_preal(A)";
by (res_inst_tac [("X1","A")] (mem_Rep_preal_Ex RS exE) 1);
by (res_inst_tac [("Q","xa*x : Rep_preal(A)")] (excluded_middle RS disjE) 1);
by (Fast_tac 1);
by (dres_inst_tac [("x","xa")] prat_self_less_mult_right 1);
by (etac prat_lessE 1);
by (cut_inst_tac [("R","A"),("x","Q3")] lemma_gleason9_34 1);
by (dtac sym 1 THEN Auto_tac );
by (ftac not_in_preal_ub 1);
by (dres_inst_tac [("x","xa + Q3")] bspec 1 THEN assume_tac 1);
by (dtac prat_add_right_less_cancel 1);
by (dres_inst_tac [("x","qinv(xa)*Q3")] prat_mult_less2_mono1 1);
by (dres_inst_tac [("x","r")] prat_add_less2_mono2 1);
by (asm_full_simp_tac (simpset() addsimps
    [prat_mult_assoc RS sym,lemma1_gleason9_36]) 1);
by (dtac sym 1);
by (auto_tac (claset(),simpset() addsimps [lemma2_gleason9_36]));
by (res_inst_tac [("x","r")] bexI 1);
by (rtac notI 1);
by (dres_inst_tac [("y","r*x")] (Rep_preal RS prealE_lemma3b) 1);
by Auto_tac;
qed "lemma_gleason9_36";

Goal "prat_of_pnat (Abs_pnat 1) < x ==> \
\     ? r: Rep_preal(A). r*x ~: Rep_preal(A)";
by (rtac lemma_gleason9_36 1);
by (asm_simp_tac (simpset() addsimps [pnat_one_def]) 1);
qed "lemma_gleason9_36a";

(*** Part 2 of existence of inverse ***)
Goal "x: Rep_preal(preal_of_prat (prat_of_pnat (Abs_pnat 1))) \
\     ==> x: Rep_preal(pinv(A)*A)";
by (auto_tac (claset() addSIs [mem_Rep_preal_multI],
              simpset() addsimps [pinv_def,preal_of_prat_def] ));
by (rtac (preal_mem_inv_set RS Abs_preal_inverse RS ssubst) 1);
by (dtac prat_qinv_gt_1 1);
by (dres_inst_tac [("A","A")] lemma_gleason9_36a 1);
by Auto_tac;
by (dtac (Rep_preal RS prealE_lemma4a) 1);
by (Auto_tac  THEN dtac qinv_prat_less 1);
by (res_inst_tac [("x","qinv(u)*x")] exI 1);
by (rtac conjI 1);
by (res_inst_tac [("x","qinv(r)*x")] exI 1);
by (auto_tac (claset() addIs [prat_mult_less2_mono1],
    simpset() addsimps [qinv_mult_eq,qinv_qinv]));
by (res_inst_tac [("x","u")] bexI 1);
by (auto_tac (claset(),simpset() addsimps [prat_mult_assoc,
    prat_mult_left_commute]));
qed "preal_mem_mult_invI";

Goal "pinv(A)*A = (preal_of_prat (prat_of_pnat (Abs_pnat 1)))";
by (rtac (inj_Rep_preal RS injD) 1);
by (rtac set_ext 1);
by (fast_tac (claset() addDs [preal_mem_mult_invD,preal_mem_mult_invI]) 1);
qed "preal_mult_inv";

Goal "A*pinv(A) = (preal_of_prat (prat_of_pnat (Abs_pnat 1)))";
by (rtac (preal_mult_commute RS subst) 1);
by (rtac preal_mult_inv 1);
qed "preal_mult_inv_right";

val [prem] = goal thy
    "(!!u. z = Abs_preal(u) ==> P) ==> P";
by (cut_inst_tac [("x1","z")] 
    (rewrite_rule [preal_def] (Rep_preal RS Abs_preal_inverse)) 1);
by (res_inst_tac [("u","Rep_preal z")] prem 1);
by (dtac (inj_Rep_preal RS injD) 1);
by (Asm_simp_tac 1);
qed "eq_Abs_preal";

(*** Lemmas/Theorem(s) need lemma_gleason9_34 ***)
Goal "Rep_preal (R1) <= Rep_preal(R1 + R2)";
by (cut_inst_tac [("X","R2")] mem_Rep_preal_Ex 1);
by (auto_tac (claset() addSIs [bexI] addIs [(Rep_preal RS prealE_lemma3b),
   prat_self_less_add_left,mem_Rep_preal_addI],simpset()));
qed "Rep_preal_self_subset";

Goal "~ Rep_preal (R1 + R2) <= Rep_preal(R1)";
by (cut_inst_tac [("X","R2")] mem_Rep_preal_Ex 1);
by (etac exE 1);
by (cut_inst_tac [("R","R1")] lemma_gleason9_34 1);
by (auto_tac (claset() addIs [mem_Rep_preal_addI],simpset()));
qed "Rep_preal_sum_not_subset";

Goal "Rep_preal (R1 + R2) ~= Rep_preal(R1)";
by (rtac notI 1);
by (etac equalityE 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_preal_sum_not_subset]) 1);
qed "Rep_preal_sum_not_eq";

(*** at last --- Gleason prop. 9-3.5(iii) p. 123 ***)
Goalw [preal_less_def,psubset_def] "(R1::preal) < R1 + R2";
by (simp_tac (simpset() addsimps [Rep_preal_self_subset,
    Rep_preal_sum_not_eq RS not_sym]) 1);
qed "preal_self_less_add_left";

Goal "(R1::preal) < R2 + R1";
by (simp_tac (simpset() addsimps [preal_add_commute,preal_self_less_add_left]) 1);
qed "preal_self_less_add_right";

(*** Properties of <= ***)

Goalw [preal_le_def,psubset_def,preal_less_def] 
                     "z<=w ==> ~(w<(z::preal))";
by (auto_tac  (claset() addDs [equalityI],simpset()));
qed "preal_leD";

val preal_leE = make_elim preal_leD;

Goalw [preal_le_def,psubset_def,preal_less_def]
                   "~ z <= w ==> w<(z::preal)";
by (cut_inst_tac [("r1.0","w"),("r2.0","z")] preal_linear 1);
by (auto_tac  (claset(),simpset() addsimps [preal_less_def,psubset_def]));
qed "not_preal_leE";
		       
Goal "~(w < z) ==> z <= (w::preal)";
by (fast_tac (claset() addIs [not_preal_leE]) 1);
qed "preal_leI";

Goal "(~(w < z)) = (z <= (w::preal))";
by (fast_tac (claset() addSIs [preal_leI,preal_leD]) 1);
qed "preal_less_le_iff";

Goalw [preal_le_def,preal_less_def,psubset_def] 
                  "z < w ==> z <= (w::preal)";
by (Fast_tac 1);
qed "preal_less_imp_le";

Goalw [preal_le_def,preal_less_def,psubset_def] 
                      "!!(x::preal). x <= y ==> x < y | x = y";
by (auto_tac (claset() addIs [inj_Rep_preal RS injD],simpset()));
qed "preal_le_imp_less_or_eq";

Goalw [preal_le_def,preal_less_def,psubset_def] 
                       "!!(x::preal). x < y | x = y ==> x <=y";
by Auto_tac;
qed "preal_less_or_eq_imp_le";

Goalw [preal_le_def] "w <= (w::preal)";
by (Simp_tac 1);
qed "preal_le_refl";

val prems = goal thy "!!i. [| i <= j; j < k |] ==> i < (k::preal)";
by (dtac preal_le_imp_less_or_eq 1);
by (fast_tac (claset() addIs [preal_less_trans]) 1);
qed "preal_le_less_trans";

val prems = goal thy "!!i. [| i < j; j <= k |] ==> i < (k::preal)";
by (dtac preal_le_imp_less_or_eq 1);
by (fast_tac (claset() addIs [preal_less_trans]) 1);
qed "preal_less_le_trans";

Goal "[| i <= j; j <= k |] ==> i <= (k::preal)";
by (EVERY1 [dtac preal_le_imp_less_or_eq, dtac preal_le_imp_less_or_eq,
            rtac preal_less_or_eq_imp_le, fast_tac (claset() addIs [preal_less_trans])]);
qed "preal_le_trans";

Goal "[| z <= w; w <= z |] ==> z = (w::preal)";
by (EVERY1 [dtac preal_le_imp_less_or_eq, dtac preal_le_imp_less_or_eq,
            fast_tac (claset() addEs [preal_less_irrefl,preal_less_asym])]);
qed "preal_le_anti_sym";

Goal "[| ~ y < x; y ~= x |] ==> x < (y::preal)";
by (rtac not_preal_leE 1);
by (fast_tac (claset() addDs [preal_le_imp_less_or_eq]) 1);
qed "not_less_not_eq_preal_less";

(****)(****)(****)(****)(****)(****)(****)(****)(****)(****)(****)(****)(****)(****)

(**** Set up all lemmas for proving A < B ==> ?D. A + D = B ****)
(**** Gleason prop. 9-3.5(iv) p. 123 ****)
(**** Define the D required and show that it is a positive real ****)

(* useful lemmas - proved elsewhere? *)
Goalw [psubset_def] "A < B ==> ? x. x ~: A & x : B";
by (etac conjE 1);
by (etac swap 1);
by (etac equalityI 1);
by Auto_tac;
qed "lemma_psubset_mem";

Goalw [psubset_def] "~ (A::'a set) < A";
by (Fast_tac 1);
qed "lemma_psubset_not_refl";

Goalw [psubset_def] "!!(A::'a set). [| A < B; B < C |] ==> A < C";
by (auto_tac (claset() addDs [subset_antisym],simpset()));
qed "psubset_trans";

Goalw [psubset_def] "!!(A::'a set). [| A <= B; B < C |] ==> A < C";
by (auto_tac (claset() addDs [subset_antisym],simpset()));
qed "subset_psubset_trans";

Goalw [psubset_def] "!!(A::'a set). [| A < B; B <= C |] ==> A < C";
by (auto_tac (claset() addDs [subset_antisym],simpset()));
qed "subset_psubset_trans2";

Goalw [psubset_def] "!!(A::'a set). [| A < B; c : A |] ==> c : B";
by (auto_tac (claset() addDs [subsetD],simpset()));
qed "psubsetD";

(** Part 1 of Dedekind sections def **)
Goalw [preal_less_def]
     "A < B ==> \
\     ? q. q : {d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}";
by (EVERY1[dtac lemma_psubset_mem, etac exE, etac conjE]);
by (dres_inst_tac [("x1","B")] (Rep_preal RS prealE_lemma4a) 1);
by (auto_tac (claset(),simpset() addsimps [prat_less_def]));
qed "lemma_ex_mem_less_left_add1";

Goal
     "A < B ==> \
\       {} < {d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}";
by (dtac lemma_ex_mem_less_left_add1 1);
by (auto_tac (claset() addSIs [psubsetI] addEs [equalityCE],simpset()));
qed "preal_less_set_not_empty";

(** Part 2 of Dedekind sections def **)
Goal "? q. q ~: {d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}";
by (cut_inst_tac [("X","B")] not_mem_Rep_preal_Ex 1);
by (etac exE 1);
by (res_inst_tac [("x","x")] exI 1);
by Auto_tac;
by (cut_inst_tac [("x","x"),("y","n")] prat_self_less_add_right 1);
by (auto_tac (claset() addDs [Rep_preal RS prealE_lemma3b],simpset()));
qed "lemma_ex_not_mem_less_left_add1";

Goal "{d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)} < UNIV";
by (auto_tac (claset() addSIs [psubsetI],simpset()));
by (cut_inst_tac [("A","A"),("B","B")] lemma_ex_not_mem_less_left_add1 1);
by (etac exE 1);
by (eres_inst_tac [("c","q")] equalityCE 1);
by Auto_tac;
qed "preal_less_set_not_prat_set";

(** Part 3 of Dedekind sections def **)
Goal "A < B ==> ! y: {d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}. \
 \      !z. z < y --> z : {d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}";
by Auto_tac;
by (dres_inst_tac [("x","n")] prat_add_less2_mono2 1);
by (dtac (Rep_preal RS prealE_lemma3b) 1);
by Auto_tac;
qed "preal_less_set_lemma3";

Goal "A < B ==> ! y: {d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}. \
\       Bex {d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)} (op < y)";
by Auto_tac;
by (dtac (Rep_preal RS prealE_lemma4a) 1);
by (auto_tac (claset(),simpset() addsimps [prat_less_def,prat_add_assoc]));
qed "preal_less_set_lemma4";

Goal 
     "!! (A::preal). A < B ==> \
\     {d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}: preal";
by (rtac prealI2 1);
by (rtac preal_less_set_not_empty 1);
by (rtac preal_less_set_not_prat_set 2);
by (rtac preal_less_set_lemma3 2);
by (rtac preal_less_set_lemma4 3);
by Auto_tac;
qed "preal_mem_less_set";

(** proving that A + D <= B **)
Goalw [preal_le_def] 
       "!! (A::preal). A < B ==> \
\         A + Abs_preal({d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}) <= B";
by (rtac subsetI 1);
by (dtac mem_Rep_preal_addD 1);
by (auto_tac (claset(),simpset() addsimps [
    preal_mem_less_set RS Abs_preal_inverse]));
by (dtac not_in_preal_ub 1);
by (dtac bspec 1 THEN assume_tac 1);
by (dres_inst_tac [("x","y")] prat_add_less2_mono1 1);
by (dres_inst_tac [("x1","B")] (Rep_preal RS prealE_lemma3b) 1);
by Auto_tac;
qed "preal_less_add_left_subsetI";

(** proving that B <= A + D  --- trickier **)
(** lemma **)
Goal "x : Rep_preal(B) ==> ? e. x + e : Rep_preal(B)";
by (dtac (Rep_preal RS prealE_lemma4a) 1);
by (auto_tac (claset(),simpset() addsimps [prat_less_def]));
qed "lemma_sum_mem_Rep_preal_ex";

Goalw [preal_le_def] 
       "!! (A::preal). A < B ==> \
\         B <= A + Abs_preal({d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)})";
by (rtac subsetI 1);
by (res_inst_tac [("Q","x: Rep_preal(A)")] (excluded_middle RS disjE) 1);
by (rtac mem_Rep_preal_addI 1);
by (dtac lemma_sum_mem_Rep_preal_ex 1);
by (etac exE 1);
by (cut_inst_tac [("R","A"),("x","e")] lemma_gleason9_34 1 THEN etac bexE 1);
by (dtac not_in_preal_ub 1 THEN dtac bspec 1 THEN assume_tac 1);
by (etac prat_lessE 1);
by (res_inst_tac [("x","r")] bexI 1);
by (res_inst_tac [("x","Q3")] bexI 1);
by (cut_facts_tac [Rep_preal_self_subset] 4);
by (auto_tac (claset(),simpset() addsimps [
    preal_mem_less_set RS Abs_preal_inverse]));
by (res_inst_tac [("x","r+e")] exI 1);
by (asm_full_simp_tac (simpset() addsimps prat_add_ac) 1);
qed "preal_less_add_left_subsetI2";

(*** required proof ***)
Goal "!! (A::preal). A < B ==> \
\         A + Abs_preal({d. ? n. n ~: Rep_preal(A) & n + d : Rep_preal(B)}) = B";
by (blast_tac (claset() addIs [preal_le_anti_sym,
                preal_less_add_left_subsetI,preal_less_add_left_subsetI2]) 1);
qed "preal_less_add_left";

Goal "!! (A::preal). A < B ==> ? D. A + D = B";
by (fast_tac (claset() addDs [preal_less_add_left]) 1);
qed "preal_less_add_left_Ex";        

Goal "!!(A::preal). A < B ==> A + C < B + C";
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
    simpset() addsimps [preal_add_assoc]));
by (res_inst_tac [("y1","D")] (preal_add_commute RS subst) 1);
by (auto_tac (claset() addIs [preal_self_less_add_left],
          simpset() addsimps [preal_add_assoc RS sym]));
qed "preal_add_less2_mono1";

Goal "!!(A::preal). A < B ==> C + A < C + B";
by (auto_tac (claset() addIs [preal_add_less2_mono1],
    simpset() addsimps [preal_add_commute]));
qed "preal_add_less2_mono2";

Goal 
      "!!(q1::preal). q1 < q2 ==> q1 * x < q2 * x";
by (dtac preal_less_add_left_Ex 1);
by (auto_tac (claset(),simpset() addsimps [preal_add_mult_distrib,
    preal_self_less_add_left]));
qed "preal_mult_less_mono1";

Goal "!!(q1::preal). q1 < q2  ==> x * q1 < x * q2";
by (auto_tac (claset() addDs [preal_mult_less_mono1],
    simpset() addsimps [preal_mult_commute]));
qed "preal_mult_left_less_mono1";

Goal "!!(q1::preal). q1 <= q2  ==> x * q1 <= x * q2";
by (dtac preal_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [preal_le_refl,
    preal_less_imp_le,preal_mult_left_less_mono1],simpset()));
qed "preal_mult_left_le_mono1";
 
Goal "!!(q1::preal). q1 <= q2  ==> q1 * x <= q2 * x";
by (auto_tac (claset() addDs [preal_mult_left_le_mono1],
    simpset() addsimps [preal_mult_commute]));
qed "preal_mult_le_mono1";
 
Goal "!!(q1::preal). q1 <= q2  ==> x + q1 <= x + q2";
by (dtac preal_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [preal_le_refl,
    preal_less_imp_le,preal_add_less2_mono1],
    simpset() addsimps [preal_add_commute]));
qed "preal_add_left_le_mono1";

Goal "!!(q1::preal). q1 <= q2  ==> q1 + x <= q2 + x";
by (auto_tac (claset() addDs [preal_add_left_le_mono1],
    simpset() addsimps [preal_add_commute]));
qed "preal_add_le_mono1";
 
Goal "!!(A::preal). A + C < B + C ==> A < B";
by (cut_facts_tac [preal_linear] 1);
by (auto_tac (claset() addEs [preal_less_irrefl],simpset()));
by (dres_inst_tac [("A","B"),("C","C")] preal_add_less2_mono1 1);
by (fast_tac (claset() addDs [preal_less_trans] 
                addEs [preal_less_irrefl]) 1);
qed "preal_add_right_less_cancel";

Goal "!!(A::preal). C + A < C + B ==> A < B";
by (auto_tac (claset() addEs [preal_add_right_less_cancel],
              simpset() addsimps [preal_add_commute]));
qed "preal_add_left_less_cancel";

Goal "((A::preal) + C < B + C) = (A < B)";
by (REPEAT(ares_tac [iffI,preal_add_less2_mono1,
    preal_add_right_less_cancel] 1));
qed "preal_add_less_iff1";

Addsimps [preal_add_less_iff1];

Goal "(C + (A::preal) < C + B) = (A < B)";
by (REPEAT(ares_tac [iffI,preal_add_less2_mono2,
    preal_add_left_less_cancel] 1));
qed "preal_add_less_iff2";

Addsimps [preal_add_less_iff2];

Goal "[| x1 < y1; x2 < y2 |] ==> x1 + x2 < y1 + (y2::preal)";
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
    simpset() addsimps  preal_add_ac));
by (rtac (preal_add_assoc RS subst) 1);
by (rtac preal_self_less_add_right 1);
qed "preal_add_less_mono";

Goal "[| x1 < y1; x2 < y2 |] ==> x1 * x2 < y1 * (y2::preal)";
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
              simpset() addsimps [preal_add_mult_distrib,
              preal_add_mult_distrib2,preal_self_less_add_left,
              preal_add_assoc] @ preal_mult_ac));
qed "preal_mult_less_mono";

Goal "!!(A::preal). A + C = B + C ==> A = B";
by (cut_facts_tac [preal_linear] 1);
by Auto_tac;
by (ALLGOALS(dres_inst_tac [("C","C")] preal_add_less2_mono1));
by (auto_tac (claset() addEs [preal_less_irrefl],simpset()));
qed "preal_add_right_cancel";

Goal "!!(A::preal). C + A = C + B ==> A = B";
by (auto_tac (claset() addIs [preal_add_right_cancel],
              simpset() addsimps [preal_add_commute]));
qed "preal_add_left_cancel";

Goal "(C + A = C + B) = ((A::preal) = B)";
by (fast_tac (claset() addIs [preal_add_left_cancel]) 1);
qed "preal_add_left_cancel_iff";

Goal "(A + C = B + C) = ((A::preal) = B)";
by (fast_tac (claset() addIs [preal_add_right_cancel]) 1);
qed "preal_add_right_cancel_iff";

Addsimps [preal_add_left_cancel_iff,preal_add_right_cancel_iff];

(*** Completeness of preal ***)

(*** prove that supremum is a cut ***)
Goal "? (X::preal). X: P ==> \
\         ? q.  q: {w. ? X. X : P & w : Rep_preal X}";
by Safe_tac;
by (cut_inst_tac [("X","X")] mem_Rep_preal_Ex 1);
by Auto_tac;
qed "preal_sup_mem_Ex";

(** Part 1 of Dedekind def **)
Goal "? (X::preal). X: P ==> \
\         {} < {w. ? X : P. w : Rep_preal X}";
by (dtac preal_sup_mem_Ex 1);
by (auto_tac (claset() addSIs [psubsetI] addEs [equalityCE],simpset()));
qed "preal_sup_set_not_empty";

(** Part 2 of Dedekind sections def **) 
Goalw [preal_less_def] "? Y. (! X: P. X < Y)  \             
\         ==> ? q. q ~: {w. ? X. X: P & w: Rep_preal(X)}"; (**)
by (auto_tac (claset(),simpset() addsimps [psubset_def]));
by (cut_inst_tac [("X","Y")] not_mem_Rep_preal_Ex 1);
by (etac exE 1);
by (res_inst_tac [("x","x")] exI 1);
by (auto_tac (claset() addSDs [bspec],simpset()));
qed "preal_sup_not_mem_Ex";

Goalw [preal_le_def] "? Y. (! X: P. X <= Y)  \
\         ==> ? q. q ~: {w. ? X. X: P & w: Rep_preal(X)}";
by (Step_tac 1);
by (cut_inst_tac [("X","Y")] not_mem_Rep_preal_Ex 1);
by (etac exE 1);
by (res_inst_tac [("x","x")] exI 1);
by (auto_tac (claset() addSDs [bspec],simpset()));
qed "preal_sup_not_mem_Ex1";

Goal "? Y. (! X: P. X < Y)  \                                    
\         ==> {w. ? X: P. w: Rep_preal(X)} < UNIV";       (**)
by (dtac preal_sup_not_mem_Ex 1);
by (auto_tac (claset() addSIs [psubsetI],simpset()));
by (eres_inst_tac [("c","q")] equalityCE 1);
by Auto_tac;
qed "preal_sup_set_not_prat_set";

Goal "? Y. (! X: P. X <= Y)  \
\         ==> {w. ? X: P. w: Rep_preal(X)} < UNIV";
by (dtac preal_sup_not_mem_Ex1 1);
by (auto_tac (claset() addSIs [psubsetI],simpset()));
by (eres_inst_tac [("c","q")] equalityCE 1);
by Auto_tac;
qed "preal_sup_set_not_prat_set1";

(** Part 3 of Dedekind sections def **)
Goal "[|? (X::preal). X: P; ? Y. (! X:P. X < Y) |] \              
\         ==> ! y: {w. ? X: P. w: Rep_preal X}. \
\             !z. z < y --> z: {w. ? X: P. w: Rep_preal X}";         (**)
by (auto_tac(claset() addEs [Rep_preal RS prealE_lemma3b],simpset()));
qed "preal_sup_set_lemma3";

Goal "[|? (X::preal). X: P; ? Y. (! X:P. X <= Y) |] \
\         ==> ! y: {w. ? X: P. w: Rep_preal X}. \
\             !z. z < y --> z: {w. ? X: P. w: Rep_preal X}";
by (auto_tac(claset() addEs [Rep_preal RS prealE_lemma3b],simpset()));
qed "preal_sup_set_lemma3_1";

Goal "[|? (X::preal). X: P; ? Y. (! X:P. X < Y) |] \              
\         ==>  !y: {w. ? X: P. w: Rep_preal X}. \                        
\             Bex {w. ? X: P. w: Rep_preal X} (op < y)";                (**)
by (blast_tac (claset() addDs [(Rep_preal RS prealE_lemma4a)]) 1);
qed "preal_sup_set_lemma4";

Goal "[|? (X::preal). X: P; ? Y. (! X:P. X <= Y) |] \
\         ==>  !y: {w. ? X: P. w: Rep_preal X}. \
\             Bex {w. ? X: P. w: Rep_preal X} (op < y)";
by (blast_tac (claset() addDs [(Rep_preal RS prealE_lemma4a)]) 1);
qed "preal_sup_set_lemma4_1";

Goal "[|? (X::preal). X: P; ? Y. (! X:P. X < Y) |] \            
\         ==> {w. ? X: P. w: Rep_preal(X)}: preal";                      (**)
by (rtac prealI2 1);
by (rtac preal_sup_set_not_empty 1);
by (rtac preal_sup_set_not_prat_set 2);
by (rtac preal_sup_set_lemma3 3);
by (rtac preal_sup_set_lemma4 5);
by Auto_tac;
qed "preal_sup";

Goal "[|? (X::preal). X: P; ? Y. (! X:P. X <= Y) |] \
\         ==> {w. ? X: P. w: Rep_preal(X)}: preal";
by (rtac prealI2 1);
by (rtac preal_sup_set_not_empty 1);
by (rtac preal_sup_set_not_prat_set1 2);
by (rtac preal_sup_set_lemma3_1 3);
by (rtac preal_sup_set_lemma4_1 5);
by Auto_tac;
qed "preal_sup1";

Goalw [psup_def] "? Y. (! X:P. X < Y) ==> ! x: P. x <= psup P";      (**) 
by (auto_tac (claset(),simpset() addsimps [preal_le_def]));
by (rtac (preal_sup RS Abs_preal_inverse RS ssubst) 1);
by Auto_tac;
qed "preal_psup_leI";

Goalw [psup_def] "? Y. (! X:P. X <= Y) ==> ! x: P. x <= psup P";
by (auto_tac (claset(),simpset() addsimps [preal_le_def]));
by (rtac (preal_sup1 RS Abs_preal_inverse RS ssubst) 1);
by (auto_tac (claset(),simpset() addsimps [preal_le_def]));
qed "preal_psup_leI2";

Goal "[| ? Y. (! X:P. X < Y); x : P |] ==> x <= psup P";              (**)
by (blast_tac (claset() addSDs [preal_psup_leI]) 1);
qed "preal_psup_leI2b";

Goal "[| ? Y. (! X:P. X <= Y); x : P |] ==> x <= psup P";
by (blast_tac (claset() addSDs [preal_psup_leI2]) 1);
qed "preal_psup_leI2a";

Goalw [psup_def] "[| ? X. X : P; ! X:P. X < Y |] ==> psup P <= Y";   (**)
by (auto_tac (claset(),simpset() addsimps [preal_le_def]));
by (dtac (([exI,exI] MRS preal_sup) RS Abs_preal_inverse RS subst) 1);
by (rotate_tac 1 2);
by (assume_tac 2);
by (auto_tac (claset() addSDs [bspec],simpset() addsimps [preal_less_def,psubset_def]));
qed "psup_le_ub";

Goalw [psup_def] "[| ? X. X : P; ! X:P. X <= Y |] ==> psup P <= Y";
by (auto_tac (claset(),simpset() addsimps [preal_le_def]));
by (dtac (([exI,exI] MRS preal_sup1) RS Abs_preal_inverse RS subst) 1);
by (rotate_tac 1 2);
by (assume_tac 2);
by (auto_tac (claset() addSDs [bspec],
    simpset() addsimps [preal_less_def,psubset_def,preal_le_def]));
qed "psup_le_ub1";

(** supremum property **)
Goal "[|? (X::preal). X: P; ? Y. (! X:P. X < Y) |] \                  
\         ==> (!Y. (? X: P. Y < X) = (Y < psup P))";              
by (forward_tac [preal_sup RS Abs_preal_inverse] 1);
by (Fast_tac 1);
by (auto_tac (claset() addSIs [psubsetI],simpset() addsimps [psup_def,preal_less_def]));
by (blast_tac (claset() addDs [psubset_def RS meta_eq_to_obj_eq RS iffD1]) 1);
by (rotate_tac 4 1);
by (asm_full_simp_tac (simpset() addsimps [psubset_def]) 1);
by (dtac bspec 1 THEN assume_tac 1);
by (REPEAT(etac conjE 1));
by (EVERY1[rtac swap, assume_tac, rtac set_ext]);
by (auto_tac (claset() addSDs [lemma_psubset_mem],simpset()));
by (cut_inst_tac [("r1.0","Xa"),("r2.0","Ya")] preal_linear 1);
by (auto_tac (claset() addDs [psubsetD],simpset() addsimps [preal_less_def]));
qed "preal_complete";

(****)(****)(****)(****)(****)(****)(****)(****)(****)(****)
    (****** Embedding ******)
(*** mapping from prat into preal ***)

Goal "x < z1 + z2 ==> x * z1 * qinv (z1 + z2) < z1";
by (dres_inst_tac [("x","z1 * qinv (z1 + z2)")] prat_mult_less2_mono1 1);
by (asm_full_simp_tac (simpset() addsimps prat_mult_ac) 1);
qed "lemma_preal_rat_less";

Goal "x < z1 + z2 ==> x * z2 * qinv (z1 + z2) < z2";
by (stac prat_add_commute 1);
by (dtac (prat_add_commute RS subst) 1);
by (etac lemma_preal_rat_less 1);
qed "lemma_preal_rat_less2";

Goalw [preal_of_prat_def,preal_add_def] 
      "preal_of_prat ((z1::prat) + z2) = \
\      preal_of_prat z1 + preal_of_prat z2";
by (res_inst_tac [("f","Abs_preal")] arg_cong 1);
by (auto_tac (claset() addIs [prat_add_less_mono] addSIs [set_ext],simpset() addsimps 
    [lemma_prat_less_set_mem_preal RS Abs_preal_inverse]));
by (res_inst_tac [("x","x*z1*qinv(z1+z2)")] exI 1 THEN rtac conjI 1);
by (etac lemma_preal_rat_less 1);
by (res_inst_tac [("x","x*z2*qinv(z1+z2)")] exI 1 THEN rtac conjI 1);
by (etac lemma_preal_rat_less2 1);
by (asm_full_simp_tac (simpset() addsimps [prat_add_mult_distrib RS sym,
     prat_add_mult_distrib2 RS sym] @ prat_mult_ac) 1);
qed "preal_of_prat_add";

Goal "x < xa ==> x*z1*qinv(xa) < z1";
by (dres_inst_tac [("x","z1 * qinv xa")] prat_mult_less2_mono1 1);
by (dtac (prat_mult_left_commute RS subst) 1);
by (asm_full_simp_tac (simpset() addsimps prat_mult_ac) 1);
qed "lemma_preal_rat_less3";

Goal "xa < z1 * z2 ==> xa*z2*qinv(z1*z2) < z2";
by (dres_inst_tac [("x","z2 * qinv(z1*z2)")] prat_mult_less2_mono1 1);
by (dtac (prat_mult_left_commute RS subst) 1);
by (asm_full_simp_tac (simpset() addsimps prat_mult_ac) 1);
qed "lemma_preal_rat_less4";

Goalw [preal_of_prat_def,preal_mult_def] 
      "preal_of_prat ((z1::prat) * z2) = \
\      preal_of_prat z1 * preal_of_prat z2";
by (res_inst_tac [("f","Abs_preal")] arg_cong 1);
by (auto_tac (claset() addIs [prat_mult_less_mono] addSIs [set_ext],simpset() addsimps 
    [lemma_prat_less_set_mem_preal RS Abs_preal_inverse]));
by (dtac prat_dense 1);
by (Step_tac 1);
by (res_inst_tac [("x","x*z1*qinv(xa)")] exI 1 THEN rtac conjI 1);
by (etac lemma_preal_rat_less3 1);
by (res_inst_tac [("x"," xa*z2*qinv(z1*z2)")] exI 1 THEN rtac conjI 1);
by (etac lemma_preal_rat_less4 1);
by (asm_full_simp_tac (simpset() 
    addsimps [qinv_mult_eq RS sym] @ prat_mult_ac) 1);
by (asm_full_simp_tac (simpset() 
    addsimps [prat_mult_assoc RS sym]) 1);
qed "preal_of_prat_mult";

Goalw [preal_of_prat_def,preal_less_def] 
      "(preal_of_prat p < preal_of_prat q) = (p < q)";
by (auto_tac (claset() addSDs [lemma_prat_set_eq] addEs [prat_less_trans],
    simpset() addsimps [lemma_prat_less_set_mem_preal,
    psubset_def,prat_less_not_refl]));
by (res_inst_tac [("q1.0","p"),("q2.0","q")] prat_linear_less2 1);
by (auto_tac (claset() addIs [prat_less_irrefl],simpset()));
qed "preal_of_prat_less_iff";

Addsimps [preal_of_prat_less_iff];
