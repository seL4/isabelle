(*  Title:      HOL/IntDiv.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"

Here is the division algorithm in ML:

    fun posDivAlg (a,b) =
      if a<b then (0,a)
      else let val (q,r) = posDivAlg(a, 2*b)
	       in  if 0<=r-b then (2*q+1, r-b) else (2*q, r)
	   end;

    fun negDivAlg (a,b) =
      if 0<=a+b then (~1,a+b)
      else let val (q,r) = negDivAlg(a, 2*b)
	       in  if 0<=r-b then (2*q+1, r-b) else (2*q, r)
	   end;

    fun negateSnd (q,r:int) = (q,~r);

    fun divAlg (a,b) = if 0<=a then 
			  if b>0 then posDivAlg (a,b) 
			   else if a=0 then (0,0)
				else negateSnd (negDivAlg (~a,~b))
		       else 
			  if 0<b then negDivAlg (a,b)
			  else        negateSnd (posDivAlg (~a,~b));
*)

Addsimps [zless_nat_conj];

(*** Uniqueness and monotonicity of quotients and remainders ***)

Goal "[| b*q' + r'  <= b*q + r;  #0 <= r';  #0 < b;  r < b |] \
\     ==> q' <= (q::int)";
by (subgoal_tac "r' + b * (q'-q) <= r" 1);
by (simp_tac (simpset() addsimps [zdiff_zmult_distrib2]) 2);
by (subgoal_tac "#0 < b * (#1 + q - q')" 1);
by (etac order_le_less_trans 2);
by (full_simp_tac (simpset() addsimps [zdiff_zmult_distrib2,
				       zadd_zmult_distrib2]) 2);
by (subgoal_tac "b * q' < b * (#1 + q)" 1);
by (full_simp_tac (simpset() addsimps [zdiff_zmult_distrib2,
				       zadd_zmult_distrib2]) 2);
by (Asm_full_simp_tac 1);
qed "unique_quotient_lemma";

Goal "[| b*q' + r' <= b*q + r;  r <= #0;  b < #0;  b < r' |] \
\     ==> q <= (q'::int)";
by (res_inst_tac [("b", "-b"), ("r", "-r'"), ("r'", "-r")] 
    unique_quotient_lemma 1);
by (auto_tac (claset(), 
	      simpset() addsimps [zmult_zminus, zmult_zminus_right])); 
qed "unique_quotient_lemma_neg";


Goal "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  b ~= #0 |] \
\     ==> q = q'";
by (asm_full_simp_tac 
    (simpset() addsimps split_ifs@
                        [quorem_def, linorder_neq_iff]) 1);
by Safe_tac; 
by (ALLGOALS Asm_full_simp_tac);
by (REPEAT 
    (blast_tac (claset() addIs [order_antisym]
			 addDs [order_eq_refl RS unique_quotient_lemma, 
				order_eq_refl RS unique_quotient_lemma_neg,
				sym]) 1));
qed "unique_quotient";


Goal "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  b ~= #0 |] \
\     ==> r = r'";
by (subgoal_tac "q = q'" 1);
by (blast_tac (claset() addIs [unique_quotient]) 2);
by (asm_full_simp_tac (simpset() addsimps [quorem_def]) 1);
qed "unique_remainder";


(*** Correctness of posDivAlg, the division algorithm for a>=0 and b>0 ***)


Goal "adjust a b (q,r) = (let diff = r-b in \
\                         if #0 <= diff then (#2*q + #1, diff)  \
\                                       else (#2*q, r))";
by (simp_tac (simpset() addsimps [Let_def,adjust_def]) 1);
qed "adjust_eq";
Addsimps [adjust_eq];

(*Proving posDivAlg's termination condition*)
val [tc] = posDivAlg.tcs;
goalw_cterm [] (cterm_of (sign_of (the_context ())) (HOLogic.mk_Trueprop tc));
by Auto_tac;
val lemma = result();

(* removing the termination condition from the generated theorems *)

bind_thm ("posDivAlg_raw_eqn", lemma RS hd posDivAlg.simps);

(**use with simproc to avoid re-proving the premise*)
Goal "#0 < b ==> \
\     posDivAlg (a,b) =      \
\      (if a<b then (#0,a) else adjust a b (posDivAlg(a, #2*b)))";
by (rtac (posDivAlg_raw_eqn RS trans) 1);
by (Asm_simp_tac 1);
qed "posDivAlg_eqn";

bind_thm ("posDivAlg_induct", lemma RS posDivAlg.induct);


(*Correctness of posDivAlg: it computes quotients correctly*)
Goal "#0 <= a --> #0 < b --> quorem ((a, b), posDivAlg (a, b))";
by (res_inst_tac [("u", "a"), ("v", "b")] posDivAlg_induct 1);
by Auto_tac;
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [quorem_def])));
(*base case: a<b*)
by (asm_full_simp_tac (simpset() addsimps [posDivAlg_eqn]) 1);
(*main argument*)
by (stac posDivAlg_eqn 1);
by (ALLGOALS Asm_simp_tac);
by (etac splitE 1);
by (auto_tac (claset(), simpset() addsimps [zadd_zmult_distrib2, Let_def]));
qed_spec_mp "posDivAlg_correct";


(*** Correctness of negDivAlg, the division algorithm for a<0 and b>0 ***)

(*Proving negDivAlg's termination condition*)
val [tc] = negDivAlg.tcs;
goalw_cterm [] (cterm_of (sign_of (the_context ())) (HOLogic.mk_Trueprop tc));
by Auto_tac;
val lemma = result();

(* removing the termination condition from the generated theorems *)

bind_thm ("negDivAlg_raw_eqn", lemma RS hd negDivAlg.simps);

(**use with simproc to avoid re-proving the premise*)
Goal "#0 < b ==> \
\     negDivAlg (a,b) =      \
\      (if #0<=a+b then (#-1,a+b) else adjust a b (negDivAlg(a, #2*b)))";
by (rtac (negDivAlg_raw_eqn RS trans) 1);
by (Asm_simp_tac 1);
qed "negDivAlg_eqn";

bind_thm ("negDivAlg_induct", lemma RS negDivAlg.induct);


(*Correctness of negDivAlg: it computes quotients correctly
  It doesn't work if a=0 because the 0/b=0 rather than -1*)
Goal "a < #0 --> #0 < b --> quorem ((a, b), negDivAlg (a, b))";
by (res_inst_tac [("u", "a"), ("v", "b")] negDivAlg_induct 1);
by Auto_tac;
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [quorem_def])));
(*base case: 0<=a+b*)
by (asm_full_simp_tac (simpset() addsimps [negDivAlg_eqn]) 1);
(*main argument*)
by (stac negDivAlg_eqn 1);
by (ALLGOALS Asm_simp_tac);
by (etac splitE 1);
by (auto_tac (claset(), simpset() addsimps [zadd_zmult_distrib2, Let_def]));
qed_spec_mp "negDivAlg_correct";


(*** Existence shown by proving the division algorithm to be correct ***)

(*the case a=0*)
Goal "b ~= #0 ==> quorem ((#0,b), (#0,#0))";
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, linorder_neq_iff]));
qed "quorem_0";

Goal "posDivAlg (#0, b) = (#0, #0)";
by (stac posDivAlg_raw_eqn 1);
by Auto_tac;
qed "posDivAlg_0";
Addsimps [posDivAlg_0];

Goal "negDivAlg (#-1, b) = (#-1, b-#1)";
by (stac negDivAlg_raw_eqn 1);
by Auto_tac;
qed "negDivAlg_minus1";
Addsimps [negDivAlg_minus1];

Goalw [negateSnd_def] "negateSnd(q,r) = (q,-r)";
by Auto_tac;
qed "negateSnd_eq";
Addsimps [negateSnd_eq];

Goal "quorem ((-a,-b), qr) ==> quorem ((a,b), negateSnd qr)";
by (auto_tac (claset(), simpset() addsimps split_ifs@[quorem_def]));
qed "quorem_neg";

Goal "b ~= #0 ==> quorem ((a,b), divAlg(a,b))";
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_0, divAlg_def]));
by (REPEAT_FIRST (resolve_tac [quorem_neg, posDivAlg_correct,
			       negDivAlg_correct]));
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, linorder_neq_iff]));
qed "divAlg_correct";

(** Aribtrary definitions for division by zero.  Useful to simplify 
    certain equations **)

Goal "a div (#0::int) = #0";
by (simp_tac (simpset() addsimps [div_def, divAlg_def, posDivAlg_raw_eqn]) 1);
qed "DIVISION_BY_ZERO_ZDIV";  (*NOT for adding to default simpset*)

Goal "a mod (#0::int) = a";
by (simp_tac (simpset() addsimps [mod_def, divAlg_def, posDivAlg_raw_eqn]) 1);
qed "DIVISION_BY_ZERO_ZMOD";  (*NOT for adding to default simpset*)

fun zdiv_undefined_case_tac s i =
  case_tac s i THEN 
  asm_simp_tac (simpset() addsimps [DIVISION_BY_ZERO_ZDIV, 
				    DIVISION_BY_ZERO_ZMOD]) i;

(** Basic laws about division and remainder **)

Goal "(a::int) = b * (a div b) + (a mod b)";
by (zdiv_undefined_case_tac "b = #0" 1);
by (cut_inst_tac [("a","a"),("b","b")] divAlg_correct 1);
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, div_def, mod_def]));
qed "zmod_zdiv_equality";  

Goal "(#0::int) < b ==> #0 <= a mod b & a mod b < b";
by (cut_inst_tac [("a","a"),("b","b")] divAlg_correct 1);
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, mod_def]));
bind_thm ("pos_mod_sign", result() RS conjunct1);
bind_thm ("pos_mod_bound", result() RS conjunct2);

Goal "b < (#0::int) ==> a mod b <= #0 & b < a mod b";
by (cut_inst_tac [("a","a"),("b","b")] divAlg_correct 1);
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, div_def, mod_def]));
bind_thm ("neg_mod_sign", result() RS conjunct1);
bind_thm ("neg_mod_bound", result() RS conjunct2);


(** proving general properties of div and mod **)

Goal "b ~= #0 ==> quorem ((a, b), (a div b, a mod b))";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (auto_tac
    (claset(),
     simpset() addsimps [quorem_def, linorder_neq_iff, 
			 pos_mod_sign,pos_mod_bound,
			 neg_mod_sign, neg_mod_bound]));
qed "quorem_div_mod";

Goal "[| quorem((a,b),(q,r));  b ~= #0 |] ==> a div b = q";
by (asm_simp_tac (simpset() addsimps [quorem_div_mod RS unique_quotient]) 1);
qed "quorem_div";

Goal "[| quorem((a,b),(q,r));  b ~= #0 |] ==> a mod b = r";
by (asm_simp_tac (simpset() addsimps [quorem_div_mod RS unique_remainder]) 1);
qed "quorem_mod";

Goal "[| (#0::int) <= a;  a < b |] ==> a div b = #0";
by (rtac quorem_div 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
qed "div_pos_pos_trivial";

Goal "[| a <= (#0::int);  b < a |] ==> a div b = #0";
by (rtac quorem_div 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
qed "div_neg_neg_trivial";

Goal "[| (#0::int) < a;  a+b <= #0 |] ==> a div b = #-1";
by (rtac quorem_div 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
qed "div_pos_neg_trivial";

(*There is no div_neg_pos_trivial because  #0 div b = #0 would supersede it*)

Goal "[| (#0::int) <= a;  a < b |] ==> a mod b = a";
by (res_inst_tac [("q","#0")] quorem_mod 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
qed "mod_pos_pos_trivial";

Goal "[| a <= (#0::int);  b < a |] ==> a mod b = a";
by (res_inst_tac [("q","#0")] quorem_mod 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
qed "mod_neg_neg_trivial";

Goal "[| (#0::int) < a;  a+b <= #0 |] ==> a mod b = a+b";
by (res_inst_tac [("q","#-1")] quorem_mod 1);
by (auto_tac (claset(), simpset() addsimps [quorem_def]));
qed "mod_pos_neg_trivial";

(*There is no mod_neg_pos_trivial...*)


(*Simpler laws such as -a div b = -(a div b) FAIL*)
Goal "(-a) div (-b) = a div (b::int)";
by (zdiv_undefined_case_tac "b = #0" 1);
by (stac ((simplify(simpset()) (quorem_div_mod RS quorem_neg)) 
	  RS quorem_div) 1);
by Auto_tac;
qed "zdiv_zminus_zminus";
Addsimps [zdiv_zminus_zminus];

(*Simpler laws such as -a mod b = -(a mod b) FAIL*)
Goal "(-a) mod (-b) = - (a mod (b::int))";
by (zdiv_undefined_case_tac "b = #0" 1);
by (stac ((simplify(simpset()) (quorem_div_mod RS quorem_neg)) 
	  RS quorem_mod) 1);
by Auto_tac;
qed "zmod_zminus_zminus";
Addsimps [zmod_zminus_zminus];


(*** division of a number by itself ***)

Goal "[| (#0::int) < a; a = r + a*q; r < a |] ==> #1 <= q";
by (subgoal_tac "#0 < a*q" 1);
by (arith_tac 2);
by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 1);
val lemma1 = result();

Goal "[| (#0::int) < a; a = r + a*q; #0 <= r |] ==> q <= #1";
by (subgoal_tac "#0 <= a*(#1-q)" 1);
by (asm_simp_tac (simpset() addsimps [zdiff_zmult_distrib2]) 2);
by (asm_full_simp_tac (simpset() addsimps [int_0_le_mult_iff]) 1);
val lemma2 = result();

Goal "[| quorem((a,a),(q,r));  a ~= (#0::int) |] ==> q = #1";
by (asm_full_simp_tac 
    (simpset() addsimps split_ifs@[quorem_def, linorder_neq_iff]) 1);
by (rtac order_antisym 1);
by Safe_tac;
by Auto_tac;
by (res_inst_tac [("a", "-a"),("r", "-r")] lemma1 3);
by (res_inst_tac [("a", "-a"),("r", "-r")] lemma2 1);
by (REPEAT (force_tac  (claset() addIs [lemma1,lemma2], 
	      simpset() addsimps [zadd_commute, zmult_zminus]) 1));
qed "self_quotient";

Goal "[| quorem((a,a),(q,r));  a ~= (#0::int) |] ==> r = #0";
by (ftac self_quotient 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [quorem_def]) 1);
qed "self_remainder";

Goal "a ~= #0 ==> a div a = (#1::int)";
by (asm_simp_tac (simpset() addsimps [quorem_div_mod RS self_quotient]) 1);
qed "zdiv_self";
Addsimps [zdiv_self];

(*Here we have 0 mod 0 = 0, also assumed by Knuth (who puts m mod 0 = 0) *)
Goal "a mod a = (#0::int)";
by (zdiv_undefined_case_tac "a = #0" 1);
by (asm_simp_tac (simpset() addsimps [quorem_div_mod RS self_remainder]) 1);
qed "zmod_self";
Addsimps [zmod_self];


(*** Computation of division and remainder ***)

Goal "(#0::int) div b = #0";
by (simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "zdiv_zero";

Goal "(#0::int) < b ==> #-1 div b = #-1";
by (asm_simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "div_eq_minus1";

Goal "(#0::int) mod b = #0";
by (simp_tac (simpset() addsimps [mod_def, divAlg_def]) 1);
qed "zmod_zero";

Addsimps [zdiv_zero, zmod_zero];

Goal "(#0::int) < b ==> #-1 div b = #-1";
by (asm_simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "zdiv_minus1";

Goal "(#0::int) < b ==> #-1 mod b = b-#1";
by (asm_simp_tac (simpset() addsimps [mod_def, divAlg_def]) 1);
qed "zmod_minus1";

(** a positive, b positive **)

Goal "[| #0 < a;  #0 <= b |] ==> a div b = fst (posDivAlg(a,b))";
by (asm_simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "div_pos_pos";

Goal "[| #0 < a;  #0 <= b |] ==> a mod b = snd (posDivAlg(a,b))";
by (asm_simp_tac (simpset() addsimps [mod_def, divAlg_def]) 1);
qed "mod_pos_pos";

(** a negative, b positive **)

Goal "[| a < #0;  #0 < b |] ==> a div b = fst (negDivAlg(a,b))";
by (asm_simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "div_neg_pos";

Goal "[| a < #0;  #0 < b |] ==> a mod b = snd (negDivAlg(a,b))";
by (asm_simp_tac (simpset() addsimps [mod_def, divAlg_def]) 1);
qed "mod_neg_pos";

(** a positive, b negative **)

Goal "[| #0 < a;  b < #0 |] ==> a div b = fst (negateSnd(negDivAlg(-a,-b)))";
by (asm_simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "div_pos_neg";

Goal "[| #0 < a;  b < #0 |] ==> a mod b = snd (negateSnd(negDivAlg(-a,-b)))";
by (asm_simp_tac (simpset() addsimps [mod_def, divAlg_def]) 1);
qed "mod_pos_neg";

(** a negative, b negative **)

Goal "[| a < #0;  b <= #0 |] ==> a div b = fst (negateSnd(posDivAlg(-a,-b)))";
by (asm_simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "div_neg_neg";

Goal "[| a < #0;  b <= #0 |] ==> a mod b = snd (negateSnd(posDivAlg(-a,-b)))";
by (asm_simp_tac (simpset() addsimps [mod_def, divAlg_def]) 1);
qed "mod_neg_neg";

Addsimps (map (read_instantiate_sg (sign_of (the_context ()))
	       [("a", "number_of ?v"), ("b", "number_of ?w")])
	  [div_pos_pos, div_neg_pos, div_pos_neg, div_neg_neg,
	   mod_pos_pos, mod_neg_pos, mod_pos_neg, mod_neg_neg,
	   posDivAlg_eqn, negDivAlg_eqn]);


(** Special-case simplification **)

Goal "a mod (#1::int) = #0";
by (cut_inst_tac [("a","a"),("b","#1")] pos_mod_sign 1);
by (cut_inst_tac [("a","a"),("b","#1")] pos_mod_bound 2);
by Auto_tac;
qed "zmod_1";
Addsimps [zmod_1];

Goal "a div (#1::int) = a";
by (cut_inst_tac [("a","a"),("b","#1")] zmod_zdiv_equality 1);
by Auto_tac;
qed "zdiv_1";
Addsimps [zdiv_1];

Goal "a mod (#-1::int) = #0";
by (cut_inst_tac [("a","a"),("b","#-1")] neg_mod_sign 1);
by (cut_inst_tac [("a","a"),("b","#-1")] neg_mod_bound 2);
by Auto_tac;
qed "zmod_minus1_right";
Addsimps [zmod_minus1_right];

Goal "a div (#-1::int) = -a";
by (cut_inst_tac [("a","a"),("b","#-1")] zmod_zdiv_equality 1);
by Auto_tac;
qed "zdiv_minus1_right";
Addsimps [zdiv_minus1_right];


(*** Monotonicity in the first argument (divisor) ***)

Goal "[| a <= a';  #0 < (b::int) |] ==> a div b <= a' div b";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a'"),("b","b")] zmod_zdiv_equality 1);
by (rtac unique_quotient_lemma 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_sign,pos_mod_bound])));
qed "zdiv_mono1";

Goal "[| a <= a';  (b::int) < #0 |] ==> a' div b <= a div b";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a'"),("b","b")] zmod_zdiv_equality 1);
by (rtac unique_quotient_lemma_neg 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [neg_mod_sign,neg_mod_bound])));
qed "zdiv_mono1_neg";


(*** Monotonicity in the second argument (dividend) ***)

Goal "[| b*q + r = b'*q' + r';  #0 <= b'*q' + r';  \
\        r' < b';  #0 <= r;  #0 < b';  b' <= b |]  \
\     ==> q <= (q'::int)";
by (subgoal_tac "#0 <= q'" 1);
 by (subgoal_tac "#0 < b'*(q' + #1)" 2);
  by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 3);
 by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 2);
by (subgoal_tac "b*q < b*(q' + #1)" 1);
 by (Asm_full_simp_tac 1);
by (subgoal_tac "b*q = r' - r + b'*q'" 1);
 by (Simp_tac 2);
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
by (stac zadd_commute 1 THEN rtac zadd_zless_mono 1 THEN arith_tac 1);
by (rtac zmult_zle_mono1 1);
by Auto_tac;
qed "zdiv_mono2_lemma";

Goal "[| (#0::int) <= a;  #0 < b';  b' <= b |]  \
\     ==> a div b <= a div b'";
by (subgoal_tac "b ~= #0" 1);
by (arith_tac 2);
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a"),("b","b'")] zmod_zdiv_equality 1);
by (rtac zdiv_mono2_lemma 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_sign,pos_mod_bound])));
qed "zdiv_mono2";

Goal "[| b*q + r = b'*q' + r';  b'*q' + r' < #0;  \
\        r < b;  #0 <= r';  #0 < b';  b' <= b |]  \
\     ==> q' <= (q::int)";
by (subgoal_tac "q' < #0" 1);
 by (subgoal_tac "b'*q' < #0" 2);
  by (arith_tac 3);
 by (asm_full_simp_tac (simpset() addsimps [zmult_less_0_iff]) 2);
by (subgoal_tac "b*q' < b*(q + #1)" 1);
 by (Asm_full_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
by (subgoal_tac "b*q' <= b'*q'" 1);
 by (asm_simp_tac (simpset() addsimps [zmult_zle_mono1_neg]) 2);
by (subgoal_tac "b'*q' < b + b*q" 1);
 by (Asm_simp_tac 2);
by (arith_tac 1);
qed "zdiv_mono2_neg_lemma";

Goal "[| a < (#0::int);  #0 < b';  b' <= b |]  \
\     ==> a div b' <= a div b";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a"),("b","b'")] zmod_zdiv_equality 1);
by (rtac zdiv_mono2_neg_lemma 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_sign,pos_mod_bound])));
qed "zdiv_mono2_neg";


(*** More algebraic laws for div and mod ***)

(** proving (a*b) div c = a * (b div c) + a * (b mod c) **)

Goal "[| quorem((b,c),(q,r));  c ~= #0 |] \
\     ==> quorem ((a*b, c), (a*q + a*r div c, a*r mod c))";
by (auto_tac
    (claset(),
     simpset() addsimps split_ifs@
                        [quorem_def, linorder_neq_iff, 
			 zadd_zmult_distrib2,
			 pos_mod_sign,pos_mod_bound,
			 neg_mod_sign, neg_mod_bound]));
by (ALLGOALS(rtac zmod_zdiv_equality));
val lemma = result();

Goal "(a*b) div c = a*(b div c) + a*(b mod c) div (c::int)";
by (zdiv_undefined_case_tac "c = #0" 1);
by (blast_tac (claset() addIs [quorem_div_mod RS lemma RS quorem_div]) 1);
qed "zdiv_zmult1_eq";

Goal "(a*b) mod c = a*(b mod c) mod (c::int)";
by (zdiv_undefined_case_tac "c = #0" 1);
by (blast_tac (claset() addIs [quorem_div_mod RS lemma RS quorem_mod]) 1);
qed "zmod_zmult1_eq";

Goal "(a*b) mod (c::int) = ((a mod c) * b) mod c";
by (rtac trans 1);
by (res_inst_tac [("s","b*a mod c")] trans 1);
by (rtac zmod_zmult1_eq 2);
by (ALLGOALS (simp_tac (simpset() addsimps [zmult_commute])));
qed "zmod_zmult1_eq'";

Goal "(a*b) mod (c::int) = ((a mod c) * (b mod c)) mod c";
by (rtac (zmod_zmult1_eq' RS trans) 1);
by (rtac zmod_zmult1_eq 1);
qed "zmod_zmult_distrib";

Goal "b ~= (#0::int) ==> (a*b) div b = a";
by (asm_simp_tac (simpset() addsimps [zdiv_zmult1_eq]) 1);
qed "zdiv_zmult_self1";

Goal "b ~= (#0::int) ==> (b*a) div b = a";
by (stac zmult_commute 1 THEN etac zdiv_zmult_self1 1);
qed "zdiv_zmult_self2";

Addsimps [zdiv_zmult_self1, zdiv_zmult_self2];

Goal "(a*b) mod b = (#0::int)";
by (simp_tac (simpset() addsimps [zmod_zmult1_eq]) 1);
qed "zmod_zmult_self1";

Goal "(b*a) mod b = (#0::int)";
by (simp_tac (simpset() addsimps [zmult_commute, zmod_zmult1_eq]) 1);
qed "zmod_zmult_self2";

Addsimps [zmod_zmult_self1, zmod_zmult_self2];


(** proving (a+b) div c = a div c + b div c + ((a mod c + b mod c) div c) **)

Goal "[| quorem((a,c),(aq,ar));  quorem((b,c),(bq,br));  c ~= #0 |] \
\     ==> quorem ((a+b, c), (aq + bq + (ar+br) div c, (ar+br) mod c))";
by (auto_tac
    (claset(),
     simpset() addsimps split_ifs@
                        [quorem_def, linorder_neq_iff, 
			 zadd_zmult_distrib2,
			 pos_mod_sign,pos_mod_bound,
			 neg_mod_sign, neg_mod_bound]));
by (ALLGOALS(rtac zmod_zdiv_equality));
val lemma = result();

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
Goal "(a+b) div (c::int) = a div c + b div c + ((a mod c + b mod c) div c)";
by (zdiv_undefined_case_tac "c = #0" 1);
by (blast_tac (claset() addIs [[quorem_div_mod,quorem_div_mod]
			       MRS lemma RS quorem_div]) 1);
qed "zdiv_zadd1_eq";

Goal "(a+b) mod (c::int) = (a mod c + b mod c) mod c";
by (zdiv_undefined_case_tac "c = #0" 1);
by (blast_tac (claset() addIs [[quorem_div_mod,quorem_div_mod]
			       MRS lemma RS quorem_mod]) 1);
qed "zmod_zadd1_eq";

Goal "(a mod b) div b = (#0::int)";
by (zdiv_undefined_case_tac "b = #0" 1);
by (auto_tac (claset(), 
       simpset() addsimps [linorder_neq_iff, 
			   pos_mod_sign, pos_mod_bound, div_pos_pos_trivial, 
			   neg_mod_sign, neg_mod_bound, div_neg_neg_trivial]));
qed "mod_div_trivial";
Addsimps [mod_div_trivial];

Goal "(a mod b) mod b = a mod (b::int)";
by (zdiv_undefined_case_tac "b = #0" 1);
by (auto_tac (claset(), 
       simpset() addsimps [linorder_neq_iff, 
			   pos_mod_sign, pos_mod_bound, mod_pos_pos_trivial, 
			   neg_mod_sign, neg_mod_bound, mod_neg_neg_trivial]));
qed "mod_mod_trivial";
Addsimps [mod_mod_trivial];

Goal "(a+b) mod (c::int) = ((a mod c) + b) mod c";
by (rtac (trans RS sym) 1);
by (rtac zmod_zadd1_eq 1);
by (Simp_tac 1);
by (rtac (zmod_zadd1_eq RS sym) 1);
qed "zmod_zadd_left_eq";

Goal "(a+b) mod (c::int) = (a + (b mod c)) mod c";
by (rtac (trans RS sym) 1);
by (rtac zmod_zadd1_eq 1);
by (Simp_tac 1);
by (rtac (zmod_zadd1_eq RS sym) 1);
qed "zmod_zadd_right_eq";


Goal "a ~= (#0::int) ==> (a+b) div a = b div a + #1";
by (asm_simp_tac (simpset() addsimps [zdiv_zadd1_eq]) 1);
qed "zdiv_zadd_self1";

Goal "a ~= (#0::int) ==> (b+a) div a = b div a + #1";
by (asm_simp_tac (simpset() addsimps [zdiv_zadd1_eq]) 1);
qed "zdiv_zadd_self2";
Addsimps [zdiv_zadd_self1, zdiv_zadd_self2];

Goal "(a+b) mod a = b mod (a::int)";
by (zdiv_undefined_case_tac "a = #0" 1);
by (asm_simp_tac (simpset() addsimps [zmod_zadd1_eq]) 1);
qed "zmod_zadd_self1";

Goal "(b+a) mod a = b mod (a::int)";
by (zdiv_undefined_case_tac "a = #0" 1);
by (asm_simp_tac (simpset() addsimps [zmod_zadd1_eq]) 1);
qed "zmod_zadd_self2";
Addsimps [zmod_zadd_self1, zmod_zadd_self2];


(*** proving  a div (b*c) = (a div b) div c ***)

(*The condition c>0 seems necessary.  Consider that 7 div ~6 = ~2 but
  7 div 2 div ~3 = 3 div ~3 = ~1.  The subcase (a div b) mod c = 0 seems
  to cause particular problems.*)

(** first, four lemmas to bound the remainder for the cases b<0 and b>0 **)

Goal "[| (#0::int) < c;  b < r;  r <= #0 |] ==> b*c < b*(q mod c) + r";
by (subgoal_tac "b * (c - q mod c) < r * #1" 1);
by (asm_full_simp_tac (simpset() addsimps [zdiff_zmult_distrib2]) 1);
by (rtac order_le_less_trans 1);
by (etac zmult_zless_mono1 2);
by (rtac zmult_zle_mono2_neg 1);
by (auto_tac
    (claset(),
     simpset() addsimps zcompare_rls@
                        [zadd_commute, add1_zle_eq, pos_mod_bound]));
val lemma1 = result();

Goal "[| (#0::int) < c;   b < r;  r <= #0 |] ==> b * (q mod c) + r <= #0";
by (subgoal_tac "b * (q mod c) <= #0" 1);
by (arith_tac 1);
by (asm_simp_tac (simpset() addsimps [zmult_le_0_iff, pos_mod_sign]) 1);
val lemma2 = result();

Goal "[| (#0::int) < c;  #0 <= r;  r < b |] ==> #0 <= b * (q mod c) + r";
by (subgoal_tac "#0 <= b * (q mod c)" 1);
by (arith_tac 1);
by (asm_simp_tac (simpset() addsimps [int_0_le_mult_iff, pos_mod_sign]) 1);
val lemma3 = result();

Goal "[| (#0::int) < c; #0 <= r; r < b |] ==> b * (q mod c) + r < b * c";
by (subgoal_tac "r * #1 < b * (c - q mod c)" 1);
by (asm_full_simp_tac (simpset() addsimps [zdiff_zmult_distrib2]) 1);
by (rtac order_less_le_trans 1);
by (etac zmult_zless_mono1 1);
by (rtac zmult_zle_mono2 2);
by (auto_tac
    (claset(),
     simpset() addsimps zcompare_rls@
                        [zadd_commute, add1_zle_eq, pos_mod_bound]));
val lemma4 = result();

Goal "[| quorem ((a,b), (q,r));  b ~= #0;  #0 < c |] \
\     ==> quorem ((a, b*c), (q div c, b*(q mod c) + r))";
by (auto_tac  
    (claset(),
     simpset() addsimps zmult_ac@
                        [zmod_zdiv_equality, quorem_def, linorder_neq_iff,
			 int_0_less_mult_iff,
			 zadd_zmult_distrib2 RS sym,
			 lemma1, lemma2, lemma3, lemma4]));
val lemma = result();

Goal "(#0::int) < c ==> a div (b*c) = (a div b) div c";
by (zdiv_undefined_case_tac "b = #0" 1);
by (force_tac (claset(),
	       simpset() addsimps [quorem_div_mod RS lemma RS quorem_div, 
				   zmult_eq_0_iff]) 1);
qed "zdiv_zmult2_eq";

Goal "(#0::int) < c ==> a mod (b*c) = b*(a div b mod c) + a mod b";
by (zdiv_undefined_case_tac "b = #0" 1);
by (force_tac (claset(),
	       simpset() addsimps [quorem_div_mod RS lemma RS quorem_mod, 
				   zmult_eq_0_iff]) 1);
qed "zmod_zmult2_eq";


(*** Cancellation of common factors in "div" ***)

Goal "[| (#0::int) < b;  c ~= #0 |] ==> (c*a) div (c*b) = a div b";
by (stac zdiv_zmult2_eq 1);
by Auto_tac;
val lemma1 = result();

Goal "[| b < (#0::int);  c ~= #0 |] ==> (c*a) div (c*b) = a div b";
by (subgoal_tac "(c * (-a)) div (c * (-b)) = (-a) div (-b)" 1);
by (rtac lemma1 2);
by Auto_tac;
val lemma2 = result();

Goal "c ~= (#0::int) ==> (c*a) div (c*b) = a div b";
by (zdiv_undefined_case_tac "b = #0" 1);
by (auto_tac
    (claset(), 
     simpset() addsimps [read_instantiate [("x", "b")] linorder_neq_iff, 
			 lemma1, lemma2]));
qed "zdiv_zmult_zmult1";

Goal "c ~= (#0::int) ==> (a*c) div (b*c) = a div b";
by (dtac zdiv_zmult_zmult1 1);
by (auto_tac (claset(), simpset() addsimps [zmult_commute]));
qed "zdiv_zmult_zmult2";



(*** Distribution of factors over "mod" ***)

Goal "[| (#0::int) < b;  c ~= #0 |] ==> (c*a) mod (c*b) = c * (a mod b)";
by (stac zmod_zmult2_eq 1);
by Auto_tac;
val lemma1 = result();

Goal "[| b < (#0::int);  c ~= #0 |] ==> (c*a) mod (c*b) = c * (a mod b)";
by (subgoal_tac "(c * (-a)) mod (c * (-b)) = c * ((-a) mod (-b))" 1);
by (rtac lemma1 2);
by Auto_tac;
val lemma2 = result();

Goal "(c*a) mod (c*b) = (c::int) * (a mod b)";
by (zdiv_undefined_case_tac "b = #0" 1);
by (zdiv_undefined_case_tac "c = #0" 1);
by (auto_tac
    (claset(), 
     simpset() addsimps [read_instantiate [("x", "b")] linorder_neq_iff, 
			 lemma1, lemma2]));
qed "zmod_zmult_zmult1";

Goal "(a*c) mod (b*c) = (a mod b) * (c::int)";
by (cut_inst_tac [("c","c")] zmod_zmult_zmult1 1);
by (auto_tac (claset(), simpset() addsimps [zmult_commute]));
qed "zmod_zmult_zmult2";


(*** Speeding up the division algorithm with shifting ***)

(** computing "div" by shifting **)

Goal "(#0::int) <= a ==> (#1 + #2*b) div (#2*a) = b div a";
by (zdiv_undefined_case_tac "a = #0" 1);
by (subgoal_tac "#1 <= a" 1);
 by (arith_tac 2);
by (subgoal_tac "#1 < a * #2" 1);
 by (arith_tac 2);
by (subgoal_tac "#2*(#1 + b mod a) <= #2*a" 1);
 by (rtac zmult_zle_mono2 2);
by (auto_tac (claset(),
	      simpset() addsimps [zadd_commute, zmult_commute, 
				  add1_zle_eq, pos_mod_bound]));
by (stac zdiv_zadd1_eq 1);
by (asm_simp_tac (simpset() addsimps [zdiv_zmult_zmult2, zmod_zmult_zmult2, 
				      div_pos_pos_trivial]) 1);
by (stac div_pos_pos_trivial 1);
by (asm_simp_tac (simpset() 
           addsimps [mod_pos_pos_trivial,
                    pos_mod_sign RS zadd_zle_mono1 RSN (2,order_trans)]) 1);
by (auto_tac (claset(),
	      simpset() addsimps [mod_pos_pos_trivial]));
by (subgoal_tac "#0 <= b mod a" 1);
 by (asm_simp_tac (simpset() addsimps [pos_mod_sign]) 2);
by (arith_tac 1);
qed "pos_zdiv_mult_2";


Goal "a <= (#0::int) ==> (#1 + #2*b) div (#2*a) = (b+#1) div a";
by (subgoal_tac "(#1 + #2*(-b-#1)) div (#2 * (-a)) = (-b-#1) div (-a)" 1);
by (rtac pos_zdiv_mult_2 2);
by (auto_tac (claset(),
	      simpset() addsimps [zmult_zminus_right]));
by (subgoal_tac "(#-1 - (#2 * b)) = - (#1 + (#2 * b))" 1);
by (Simp_tac 2);
by (asm_full_simp_tac (HOL_ss
		       addsimps [zdiv_zminus_zminus, zdiff_def,
				 zminus_zadd_distrib RS sym]) 1);
qed "neg_zdiv_mult_2";


(*Not clear why this must be proved separately; probably number_of causes
  simplification problems*)
Goal "~ #0 <= x ==> x <= (#0::int)";
by Auto_tac;
val lemma = result();

Goal "number_of (v BIT b) div number_of (w BIT False) = \
\         (if ~b | (#0::int) <= number_of w                   \
\          then number_of v div (number_of w)    \
\          else (number_of v + (#1::int)) div (number_of w))";
by (simp_tac (simpset_of Int.thy addsimps [zadd_assoc, number_of_BIT]) 1);
by (asm_simp_tac (simpset()
                  delsimps bin_arith_extra_simps@bin_rel_simps
		  addsimps [zdiv_zmult_zmult1,
			    pos_zdiv_mult_2, lemma, neg_zdiv_mult_2]) 1);
qed "zdiv_number_of_BIT";

Addsimps [zdiv_number_of_BIT];


(** computing "mod" by shifting (proofs resemble those for "div") **)

Goal "(#0::int) <= a ==> (#1 + #2*b) mod (#2*a) = #1 + #2 * (b mod a)";
by (zdiv_undefined_case_tac "a = #0" 1);
by (subgoal_tac "#1 <= a" 1);
 by (arith_tac 2);
by (subgoal_tac "#1 < a * #2" 1);
 by (arith_tac 2);
by (subgoal_tac "#2*(#1 + b mod a) <= #2*a" 1);
 by (rtac zmult_zle_mono2 2);
by (auto_tac (claset(),
	      simpset() addsimps [zadd_commute, zmult_commute, 
				  add1_zle_eq, pos_mod_bound]));
by (stac zmod_zadd1_eq 1);
by (asm_simp_tac (simpset() addsimps [zmod_zmult_zmult2, 
				      mod_pos_pos_trivial]) 1);
by (rtac mod_pos_pos_trivial 1);
by (asm_simp_tac (simpset() 
                  addsimps [mod_pos_pos_trivial,
                    pos_mod_sign RS zadd_zle_mono1 RSN (2,order_trans)]) 1);
by (auto_tac (claset(),
	      simpset() addsimps [mod_pos_pos_trivial]));
by (subgoal_tac "#0 <= b mod a" 1);
 by (asm_simp_tac (simpset() addsimps [pos_mod_sign]) 2);
by (arith_tac 1);
qed "pos_zmod_mult_2";


Goal "a <= (#0::int) ==> (#1 + #2*b) mod (#2*a) = #2 * ((b+#1) mod a) - #1";
by (subgoal_tac 
    "(#1 + #2*(-b-#1)) mod (#2*(-a)) = #1 + #2*((-b-#1) mod (-a))" 1);
by (rtac pos_zmod_mult_2 2);
by (auto_tac (claset(),
	      simpset() addsimps [zmult_zminus_right]));
by (subgoal_tac "(#-1 - (#2 * b)) = - (#1 + (#2 * b))" 1);
by (Simp_tac 2);
by (asm_full_simp_tac (HOL_ss
		       addsimps [zmod_zminus_zminus, zdiff_def,
				 zminus_zadd_distrib RS sym]) 1);
by (dtac (zminus_equation RS iffD1 RS sym) 1);
by Auto_tac;
qed "neg_zmod_mult_2";

Goal "number_of (v BIT b) mod number_of (w BIT False) = \
\         (if b then \
\               if (#0::int) <= number_of w \
\               then #2 * (number_of v mod number_of w) + #1    \
\               else #2 * ((number_of v + (#1::int)) mod number_of w) - #1  \
\          else #2 * (number_of v mod number_of w))";
by (simp_tac (simpset_of Int.thy addsimps [zadd_assoc, number_of_BIT]) 1);
by (asm_simp_tac (simpset()
		  delsimps bin_arith_extra_simps@bin_rel_simps
		  addsimps [zmod_zmult_zmult1,
			    pos_zmod_mult_2, lemma, neg_zmod_mult_2]) 1);
qed "zmod_number_of_BIT";

Addsimps [zmod_number_of_BIT];


(** Quotients of signs **)

Goal "[| a < (#0::int);  #0 < b |] ==> a div b < #0";
by (subgoal_tac "a div b <= #-1" 1);
by (Force_tac 1);
by (rtac order_trans 1);
by (res_inst_tac [("a'","#-1")]  zdiv_mono1 1);
by (auto_tac (claset(), simpset() addsimps [zdiv_minus1]));
qed "div_neg_pos_less0";

Goal "[| (#0::int) <= a;  b < #0 |] ==> a div b <= #0";
by (dtac zdiv_mono1_neg 1);
by Auto_tac;
qed "div_nonneg_neg_le0";

Goal "(#0::int) < b ==> (#0 <= a div b) = (#0 <= a)";
by Auto_tac;
by (dtac zdiv_mono1 2);
by (auto_tac (claset(), simpset() addsimps [linorder_neq_iff]));
by (full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
by (blast_tac (claset() addIs [div_neg_pos_less0]) 1);
qed "pos_imp_zdiv_nonneg_iff";

Goal "b < (#0::int) ==> (#0 <= a div b) = (a <= (#0::int))";
by (stac (zdiv_zminus_zminus RS sym) 1);
by (stac pos_imp_zdiv_nonneg_iff 1);
by Auto_tac;
qed "neg_imp_zdiv_nonneg_iff";

(*But not (a div b <= 0 iff a<=0); consider a=1, b=2 when a div b = 0.*)
Goal "(#0::int) < b ==> (a div b < #0) = (a < #0)";
by (asm_simp_tac (simpset() addsimps [linorder_not_le RS sym,
				      pos_imp_zdiv_nonneg_iff]) 1);
qed "pos_imp_zdiv_neg_iff";

(*Again the law fails for <=: consider a = -1, b = -2 when a div b = 0*)
Goal "b < (#0::int) ==> (a div b < #0) = (#0 < a)";
by (asm_simp_tac (simpset() addsimps [linorder_not_le RS sym,
				      neg_imp_zdiv_nonneg_iff]) 1);
qed "neg_imp_zdiv_neg_iff";
