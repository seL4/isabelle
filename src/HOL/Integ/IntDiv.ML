(*  Title:      HOL/IntDiv.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"
*)

Addsimps [zless_nat_conj];

(*** Uniqueness and monotonicity of quotients and remainders ***)

Goal "[| r' + b*q' <= r + b*q;  #0 <= r';  #0 < b;  r < b |] \
\     ==> q' <= (q::int)";
by (subgoal_tac "r' + b * (q'-q) <= r" 1);
by (simp_tac (simpset() addsimps zcompare_rls@[zdiff_zmult_distrib2]) 2);
by (subgoal_tac "#0 < b * (#1 + q - q')" 1);
by (etac order_le_less_trans 2);
by (full_simp_tac (simpset() addsimps zcompare_rls@[zdiff_zmult_distrib2,
						    zadd_zmult_distrib2]) 2);
by (subgoal_tac "b * q' < b * (#1 + q)" 1);
by (full_simp_tac (simpset() addsimps zcompare_rls@[zdiff_zmult_distrib2,
						    zadd_zmult_distrib2]) 2);
by (Asm_full_simp_tac 1);
qed "unique_quotient_lemma";

Goal "[| r' + b*q' <= r + b*q;  r <= #0;  b < #0;  b < r' |] \
\     ==> q <= (q'::int)";
by (res_inst_tac [("b", "-b"), ("r", "-r'"), ("r'", "-r")] 
    unique_quotient_lemma 1);
by (auto_tac (claset(), 
	      simpset() addsimps zcompare_rls@[zmult_zminus_right])); 
qed "unique_quotient_lemma_neg";


Goal "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  b ~= #0 |] \
\     ==> q = q'";
by (asm_full_simp_tac 
    (simpset() addsimps split_ifs@[quorem_def, linorder_neq_iff]) 1);
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

Goal "adjust a b (q,r) = (if #0 <= r-b then (#2*q + #1, r-b)  \
\                         else (#2*q, r))";
by (simp_tac (simpset() addsimps [adjust_def]) 1);
qed "adjust_eq";
Addsimps [adjust_eq];

(*Proving posDivAlg's termination condition*)
val [tc] = posDivAlg.tcs;
goalw_cterm [] (cterm_of (sign_of thy) (HOLogic.mk_Trueprop tc));
by (auto_tac (claset(), simpset() addsimps [zmult_2_right]));
val lemma = result();

(* removing the termination condition from the generated theorems *)

bind_thm ("posDivAlg_raw_eqn", lemma RS hd posDivAlg.rules);

(**use with simproc to avoid re-proving the premise*)
Goal "#0 < b ==> \
\     posDivAlg (a,b) =      \
\      (if a<b then (#0,a) else adjust a b (posDivAlg(a, #2*b)))";
by (rtac (posDivAlg_raw_eqn RS trans) 1);
by (Asm_simp_tac 1);
qed "posDivAlg_eqn";

val posDivAlg_induct = lemma RS posDivAlg.induct;


(*Correctness of posDivAlg: it computes quotients correctly*)
Goal "#0 <= a --> #0 < b --> quorem ((a, b), posDivAlg (a, b))";
by (res_inst_tac [("u", "a"), ("v", "b")] posDivAlg_induct 1);
by Auto_tac;
by (ALLGOALS 
    (asm_full_simp_tac (simpset() addsimps [quorem_def,
					    pos_times_pos_is_pos])));
(*base case: a<b*)
by (asm_full_simp_tac (simpset() addsimps [posDivAlg_eqn]) 1);
(*main argument*)
by (stac posDivAlg_eqn 1);
by (ALLGOALS Asm_simp_tac);
by (etac splitE 1);
by Auto_tac;
(*the "add one" case*)
by (asm_full_simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
(*the "just double" case*)
by (asm_full_simp_tac (simpset() addsimps zcompare_rls@[zmult_2_right]) 1);
qed_spec_mp "posDivAlg_correct";


(*** Correctness of negDivAlg, the division algorithm for a<0 and b>0 ***)

(*Proving negDivAlg's termination condition*)
val [tc] = negDivAlg.tcs;
goalw_cterm [] (cterm_of (sign_of thy) (HOLogic.mk_Trueprop tc));
by (auto_tac (claset(), simpset() addsimps [zmult_2_right]));
val lemma = result();

(* removing the termination condition from the generated theorems *)

bind_thm ("negDivAlg_raw_eqn", lemma RS hd negDivAlg.rules);

(**use with simproc to avoid re-proving the premise*)
Goal "#0 < b ==> \
\     negDivAlg (a,b) =      \
\      (if #0<=a+b then (#-1,a+b) else adjust a b (negDivAlg(a, #2*b)))";
by (rtac (negDivAlg_raw_eqn RS trans) 1);
by (Asm_simp_tac 1);
qed "negDivAlg_eqn";

val negDivAlg_induct = lemma RS negDivAlg.induct;


(*Correctness of negDivAlg: it computes quotients correctly
  It doesn't work if a=0 because the 0/b=0 rather than -1*)
Goal "a < #0 --> #0 < b --> quorem ((a, b), negDivAlg (a, b))";
by (res_inst_tac [("u", "a"), ("v", "b")] negDivAlg_induct 1);
by Auto_tac;
by (ALLGOALS 
    (asm_full_simp_tac (simpset() addsimps [quorem_def,
					    pos_times_pos_is_pos])));
(*base case: 0<=a+b*)
by (asm_full_simp_tac (simpset() addsimps [negDivAlg_eqn]) 1);
(*main argument*)
by (stac negDivAlg_eqn 1);
by (ALLGOALS Asm_simp_tac);
by (etac splitE 1);
by Auto_tac;
(*the "add one" case*)
by (asm_full_simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
(*the "just double" case*)
by (asm_full_simp_tac (simpset() addsimps zcompare_rls@[zmult_2_right]) 1);
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

Goal "b ~= (#0::int) ==> a = b * (a div b) + (a mod b)";
by (cut_inst_tac [("a","a"),("b","b")] divAlg_correct 1);
by (auto_tac (claset(), 
	      simpset() addsimps [quorem_def, div_def, mod_def]));
qed "zmod_zdiv_equality";  
   (*the name mod_div_equality would hide the other one proved in Divides.ML
     existing users aren't using name spaces for theorems*)

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


(*** Computation of division and remainder ***)

Goal "(#0::int) div b = #0";
by (simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "div_zero";

Goal "(#0::int) mod b = #0";
by (simp_tac (simpset() addsimps [mod_def, divAlg_def]) 1);
qed "mod_zero";

Addsimps [div_zero, mod_zero];

(** a positive, b positive **)

Goal "[| #0 < a;  #0 < b |] ==> a div b = fst (posDivAlg(a,b))";
by (asm_simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "div_pos_pos";

Goal "[| #0 < a;  #0 < b |] ==> a mod b = snd (posDivAlg(a,b))";
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

Goal "[| a < #0;  b < #0 |] ==> a div b = fst (negateSnd(posDivAlg(-a,-b)))";
by (asm_simp_tac (simpset() addsimps [div_def, divAlg_def]) 1);
qed "div_neg_neg";

Goal "[| a < #0;  b < #0 |] ==> a mod b = snd (negateSnd(posDivAlg(-a,-b)))";
by (asm_simp_tac (simpset() addsimps [mod_def, divAlg_def]) 1);
qed "mod_neg_neg";

Addsimps (map (read_instantiate_sg (sign_of IntDiv.thy)
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
qed "zmod_minus1";
Addsimps [zmod_minus1];

Goal "a div (#-1::int) = -a";
by (cut_inst_tac [("a","a"),("b","#-1")] zmod_zdiv_equality 1);
by Auto_tac;
qed "zdiv_minus1";
Addsimps [zdiv_minus1];


(** Monotonicity results **)


Goal "[| a <= a';  #0 < (b::int) |] ==> a div b <= a' div b";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a'"),("b","b")] zmod_zdiv_equality 2);
by Auto_tac;
by (rtac unique_quotient_lemma 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_sign,pos_mod_bound])));
qed "zdiv_mono1";

Goal "[| a <= a';  (b::int) < #0 |] ==> a' div b <= a div b";
by (cut_inst_tac [("a","a"),("b","b")] zmod_zdiv_equality 1);
by (cut_inst_tac [("a","a'"),("b","b")] zmod_zdiv_equality 2);
by Auto_tac;
by (rtac unique_quotient_lemma_neg 1);
by (etac subst 1);
by (etac subst 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [neg_mod_sign,neg_mod_bound])));
qed "zdiv_mono1_neg";



(** The division algorithm in ML **)

fun posDivAlg (a,b) =
  if a<b then (0,a)
  else let val (q,r) = posDivAlg(a, 2*b)
           in  if 0<=r-b then (2*q+1, r-b)
               else (2*q, r)
       end;

fun negDivAlg (a,b) =
  if 0<=a+b then (~1,a+b)
  else let val (q,r) = negDivAlg(a, 2*b)
           in  if 0<=r-b then (2*q+1, r-b)
               else (2*q, r)
       end;

fun negateSnd (q,r:int) = (q,~r);

fun divAlg (a,b) = if 0<=a then 
                      if b>0 then posDivAlg (a,b) 
                       else if a=0 then (0,0)
                            else negateSnd (negDivAlg (~a,~b))
                   else 
                      if 0<b then negDivAlg (a,b)
                      else        negateSnd (posDivAlg (~a,~b));
