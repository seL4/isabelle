(*  Title:      HOL/IntDiv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"

Here is the division algorithm in ML:

    fun posDivAlg (a,b) =
      if a<b then (0,a)
      else let val (q,r) = posDivAlg(a, 2*b)
	       in  if 0<=r-b then (2*q+1, r-b) else (2*q, r)
	   end

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


theory IntDiv = IntArith + Recdef:

declare zless_nat_conj [simp]

constdefs
  quorem :: "(int*int) * (int*int) => bool"
    "quorem == %((a,b), (q,r)).
                      a = b*q + r &
                      (if 0 < b then 0<=r & r<b else b<r & r <= 0)"

  adjust :: "[int, int*int] => int*int"
    "adjust b == %(q,r). if 0 <= r-b then (2*q + 1, r-b)
                         else (2*q, r)"

(** the division algorithm **)

(*for the case a>=0, b>0*)
consts posDivAlg :: "int*int => int*int"
recdef posDivAlg "inv_image less_than (%(a,b). nat(a - b + 1))"
    "posDivAlg (a,b) =
       (if (a<b | b<=0) then (0,a)
        else adjust b (posDivAlg(a, 2*b)))"

(*for the case a<0, b>0*)
consts negDivAlg :: "int*int => int*int"
recdef negDivAlg "inv_image less_than (%(a,b). nat(- a - b))"
    "negDivAlg (a,b) =
       (if (0<=a+b | b<=0) then (-1,a+b)
        else adjust b (negDivAlg(a, 2*b)))"

(*for the general case b~=0*)

constdefs
  negateSnd :: "int*int => int*int"
    "negateSnd == %(q,r). (q,-r)"

  (*The full division algorithm considers all possible signs for a, b
    including the special case a=0, b<0, because negDivAlg requires a<0*)
  divAlg :: "int*int => int*int"
    "divAlg ==
       %(a,b). if 0<=a then
                  if 0<=b then posDivAlg (a,b)
                  else if a=0 then (0,0)
                       else negateSnd (negDivAlg (-a,-b))
               else 
                  if 0<b then negDivAlg (a,b)
                  else         negateSnd (posDivAlg (-a,-b))"

instance
  int :: "Divides.div" ..       (*avoid clash with 'div' token*)

defs
  div_def:   "a div b == fst (divAlg (a,b))"
  mod_def:   "a mod b == snd (divAlg (a,b))"



(*** Uniqueness and monotonicity of quotients and remainders ***)

lemma unique_quotient_lemma:
     "[| b*q' + r'  <= b*q + r;  0 <= r';  0 < b;  r < b |]  
      ==> q' <= (q::int)"
apply (subgoal_tac "r' + b * (q'-q) <= r")
 prefer 2 apply (simp add: zdiff_zmult_distrib2)
apply (subgoal_tac "0 < b * (1 + q - q') ")
apply (erule_tac [2] order_le_less_trans)
 prefer 2 apply (simp add: zdiff_zmult_distrib2 zadd_zmult_distrib2)
apply (subgoal_tac "b * q' < b * (1 + q) ")
 prefer 2 apply (simp add: zdiff_zmult_distrib2 zadd_zmult_distrib2)
apply (simp add: zmult_zless_cancel1)
done

lemma unique_quotient_lemma_neg:
     "[| b*q' + r' <= b*q + r;  r <= 0;  b < 0;  b < r' |]  
      ==> q <= (q'::int)"
by (rule_tac b = "-b" and r = "-r'" and r' = "-r" in unique_quotient_lemma, 
    auto)

lemma unique_quotient:
     "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  b ~= 0 |]  
      ==> q = q'"
apply (simp add: quorem_def linorder_neq_iff split: split_if_asm)
apply (blast intro: order_antisym
             dest: order_eq_refl [THEN unique_quotient_lemma] 
             order_eq_refl [THEN unique_quotient_lemma_neg] sym)+
done


lemma unique_remainder:
     "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  b ~= 0 |]  
      ==> r = r'"
apply (subgoal_tac "q = q'")
 apply (simp add: quorem_def)
apply (blast intro: unique_quotient)
done


(*** Correctness of posDivAlg, the division algorithm for a>=0 and b>0 ***)

lemma adjust_eq [simp]:
     "adjust b (q,r) = 
      (let diff = r-b in  
	if 0 <= diff then (2*q + 1, diff)   
                     else (2*q, r))"
by (simp add: Let_def adjust_def)

declare posDivAlg.simps [simp del]

(**use with a simproc to avoid repeatedly proving the premise*)
lemma posDivAlg_eqn:
     "0 < b ==>  
      posDivAlg (a,b) = (if a<b then (0,a) else adjust b (posDivAlg(a, 2*b)))"
by (rule posDivAlg.simps [THEN trans], simp)

(*Correctness of posDivAlg: it computes quotients correctly*)
lemma posDivAlg_correct [rule_format]:
     "0 <= a --> 0 < b --> quorem ((a, b), posDivAlg (a, b))"
apply (induct_tac a b rule: posDivAlg.induct, auto)
 apply (simp_all add: quorem_def)
 (*base case: a<b*)
 apply (simp add: posDivAlg_eqn)
(*main argument*)
apply (subst posDivAlg_eqn, simp_all)
apply (erule splitE)
apply (auto simp add: zadd_zmult_distrib2 Let_def)
done


(*** Correctness of negDivAlg, the division algorithm for a<0 and b>0 ***)

declare negDivAlg.simps [simp del]

(**use with a simproc to avoid repeatedly proving the premise*)
lemma negDivAlg_eqn:
     "0 < b ==>  
      negDivAlg (a,b) =       
       (if 0<=a+b then (-1,a+b) else adjust b (negDivAlg(a, 2*b)))"
by (rule negDivAlg.simps [THEN trans], simp)

(*Correctness of negDivAlg: it computes quotients correctly
  It doesn't work if a=0 because the 0/b equals 0, not -1*)
lemma negDivAlg_correct [rule_format]:
     "a < 0 --> 0 < b --> quorem ((a, b), negDivAlg (a, b))"
apply (induct_tac a b rule: negDivAlg.induct, auto)
 apply (simp_all add: quorem_def)
 (*base case: 0<=a+b*)
 apply (simp add: negDivAlg_eqn)
(*main argument*)
apply (subst negDivAlg_eqn, assumption)
apply (erule splitE)
apply (auto simp add: zadd_zmult_distrib2 Let_def)
done


(*** Existence shown by proving the division algorithm to be correct ***)

(*the case a=0*)
lemma quorem_0: "b ~= 0 ==> quorem ((0,b), (0,0))"
by (auto simp add: quorem_def linorder_neq_iff)

lemma posDivAlg_0 [simp]: "posDivAlg (0, b) = (0, 0)"
by (subst posDivAlg.simps, auto)

lemma negDivAlg_minus1 [simp]: "negDivAlg (-1, b) = (-1, b - 1)"
by (subst negDivAlg.simps, auto)

lemma negateSnd_eq [simp]: "negateSnd(q,r) = (q,-r)"
by (unfold negateSnd_def, auto)

lemma quorem_neg: "quorem ((-a,-b), qr) ==> quorem ((a,b), negateSnd qr)"
by (auto simp add: split_ifs quorem_def)

lemma divAlg_correct: "b ~= 0 ==> quorem ((a,b), divAlg(a,b))"
by (force simp add: linorder_neq_iff quorem_0 divAlg_def quorem_neg
                    posDivAlg_correct negDivAlg_correct)

(** Arbitrary definitions for division by zero.  Useful to simplify 
    certain equations **)

lemma DIVISION_BY_ZERO: "a div (0::int) = 0 & a mod (0::int) = a"
by (simp add: div_def mod_def divAlg_def posDivAlg.simps)  (*NOT for adding to default simpset*)

(** Basic laws about division and remainder **)

lemma zmod_zdiv_equality: "(a::int) = b * (a div b) + (a mod b)"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (cut_tac a = a and b = b in divAlg_correct)
apply (auto simp add: quorem_def div_def mod_def)
done

lemma pos_mod_conj : "(0::int) < b ==> 0 <= a mod b & a mod b < b"
apply (cut_tac a = a and b = b in divAlg_correct)
apply (auto simp add: quorem_def mod_def)
done

lemmas pos_mod_sign  = pos_mod_conj [THEN conjunct1, standard]
   and pos_mod_bound = pos_mod_conj [THEN conjunct2, standard]

lemma neg_mod_conj : "b < (0::int) ==> a mod b <= 0 & b < a mod b"
apply (cut_tac a = a and b = b in divAlg_correct)
apply (auto simp add: quorem_def div_def mod_def)
done

lemmas neg_mod_sign  = neg_mod_conj [THEN conjunct1, standard]
   and neg_mod_bound = neg_mod_conj [THEN conjunct2, standard]


(** proving general properties of div and mod **)

lemma quorem_div_mod: "b ~= 0 ==> quorem ((a, b), (a div b, a mod b))"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (force simp add: quorem_def linorder_neq_iff pos_mod_sign pos_mod_bound
                       neg_mod_sign neg_mod_bound)
done

lemma quorem_div: "[| quorem((a,b),(q,r));  b ~= 0 |] ==> a div b = q"
by (simp add: quorem_div_mod [THEN unique_quotient])

lemma quorem_mod: "[| quorem((a,b),(q,r));  b ~= 0 |] ==> a mod b = r"
by (simp add: quorem_div_mod [THEN unique_remainder])

lemma div_pos_pos_trivial: "[| (0::int) <= a;  a < b |] ==> a div b = 0"
apply (rule quorem_div)
apply (auto simp add: quorem_def)
done

lemma div_neg_neg_trivial: "[| a <= (0::int);  b < a |] ==> a div b = 0"
apply (rule quorem_div)
apply (auto simp add: quorem_def)
done

lemma div_pos_neg_trivial: "[| (0::int) < a;  a+b <= 0 |] ==> a div b = -1"
apply (rule quorem_div)
apply (auto simp add: quorem_def)
done

(*There is no div_neg_pos_trivial because  0 div b = 0 would supersede it*)

lemma mod_pos_pos_trivial: "[| (0::int) <= a;  a < b |] ==> a mod b = a"
apply (rule_tac q = 0 in quorem_mod)
apply (auto simp add: quorem_def)
done

lemma mod_neg_neg_trivial: "[| a <= (0::int);  b < a |] ==> a mod b = a"
apply (rule_tac q = 0 in quorem_mod)
apply (auto simp add: quorem_def)
done

lemma mod_pos_neg_trivial: "[| (0::int) < a;  a+b <= 0 |] ==> a mod b = a+b"
apply (rule_tac q = "-1" in quorem_mod)
apply (auto simp add: quorem_def)
done

(*There is no mod_neg_pos_trivial...*)


(*Simpler laws such as -a div b = -(a div b) FAIL, but see just below*)
lemma zdiv_zminus_zminus [simp]: "(-a) div (-b) = a div (b::int)"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (simp add: quorem_div_mod [THEN quorem_neg, simplified, 
                                 THEN quorem_div, THEN sym])

done

(*Simpler laws such as -a mod b = -(a mod b) FAIL, but see just below*)
lemma zmod_zminus_zminus [simp]: "(-a) mod (-b) = - (a mod (b::int))"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (subst quorem_div_mod [THEN quorem_neg, simplified, THEN quorem_mod],
       auto)
done

(*** div, mod and unary minus ***)

lemma zminus1_lemma:
     "quorem((a,b),(q,r))  
      ==> quorem ((-a,b), (if r=0 then -q else -q - 1),  
                          (if r=0 then 0 else b-r))"
by (force simp add: split_ifs quorem_def linorder_neq_iff zdiff_zmult_distrib2)


lemma zdiv_zminus1_eq_if:
     "b ~= (0::int)  
      ==> (-a) div b =  
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (blast intro: quorem_div_mod [THEN zminus1_lemma, THEN quorem_div])

lemma zmod_zminus1_eq_if:
     "(-a::int) mod b = (if a mod b = 0 then 0 else  b - (a mod b))"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (blast intro: quorem_div_mod [THEN zminus1_lemma, THEN quorem_mod])
done

lemma zdiv_zminus2: "a div (-b) = (-a::int) div b"
by (cut_tac a = "-a" in zdiv_zminus_zminus, auto)

lemma zmod_zminus2: "a mod (-b) = - ((-a::int) mod b)"
by (cut_tac a = "-a" and b = b in zmod_zminus_zminus, auto)

lemma zdiv_zminus2_eq_if:
     "b ~= (0::int)  
      ==> a div (-b) =  
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (simp add: zdiv_zminus1_eq_if zdiv_zminus2)

lemma zmod_zminus2_eq_if:
     "a mod (-b::int) = (if a mod b = 0 then 0 else  (a mod b) - b)"
by (simp add: zmod_zminus1_eq_if zmod_zminus2)


(*** division of a number by itself ***)

lemma lemma1: "[| (0::int) < a; a = r + a*q; r < a |] ==> 1 <= q"
apply (subgoal_tac "0 < a*q")
 apply (simp add: int_0_less_mult_iff, arith)
done

lemma lemma2: "[| (0::int) < a; a = r + a*q; 0 <= r |] ==> q <= 1"
apply (subgoal_tac "0 <= a* (1-q) ")
 apply (simp add: int_0_le_mult_iff)
apply (simp add: zdiff_zmult_distrib2)
done

lemma self_quotient: "[| quorem((a,a),(q,r));  a ~= (0::int) |] ==> q = 1"
apply (simp add: split_ifs quorem_def linorder_neq_iff)
apply (rule order_antisym, auto)
apply (rule_tac [3] a = "-a" and r = "-r" in lemma1)
apply (rule_tac a = "-a" and r = "-r" in lemma2)
apply (force intro: lemma1 lemma2 simp add: zadd_commute zmult_zminus)+
done

lemma self_remainder: "[| quorem((a,a),(q,r));  a ~= (0::int) |] ==> r = 0"
apply (frule self_quotient, assumption)
apply (simp add: quorem_def)
done

lemma zdiv_self [simp]: "a ~= 0 ==> a div a = (1::int)"
by (simp add: quorem_div_mod [THEN self_quotient])

(*Here we have 0 mod 0 = 0, also assumed by Knuth (who puts m mod 0 = 0) *)
lemma zmod_self [simp]: "a mod a = (0::int)"
apply (case_tac "a = 0", simp add: DIVISION_BY_ZERO)
apply (simp add: quorem_div_mod [THEN self_remainder])
done


(*** Computation of division and remainder ***)

lemma zdiv_zero [simp]: "(0::int) div b = 0"
by (simp add: div_def divAlg_def)

lemma div_eq_minus1: "(0::int) < b ==> -1 div b = -1"
by (simp add: div_def divAlg_def)

lemma zmod_zero [simp]: "(0::int) mod b = 0"
by (simp add: mod_def divAlg_def)

lemma zdiv_minus1: "(0::int) < b ==> -1 div b = -1"
by (simp add: div_def divAlg_def)

lemma zmod_minus1: "(0::int) < b ==> -1 mod b = b - 1"
by (simp add: mod_def divAlg_def)

(** a positive, b positive **)

lemma div_pos_pos: "[| 0 < a;  0 <= b |] ==> a div b = fst (posDivAlg(a,b))"
by (simp add: div_def divAlg_def)

lemma mod_pos_pos: "[| 0 < a;  0 <= b |] ==> a mod b = snd (posDivAlg(a,b))"
by (simp add: mod_def divAlg_def)

(** a negative, b positive **)

lemma div_neg_pos: "[| a < 0;  0 < b |] ==> a div b = fst (negDivAlg(a,b))"
by (simp add: div_def divAlg_def)

lemma mod_neg_pos: "[| a < 0;  0 < b |] ==> a mod b = snd (negDivAlg(a,b))"
by (simp add: mod_def divAlg_def)

(** a positive, b negative **)

lemma div_pos_neg:
     "[| 0 < a;  b < 0 |] ==> a div b = fst (negateSnd(negDivAlg(-a,-b)))"
by (simp add: div_def divAlg_def)

lemma mod_pos_neg:
     "[| 0 < a;  b < 0 |] ==> a mod b = snd (negateSnd(negDivAlg(-a,-b)))"
by (simp add: mod_def divAlg_def)

(** a negative, b negative **)

lemma div_neg_neg:
     "[| a < 0;  b <= 0 |] ==> a div b = fst (negateSnd(posDivAlg(-a,-b)))"
by (simp add: div_def divAlg_def)

lemma mod_neg_neg:
     "[| a < 0;  b <= 0 |] ==> a mod b = snd (negateSnd(posDivAlg(-a,-b)))"
by (simp add: mod_def divAlg_def)

text {*Simplify expresions in which div and mod combine numerical constants*}

declare div_pos_pos [of "number_of v" "number_of w", standard, simp]
declare div_neg_pos [of "number_of v" "number_of w", standard, simp]
declare div_pos_neg [of "number_of v" "number_of w", standard, simp]
declare div_neg_neg [of "number_of v" "number_of w", standard, simp]

declare mod_pos_pos [of "number_of v" "number_of w", standard, simp]
declare mod_neg_pos [of "number_of v" "number_of w", standard, simp]
declare mod_pos_neg [of "number_of v" "number_of w", standard, simp]
declare mod_neg_neg [of "number_of v" "number_of w", standard, simp]

declare posDivAlg_eqn [of "number_of v" "number_of w", standard, simp]
declare negDivAlg_eqn [of "number_of v" "number_of w", standard, simp]


(** Special-case simplification **)

lemma zmod_1 [simp]: "a mod (1::int) = 0"
apply (cut_tac a = a and b = 1 in pos_mod_sign)
apply (cut_tac [2] a = a and b = 1 in pos_mod_bound, auto)
done 

lemma zdiv_1 [simp]: "a div (1::int) = a"
by (cut_tac a = a and b = 1 in zmod_zdiv_equality, auto)

lemma zmod_minus1_right [simp]: "a mod (-1::int) = 0"
apply (cut_tac a = a and b = "-1" in neg_mod_sign)
apply (cut_tac [2] a = a and b = "-1" in neg_mod_bound, auto)
done

lemma zdiv_minus1_right [simp]: "a div (-1::int) = -a"
by (cut_tac a = a and b = "-1" in zmod_zdiv_equality, auto)

(** The last remaining special cases for constant arithmetic:
    1 div z and 1 mod z **)

declare div_pos_pos [OF int_0_less_1, of "number_of w", standard, simp]
declare div_pos_neg [OF int_0_less_1, of "number_of w", standard, simp]
declare mod_pos_pos [OF int_0_less_1, of "number_of w", standard, simp]
declare mod_pos_neg [OF int_0_less_1, of "number_of w", standard, simp]

declare posDivAlg_eqn [of concl: 1 "number_of w", standard, simp]
declare negDivAlg_eqn [of concl: 1 "number_of w", standard, simp]


(*** Monotonicity in the first argument (divisor) ***)

lemma zdiv_mono1: "[| a <= a';  0 < (b::int) |] ==> a div b <= a' div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a' and b = b in zmod_zdiv_equality)
apply (rule unique_quotient_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all add: pos_mod_sign pos_mod_bound)
done

lemma zdiv_mono1_neg: "[| a <= a';  (b::int) < 0 |] ==> a' div b <= a div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a' and b = b in zmod_zdiv_equality)
apply (rule unique_quotient_lemma_neg)
apply (erule subst)
apply (erule subst)
apply (simp_all add: neg_mod_sign neg_mod_bound)
done


(*** Monotonicity in the second argument (dividend) ***)

lemma q_pos_lemma:
     "[| 0 <= b'*q' + r'; r' < b';  0 < b' |] ==> 0 <= (q'::int)"
apply (subgoal_tac "0 < b'* (q' + 1) ")
 apply (simp add: int_0_less_mult_iff)
apply (simp add: zadd_zmult_distrib2)
done

lemma zdiv_mono2_lemma:
     "[| b*q + r = b'*q' + r';  0 <= b'*q' + r';   
         r' < b';  0 <= r;  0 < b';  b' <= b |]   
      ==> q <= (q'::int)"
apply (frule q_pos_lemma, assumption+) 
apply (subgoal_tac "b*q < b* (q' + 1) ")
 apply (simp add: zmult_zless_cancel1)
apply (subgoal_tac "b*q = r' - r + b'*q'")
 prefer 2 apply simp
apply (simp (no_asm_simp) add: zadd_zmult_distrib2)
apply (subst zadd_commute, rule zadd_zless_mono, arith)
apply (rule zmult_zle_mono1, auto)
done

lemma zdiv_mono2:
     "[| (0::int) <= a;  0 < b';  b' <= b |] ==> a div b <= a div b'"
apply (subgoal_tac "b ~= 0")
 prefer 2 apply arith
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a and b = b' in zmod_zdiv_equality)
apply (rule zdiv_mono2_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all add: pos_mod_sign pos_mod_bound)
done

lemma q_neg_lemma:
     "[| b'*q' + r' < 0;  0 <= r';  0 < b' |] ==> q' <= (0::int)"
apply (subgoal_tac "b'*q' < 0")
 apply (simp add: zmult_less_0_iff, arith)
done

lemma zdiv_mono2_neg_lemma:
     "[| b*q + r = b'*q' + r';  b'*q' + r' < 0;   
         r < b;  0 <= r';  0 < b';  b' <= b |]   
      ==> q' <= (q::int)"
apply (frule q_neg_lemma, assumption+) 
apply (subgoal_tac "b*q' < b* (q + 1) ")
 apply (simp add: zmult_zless_cancel1)
apply (simp add: zadd_zmult_distrib2)
apply (subgoal_tac "b*q' <= b'*q'")
 prefer 2 apply (simp add: zmult_zle_mono1_neg)
apply (subgoal_tac "b'*q' < b + b*q")
 apply arith
apply simp 
done

lemma zdiv_mono2_neg:
     "[| a < (0::int);  0 < b';  b' <= b |] ==> a div b' <= a div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a and b = b' in zmod_zdiv_equality)
apply (rule zdiv_mono2_neg_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all add: pos_mod_sign pos_mod_bound)
done


(*** More algebraic laws for div and mod ***)

(** proving (a*b) div c = a * (b div c) + a * (b mod c) **)

lemma zmult1_lemma:
     "[| quorem((b,c),(q,r));  c ~= 0 |]  
      ==> quorem ((a*b, c), (a*q + a*r div c, a*r mod c))"
by (force simp add: split_ifs quorem_def linorder_neq_iff zadd_zmult_distrib2
                    pos_mod_sign pos_mod_bound neg_mod_sign neg_mod_bound 
                    zmod_zdiv_equality)

lemma zdiv_zmult1_eq: "(a*b) div c = a*(b div c) + a*(b mod c) div (c::int)"
apply (case_tac "c = 0", simp add: DIVISION_BY_ZERO)
apply (blast intro: quorem_div_mod [THEN zmult1_lemma, THEN quorem_div])
done

lemma zmod_zmult1_eq: "(a*b) mod c = a*(b mod c) mod (c::int)"
apply (case_tac "c = 0", simp add: DIVISION_BY_ZERO)
apply (blast intro: quorem_div_mod [THEN zmult1_lemma, THEN quorem_mod])
done

lemma zmod_zmult1_eq': "(a*b) mod (c::int) = ((a mod c) * b) mod c"
apply (rule trans)
apply (rule_tac s = "b*a mod c" in trans)
apply (rule_tac [2] zmod_zmult1_eq)
apply (simp_all add: zmult_commute)
done

lemma zmod_zmult_distrib: "(a*b) mod (c::int) = ((a mod c) * (b mod c)) mod c"
apply (rule zmod_zmult1_eq' [THEN trans])
apply (rule zmod_zmult1_eq)
done

lemma zdiv_zmult_self1 [simp]: "b ~= (0::int) ==> (a*b) div b = a"
by (simp add: zdiv_zmult1_eq)

lemma zdiv_zmult_self2 [simp]: "b ~= (0::int) ==> (b*a) div b = a"
by (subst zmult_commute, erule zdiv_zmult_self1)

lemma zmod_zmult_self1 [simp]: "(a*b) mod b = (0::int)"
by (simp add: zmod_zmult1_eq)

lemma zmod_zmult_self2 [simp]: "(b*a) mod b = (0::int)"
by (simp add: zmult_commute zmod_zmult1_eq)

lemma zmod_eq_0_iff: "(m mod d = 0) = (EX q::int. m = d*q)"
by (cut_tac a = m and b = d in zmod_zdiv_equality, auto)

declare zmod_eq_0_iff [THEN iffD1, dest!]


(** proving (a+b) div c = a div c + b div c + ((a mod c + b mod c) div c) **)

lemma zadd1_lemma:
     "[| quorem((a,c),(aq,ar));  quorem((b,c),(bq,br));  c ~= 0 |]  
      ==> quorem ((a+b, c), (aq + bq + (ar+br) div c, (ar+br) mod c))"
by (force simp add: split_ifs quorem_def linorder_neq_iff zadd_zmult_distrib2
                    pos_mod_sign pos_mod_bound neg_mod_sign neg_mod_bound
                    zmod_zdiv_equality)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma zdiv_zadd1_eq:
     "(a+b) div (c::int) = a div c + b div c + ((a mod c + b mod c) div c)"
apply (case_tac "c = 0", simp add: DIVISION_BY_ZERO)
apply (blast intro: zadd1_lemma [OF quorem_div_mod quorem_div_mod] quorem_div)
done

lemma zmod_zadd1_eq: "(a+b) mod (c::int) = (a mod c + b mod c) mod c"
apply (case_tac "c = 0", simp add: DIVISION_BY_ZERO)
apply (blast intro: zadd1_lemma [OF quorem_div_mod quorem_div_mod] quorem_mod)
done

lemma mod_div_trivial [simp]: "(a mod b) div b = (0::int)"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (auto simp add: linorder_neq_iff pos_mod_sign pos_mod_bound
            div_pos_pos_trivial neg_mod_sign neg_mod_bound div_neg_neg_trivial)
done

lemma mod_mod_trivial [simp]: "(a mod b) mod b = a mod (b::int)"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (force simp add: linorder_neq_iff pos_mod_sign pos_mod_bound
                       mod_pos_pos_trivial neg_mod_sign neg_mod_bound 
                       mod_neg_neg_trivial)
done

lemma zmod_zadd_left_eq: "(a+b) mod (c::int) = ((a mod c) + b) mod c"
apply (rule trans [symmetric])
apply (rule zmod_zadd1_eq, simp)
apply (rule zmod_zadd1_eq [symmetric])
done

lemma zmod_zadd_right_eq: "(a+b) mod (c::int) = (a + (b mod c)) mod c"
apply (rule trans [symmetric])
apply (rule zmod_zadd1_eq, simp)
apply (rule zmod_zadd1_eq [symmetric])
done

lemma zdiv_zadd_self1[simp]: "a ~= (0::int) ==> (a+b) div a = b div a + 1"
by (simp add: zdiv_zadd1_eq)

lemma zdiv_zadd_self2[simp]: "a ~= (0::int) ==> (b+a) div a = b div a + 1"
by (simp add: zdiv_zadd1_eq)

lemma zmod_zadd_self1[simp]: "(a+b) mod a = b mod (a::int)"
apply (case_tac "a = 0", simp add: DIVISION_BY_ZERO)
apply (simp add: zmod_zadd1_eq)
done

lemma zmod_zadd_self2[simp]: "(b+a) mod a = b mod (a::int)"
apply (case_tac "a = 0", simp add: DIVISION_BY_ZERO)
apply (simp add: zmod_zadd1_eq)
done


(*** proving  a div (b*c) = (a div b) div c ***)

(*The condition c>0 seems necessary.  Consider that 7 div ~6 = ~2 but
  7 div 2 div ~3 = 3 div ~3 = ~1.  The subcase (a div b) mod c = 0 seems
  to cause particular problems.*)

(** first, four lemmas to bound the remainder for the cases b<0 and b>0 **)

lemma lemma1: "[| (0::int) < c;  b < r;  r <= 0 |] ==> b*c < b*(q mod c) + r"
apply (subgoal_tac "b * (c - q mod c) < r * 1")
apply (simp add: zdiff_zmult_distrib2)
apply (rule order_le_less_trans)
apply (erule_tac [2] zmult_zless_mono1)
apply (rule zmult_zle_mono2_neg)
apply (auto simp add: zcompare_rls zadd_commute [of 1]
                      add1_zle_eq pos_mod_bound)
done

lemma lemma2: "[| (0::int) < c;   b < r;  r <= 0 |] ==> b * (q mod c) + r <= 0"
apply (subgoal_tac "b * (q mod c) <= 0")
 apply arith
apply (simp add: zmult_le_0_iff pos_mod_sign)
done

lemma lemma3: "[| (0::int) < c;  0 <= r;  r < b |] ==> 0 <= b * (q mod c) + r"
apply (subgoal_tac "0 <= b * (q mod c) ")
apply arith
apply (simp add: int_0_le_mult_iff pos_mod_sign)
done

lemma lemma4: "[| (0::int) < c; 0 <= r; r < b |] ==> b * (q mod c) + r < b * c"
apply (subgoal_tac "r * 1 < b * (c - q mod c) ")
apply (simp add: zdiff_zmult_distrib2)
apply (rule order_less_le_trans)
apply (erule zmult_zless_mono1)
apply (rule_tac [2] zmult_zle_mono2)
apply (auto simp add: zcompare_rls zadd_commute [of 1]
                      add1_zle_eq pos_mod_bound)
done

lemma zmult2_lemma: "[| quorem ((a,b), (q,r));  b ~= 0;  0 < c |]  
      ==> quorem ((a, b*c), (q div c, b*(q mod c) + r))"
by (auto simp add: zmult_ac zmod_zdiv_equality quorem_def linorder_neq_iff
                   int_0_less_mult_iff zadd_zmult_distrib2 [symmetric] 
                   lemma1 lemma2 lemma3 lemma4)

lemma zdiv_zmult2_eq: "(0::int) < c ==> a div (b*c) = (a div b) div c"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (force simp add: quorem_div_mod [THEN zmult2_lemma, THEN quorem_div])
done

lemma zmod_zmult2_eq:
     "(0::int) < c ==> a mod (b*c) = b*(a div b mod c) + a mod b"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (force simp add: quorem_div_mod [THEN zmult2_lemma, THEN quorem_mod])
done


(*** Cancellation of common factors in div ***)

lemma lemma1: "[| (0::int) < b;  c ~= 0 |] ==> (c*a) div (c*b) = a div b"
by (subst zdiv_zmult2_eq, auto)

lemma lemma2: "[| b < (0::int);  c ~= 0 |] ==> (c*a) div (c*b) = a div b"
apply (subgoal_tac " (c * (-a)) div (c * (-b)) = (-a) div (-b) ")
apply (rule_tac [2] lemma1, auto)
done

lemma zdiv_zmult_zmult1: "c ~= (0::int) ==> (c*a) div (c*b) = a div b"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (auto simp add: linorder_neq_iff lemma1 lemma2)
done

lemma zdiv_zmult_zmult2: "c ~= (0::int) ==> (a*c) div (b*c) = a div b"
apply (drule zdiv_zmult_zmult1)
apply (auto simp add: zmult_commute)
done



(*** Distribution of factors over mod ***)

lemma lemma1: "[| (0::int) < b;  c ~= 0 |] ==> (c*a) mod (c*b) = c * (a mod b)"
by (subst zmod_zmult2_eq, auto)

lemma lemma2: "[| b < (0::int);  c ~= 0 |] ==> (c*a) mod (c*b) = c * (a mod b)"
apply (subgoal_tac " (c * (-a)) mod (c * (-b)) = c * ((-a) mod (-b))")
apply (rule_tac [2] lemma1, auto)
done

lemma zmod_zmult_zmult1: "(c*a) mod (c*b) = (c::int) * (a mod b)"
apply (case_tac "b = 0", simp add: DIVISION_BY_ZERO)
apply (case_tac "c = 0", simp add: DIVISION_BY_ZERO)
apply (auto simp add: linorder_neq_iff lemma1 lemma2)
done

lemma zmod_zmult_zmult2: "(a*c) mod (b*c) = (a mod b) * (c::int)"
apply (cut_tac c = c in zmod_zmult_zmult1)
apply (auto simp add: zmult_commute)
done


(*** Speeding up the division algorithm with shifting ***)

(** computing div by shifting **)

lemma pos_zdiv_mult_2: "(0::int) <= a ==> (1 + 2*b) div (2*a) = b div a"
apply (case_tac "a = 0", simp add: DIVISION_BY_ZERO)
apply (subgoal_tac "1 <= a")
 prefer 2 apply arith
apply (subgoal_tac "1 < a * 2")
 prefer 2 apply arith
apply (subgoal_tac "2* (1 + b mod a) <= 2*a")
 apply (rule_tac [2] zmult_zle_mono2)
apply (auto simp add: zadd_commute [of 1] zmult_commute add1_zle_eq 
                      pos_mod_bound)
apply (subst zdiv_zadd1_eq)
apply (simp add: zdiv_zmult_zmult2 zmod_zmult_zmult2 div_pos_pos_trivial)
apply (subst div_pos_pos_trivial)
apply (auto simp add: mod_pos_pos_trivial)
apply (subgoal_tac "0 <= b mod a", arith)
apply (simp add: pos_mod_sign)
done


lemma neg_zdiv_mult_2: "a <= (0::int) ==> (1 + 2*b) div (2*a) = (b+1) div a"
apply (subgoal_tac " (1 + 2* (-b - 1)) div (2 * (-a)) = (-b - 1) div (-a) ")
apply (rule_tac [2] pos_zdiv_mult_2)
apply (auto simp add: zmult_zminus_right)
apply (subgoal_tac " (-1 - (2 * b)) = - (1 + (2 * b))")
apply (simp only: zdiv_zminus_zminus zdiff_def zminus_zadd_distrib [symmetric],
       simp) 
done


(*Not clear why this must be proved separately; probably number_of causes
  simplification problems*)
lemma not_0_le_lemma: "~ 0 <= x ==> x <= (0::int)"
by auto

lemma zdiv_number_of_BIT[simp]:
     "number_of (v BIT b) div number_of (w BIT False) =  
          (if ~b | (0::int) <= number_of w                    
           then number_of v div (number_of w)     
           else (number_of v + (1::int)) div (number_of w))"
apply (simp only: zadd_assoc number_of_BIT)
(*create subgoal because the next step can't simplify numerals*)
apply (subgoal_tac "2 ~= (0::int) ")
apply (simp del: bin_arith_extra_simps 
         add: zdiv_zmult_zmult1 pos_zdiv_mult_2 not_0_le_lemma neg_zdiv_mult_2)
apply simp
done


(** computing mod by shifting (proofs resemble those for div) **)

lemma pos_zmod_mult_2:
     "(0::int) <= a ==> (1 + 2*b) mod (2*a) = 1 + 2 * (b mod a)"
apply (case_tac "a = 0", simp add: DIVISION_BY_ZERO)
apply (subgoal_tac "1 <= a")
 prefer 2 apply arith
apply (subgoal_tac "1 < a * 2")
 prefer 2 apply arith
apply (subgoal_tac "2* (1 + b mod a) <= 2*a")
 apply (rule_tac [2] zmult_zle_mono2)
apply (auto simp add: zadd_commute [of 1] zmult_commute add1_zle_eq 
                      pos_mod_bound)
apply (subst zmod_zadd1_eq)
apply (simp add: zmod_zmult_zmult2 mod_pos_pos_trivial)
apply (rule mod_pos_pos_trivial)
apply (auto simp add: mod_pos_pos_trivial)
apply (subgoal_tac "0 <= b mod a", arith)
apply (simp add: pos_mod_sign)
done


lemma neg_zmod_mult_2:
     "a <= (0::int) ==> (1 + 2*b) mod (2*a) = 2 * ((b+1) mod a) - 1"
apply (subgoal_tac "(1 + 2* (-b - 1)) mod (2* (-a)) = 
                    1 + 2* ((-b - 1) mod (-a))")
apply (rule_tac [2] pos_zmod_mult_2)
apply (auto simp add: zmult_zminus_right)
apply (subgoal_tac " (-1 - (2 * b)) = - (1 + (2 * b))")
 prefer 2 apply simp 
apply (simp only: zmod_zminus_zminus zdiff_def zminus_zadd_distrib [symmetric])
done

lemma zmod_number_of_BIT [simp]:
     "number_of (v BIT b) mod number_of (w BIT False) =  
          (if b then  
                if (0::int) <= number_of w  
                then 2 * (number_of v mod number_of w) + 1     
                else 2 * ((number_of v + (1::int)) mod number_of w) - 1   
           else 2 * (number_of v mod number_of w))"
apply (simp only: zadd_assoc number_of_BIT)
apply (simp del: bin_arith_extra_simps bin_rel_simps 
         add: zmod_zmult_zmult1 pos_zmod_mult_2 not_0_le_lemma neg_zmod_mult_2)
apply simp
done



(** Quotients of signs **)

lemma div_neg_pos_less0: "[| a < (0::int);  0 < b |] ==> a div b < 0"
apply (subgoal_tac "a div b <= -1", force)
apply (rule order_trans)
apply (rule_tac a' = "-1" in zdiv_mono1)
apply (auto simp add: zdiv_minus1)
done

lemma div_nonneg_neg_le0: "[| (0::int) <= a;  b < 0 |] ==> a div b <= 0"
by (drule zdiv_mono1_neg, auto)

lemma pos_imp_zdiv_nonneg_iff: "(0::int) < b ==> (0 <= a div b) = (0 <= a)"
apply auto
apply (drule_tac [2] zdiv_mono1)
apply (auto simp add: linorder_neq_iff)
apply (simp (no_asm_use) add: linorder_not_less [symmetric])
apply (blast intro: div_neg_pos_less0)
done

lemma neg_imp_zdiv_nonneg_iff:
     "b < (0::int) ==> (0 <= a div b) = (a <= (0::int))"
apply (subst zdiv_zminus_zminus [symmetric])
apply (subst pos_imp_zdiv_nonneg_iff, auto)
done

(*But not (a div b <= 0 iff a<=0); consider a=1, b=2 when a div b = 0.*)
lemma pos_imp_zdiv_neg_iff: "(0::int) < b ==> (a div b < 0) = (a < 0)"
by (simp add: linorder_not_le [symmetric] pos_imp_zdiv_nonneg_iff)

(*Again the law fails for <=: consider a = -1, b = -2 when a div b = 0*)
lemma neg_imp_zdiv_neg_iff: "b < (0::int) ==> (a div b < 0) = (0 < a)"
by (simp add: linorder_not_le [symmetric] neg_imp_zdiv_nonneg_iff)

ML
{*
val quorem_def = thm "quorem_def";

val unique_quotient = thm "unique_quotient";
val unique_remainder = thm "unique_remainder";
val adjust_eq = thm "adjust_eq";
val posDivAlg_eqn = thm "posDivAlg_eqn";
val posDivAlg_correct = thm "posDivAlg_correct";
val negDivAlg_eqn = thm "negDivAlg_eqn";
val negDivAlg_correct = thm "negDivAlg_correct";
val quorem_0 = thm "quorem_0";
val posDivAlg_0 = thm "posDivAlg_0";
val negDivAlg_minus1 = thm "negDivAlg_minus1";
val negateSnd_eq = thm "negateSnd_eq";
val quorem_neg = thm "quorem_neg";
val divAlg_correct = thm "divAlg_correct";
val DIVISION_BY_ZERO = thm "DIVISION_BY_ZERO";
val zmod_zdiv_equality = thm "zmod_zdiv_equality";
val pos_mod_conj = thm "pos_mod_conj";
val pos_mod_sign = thm "pos_mod_sign";
val neg_mod_conj = thm "neg_mod_conj";
val neg_mod_sign = thm "neg_mod_sign";
val quorem_div_mod = thm "quorem_div_mod";
val quorem_div = thm "quorem_div";
val quorem_mod = thm "quorem_mod";
val div_pos_pos_trivial = thm "div_pos_pos_trivial";
val div_neg_neg_trivial = thm "div_neg_neg_trivial";
val div_pos_neg_trivial = thm "div_pos_neg_trivial";
val mod_pos_pos_trivial = thm "mod_pos_pos_trivial";
val mod_neg_neg_trivial = thm "mod_neg_neg_trivial";
val mod_pos_neg_trivial = thm "mod_pos_neg_trivial";
val zdiv_zminus_zminus = thm "zdiv_zminus_zminus";
val zmod_zminus_zminus = thm "zmod_zminus_zminus";
val zdiv_zminus1_eq_if = thm "zdiv_zminus1_eq_if";
val zmod_zminus1_eq_if = thm "zmod_zminus1_eq_if";
val zdiv_zminus2 = thm "zdiv_zminus2";
val zmod_zminus2 = thm "zmod_zminus2";
val zdiv_zminus2_eq_if = thm "zdiv_zminus2_eq_if";
val zmod_zminus2_eq_if = thm "zmod_zminus2_eq_if";
val self_quotient = thm "self_quotient";
val self_remainder = thm "self_remainder";
val zdiv_self = thm "zdiv_self";
val zmod_self = thm "zmod_self";
val zdiv_zero = thm "zdiv_zero";
val div_eq_minus1 = thm "div_eq_minus1";
val zmod_zero = thm "zmod_zero";
val zdiv_minus1 = thm "zdiv_minus1";
val zmod_minus1 = thm "zmod_minus1";
val div_pos_pos = thm "div_pos_pos";
val mod_pos_pos = thm "mod_pos_pos";
val div_neg_pos = thm "div_neg_pos";
val mod_neg_pos = thm "mod_neg_pos";
val div_pos_neg = thm "div_pos_neg";
val mod_pos_neg = thm "mod_pos_neg";
val div_neg_neg = thm "div_neg_neg";
val mod_neg_neg = thm "mod_neg_neg";
val zmod_1 = thm "zmod_1";
val zdiv_1 = thm "zdiv_1";
val zmod_minus1_right = thm "zmod_minus1_right";
val zdiv_minus1_right = thm "zdiv_minus1_right";
val zdiv_mono1 = thm "zdiv_mono1";
val zdiv_mono1_neg = thm "zdiv_mono1_neg";
val zdiv_mono2 = thm "zdiv_mono2";
val zdiv_mono2_neg = thm "zdiv_mono2_neg";
val zdiv_zmult1_eq = thm "zdiv_zmult1_eq";
val zmod_zmult1_eq = thm "zmod_zmult1_eq";
val zmod_zmult1_eq' = thm "zmod_zmult1_eq'";
val zmod_zmult_distrib = thm "zmod_zmult_distrib";
val zdiv_zmult_self1 = thm "zdiv_zmult_self1";
val zdiv_zmult_self2 = thm "zdiv_zmult_self2";
val zmod_zmult_self1 = thm "zmod_zmult_self1";
val zmod_zmult_self2 = thm "zmod_zmult_self2";
val zmod_eq_0_iff = thm "zmod_eq_0_iff";
val zdiv_zadd1_eq = thm "zdiv_zadd1_eq";
val zmod_zadd1_eq = thm "zmod_zadd1_eq";
val mod_div_trivial = thm "mod_div_trivial";
val mod_mod_trivial = thm "mod_mod_trivial";
val zmod_zadd_left_eq = thm "zmod_zadd_left_eq";
val zmod_zadd_right_eq = thm "zmod_zadd_right_eq";
val zdiv_zadd_self1 = thm "zdiv_zadd_self1";
val zdiv_zadd_self2 = thm "zdiv_zadd_self2";
val zmod_zadd_self1 = thm "zmod_zadd_self1";
val zmod_zadd_self2 = thm "zmod_zadd_self2";
val zdiv_zmult2_eq = thm "zdiv_zmult2_eq";
val zmod_zmult2_eq = thm "zmod_zmult2_eq";
val zdiv_zmult_zmult1 = thm "zdiv_zmult_zmult1";
val zdiv_zmult_zmult2 = thm "zdiv_zmult_zmult2";
val zmod_zmult_zmult1 = thm "zmod_zmult_zmult1";
val zmod_zmult_zmult2 = thm "zmod_zmult_zmult2";
val pos_zdiv_mult_2 = thm "pos_zdiv_mult_2";
val neg_zdiv_mult_2 = thm "neg_zdiv_mult_2";
val zdiv_number_of_BIT = thm "zdiv_number_of_BIT";
val pos_zmod_mult_2 = thm "pos_zmod_mult_2";
val neg_zmod_mult_2 = thm "neg_zmod_mult_2";
val zmod_number_of_BIT = thm "zmod_number_of_BIT";
val div_neg_pos_less0 = thm "div_neg_pos_less0";
val div_nonneg_neg_le0 = thm "div_nonneg_neg_le0";
val pos_imp_zdiv_nonneg_iff = thm "pos_imp_zdiv_nonneg_iff";
val neg_imp_zdiv_nonneg_iff = thm "neg_imp_zdiv_nonneg_iff";
val pos_imp_zdiv_neg_iff = thm "pos_imp_zdiv_neg_iff";
val neg_imp_zdiv_neg_iff = thm "neg_imp_zdiv_neg_iff";
*}

end
