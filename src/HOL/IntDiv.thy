(*  Title:      HOL/IntDiv.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

*)

header{* The Division Operators div and mod *}

theory IntDiv
imports Int Divides FunDef
begin

definition divmod_rel :: "int \<Rightarrow> int \<Rightarrow> int \<times> int \<Rightarrow> bool" where
    --{*definition of quotient and remainder*}
    [code]: "divmod_rel a b = (\<lambda>(q, r). a = b * q + r \<and>
               (if 0 < b then 0 \<le> r \<and> r < b else b < r \<and> r \<le> 0))"

definition adjust :: "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
    --{*for the division algorithm*}
    [code]: "adjust b = (\<lambda>(q, r). if 0 \<le> r - b then (2 * q + 1, r - b)
                         else (2 * q, r))"

text{*algorithm for the case @{text "a\<ge>0, b>0"}*}
function posDivAlg :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "posDivAlg a b = (if a < b \<or>  b \<le> 0 then (0, a)
     else adjust b (posDivAlg a (2 * b)))"
by auto
termination by (relation "measure (\<lambda>(a, b). nat (a - b + 1))") auto

text{*algorithm for the case @{text "a<0, b>0"}*}
function negDivAlg :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "negDivAlg a b = (if 0 \<le>a + b \<or> b \<le> 0  then (-1, a + b)
     else adjust b (negDivAlg a (2 * b)))"
by auto
termination by (relation "measure (\<lambda>(a, b). nat (- a - b))") auto

text{*algorithm for the general case @{term "b\<noteq>0"}*}
definition negateSnd :: "int \<times> int \<Rightarrow> int \<times> int" where
  [code_inline]: "negateSnd = apsnd uminus"

definition divmod :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
    --{*The full division algorithm considers all possible signs for a, b
       including the special case @{text "a=0, b<0"} because 
       @{term negDivAlg} requires @{term "a<0"}.*}
  "divmod a b = (if 0 \<le> a then if 0 \<le> b then posDivAlg a b
                  else if a = 0 then (0, 0)
                       else negateSnd (negDivAlg (-a) (-b))
               else 
                  if 0 < b then negDivAlg a b
                  else negateSnd (posDivAlg (-a) (-b)))"

instantiation int :: Divides.div
begin

definition
  div_def: "a div b = fst (divmod a b)"

definition
  mod_def: "a mod b = snd (divmod a b)"

instance ..

end

lemma divmod_mod_div:
  "divmod p q = (p div q, p mod q)"
  by (auto simp add: div_def mod_def)

text{*
Here is the division algorithm in ML:

\begin{verbatim}
    fun posDivAlg (a,b) =
      if a<b then (0,a)
      else let val (q,r) = posDivAlg(a, 2*b)
	       in  if 0\<le>r-b then (2*q+1, r-b) else (2*q, r)
	   end

    fun negDivAlg (a,b) =
      if 0\<le>a+b then (~1,a+b)
      else let val (q,r) = negDivAlg(a, 2*b)
	       in  if 0\<le>r-b then (2*q+1, r-b) else (2*q, r)
	   end;

    fun negateSnd (q,r:int) = (q,~r);

    fun divmod (a,b) = if 0\<le>a then 
			  if b>0 then posDivAlg (a,b) 
			   else if a=0 then (0,0)
				else negateSnd (negDivAlg (~a,~b))
		       else 
			  if 0<b then negDivAlg (a,b)
			  else        negateSnd (posDivAlg (~a,~b));
\end{verbatim}
*}



subsection{*Uniqueness and Monotonicity of Quotients and Remainders*}

lemma unique_quotient_lemma:
     "[| b*q' + r'  \<le> b*q + r;  0 \<le> r';  r' < b;  r < b |]  
      ==> q' \<le> (q::int)"
apply (subgoal_tac "r' + b * (q'-q) \<le> r")
 prefer 2 apply (simp add: right_diff_distrib)
apply (subgoal_tac "0 < b * (1 + q - q') ")
apply (erule_tac [2] order_le_less_trans)
 prefer 2 apply (simp add: right_diff_distrib right_distrib)
apply (subgoal_tac "b * q' < b * (1 + q) ")
 prefer 2 apply (simp add: right_diff_distrib right_distrib)
apply (simp add: mult_less_cancel_left)
done

lemma unique_quotient_lemma_neg:
     "[| b*q' + r' \<le> b*q + r;  r \<le> 0;  b < r;  b < r' |]  
      ==> q \<le> (q'::int)"
by (rule_tac b = "-b" and r = "-r'" and r' = "-r" in unique_quotient_lemma, 
    auto)

lemma unique_quotient:
     "[| divmod_rel a b (q, r); divmod_rel a b (q', r');  b \<noteq> 0 |]  
      ==> q = q'"
apply (simp add: divmod_rel_def linorder_neq_iff split: split_if_asm)
apply (blast intro: order_antisym
             dest: order_eq_refl [THEN unique_quotient_lemma] 
             order_eq_refl [THEN unique_quotient_lemma_neg] sym)+
done


lemma unique_remainder:
     "[| divmod_rel a b (q, r); divmod_rel a b (q', r');  b \<noteq> 0 |]  
      ==> r = r'"
apply (subgoal_tac "q = q'")
 apply (simp add: divmod_rel_def)
apply (blast intro: unique_quotient)
done


subsection{*Correctness of @{term posDivAlg}, the Algorithm for Non-Negative Dividends*}

text{*And positive divisors*}

lemma adjust_eq [simp]:
     "adjust b (q,r) = 
      (let diff = r-b in  
	if 0 \<le> diff then (2*q + 1, diff)   
                     else (2*q, r))"
by (simp add: Let_def adjust_def)

declare posDivAlg.simps [simp del]

text{*use with a simproc to avoid repeatedly proving the premise*}
lemma posDivAlg_eqn:
     "0 < b ==>  
      posDivAlg a b = (if a<b then (0,a) else adjust b (posDivAlg a (2*b)))"
by (rule posDivAlg.simps [THEN trans], simp)

text{*Correctness of @{term posDivAlg}: it computes quotients correctly*}
theorem posDivAlg_correct:
  assumes "0 \<le> a" and "0 < b"
  shows "divmod_rel a b (posDivAlg a b)"
using prems apply (induct a b rule: posDivAlg.induct)
apply auto
apply (simp add: divmod_rel_def)
apply (subst posDivAlg_eqn, simp add: right_distrib)
apply (case_tac "a < b")
apply simp_all
apply (erule splitE)
apply (auto simp add: right_distrib Let_def)
done


subsection{*Correctness of @{term negDivAlg}, the Algorithm for Negative Dividends*}

text{*And positive divisors*}

declare negDivAlg.simps [simp del]

text{*use with a simproc to avoid repeatedly proving the premise*}
lemma negDivAlg_eqn:
     "0 < b ==>  
      negDivAlg a b =       
       (if 0\<le>a+b then (-1,a+b) else adjust b (negDivAlg a (2*b)))"
by (rule negDivAlg.simps [THEN trans], simp)

(*Correctness of negDivAlg: it computes quotients correctly
  It doesn't work if a=0 because the 0/b equals 0, not -1*)
lemma negDivAlg_correct:
  assumes "a < 0" and "b > 0"
  shows "divmod_rel a b (negDivAlg a b)"
using prems apply (induct a b rule: negDivAlg.induct)
apply (auto simp add: linorder_not_le)
apply (simp add: divmod_rel_def)
apply (subst negDivAlg_eqn, assumption)
apply (case_tac "a + b < (0\<Colon>int)")
apply simp_all
apply (erule splitE)
apply (auto simp add: right_distrib Let_def)
done


subsection{*Existence Shown by Proving the Division Algorithm to be Correct*}

(*the case a=0*)
lemma divmod_rel_0: "b \<noteq> 0 ==> divmod_rel 0 b (0, 0)"
by (auto simp add: divmod_rel_def linorder_neq_iff)

lemma posDivAlg_0 [simp]: "posDivAlg 0 b = (0, 0)"
by (subst posDivAlg.simps, auto)

lemma negDivAlg_minus1 [simp]: "negDivAlg -1 b = (-1, b - 1)"
by (subst negDivAlg.simps, auto)

lemma negateSnd_eq [simp]: "negateSnd(q,r) = (q,-r)"
by (simp add: negateSnd_def)

lemma divmod_rel_neg: "divmod_rel (-a) (-b) qr ==> divmod_rel a b (negateSnd qr)"
by (auto simp add: split_ifs divmod_rel_def)

lemma divmod_correct: "b \<noteq> 0 ==> divmod_rel a b (divmod a b)"
by (force simp add: linorder_neq_iff divmod_rel_0 divmod_def divmod_rel_neg
                    posDivAlg_correct negDivAlg_correct)

text{*Arbitrary definitions for division by zero.  Useful to simplify 
    certain equations.*}

lemma DIVISION_BY_ZERO [simp]: "a div (0::int) = 0 & a mod (0::int) = a"
by (simp add: div_def mod_def divmod_def posDivAlg.simps)  


text{*Basic laws about division and remainder*}

lemma zmod_zdiv_equality: "(a::int) = b * (a div b) + (a mod b)"
apply (case_tac "b = 0", simp)
apply (cut_tac a = a and b = b in divmod_correct)
apply (auto simp add: divmod_rel_def div_def mod_def)
done

lemma zdiv_zmod_equality: "(b * (a div b) + (a mod b)) + k = (a::int)+k"
by(simp add: zmod_zdiv_equality[symmetric])

lemma zdiv_zmod_equality2: "((a div b) * b + (a mod b)) + k = (a::int)+k"
by(simp add: mult_commute zmod_zdiv_equality[symmetric])

text {* Tool setup *}

ML {*
local

structure CancelDivMod = CancelDivModFun(struct

  val div_name = @{const_name div};
  val mod_name = @{const_name mod};
  val mk_binop = HOLogic.mk_binop;
  val mk_sum = Numeral_Simprocs.mk_sum HOLogic.intT;
  val dest_sum = Numeral_Simprocs.dest_sum;

  val div_mod_eqs = map mk_meta_eq [@{thm zdiv_zmod_equality}, @{thm zdiv_zmod_equality2}];

  val trans = trans;

  val prove_eq_sums = Arith_Data.prove_conv2 all_tac (Arith_Data.simp_all_tac 
    (@{thm diff_minus} :: @{thms add_0s} @ @{thms add_ac}))

end)

in

val cancel_div_mod_int_proc = Simplifier.simproc @{theory}
  "cancel_zdiv_zmod" ["(k::int) + l"] (K CancelDivMod.proc);

val _ = Addsimprocs [cancel_div_mod_int_proc];

end
*}

lemma pos_mod_conj : "(0::int) < b ==> 0 \<le> a mod b & a mod b < b"
apply (cut_tac a = a and b = b in divmod_correct)
apply (auto simp add: divmod_rel_def mod_def)
done

lemmas pos_mod_sign  [simp] = pos_mod_conj [THEN conjunct1, standard]
   and pos_mod_bound [simp] = pos_mod_conj [THEN conjunct2, standard]

lemma neg_mod_conj : "b < (0::int) ==> a mod b \<le> 0 & b < a mod b"
apply (cut_tac a = a and b = b in divmod_correct)
apply (auto simp add: divmod_rel_def div_def mod_def)
done

lemmas neg_mod_sign  [simp] = neg_mod_conj [THEN conjunct1, standard]
   and neg_mod_bound [simp] = neg_mod_conj [THEN conjunct2, standard]



subsection{*General Properties of div and mod*}

lemma divmod_rel_div_mod: "b \<noteq> 0 ==> divmod_rel a b (a div b, a mod b)"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (force simp add: divmod_rel_def linorder_neq_iff)
done

lemma divmod_rel_div: "[| divmod_rel a b (q, r);  b \<noteq> 0 |] ==> a div b = q"
by (simp add: divmod_rel_div_mod [THEN unique_quotient])

lemma divmod_rel_mod: "[| divmod_rel a b (q, r);  b \<noteq> 0 |] ==> a mod b = r"
by (simp add: divmod_rel_div_mod [THEN unique_remainder])

lemma div_pos_pos_trivial: "[| (0::int) \<le> a;  a < b |] ==> a div b = 0"
apply (rule divmod_rel_div)
apply (auto simp add: divmod_rel_def)
done

lemma div_neg_neg_trivial: "[| a \<le> (0::int);  b < a |] ==> a div b = 0"
apply (rule divmod_rel_div)
apply (auto simp add: divmod_rel_def)
done

lemma div_pos_neg_trivial: "[| (0::int) < a;  a+b \<le> 0 |] ==> a div b = -1"
apply (rule divmod_rel_div)
apply (auto simp add: divmod_rel_def)
done

(*There is no div_neg_pos_trivial because  0 div b = 0 would supersede it*)

lemma mod_pos_pos_trivial: "[| (0::int) \<le> a;  a < b |] ==> a mod b = a"
apply (rule_tac q = 0 in divmod_rel_mod)
apply (auto simp add: divmod_rel_def)
done

lemma mod_neg_neg_trivial: "[| a \<le> (0::int);  b < a |] ==> a mod b = a"
apply (rule_tac q = 0 in divmod_rel_mod)
apply (auto simp add: divmod_rel_def)
done

lemma mod_pos_neg_trivial: "[| (0::int) < a;  a+b \<le> 0 |] ==> a mod b = a+b"
apply (rule_tac q = "-1" in divmod_rel_mod)
apply (auto simp add: divmod_rel_def)
done

text{*There is no @{text mod_neg_pos_trivial}.*}


(*Simpler laws such as -a div b = -(a div b) FAIL, but see just below*)
lemma zdiv_zminus_zminus [simp]: "(-a) div (-b) = a div (b::int)"
apply (case_tac "b = 0", simp)
apply (simp add: divmod_rel_div_mod [THEN divmod_rel_neg, simplified, 
                                 THEN divmod_rel_div, THEN sym])

done

(*Simpler laws such as -a mod b = -(a mod b) FAIL, but see just below*)
lemma zmod_zminus_zminus [simp]: "(-a) mod (-b) = - (a mod (b::int))"
apply (case_tac "b = 0", simp)
apply (subst divmod_rel_div_mod [THEN divmod_rel_neg, simplified, THEN divmod_rel_mod],
       auto)
done


subsection{*Laws for div and mod with Unary Minus*}

lemma zminus1_lemma:
     "divmod_rel a b (q, r)
      ==> divmod_rel (-a) b (if r=0 then -q else -q - 1,  
                          if r=0 then 0 else b-r)"
by (force simp add: split_ifs divmod_rel_def linorder_neq_iff right_diff_distrib)


lemma zdiv_zminus1_eq_if:
     "b \<noteq> (0::int)  
      ==> (-a) div b =  
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (blast intro: divmod_rel_div_mod [THEN zminus1_lemma, THEN divmod_rel_div])

lemma zmod_zminus1_eq_if:
     "(-a::int) mod b = (if a mod b = 0 then 0 else  b - (a mod b))"
apply (case_tac "b = 0", simp)
apply (blast intro: divmod_rel_div_mod [THEN zminus1_lemma, THEN divmod_rel_mod])
done

lemma zmod_zminus1_not_zero:
  fixes k l :: int
  shows "- k mod l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  unfolding zmod_zminus1_eq_if by auto

lemma zdiv_zminus2: "a div (-b) = (-a::int) div b"
by (cut_tac a = "-a" in zdiv_zminus_zminus, auto)

lemma zmod_zminus2: "a mod (-b) = - ((-a::int) mod b)"
by (cut_tac a = "-a" and b = b in zmod_zminus_zminus, auto)

lemma zdiv_zminus2_eq_if:
     "b \<noteq> (0::int)  
      ==> a div (-b) =  
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (simp add: zdiv_zminus1_eq_if zdiv_zminus2)

lemma zmod_zminus2_eq_if:
     "a mod (-b::int) = (if a mod b = 0 then 0 else  (a mod b) - b)"
by (simp add: zmod_zminus1_eq_if zmod_zminus2)

lemma zmod_zminus2_not_zero:
  fixes k l :: int
  shows "k mod - l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  unfolding zmod_zminus2_eq_if by auto 


subsection{*Division of a Number by Itself*}

lemma self_quotient_aux1: "[| (0::int) < a; a = r + a*q; r < a |] ==> 1 \<le> q"
apply (subgoal_tac "0 < a*q")
 apply (simp add: zero_less_mult_iff, arith)
done

lemma self_quotient_aux2: "[| (0::int) < a; a = r + a*q; 0 \<le> r |] ==> q \<le> 1"
apply (subgoal_tac "0 \<le> a* (1-q) ")
 apply (simp add: zero_le_mult_iff)
apply (simp add: right_diff_distrib)
done

lemma self_quotient: "[| divmod_rel a a (q, r);  a \<noteq> (0::int) |] ==> q = 1"
apply (simp add: split_ifs divmod_rel_def linorder_neq_iff)
apply (rule order_antisym, safe, simp_all)
apply (rule_tac [3] a = "-a" and r = "-r" in self_quotient_aux1)
apply (rule_tac a = "-a" and r = "-r" in self_quotient_aux2)
apply (force intro: self_quotient_aux1 self_quotient_aux2 simp add: add_commute)+
done

lemma self_remainder: "[| divmod_rel a a (q, r);  a \<noteq> (0::int) |] ==> r = 0"
apply (frule self_quotient, assumption)
apply (simp add: divmod_rel_def)
done

lemma zdiv_self [simp]: "a \<noteq> 0 ==> a div a = (1::int)"
by (simp add: divmod_rel_div_mod [THEN self_quotient])

(*Here we have 0 mod 0 = 0, also assumed by Knuth (who puts m mod 0 = 0) *)
lemma zmod_self [simp]: "a mod a = (0::int)"
apply (case_tac "a = 0", simp)
apply (simp add: divmod_rel_div_mod [THEN self_remainder])
done


subsection{*Computation of Division and Remainder*}

lemma zdiv_zero [simp]: "(0::int) div b = 0"
by (simp add: div_def divmod_def)

lemma div_eq_minus1: "(0::int) < b ==> -1 div b = -1"
by (simp add: div_def divmod_def)

lemma zmod_zero [simp]: "(0::int) mod b = 0"
by (simp add: mod_def divmod_def)

lemma zmod_minus1: "(0::int) < b ==> -1 mod b = b - 1"
by (simp add: mod_def divmod_def)

text{*a positive, b positive *}

lemma div_pos_pos: "[| 0 < a;  0 \<le> b |] ==> a div b = fst (posDivAlg a b)"
by (simp add: div_def divmod_def)

lemma mod_pos_pos: "[| 0 < a;  0 \<le> b |] ==> a mod b = snd (posDivAlg a b)"
by (simp add: mod_def divmod_def)

text{*a negative, b positive *}

lemma div_neg_pos: "[| a < 0;  0 < b |] ==> a div b = fst (negDivAlg a b)"
by (simp add: div_def divmod_def)

lemma mod_neg_pos: "[| a < 0;  0 < b |] ==> a mod b = snd (negDivAlg a b)"
by (simp add: mod_def divmod_def)

text{*a positive, b negative *}

lemma div_pos_neg:
     "[| 0 < a;  b < 0 |] ==> a div b = fst (negateSnd (negDivAlg (-a) (-b)))"
by (simp add: div_def divmod_def)

lemma mod_pos_neg:
     "[| 0 < a;  b < 0 |] ==> a mod b = snd (negateSnd (negDivAlg (-a) (-b)))"
by (simp add: mod_def divmod_def)

text{*a negative, b negative *}

lemma div_neg_neg:
     "[| a < 0;  b \<le> 0 |] ==> a div b = fst (negateSnd (posDivAlg (-a) (-b)))"
by (simp add: div_def divmod_def)

lemma mod_neg_neg:
     "[| a < 0;  b \<le> 0 |] ==> a mod b = snd (negateSnd (posDivAlg (-a) (-b)))"
by (simp add: mod_def divmod_def)

text {*Simplify expresions in which div and mod combine numerical constants*}

lemma divmod_relI:
  "\<lbrakk>a == b * q + r; if 0 < b then 0 \<le> r \<and> r < b else b < r \<and> r \<le> 0\<rbrakk>
    \<Longrightarrow> divmod_rel a b (q, r)"
  unfolding divmod_rel_def by simp

lemmas divmod_rel_div_eq = divmod_relI [THEN divmod_rel_div, THEN eq_reflection]
lemmas divmod_rel_mod_eq = divmod_relI [THEN divmod_rel_mod, THEN eq_reflection]
lemmas arithmetic_simps =
  arith_simps
  add_special
  OrderedGroup.add_0_left
  OrderedGroup.add_0_right
  mult_zero_left
  mult_zero_right
  mult_1_left
  mult_1_right

(* simprocs adapted from HOL/ex/Binary.thy *)
ML {*
local
  val mk_number = HOLogic.mk_number HOLogic.intT;
  fun mk_cert u k l = @{term "plus :: int \<Rightarrow> int \<Rightarrow> int"} $
    (@{term "times :: int \<Rightarrow> int \<Rightarrow> int"} $ u $ mk_number k) $
      mk_number l;
  fun prove ctxt prop = Goal.prove ctxt [] [] prop
    (K (ALLGOALS (full_simp_tac (HOL_basic_ss addsimps @{thms arithmetic_simps}))));
  fun binary_proc proc ss ct =
    (case Thm.term_of ct of
      _ $ t $ u =>
      (case try (pairself (`(snd o HOLogic.dest_number))) (t, u) of
        SOME args => proc (Simplifier.the_context ss) args
      | NONE => NONE)
    | _ => NONE);
in
  fun divmod_proc rule = binary_proc (fn ctxt => fn ((m, t), (n, u)) =>
    if n = 0 then NONE
    else let val (k, l) = Integer.div_mod m n;
    in SOME (rule OF [prove ctxt (Logic.mk_equals (t, mk_cert u k l))]) end);
end
*}

simproc_setup binary_int_div ("number_of m div number_of n :: int") =
  {* K (divmod_proc (@{thm divmod_rel_div_eq})) *}

simproc_setup binary_int_mod ("number_of m mod number_of n :: int") =
  {* K (divmod_proc (@{thm divmod_rel_mod_eq})) *}

lemmas posDivAlg_eqn_number_of [simp] =
    posDivAlg_eqn [of "number_of v" "number_of w", standard]

lemmas negDivAlg_eqn_number_of [simp] =
    negDivAlg_eqn [of "number_of v" "number_of w", standard]


text{*Special-case simplification *}

lemma zmod_minus1_right [simp]: "a mod (-1::int) = 0"
apply (cut_tac a = a and b = "-1" in neg_mod_sign)
apply (cut_tac [2] a = a and b = "-1" in neg_mod_bound)
apply (auto simp del: neg_mod_sign neg_mod_bound)
done

lemma zdiv_minus1_right [simp]: "a div (-1::int) = -a"
by (cut_tac a = a and b = "-1" in zmod_zdiv_equality, auto)

(** The last remaining special cases for constant arithmetic:
    1 div z and 1 mod z **)

lemmas div_pos_pos_1_number_of [simp] =
    div_pos_pos [OF int_0_less_1, of "number_of w", standard]

lemmas div_pos_neg_1_number_of [simp] =
    div_pos_neg [OF int_0_less_1, of "number_of w", standard]

lemmas mod_pos_pos_1_number_of [simp] =
    mod_pos_pos [OF int_0_less_1, of "number_of w", standard]

lemmas mod_pos_neg_1_number_of [simp] =
    mod_pos_neg [OF int_0_less_1, of "number_of w", standard]


lemmas posDivAlg_eqn_1_number_of [simp] =
    posDivAlg_eqn [of concl: 1 "number_of w", standard]

lemmas negDivAlg_eqn_1_number_of [simp] =
    negDivAlg_eqn [of concl: 1 "number_of w", standard]



subsection{*Monotonicity in the First Argument (Dividend)*}

lemma zdiv_mono1: "[| a \<le> a';  0 < (b::int) |] ==> a div b \<le> a' div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a' and b = b in zmod_zdiv_equality)
apply (rule unique_quotient_lemma)
apply (erule subst)
apply (erule subst, simp_all)
done

lemma zdiv_mono1_neg: "[| a \<le> a';  (b::int) < 0 |] ==> a' div b \<le> a div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a' and b = b in zmod_zdiv_equality)
apply (rule unique_quotient_lemma_neg)
apply (erule subst)
apply (erule subst, simp_all)
done


subsection{*Monotonicity in the Second Argument (Divisor)*}

lemma q_pos_lemma:
     "[| 0 \<le> b'*q' + r'; r' < b';  0 < b' |] ==> 0 \<le> (q'::int)"
apply (subgoal_tac "0 < b'* (q' + 1) ")
 apply (simp add: zero_less_mult_iff)
apply (simp add: right_distrib)
done

lemma zdiv_mono2_lemma:
     "[| b*q + r = b'*q' + r';  0 \<le> b'*q' + r';   
         r' < b';  0 \<le> r;  0 < b';  b' \<le> b |]   
      ==> q \<le> (q'::int)"
apply (frule q_pos_lemma, assumption+) 
apply (subgoal_tac "b*q < b* (q' + 1) ")
 apply (simp add: mult_less_cancel_left)
apply (subgoal_tac "b*q = r' - r + b'*q'")
 prefer 2 apply simp
apply (simp (no_asm_simp) add: right_distrib)
apply (subst add_commute, rule zadd_zless_mono, arith)
apply (rule mult_right_mono, auto)
done

lemma zdiv_mono2:
     "[| (0::int) \<le> a;  0 < b';  b' \<le> b |] ==> a div b \<le> a div b'"
apply (subgoal_tac "b \<noteq> 0")
 prefer 2 apply arith
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a and b = b' in zmod_zdiv_equality)
apply (rule zdiv_mono2_lemma)
apply (erule subst)
apply (erule subst, simp_all)
done

lemma q_neg_lemma:
     "[| b'*q' + r' < 0;  0 \<le> r';  0 < b' |] ==> q' \<le> (0::int)"
apply (subgoal_tac "b'*q' < 0")
 apply (simp add: mult_less_0_iff, arith)
done

lemma zdiv_mono2_neg_lemma:
     "[| b*q + r = b'*q' + r';  b'*q' + r' < 0;   
         r < b;  0 \<le> r';  0 < b';  b' \<le> b |]   
      ==> q' \<le> (q::int)"
apply (frule q_neg_lemma, assumption+) 
apply (subgoal_tac "b*q' < b* (q + 1) ")
 apply (simp add: mult_less_cancel_left)
apply (simp add: right_distrib)
apply (subgoal_tac "b*q' \<le> b'*q'")
 prefer 2 apply (simp add: mult_right_mono_neg, arith)
done

lemma zdiv_mono2_neg:
     "[| a < (0::int);  0 < b';  b' \<le> b |] ==> a div b' \<le> a div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a and b = b' in zmod_zdiv_equality)
apply (rule zdiv_mono2_neg_lemma)
apply (erule subst)
apply (erule subst, simp_all)
done


subsection{*More Algebraic Laws for div and mod*}

text{*proving (a*b) div c = a * (b div c) + a * (b mod c) *}

lemma zmult1_lemma:
     "[| divmod_rel b c (q, r);  c \<noteq> 0 |]  
      ==> divmod_rel (a * b) c (a*q + a*r div c, a*r mod c)"
by (force simp add: split_ifs divmod_rel_def linorder_neq_iff right_distrib)

lemma zdiv_zmult1_eq: "(a*b) div c = a*(b div c) + a*(b mod c) div (c::int)"
apply (case_tac "c = 0", simp)
apply (blast intro: divmod_rel_div_mod [THEN zmult1_lemma, THEN divmod_rel_div])
done

lemma zmod_zmult1_eq: "(a*b) mod c = a*(b mod c) mod (c::int)"
apply (case_tac "c = 0", simp)
apply (blast intro: divmod_rel_div_mod [THEN zmult1_lemma, THEN divmod_rel_mod])
done

lemma zmod_zdiv_trivial: "(a mod b) div b = (0::int)"
apply (case_tac "b = 0", simp)
apply (auto simp add: linorder_neq_iff div_pos_pos_trivial div_neg_neg_trivial)
done

text{*proving (a+b) div c = a div c + b div c + ((a mod c + b mod c) div c) *}

lemma zadd1_lemma:
     "[| divmod_rel a c (aq, ar);  divmod_rel b c (bq, br);  c \<noteq> 0 |]  
      ==> divmod_rel (a+b) c (aq + bq + (ar+br) div c, (ar+br) mod c)"
by (force simp add: split_ifs divmod_rel_def linorder_neq_iff right_distrib)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma zdiv_zadd1_eq:
     "(a+b) div (c::int) = a div c + b div c + ((a mod c + b mod c) div c)"
apply (case_tac "c = 0", simp)
apply (blast intro: zadd1_lemma [OF divmod_rel_div_mod divmod_rel_div_mod] divmod_rel_div)
done

instance int :: ring_div
proof
  fix a b c :: int
  assume not0: "b \<noteq> 0"
  show "(a + c * b) div b = c + a div b"
    unfolding zdiv_zadd1_eq [of a "c * b"] using not0 
      by (simp add: zmod_zmult1_eq zmod_zdiv_trivial zdiv_zmult1_eq)
next
  fix a b c :: int
  assume "a \<noteq> 0"
  then show "(a * b) div (a * c) = b div c"
  proof (cases "b \<noteq> 0 \<and> c \<noteq> 0")
    case False then show ?thesis by auto
  next
    case True then have "b \<noteq> 0" and "c \<noteq> 0" by auto
    with `a \<noteq> 0`
    have "\<And>q r. divmod_rel b c (q, r) \<Longrightarrow> divmod_rel (a * b) (a * c) (q, a * r)"
      apply (auto simp add: divmod_rel_def) 
      apply (auto simp add: algebra_simps)
      apply (auto simp add: zero_less_mult_iff zero_le_mult_iff mult_le_0_iff)
      done
    moreover with `c \<noteq> 0` divmod_rel_div_mod have "divmod_rel b c (b div c, b mod c)" by auto
    ultimately have "divmod_rel (a * b) (a * c) (b div c, a * (b mod c))" .
    moreover from  `a \<noteq> 0` `c \<noteq> 0` have "a * c \<noteq> 0" by simp
    ultimately show ?thesis by (rule divmod_rel_div)
  qed
qed auto

lemma posDivAlg_div_mod:
  assumes "k \<ge> 0"
  and "l \<ge> 0"
  shows "posDivAlg k l = (k div l, k mod l)"
proof (cases "l = 0")
  case True then show ?thesis by (simp add: posDivAlg.simps)
next
  case False with assms posDivAlg_correct
    have "divmod_rel k l (fst (posDivAlg k l), snd (posDivAlg k l))"
    by simp
  from divmod_rel_div [OF this `l \<noteq> 0`] divmod_rel_mod [OF this `l \<noteq> 0`]
  show ?thesis by simp
qed

lemma negDivAlg_div_mod:
  assumes "k < 0"
  and "l > 0"
  shows "negDivAlg k l = (k div l, k mod l)"
proof -
  from assms have "l \<noteq> 0" by simp
  from assms negDivAlg_correct
    have "divmod_rel k l (fst (negDivAlg k l), snd (negDivAlg k l))"
    by simp
  from divmod_rel_div [OF this `l \<noteq> 0`] divmod_rel_mod [OF this `l \<noteq> 0`]
  show ?thesis by simp
qed

lemma zmod_eq_0_iff: "(m mod d = 0) = (EX q::int. m = d*q)"
by (simp add: dvd_eq_mod_eq_0 [symmetric] dvd_def)

(* REVISIT: should this be generalized to all semiring_div types? *)
lemmas zmod_eq_0D [dest!] = zmod_eq_0_iff [THEN iffD1]


subsection{*Proving  @{term "a div (b*c) = (a div b) div c"} *}

(*The condition c>0 seems necessary.  Consider that 7 div ~6 = ~2 but
  7 div 2 div ~3 = 3 div ~3 = ~1.  The subcase (a div b) mod c = 0 seems
  to cause particular problems.*)

text{*first, four lemmas to bound the remainder for the cases b<0 and b>0 *}

lemma zmult2_lemma_aux1: "[| (0::int) < c;  b < r;  r \<le> 0 |] ==> b*c < b*(q mod c) + r"
apply (subgoal_tac "b * (c - q mod c) < r * 1")
 apply (simp add: algebra_simps)
apply (rule order_le_less_trans)
 apply (erule_tac [2] mult_strict_right_mono)
 apply (rule mult_left_mono_neg)
  using add1_zle_eq[of "q mod c"]apply(simp add: algebra_simps pos_mod_bound)
 apply (simp)
apply (simp)
done

lemma zmult2_lemma_aux2:
     "[| (0::int) < c;   b < r;  r \<le> 0 |] ==> b * (q mod c) + r \<le> 0"
apply (subgoal_tac "b * (q mod c) \<le> 0")
 apply arith
apply (simp add: mult_le_0_iff)
done

lemma zmult2_lemma_aux3: "[| (0::int) < c;  0 \<le> r;  r < b |] ==> 0 \<le> b * (q mod c) + r"
apply (subgoal_tac "0 \<le> b * (q mod c) ")
apply arith
apply (simp add: zero_le_mult_iff)
done

lemma zmult2_lemma_aux4: "[| (0::int) < c; 0 \<le> r; r < b |] ==> b * (q mod c) + r < b * c"
apply (subgoal_tac "r * 1 < b * (c - q mod c) ")
 apply (simp add: right_diff_distrib)
apply (rule order_less_le_trans)
 apply (erule mult_strict_right_mono)
 apply (rule_tac [2] mult_left_mono)
  apply simp
 using add1_zle_eq[of "q mod c"] apply (simp add: algebra_simps pos_mod_bound)
apply simp
done

lemma zmult2_lemma: "[| divmod_rel a b (q, r);  b \<noteq> 0;  0 < c |]  
      ==> divmod_rel a (b * c) (q div c, b*(q mod c) + r)"
by (auto simp add: mult_ac divmod_rel_def linorder_neq_iff
                   zero_less_mult_iff right_distrib [symmetric] 
                   zmult2_lemma_aux1 zmult2_lemma_aux2 zmult2_lemma_aux3 zmult2_lemma_aux4)

lemma zdiv_zmult2_eq: "(0::int) < c ==> a div (b*c) = (a div b) div c"
apply (case_tac "b = 0", simp)
apply (force simp add: divmod_rel_div_mod [THEN zmult2_lemma, THEN divmod_rel_div])
done

lemma zmod_zmult2_eq:
     "(0::int) < c ==> a mod (b*c) = b*(a div b mod c) + a mod b"
apply (case_tac "b = 0", simp)
apply (force simp add: divmod_rel_div_mod [THEN zmult2_lemma, THEN divmod_rel_mod])
done


subsection {*Splitting Rules for div and mod*}

text{*The proofs of the two lemmas below are essentially identical*}

lemma split_pos_lemma:
 "0<k ==> 
    P(n div k :: int)(n mod k) = (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P i j)"
apply (rule iffI, clarify)
 apply (erule_tac P="P ?x ?y" in rev_mp)  
 apply (subst mod_add_eq) 
 apply (subst zdiv_zadd1_eq) 
 apply (simp add: div_pos_pos_trivial mod_pos_pos_trivial)  
txt{*converse direction*}
apply (drule_tac x = "n div k" in spec) 
apply (drule_tac x = "n mod k" in spec, simp)
done

lemma split_neg_lemma:
 "k<0 ==>
    P(n div k :: int)(n mod k) = (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P i j)"
apply (rule iffI, clarify)
 apply (erule_tac P="P ?x ?y" in rev_mp)  
 apply (subst mod_add_eq) 
 apply (subst zdiv_zadd1_eq) 
 apply (simp add: div_neg_neg_trivial mod_neg_neg_trivial)  
txt{*converse direction*}
apply (drule_tac x = "n div k" in spec) 
apply (drule_tac x = "n mod k" in spec, simp)
done

lemma split_zdiv:
 "P(n div k :: int) =
  ((k = 0 --> P 0) & 
   (0<k --> (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P i)) & 
   (k<0 --> (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P i)))"
apply (case_tac "k=0", simp)
apply (simp only: linorder_neq_iff)
apply (erule disjE) 
 apply (simp_all add: split_pos_lemma [of concl: "%x y. P x"] 
                      split_neg_lemma [of concl: "%x y. P x"])
done

lemma split_zmod:
 "P(n mod k :: int) =
  ((k = 0 --> P n) & 
   (0<k --> (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P j)) & 
   (k<0 --> (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P j)))"
apply (case_tac "k=0", simp)
apply (simp only: linorder_neq_iff)
apply (erule disjE) 
 apply (simp_all add: split_pos_lemma [of concl: "%x y. P y"] 
                      split_neg_lemma [of concl: "%x y. P y"])
done

(* Enable arith to deal with div 2 and mod 2: *)
declare split_zdiv [of _ _ "number_of k", simplified, standard, arith_split]
declare split_zmod [of _ _ "number_of k", simplified, standard, arith_split]


subsection{*Speeding up the Division Algorithm with Shifting*}

text{*computing div by shifting *}

lemma pos_zdiv_mult_2: "(0::int) \<le> a ==> (1 + 2*b) div (2*a) = b div a"
proof cases
  assume "a=0"
    thus ?thesis by simp
next
  assume "a\<noteq>0" and le_a: "0\<le>a"   
  hence a_pos: "1 \<le> a" by arith
  hence one_less_a2: "1 < 2 * a" by arith
  hence le_2a: "2 * (1 + b mod a) \<le> 2 * a"
    unfolding mult_le_cancel_left
    by (simp add: add1_zle_eq add_commute [of 1])
  with a_pos have "0 \<le> b mod a" by simp
  hence le_addm: "0 \<le> 1 mod (2*a) + 2*(b mod a)"
    by (simp add: mod_pos_pos_trivial one_less_a2)
  with  le_2a
  have "(1 mod (2*a) + 2*(b mod a)) div (2*a) = 0"
    by (simp add: div_pos_pos_trivial le_addm mod_pos_pos_trivial one_less_a2
                  right_distrib) 
  thus ?thesis
    by (subst zdiv_zadd1_eq,
        simp add: mod_mult_mult1 one_less_a2
                  div_pos_pos_trivial)
qed

lemma neg_zdiv_mult_2: "a \<le> (0::int) ==> (1 + 2*b) div (2*a) = (b+1) div a"
apply (subgoal_tac " (1 + 2* (-b - 1)) div (2 * (-a)) = (-b - 1) div (-a) ")
apply (rule_tac [2] pos_zdiv_mult_2)
apply (auto simp add: minus_mult_right [symmetric] right_diff_distrib)
apply (subgoal_tac " (-1 - (2 * b)) = - (1 + (2 * b))")
apply (simp only: zdiv_zminus_zminus diff_minus minus_add_distrib [symmetric],
       simp) 
done

lemma zdiv_number_of_Bit0 [simp]:
     "number_of (Int.Bit0 v) div number_of (Int.Bit0 w) =  
          number_of v div (number_of w :: int)"
by (simp only: number_of_eq numeral_simps) simp

lemma zdiv_number_of_Bit1 [simp]:
     "number_of (Int.Bit1 v) div number_of (Int.Bit0 w) =  
          (if (0::int) \<le> number_of w                    
           then number_of v div (number_of w)     
           else (number_of v + (1::int)) div (number_of w))"
apply (simp only: number_of_eq numeral_simps UNIV_I split: split_if) 
apply (simp add: pos_zdiv_mult_2 neg_zdiv_mult_2 add_ac)
done


subsection{*Computing mod by Shifting (proofs resemble those for div)*}

lemma pos_zmod_mult_2:
     "(0::int) \<le> a ==> (1 + 2*b) mod (2*a) = 1 + 2 * (b mod a)"
apply (case_tac "a = 0", simp)
apply (subgoal_tac "1 < a * 2")
 prefer 2 apply arith
apply (subgoal_tac "2* (1 + b mod a) \<le> 2*a")
 apply (rule_tac [2] mult_left_mono)
apply (auto simp add: add_commute [of 1] mult_commute add1_zle_eq 
                      pos_mod_bound)
apply (subst mod_add_eq)
apply (simp add: mod_mult_mult2 mod_pos_pos_trivial)
apply (rule mod_pos_pos_trivial)
apply (auto simp add: mod_pos_pos_trivial ring_distribs)
apply (subgoal_tac "0 \<le> b mod a", arith, simp)
done

lemma neg_zmod_mult_2:
     "a \<le> (0::int) ==> (1 + 2*b) mod (2*a) = 2 * ((b+1) mod a) - 1"
apply (subgoal_tac "(1 + 2* (-b - 1)) mod (2* (-a)) = 
                    1 + 2* ((-b - 1) mod (-a))")
apply (rule_tac [2] pos_zmod_mult_2)
apply (auto simp add: right_diff_distrib)
apply (subgoal_tac " (-1 - (2 * b)) = - (1 + (2 * b))")
 prefer 2 apply simp 
apply (simp only: zmod_zminus_zminus diff_minus minus_add_distrib [symmetric])
done

lemma zmod_number_of_Bit0 [simp]:
     "number_of (Int.Bit0 v) mod number_of (Int.Bit0 w) =  
      (2::int) * (number_of v mod number_of w)"
apply (simp only: number_of_eq numeral_simps) 
apply (simp add: mod_mult_mult1 pos_zmod_mult_2 
                 neg_zmod_mult_2 add_ac)
done

lemma zmod_number_of_Bit1 [simp]:
     "number_of (Int.Bit1 v) mod number_of (Int.Bit0 w) =  
      (if (0::int) \<le> number_of w  
                then 2 * (number_of v mod number_of w) + 1     
                else 2 * ((number_of v + (1::int)) mod number_of w) - 1)"
apply (simp only: number_of_eq numeral_simps) 
apply (simp add: mod_mult_mult1 pos_zmod_mult_2 
                 neg_zmod_mult_2 add_ac)
done


subsection{*Quotients of Signs*}

lemma div_neg_pos_less0: "[| a < (0::int);  0 < b |] ==> a div b < 0"
apply (subgoal_tac "a div b \<le> -1", force)
apply (rule order_trans)
apply (rule_tac a' = "-1" in zdiv_mono1)
apply (auto simp add: div_eq_minus1)
done

lemma div_nonneg_neg_le0: "[| (0::int) \<le> a; b < 0 |] ==> a div b \<le> 0"
by (drule zdiv_mono1_neg, auto)

lemma div_nonpos_pos_le0: "[| (a::int) \<le> 0; b > 0 |] ==> a div b \<le> 0"
by (drule zdiv_mono1, auto)

lemma pos_imp_zdiv_nonneg_iff: "(0::int) < b ==> (0 \<le> a div b) = (0 \<le> a)"
apply auto
apply (drule_tac [2] zdiv_mono1)
apply (auto simp add: linorder_neq_iff)
apply (simp (no_asm_use) add: linorder_not_less [symmetric])
apply (blast intro: div_neg_pos_less0)
done

lemma neg_imp_zdiv_nonneg_iff:
     "b < (0::int) ==> (0 \<le> a div b) = (a \<le> (0::int))"
apply (subst zdiv_zminus_zminus [symmetric])
apply (subst pos_imp_zdiv_nonneg_iff, auto)
done

(*But not (a div b \<le> 0 iff a\<le>0); consider a=1, b=2 when a div b = 0.*)
lemma pos_imp_zdiv_neg_iff: "(0::int) < b ==> (a div b < 0) = (a < 0)"
by (simp add: linorder_not_le [symmetric] pos_imp_zdiv_nonneg_iff)

(*Again the law fails for \<le>: consider a = -1, b = -2 when a div b = 0*)
lemma neg_imp_zdiv_neg_iff: "b < (0::int) ==> (a div b < 0) = (0 < a)"
by (simp add: linorder_not_le [symmetric] neg_imp_zdiv_nonneg_iff)


subsection {* The Divides Relation *}

lemmas zdvd_iff_zmod_eq_0_number_of [simp] =
  dvd_eq_mod_eq_0 [of "number_of x::int" "number_of y::int", standard]

lemma zdvd_anti_sym:
    "0 < m ==> 0 < n ==> m dvd n ==> n dvd m ==> m = (n::int)"
  apply (simp add: dvd_def, auto)
  apply (simp add: mult_assoc zero_less_mult_iff zmult_eq_1_iff)
  done

lemma zdvd_dvd_eq: assumes "a \<noteq> 0" and "(a::int) dvd b" and "b dvd a" 
  shows "\<bar>a\<bar> = \<bar>b\<bar>"
proof-
  from `a dvd b` obtain k where k:"b = a*k" unfolding dvd_def by blast 
  from `b dvd a` obtain k' where k':"a = b*k'" unfolding dvd_def by blast 
  from k k' have "a = a*k*k'" by simp
  with mult_cancel_left1[where c="a" and b="k*k'"]
  have kk':"k*k' = 1" using `a\<noteq>0` by (simp add: mult_assoc)
  hence "k = 1 \<and> k' = 1 \<or> k = -1 \<and> k' = -1" by (simp add: zmult_eq_1_iff)
  thus ?thesis using k k' by auto
qed

lemma zdvd_zdiffD: "k dvd m - n ==> k dvd n ==> k dvd (m::int)"
  apply (subgoal_tac "m = n + (m - n)")
   apply (erule ssubst)
   apply (blast intro: dvd_add, simp)
  done

lemma zdvd_reduce: "(k dvd n + k * m) = (k dvd (n::int))"
apply (rule iffI)
 apply (erule_tac [2] dvd_add)
 apply (subgoal_tac "n = (n + k * m) - k * m")
  apply (erule ssubst)
  apply (erule dvd_diff)
  apply(simp_all)
done

lemma zdvd_zmod: "f dvd m ==> f dvd (n::int) ==> f dvd m mod n"
  by (rule dvd_mod) (* TODO: remove *)

lemma zdvd_zmod_imp_zdvd: "k dvd m mod n ==> k dvd n ==> k dvd (m::int)"
  by (rule dvd_mod_imp_dvd) (* TODO: remove *)

lemma dvd_imp_le_int: "(i::int) ~= 0 ==> d dvd i ==> abs d <= abs i"
apply(auto simp:abs_if)
   apply(clarsimp simp:dvd_def mult_less_0_iff)
  using mult_le_cancel_left_neg[of _ "-1::int"]
  apply(clarsimp simp:dvd_def mult_less_0_iff)
 apply(clarsimp simp:dvd_def mult_less_0_iff
         minus_mult_right simp del: mult_minus_right)
apply(clarsimp simp:dvd_def mult_less_0_iff)
done

lemma zdvd_not_zless: "0 < m ==> m < n ==> \<not> n dvd (m::int)"
  apply (auto elim!: dvdE)
  apply (subgoal_tac "0 < n")
   prefer 2
   apply (blast intro: order_less_trans)
  apply (simp add: zero_less_mult_iff)
  done

lemma zmult_div_cancel: "(n::int) * (m div n) = m - (m mod n)"
  using zmod_zdiv_equality[where a="m" and b="n"]
  by (simp add: algebra_simps)

lemma zdvd_mult_div_cancel:"(n::int) dvd m \<Longrightarrow> n * (m div n) = m"
apply (subgoal_tac "m mod n = 0")
 apply (simp add: zmult_div_cancel)
apply (simp only: dvd_eq_mod_eq_0)
done

lemma zdvd_mult_cancel: assumes d:"k * m dvd k * n" and kz:"k \<noteq> (0::int)"
  shows "m dvd n"
proof-
  from d obtain h where h: "k*n = k*m * h" unfolding dvd_def by blast
  {assume "n \<noteq> m*h" hence "k* n \<noteq> k* (m*h)" using kz by simp
    with h have False by (simp add: mult_assoc)}
  hence "n = m * h" by blast
  thus ?thesis by simp
qed


theorem ex_nat: "(\<exists>x::nat. P x) = (\<exists>x::int. 0 <= x \<and> P (nat x))"
apply (simp split add: split_nat)
apply (rule iffI)
apply (erule exE)
apply (rule_tac x = "int x" in exI)
apply simp
apply (erule exE)
apply (rule_tac x = "nat x" in exI)
apply (erule conjE)
apply (erule_tac x = "nat x" in allE)
apply simp
done

theorem zdvd_int: "(x dvd y) = (int x dvd int y)"
proof -
  have "\<And>k. int y = int x * k \<Longrightarrow> x dvd y"
  proof -
    fix k
    assume A: "int y = int x * k"
    then show "x dvd y" proof (cases k)
      case (1 n) with A have "y = x * n" by (simp add: zmult_int)
      then show ?thesis ..
    next
      case (2 n) with A have "int y = int x * (- int (Suc n))" by simp
      also have "\<dots> = - (int x * int (Suc n))" by (simp only: mult_minus_right)
      also have "\<dots> = - int (x * Suc n)" by (simp only: zmult_int)
      finally have "- int (x * Suc n) = int y" ..
      then show ?thesis by (simp only: negative_eq_positive) auto
    qed
  qed
  then show ?thesis by (auto elim!: dvdE simp only: dvd_triv_left int_mult)
qed

lemma zdvd1_eq[simp]: "(x::int) dvd 1 = ( \<bar>x\<bar> = 1)"
proof
  assume d: "x dvd 1" hence "int (nat \<bar>x\<bar>) dvd int (nat 1)" by simp
  hence "nat \<bar>x\<bar> dvd 1" by (simp add: zdvd_int)
  hence "nat \<bar>x\<bar> = 1"  by simp
  thus "\<bar>x\<bar> = 1" by (cases "x < 0", auto)
next
  assume "\<bar>x\<bar>=1" thus "x dvd 1" 
    by(cases "x < 0",simp_all add: minus_equation_iff dvd_eq_mod_eq_0)
qed
lemma zdvd_mult_cancel1: 
  assumes mp:"m \<noteq>(0::int)" shows "(m * n dvd m) = (\<bar>n\<bar> = 1)"
proof
  assume n1: "\<bar>n\<bar> = 1" thus "m * n dvd m" 
    by (cases "n >0", auto simp add: minus_dvd_iff minus_equation_iff)
next
  assume H: "m * n dvd m" hence H2: "m * n dvd m * 1" by simp
  from zdvd_mult_cancel[OF H2 mp] show "\<bar>n\<bar> = 1" by (simp only: zdvd1_eq)
qed

lemma int_dvd_iff: "(int m dvd z) = (m dvd nat (abs z))"
  unfolding zdvd_int by (cases "z \<ge> 0") simp_all

lemma dvd_int_iff: "(z dvd int m) = (nat (abs z) dvd m)"
  unfolding zdvd_int by (cases "z \<ge> 0") simp_all

lemma nat_dvd_iff: "(nat z dvd m) = (if 0 \<le> z then (z dvd int m) else m = 0)"
  by (auto simp add: dvd_int_iff)

lemma zdvd_imp_le: "[| z dvd n; 0 < n |] ==> z \<le> (n::int)"
  apply (rule_tac z=n in int_cases)
  apply (auto simp add: dvd_int_iff)
  apply (rule_tac z=z in int_cases)
  apply (auto simp add: dvd_imp_le)
  done

lemma zpower_zmod: "((x::int) mod m)^y mod m = x^y mod m"
apply (induct "y", auto)
apply (rule zmod_zmult1_eq [THEN trans])
apply (simp (no_asm_simp))
apply (rule mod_mult_eq [symmetric])
done

lemma zdiv_int: "int (a div b) = (int a) div (int b)"
apply (subst split_div, auto)
apply (subst split_zdiv, auto)
apply (rule_tac a="int (b * i) + int j" and b="int b" and r="int j" and r'=ja in IntDiv.unique_quotient)
apply (auto simp add: IntDiv.divmod_rel_def of_nat_mult)
done

lemma zmod_int: "int (a mod b) = (int a) mod (int b)"
apply (subst split_mod, auto)
apply (subst split_zmod, auto)
apply (rule_tac a="int (b * i) + int j" and b="int b" and q="int i" and q'=ia 
       in unique_remainder)
apply (auto simp add: IntDiv.divmod_rel_def of_nat_mult)
done

lemma abs_div: "(y::int) dvd x \<Longrightarrow> abs (x div y) = abs x div abs y"
by (unfold dvd_def, cases "y=0", auto simp add: abs_mult)

text{*Suggested by Matthias Daum*}
lemma int_power_div_base:
     "\<lbrakk>0 < m; 0 < k\<rbrakk> \<Longrightarrow> k ^ m div k = (k::int) ^ (m - Suc 0)"
apply (subgoal_tac "k ^ m = k ^ ((m - Suc 0) + Suc 0)")
 apply (erule ssubst)
 apply (simp only: power_add)
 apply simp_all
done

text {* by Brian Huffman *}
lemma zminus_zmod: "- ((x::int) mod m) mod m = - x mod m"
by (rule mod_minus_eq [symmetric])

lemma zdiff_zmod_left: "(x mod m - y) mod m = (x - y) mod (m::int)"
by (rule mod_diff_left_eq [symmetric])

lemma zdiff_zmod_right: "(x - y mod m) mod m = (x - y) mod (m::int)"
by (rule mod_diff_right_eq [symmetric])

lemmas zmod_simps =
  mod_add_left_eq  [symmetric]
  mod_add_right_eq [symmetric]
  zmod_zmult1_eq   [symmetric]
  mod_mult_left_eq [symmetric]
  zpower_zmod
  zminus_zmod zdiff_zmod_left zdiff_zmod_right

text {* Distributive laws for function @{text nat}. *}

lemma nat_div_distrib: "0 \<le> x \<Longrightarrow> nat (x div y) = nat x div nat y"
apply (rule linorder_cases [of y 0])
apply (simp add: div_nonneg_neg_le0)
apply simp
apply (simp add: nat_eq_iff pos_imp_zdiv_nonneg_iff zdiv_int)
done

(*Fails if y<0: the LHS collapses to (nat z) but the RHS doesn't*)
lemma nat_mod_distrib:
  "\<lbrakk>0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> nat (x mod y) = nat x mod nat y"
apply (case_tac "y = 0", simp add: DIVISION_BY_ZERO)
apply (simp add: nat_eq_iff zmod_int)
done

text{*Suggested by Matthias Daum*}
lemma int_div_less_self: "\<lbrakk>0 < x; 1 < k\<rbrakk> \<Longrightarrow> x div k < (x::int)"
apply (subgoal_tac "nat x div nat k < nat x")
 apply (simp (asm_lr) add: nat_div_distrib [symmetric])
apply (rule Divides.div_less_dividend, simp_all)
done

text {* code generator setup *}

context ring_1
begin

lemma of_int_num [code]:
  "of_int k = (if k = 0 then 0 else if k < 0 then
     - of_int (- k) else let
       (l, m) = divmod k 2;
       l' = of_int l
     in if m = 0 then l' + l' else l' + l' + 1)"
proof -
  have aux1: "k mod (2\<Colon>int) \<noteq> (0\<Colon>int) \<Longrightarrow> 
    of_int k = of_int (k div 2 * 2 + 1)"
  proof -
    have "k mod 2 < 2" by (auto intro: pos_mod_bound)
    moreover have "0 \<le> k mod 2" by (auto intro: pos_mod_sign)
    moreover assume "k mod 2 \<noteq> 0"
    ultimately have "k mod 2 = 1" by arith
    moreover have "of_int k = of_int (k div 2 * 2 + k mod 2)" by simp
    ultimately show ?thesis by auto
  qed
  have aux2: "\<And>x. of_int 2 * x = x + x"
  proof -
    fix x
    have int2: "(2::int) = 1 + 1" by arith
    show "of_int 2 * x = x + x"
    unfolding int2 of_int_add left_distrib by simp
  qed
  have aux3: "\<And>x. x * of_int 2 = x + x"
  proof -
    fix x
    have int2: "(2::int) = 1 + 1" by arith
    show "x * of_int 2 = x + x" 
    unfolding int2 of_int_add right_distrib by simp
  qed
  from aux1 show ?thesis by (auto simp add: divmod_mod_div Let_def aux2 aux3)
qed

end

lemma zmod_eq_dvd_iff: "(x::int) mod n = y mod n \<longleftrightarrow> n dvd x - y"
proof
  assume H: "x mod n = y mod n"
  hence "x mod n - y mod n = 0" by simp
  hence "(x mod n - y mod n) mod n = 0" by simp 
  hence "(x - y) mod n = 0" by (simp add: mod_diff_eq[symmetric])
  thus "n dvd x - y" by (simp add: dvd_eq_mod_eq_0)
next
  assume H: "n dvd x - y"
  then obtain k where k: "x-y = n*k" unfolding dvd_def by blast
  hence "x = n*k + y" by simp
  hence "x mod n = (n*k + y) mod n" by simp
  thus "x mod n = y mod n" by (simp add: mod_add_left_eq)
qed

lemma nat_mod_eq_lemma: assumes xyn: "(x::nat) mod n = y  mod n" and xy:"y \<le> x"
  shows "\<exists>q. x = y + n * q"
proof-
  from xy have th: "int x - int y = int (x - y)" by simp 
  from xyn have "int x mod int n = int y mod int n" 
    by (simp add: zmod_int[symmetric])
  hence "int n dvd int x - int y" by (simp only: zmod_eq_dvd_iff[symmetric]) 
  hence "n dvd x - y" by (simp add: th zdvd_int)
  then show ?thesis using xy unfolding dvd_def apply clarsimp apply (rule_tac x="k" in exI) by arith
qed

lemma nat_mod_eq_iff: "(x::nat) mod n = y mod n \<longleftrightarrow> (\<exists>q1 q2. x + n * q1 = y + n * q2)" 
  (is "?lhs = ?rhs")
proof
  assume H: "x mod n = y mod n"
  {assume xy: "x \<le> y"
    from H have th: "y mod n = x mod n" by simp
    from nat_mod_eq_lemma[OF th xy] have ?rhs 
      apply clarify  apply (rule_tac x="q" in exI) by (rule exI[where x="0"], simp)}
  moreover
  {assume xy: "y \<le> x"
    from nat_mod_eq_lemma[OF H xy] have ?rhs 
      apply clarify  apply (rule_tac x="0" in exI) by (rule_tac x="q" in exI, simp)}
  ultimately  show ?rhs using linear[of x y] by blast  
next
  assume ?rhs then obtain q1 q2 where q12: "x + n * q1 = y + n * q2" by blast
  hence "(x + n * q1) mod n = (y + n * q2) mod n" by simp
  thus  ?lhs by simp
qed


subsection {* Code generation *}

definition pdivmod :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "pdivmod k l = (\<bar>k\<bar> div \<bar>l\<bar>, \<bar>k\<bar> mod \<bar>l\<bar>)"

lemma pdivmod_posDivAlg [code]:
  "pdivmod k l = (if l = 0 then (0, \<bar>k\<bar>) else posDivAlg \<bar>k\<bar> \<bar>l\<bar>)"
by (subst posDivAlg_div_mod) (simp_all add: pdivmod_def)

lemma divmod_pdivmod: "divmod k l = (if k = 0 then (0, 0) else if l = 0 then (0, k) else
  apsnd ((op *) (sgn l)) (if 0 < l \<and> 0 \<le> k \<or> l < 0 \<and> k < 0
    then pdivmod k l
    else (let (r, s) = pdivmod k l in
      if s = 0 then (- r, 0) else (- r - 1, \<bar>l\<bar> - s))))"
proof -
  have aux: "\<And>q::int. - k = l * q \<longleftrightarrow> k = l * - q" by auto
  show ?thesis
    by (simp add: divmod_mod_div pdivmod_def)
      (auto simp add: aux not_less not_le zdiv_zminus1_eq_if
      zmod_zminus1_eq_if zdiv_zminus2_eq_if zmod_zminus2_eq_if)
qed

lemma divmod_code [code]: "divmod k l = (if k = 0 then (0, 0) else if l = 0 then (0, k) else
  apsnd ((op *) (sgn l)) (if sgn k = sgn l
    then pdivmod k l
    else (let (r, s) = pdivmod k l in
      if s = 0 then (- r, 0) else (- r - 1, \<bar>l\<bar> - s))))"
proof -
  have "k \<noteq> 0 \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> 0 < l \<and> 0 \<le> k \<or> l < 0 \<and> k < 0 \<longleftrightarrow> sgn k = sgn l"
    by (auto simp add: not_less sgn_if)
  then show ?thesis by (simp add: divmod_pdivmod)
qed

code_modulename SML
  IntDiv Integer

code_modulename OCaml
  IntDiv Integer

code_modulename Haskell
  IntDiv Integer

end
