(*  Title: 	CTT/arith
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Theorems for arith.thy (Arithmetic operators)

Proofs about elementary arithmetic: addition, multiplication, etc.
Tests definitions and simplifier.
*)

open Arith;
val arith_defs = [add_def, diff_def, absdiff_def, mult_def, mod_def, div_def];


(** Addition *)

(*typing of add: short and long versions*)

val add_typing = prove_goalw Arith.thy arith_defs
    "[| a:N;  b:N |] ==> a #+ b : N"
 (fn prems=> [ (typechk_tac prems) ]);

val add_typingL = prove_goalw Arith.thy arith_defs
    "[| a=c:N;  b=d:N |] ==> a #+ b = c #+ d : N"
 (fn prems=> [ (equal_tac prems) ]);


(*computation for add: 0 and successor cases*)

val addC0 = prove_goalw Arith.thy arith_defs
    "b:N ==> 0 #+ b = b : N"
 (fn prems=> [ (rew_tac prems) ]);

val addC_succ = prove_goalw Arith.thy arith_defs
    "[| a:N;  b:N |] ==> succ(a) #+ b = succ(a #+ b) : N"
 (fn prems=> [ (rew_tac prems) ]); 


(** Multiplication *)

(*typing of mult: short and long versions*)

val mult_typing = prove_goalw Arith.thy arith_defs
    "[| a:N;  b:N |] ==> a #* b : N"
 (fn prems=>
  [ (typechk_tac([add_typing]@prems)) ]);

val mult_typingL = prove_goalw Arith.thy arith_defs
    "[| a=c:N;  b=d:N |] ==> a #* b = c #* d : N"
 (fn prems=>
  [ (equal_tac (prems@[add_typingL])) ]);

(*computation for mult: 0 and successor cases*)

val multC0 = prove_goalw Arith.thy arith_defs
    "b:N ==> 0 #* b = 0 : N"
 (fn prems=> [ (rew_tac prems) ]);

val multC_succ = prove_goalw Arith.thy arith_defs
    "[| a:N;  b:N |] ==> succ(a) #* b = b #+ (a #* b) : N"
 (fn prems=> [ (rew_tac prems) ]);


(** Difference *)

(*typing of difference*)

val diff_typing = prove_goalw Arith.thy arith_defs
    "[| a:N;  b:N |] ==> a - b : N"
 (fn prems=> [ (typechk_tac prems) ]);

val diff_typingL = prove_goalw Arith.thy arith_defs
    "[| a=c:N;  b=d:N |] ==> a - b = c - d : N"
 (fn prems=> [ (equal_tac prems) ]);



(*computation for difference: 0 and successor cases*)

val diffC0 = prove_goalw Arith.thy arith_defs
    "a:N ==> a - 0 = a : N"
 (fn prems=> [ (rew_tac prems) ]);

(*Note: rec(a, 0, %z w.z) is pred(a). *)

val diff_0_eq_0 = prove_goalw Arith.thy arith_defs
    "b:N ==> 0 - b = 0 : N"
 (fn prems=>
  [ (NE_tac "b" 1),
    (hyp_rew_tac prems) ]);


(*Essential to simplify FIRST!!  (Else we get a critical pair)
  succ(a) - succ(b) rewrites to   pred(succ(a) - b)  *)
val diff_succ_succ = prove_goalw Arith.thy arith_defs
    "[| a:N;  b:N |] ==> succ(a) - succ(b) = a - b : N"
 (fn prems=>
  [ (hyp_rew_tac prems),
    (NE_tac "b" 1),
    (hyp_rew_tac prems) ]);



(*** Simplification *)

val arith_typing_rls =
  [add_typing, mult_typing, diff_typing];

val arith_congr_rls =
  [add_typingL, mult_typingL, diff_typingL];

val congr_rls = arith_congr_rls@standard_congr_rls;

val arithC_rls =
  [addC0, addC_succ,
   multC0, multC_succ,
   diffC0, diff_0_eq_0, diff_succ_succ];


structure Arith_simp_data: TSIMP_DATA =
  struct
  val refl		= refl_elem
  val sym		= sym_elem
  val trans		= trans_elem
  val refl_red		= refl_red
  val trans_red		= trans_red
  val red_if_equal	= red_if_equal
  val default_rls 	= arithC_rls @ comp_rls
  val routine_tac 	= routine_tac (arith_typing_rls @ routine_rls)
  end;

structure Arith_simp = TSimpFun (Arith_simp_data);

fun arith_rew_tac prems = make_rew_tac
    (Arith_simp.norm_tac(congr_rls, prems));

fun hyp_arith_rew_tac prems = make_rew_tac
    (Arith_simp.cond_norm_tac(prove_cond_tac, congr_rls, prems));


(**********
  Addition
 **********)

(*Associative law for addition*)
val add_assoc = prove_goal Arith.thy 
    "[| a:N;  b:N;  c:N |] ==> (a #+ b) #+ c = a #+ (b #+ c) : N"
 (fn prems=>
  [ (NE_tac "a" 1),
    (hyp_arith_rew_tac prems) ]);


(*Commutative law for addition.  Can be proved using three inductions.
  Must simplify after first induction!  Orientation of rewrites is delicate*)  
val add_commute = prove_goal Arith.thy 
    "[| a:N;  b:N |] ==> a #+ b = b #+ a : N"
 (fn prems=>
  [ (NE_tac "a" 1),
    (hyp_arith_rew_tac prems),
    (NE_tac "b" 2),
    (resolve_tac [sym_elem] 1),
    (NE_tac "b" 1),
    (hyp_arith_rew_tac prems) ]);


(****************
  Multiplication
 ****************)

(*Commutative law for multiplication
val mult_commute = prove_goal Arith.thy 
    "[| a:N;  b:N |] ==> a #* b = b #* a : N"
 (fn prems=>
  [ (NE_tac "a" 1),
    (hyp_arith_rew_tac prems),
    (NE_tac "b" 2),
    (resolve_tac [sym_elem] 1),
    (NE_tac "b" 1),
    (hyp_arith_rew_tac prems) ]);   NEEDS COMMUTATIVE MATCHING
***************)

(*right annihilation in product*)
val mult_0_right = prove_goal Arith.thy 
    "a:N ==> a #* 0 = 0 : N"
 (fn prems=>
  [ (NE_tac "a" 1),
    (hyp_arith_rew_tac prems) ]);

(*right successor law for multiplication*)
val mult_succ_right = prove_goal Arith.thy 
    "[| a:N;  b:N |] ==> a #* succ(b) = a #+ (a #* b) : N"
 (fn prems=>
  [ (NE_tac "a" 1),
(*swap round the associative law of addition*)
    (hyp_arith_rew_tac (prems @ [add_assoc RS sym_elem])),  
(*leaves a goal involving a commutative law*)
    (REPEAT (assume_tac 1  ORELSE  
            resolve_tac
             (prems@[add_commute,mult_typingL,add_typingL]@
	       intrL_rls@[refl_elem])   1)) ]);

(*Commutative law for multiplication*)
val mult_commute = prove_goal Arith.thy 
    "[| a:N;  b:N |] ==> a #* b = b #* a : N"
 (fn prems=>
  [ (NE_tac "a" 1),
    (hyp_arith_rew_tac (prems @ [mult_0_right, mult_succ_right])) ]);

(*addition distributes over multiplication*)
val add_mult_distrib = prove_goal Arith.thy 
    "[| a:N;  b:N;  c:N |] ==> (a #+ b) #* c = (a #* c) #+ (b #* c) : N"
 (fn prems=>
  [ (NE_tac "a" 1),
(*swap round the associative law of addition*)
    (hyp_arith_rew_tac (prems @ [add_assoc RS sym_elem])) ]);


(*Associative law for multiplication*)
val mult_assoc = prove_goal Arith.thy 
    "[| a:N;  b:N;  c:N |] ==> (a #* b) #* c = a #* (b #* c) : N"
 (fn prems=>
  [ (NE_tac "a" 1),
    (hyp_arith_rew_tac (prems @ [add_mult_distrib])) ]);


(************
  Difference
 ************

Difference on natural numbers, without negative numbers
  a - b = 0  iff  a<=b    a - b = succ(c) iff a>b   *)

val diff_self_eq_0 = prove_goal Arith.thy 
    "a:N ==> a - a = 0 : N"
 (fn prems=>
  [ (NE_tac "a" 1),
    (hyp_arith_rew_tac prems) ]);


(*  [| c : N; 0 : N; c : N |] ==> c #+ 0 = c : N  *)
val add_0_right = addC0 RSN (3, add_commute RS trans_elem);

(*Addition is the inverse of subtraction: if b<=x then b#+(x-b) = x.
  An example of induction over a quantified formula (a product).
  Uses rewriting with a quantified, implicative inductive hypothesis.*)
val prems =
goal Arith.thy 
    "b:N ==> ?a : PROD x:N. Eq(N, b-x, 0) --> Eq(N, b #+ (x-b), x)";
by (NE_tac "b" 1);
(*strip one "universal quantifier" but not the "implication"*)
by (resolve_tac intr_rls 3);  
(*case analysis on x in
    (succ(u) <= x) --> (succ(u)#+(x-succ(u)) = x) *)
by (NE_tac "x" 4 THEN assume_tac 4); 
(*Prepare for simplification of types -- the antecedent succ(u)<=x *)
by (resolve_tac [replace_type] 5);
by (resolve_tac [replace_type] 4);
by (arith_rew_tac prems); 
(*Solves first 0 goal, simplifies others.  Two sugbgoals remain.
  Both follow by rewriting, (2) using quantified induction hyp*)
by (intr_tac[]);  (*strips remaining PRODs*)
by (hyp_arith_rew_tac (prems@[add_0_right]));  
by (assume_tac 1);
val add_diff_inverse_lemma = result();


(*Version of above with premise   b-a=0   i.e.    a >= b.
  Using ProdE does not work -- for ?B(?a) is ambiguous.
  Instead, add_diff_inverse_lemma states the desired induction scheme;
    the use of RS below instantiates Vars in ProdE automatically. *)
val prems =
goal Arith.thy "[| a:N;  b:N;  b-a = 0 : N |] ==> b #+ (a-b) = a : N";
by (resolve_tac [EqE] 1);
by (resolve_tac [ add_diff_inverse_lemma RS ProdE RS ProdE ] 1);
by (REPEAT (resolve_tac (prems@[EqI]) 1));
val add_diff_inverse = result();


(********************
  Absolute difference
 ********************)

(*typing of absolute difference: short and long versions*)

val absdiff_typing = prove_goalw Arith.thy arith_defs
    "[| a:N;  b:N |] ==> a |-| b : N"
 (fn prems=> [ (typechk_tac prems) ]);

val absdiff_typingL = prove_goalw Arith.thy arith_defs
    "[| a=c:N;  b=d:N |] ==> a |-| b = c |-| d : N"
 (fn prems=> [ (equal_tac prems) ]);

val absdiff_self_eq_0 = prove_goalw Arith.thy [absdiff_def]
    "a:N ==> a |-| a = 0 : N"
 (fn prems=>
  [ (arith_rew_tac (prems@[diff_self_eq_0])) ]);

val absdiffC0 = prove_goalw Arith.thy [absdiff_def]
    "a:N ==> 0 |-| a = a : N"
 (fn prems=>
  [ (hyp_arith_rew_tac prems) ]);


val absdiff_succ_succ = prove_goalw Arith.thy [absdiff_def]
    "[| a:N;  b:N |] ==> succ(a) |-| succ(b)  =  a |-| b : N"
 (fn prems=>
  [ (hyp_arith_rew_tac prems) ]);

(*Note how easy using commutative laws can be?  ...not always... *)
val prems = goalw Arith.thy [absdiff_def]
    "[| a:N;  b:N |] ==> a |-| b = b |-| a : N";
by (resolve_tac [add_commute] 1);
by (typechk_tac ([diff_typing]@prems));
val absdiff_commute = result();

(*If a+b=0 then a=0.   Surprisingly tedious*)
val prems =
goal Arith.thy "[| a:N;  b:N |] ==> ?c : PROD u: Eq(N,a#+b,0) .  Eq(N,a,0)";
by (NE_tac "a" 1);
by (resolve_tac [replace_type] 3);
by (arith_rew_tac prems);
by (intr_tac[]);  (*strips remaining PRODs*)
by (resolve_tac [ zero_ne_succ RS FE ] 2);
by (etac (EqE RS sym_elem) 3);
by (typechk_tac ([add_typing] @prems));
val add_eq0_lemma = result();

(*Version of above with the premise  a+b=0.
  Again, resolution instantiates variables in ProdE *)
val prems =
goal Arith.thy "[| a:N;  b:N;  a #+ b = 0 : N |] ==> a = 0 : N";
by (resolve_tac [EqE] 1);
by (resolve_tac [add_eq0_lemma RS ProdE] 1);
by (resolve_tac [EqI] 3);
by (ALLGOALS (resolve_tac prems));
val add_eq0 = result();

(*Here is a lemma to infer a-b=0 and b-a=0 from a|-|b=0, below. *)
val prems = goalw Arith.thy [absdiff_def]
    "[| a:N;  b:N;  a |-| b = 0 : N |] ==> \
\    ?a : SUM v: Eq(N, a-b, 0) . Eq(N, b-a, 0)";
by (intr_tac[]);
by eqintr_tac;
by (resolve_tac [add_eq0] 2);
by (resolve_tac [add_eq0] 1);
by (resolve_tac [add_commute RS trans_elem] 6);
by (typechk_tac (diff_typing::prems));
val absdiff_eq0_lem = result();

(*if  a |-| b = 0  then  a = b  
  proof: a-b=0 and b-a=0, so b = a+(b-a) = a+0 = a*)
val prems =
goal Arith.thy "[| a |-| b = 0 : N;  a:N;  b:N |] ==> a = b : N";
by (resolve_tac [EqE] 1);
by (resolve_tac [absdiff_eq0_lem RS SumE] 1);
by (TRYALL (resolve_tac prems));
by eqintr_tac;
by (resolve_tac [add_diff_inverse RS sym_elem RS trans_elem] 1);
by (resolve_tac [EqE] 3  THEN  assume_tac 3);
by (hyp_arith_rew_tac (prems@[add_0_right]));
val absdiff_eq0 = result();

(***********************
  Remainder and Quotient
 ***********************)

(*typing of remainder: short and long versions*)

val mod_typing = prove_goalw Arith.thy [mod_def]
    "[| a:N;  b:N |] ==> a mod b : N"
 (fn prems=>
  [ (typechk_tac (absdiff_typing::prems)) ]);
 
val mod_typingL = prove_goalw Arith.thy [mod_def]
    "[| a=c:N;  b=d:N |] ==> a mod b = c mod d : N"
 (fn prems=>
  [ (equal_tac (prems@[absdiff_typingL])) ]);
 

(*computation for  mod : 0 and successor cases*)

val modC0 = prove_goalw Arith.thy [mod_def] "b:N ==> 0 mod b = 0 : N"
 (fn prems=>
  [ (rew_tac(absdiff_typing::prems)) ]);

val modC_succ = prove_goalw Arith.thy [mod_def] 
"[| a:N; b:N |] ==> succ(a) mod b = rec(succ(a mod b) |-| b, 0, %x y.succ(a mod b)) : N"
 (fn prems=>
  [ (rew_tac(absdiff_typing::prems)) ]);


(*typing of quotient: short and long versions*)

val div_typing = prove_goalw Arith.thy [div_def] "[| a:N;  b:N |] ==> a div b : N"
 (fn prems=>
  [ (typechk_tac ([absdiff_typing,mod_typing]@prems)) ]);

val div_typingL = prove_goalw Arith.thy [div_def]
   "[| a=c:N;  b=d:N |] ==> a div b = c div d : N"
 (fn prems=>
  [ (equal_tac (prems @ [absdiff_typingL, mod_typingL])) ]);

val div_typing_rls = [mod_typing, div_typing, absdiff_typing];


(*computation for quotient: 0 and successor cases*)

val divC0 = prove_goalw Arith.thy [div_def] "b:N ==> 0 div b = 0 : N"
 (fn prems=>
  [ (rew_tac([mod_typing, absdiff_typing] @ prems)) ]);

val divC_succ =
prove_goalw Arith.thy [div_def] "[| a:N;  b:N |] ==> succ(a) div b = \
\    rec(succ(a) mod b, succ(a div b), %x y. a div b) : N"
 (fn prems=>
  [ (rew_tac([mod_typing]@prems)) ]);


(*Version of above with same condition as the  mod  one*)
val divC_succ2 = prove_goal Arith.thy
    "[| a:N;  b:N |] ==> \
\    succ(a) div b =rec(succ(a mod b) |-| b, succ(a div b), %x y. a div b) : N"
 (fn prems=>
  [ (resolve_tac [ divC_succ RS trans_elem ] 1),
    (rew_tac(div_typing_rls @ prems @ [modC_succ])),
    (NE_tac "succ(a mod b)|-|b" 1),
    (rew_tac ([mod_typing, div_typing, absdiff_typing] @prems)) ]);

(*for case analysis on whether a number is 0 or a successor*)
val iszero_decidable = prove_goal Arith.thy
    "a:N ==> rec(a, inl(eq), %ka kb.inr(<ka, eq>)) : \
\		      Eq(N,a,0) + (SUM x:N. Eq(N,a, succ(x)))"
 (fn prems=>
  [ (NE_tac "a" 1),
    (resolve_tac [PlusI_inr] 3),
    (resolve_tac [PlusI_inl] 2),
    eqintr_tac,
    (equal_tac prems) ]);

(*Main Result.  Holds when b is 0 since   a mod 0 = a     and    a div 0 = 0  *)
val prems =
goal Arith.thy "[| a:N;  b:N |] ==> a mod b  #+  (a div b) #* b = a : N";
by (NE_tac "a" 1);
by (arith_rew_tac (div_typing_rls@prems@[modC0,modC_succ,divC0,divC_succ2])); 
by (resolve_tac [EqE] 1);
(*case analysis on   succ(u mod b)|-|b  *)
by (res_inst_tac [("a1", "succ(u mod b) |-| b")] 
                 (iszero_decidable RS PlusE) 1);
by (etac SumE 3);
by (hyp_arith_rew_tac (prems @ div_typing_rls @
	[modC0,modC_succ, divC0, divC_succ2])); 
(*Replace one occurence of  b  by succ(u mod b).  Clumsy!*)
by (resolve_tac [ add_typingL RS trans_elem ] 1);
by (eresolve_tac [EqE RS absdiff_eq0 RS sym_elem] 1);
by (resolve_tac [refl_elem] 3);
by (hyp_arith_rew_tac (prems @ div_typing_rls)); 
val mod_div_equality = result();

writeln"Reached end of file.";
