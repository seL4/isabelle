(*  Title:      CTT/Arith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header {* Elementary arithmetic *}

theory Arith
imports Bool
begin

subsection {* Arithmetic operators and their definitions *}

consts
  "#+"  :: "[i,i]=>i"   (infixr 65)
  "-"   :: "[i,i]=>i"   (infixr 65)
  "|-|" :: "[i,i]=>i"   (infixr 65)
  "#*"  :: "[i,i]=>i"   (infixr 70)
  div   :: "[i,i]=>i"   (infixr 70)
  mod   :: "[i,i]=>i"   (infixr 70)

syntax (xsymbols)
  "op #*"      :: "[i, i] => i"   (infixr "#\<times>" 70)

syntax (HTML output)
  "op #*"      :: "[i, i] => i"   (infixr "#\<times>" 70)

defs
  add_def:     "a#+b == rec(a, b, %u v. succ(v))"
  diff_def:    "a-b == rec(b, a, %u v. rec(v, 0, %x y. x))"
  absdiff_def: "a|-|b == (a-b) #+ (b-a)"
  mult_def:    "a#*b == rec(a, 0, %u v. b #+ v)"
  mod_def:     "a mod b == rec(a, 0, %u v. rec(succ(v) |-| b, 0, %x y. succ(v)))"
  div_def:     "a div b == rec(a, 0, %u v. rec(succ(u) mod b, succ(v), %x y. v))"

lemmas arith_defs = add_def diff_def absdiff_def mult_def mod_def div_def


subsection {* Proofs about elementary arithmetic: addition, multiplication, etc. *}

(** Addition *)

(*typing of add: short and long versions*)

lemma add_typing: "[| a:N;  b:N |] ==> a #+ b : N"
apply (unfold arith_defs)
apply (tactic "typechk_tac []")
done

lemma add_typingL: "[| a=c:N;  b=d:N |] ==> a #+ b = c #+ d : N"
apply (unfold arith_defs)
apply (tactic "equal_tac []")
done


(*computation for add: 0 and successor cases*)

lemma addC0: "b:N ==> 0 #+ b = b : N"
apply (unfold arith_defs)
apply (tactic "rew_tac []")
done

lemma addC_succ: "[| a:N;  b:N |] ==> succ(a) #+ b = succ(a #+ b) : N"
apply (unfold arith_defs)
apply (tactic "rew_tac []")
done


(** Multiplication *)

(*typing of mult: short and long versions*)

lemma mult_typing: "[| a:N;  b:N |] ==> a #* b : N"
apply (unfold arith_defs)
apply (tactic {* typechk_tac [thm "add_typing"] *})
done

lemma mult_typingL: "[| a=c:N;  b=d:N |] ==> a #* b = c #* d : N"
apply (unfold arith_defs)
apply (tactic {* equal_tac [thm "add_typingL"] *})
done

(*computation for mult: 0 and successor cases*)

lemma multC0: "b:N ==> 0 #* b = 0 : N"
apply (unfold arith_defs)
apply (tactic "rew_tac []")
done

lemma multC_succ: "[| a:N;  b:N |] ==> succ(a) #* b = b #+ (a #* b) : N"
apply (unfold arith_defs)
apply (tactic "rew_tac []")
done


(** Difference *)

(*typing of difference*)

lemma diff_typing: "[| a:N;  b:N |] ==> a - b : N"
apply (unfold arith_defs)
apply (tactic "typechk_tac []")
done

lemma diff_typingL: "[| a=c:N;  b=d:N |] ==> a - b = c - d : N"
apply (unfold arith_defs)
apply (tactic "equal_tac []")
done


(*computation for difference: 0 and successor cases*)

lemma diffC0: "a:N ==> a - 0 = a : N"
apply (unfold arith_defs)
apply (tactic "rew_tac []")
done

(*Note: rec(a, 0, %z w.z) is pred(a). *)

lemma diff_0_eq_0: "b:N ==> 0 - b = 0 : N"
apply (unfold arith_defs)
apply (tactic {* NE_tac "b" 1 *})
apply (tactic "hyp_rew_tac []")
done


(*Essential to simplify FIRST!!  (Else we get a critical pair)
  succ(a) - succ(b) rewrites to   pred(succ(a) - b)  *)
lemma diff_succ_succ: "[| a:N;  b:N |] ==> succ(a) - succ(b) = a - b : N"
apply (unfold arith_defs)
apply (tactic "hyp_rew_tac []")
apply (tactic {* NE_tac "b" 1 *})
apply (tactic "hyp_rew_tac []")
done


subsection {* Simplification *}

lemmas arith_typing_rls = add_typing mult_typing diff_typing
  and arith_congr_rls = add_typingL mult_typingL diff_typingL
lemmas congr_rls = arith_congr_rls intrL2_rls elimL_rls

lemmas arithC_rls =
  addC0 addC_succ
  multC0 multC_succ
  diffC0 diff_0_eq_0 diff_succ_succ

ML {*

structure Arith_simp_data: TSIMP_DATA =
  struct
  val refl              = thm "refl_elem"
  val sym               = thm "sym_elem"
  val trans             = thm "trans_elem"
  val refl_red          = thm "refl_red"
  val trans_red         = thm "trans_red"
  val red_if_equal      = thm "red_if_equal"
  val default_rls       = thms "arithC_rls" @ thms "comp_rls"
  val routine_tac       = routine_tac (thms "arith_typing_rls" @ thms "routine_rls")
  end

structure Arith_simp = TSimpFun (Arith_simp_data)

local val congr_rls = thms "congr_rls" in

fun arith_rew_tac prems = make_rew_tac
    (Arith_simp.norm_tac(congr_rls, prems))

fun hyp_arith_rew_tac prems = make_rew_tac
    (Arith_simp.cond_norm_tac(prove_cond_tac, congr_rls, prems))

end
*}


subsection {* Addition *}

(*Associative law for addition*)
lemma add_assoc: "[| a:N;  b:N;  c:N |] ==> (a #+ b) #+ c = a #+ (b #+ c) : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic "hyp_arith_rew_tac []")
done


(*Commutative law for addition.  Can be proved using three inductions.
  Must simplify after first induction!  Orientation of rewrites is delicate*)
lemma add_commute: "[| a:N;  b:N |] ==> a #+ b = b #+ a : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic "hyp_arith_rew_tac []")
apply (tactic {* NE_tac "b" 2 *})
apply (rule sym_elem)
apply (tactic {* NE_tac "b" 1 *})
apply (tactic "hyp_arith_rew_tac []")
done


subsection {* Multiplication *}

(*right annihilation in product*)
lemma mult_0_right: "a:N ==> a #* 0 = 0 : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic "hyp_arith_rew_tac []")
done

(*right successor law for multiplication*)
lemma mult_succ_right: "[| a:N;  b:N |] ==> a #* succ(b) = a #+ (a #* b) : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic {* hyp_arith_rew_tac [thm "add_assoc" RS thm "sym_elem"] *})
apply (assumption | rule add_commute mult_typingL add_typingL intrL_rls refl_elem)+
done

(*Commutative law for multiplication*)
lemma mult_commute: "[| a:N;  b:N |] ==> a #* b = b #* a : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic {* hyp_arith_rew_tac [thm "mult_0_right", thm "mult_succ_right"] *})
done

(*addition distributes over multiplication*)
lemma add_mult_distrib: "[| a:N;  b:N;  c:N |] ==> (a #+ b) #* c = (a #* c) #+ (b #* c) : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic {* hyp_arith_rew_tac [thm "add_assoc" RS thm "sym_elem"] *})
done

(*Associative law for multiplication*)
lemma mult_assoc: "[| a:N;  b:N;  c:N |] ==> (a #* b) #* c = a #* (b #* c) : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic {* hyp_arith_rew_tac [thm "add_mult_distrib"] *})
done


subsection {* Difference *}

text {*
Difference on natural numbers, without negative numbers
  a - b = 0  iff  a<=b    a - b = succ(c) iff a>b   *}

lemma diff_self_eq_0: "a:N ==> a - a = 0 : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic "hyp_arith_rew_tac []")
done


lemma add_0_right: "[| c : N; 0 : N; c : N |] ==> c #+ 0 = c : N"
  by (rule addC0 [THEN [3] add_commute [THEN trans_elem]])

(*Addition is the inverse of subtraction: if b<=x then b#+(x-b) = x.
  An example of induction over a quantified formula (a product).
  Uses rewriting with a quantified, implicative inductive hypothesis.*)
lemma add_diff_inverse_lemma: "b:N ==> ?a : PROD x:N. Eq(N, b-x, 0) --> Eq(N, b #+ (x-b), x)"
apply (tactic {* NE_tac "b" 1 *})
(*strip one "universal quantifier" but not the "implication"*)
apply (rule_tac [3] intr_rls)
(*case analysis on x in
    (succ(u) <= x) --> (succ(u)#+(x-succ(u)) = x) *)
apply (tactic {* NE_tac "x" 4 *}, tactic "assume_tac 4")
(*Prepare for simplification of types -- the antecedent succ(u)<=x *)
apply (rule_tac [5] replace_type)
apply (rule_tac [4] replace_type)
apply (tactic "arith_rew_tac []")
(*Solves first 0 goal, simplifies others.  Two sugbgoals remain.
  Both follow by rewriting, (2) using quantified induction hyp*)
apply (tactic "intr_tac []") (*strips remaining PRODs*)
apply (tactic {* hyp_arith_rew_tac [thm "add_0_right"] *})
apply assumption
done


(*Version of above with premise   b-a=0   i.e.    a >= b.
  Using ProdE does not work -- for ?B(?a) is ambiguous.
  Instead, add_diff_inverse_lemma states the desired induction scheme
    the use of RS below instantiates Vars in ProdE automatically. *)
lemma add_diff_inverse: "[| a:N;  b:N;  b-a = 0 : N |] ==> b #+ (a-b) = a : N"
apply (rule EqE)
apply (rule add_diff_inverse_lemma [THEN ProdE, THEN ProdE])
apply (assumption | rule EqI)+
done


subsection {* Absolute difference *}

(*typing of absolute difference: short and long versions*)

lemma absdiff_typing: "[| a:N;  b:N |] ==> a |-| b : N"
apply (unfold arith_defs)
apply (tactic "typechk_tac []")
done

lemma absdiff_typingL: "[| a=c:N;  b=d:N |] ==> a |-| b = c |-| d : N"
apply (unfold arith_defs)
apply (tactic "equal_tac []")
done

lemma absdiff_self_eq_0: "a:N ==> a |-| a = 0 : N"
apply (unfold absdiff_def)
apply (tactic {* arith_rew_tac [thm "diff_self_eq_0"] *})
done

lemma absdiffC0: "a:N ==> 0 |-| a = a : N"
apply (unfold absdiff_def)
apply (tactic "hyp_arith_rew_tac []")
done


lemma absdiff_succ_succ: "[| a:N;  b:N |] ==> succ(a) |-| succ(b)  =  a |-| b : N"
apply (unfold absdiff_def)
apply (tactic "hyp_arith_rew_tac []")
done

(*Note how easy using commutative laws can be?  ...not always... *)
lemma absdiff_commute: "[| a:N;  b:N |] ==> a |-| b = b |-| a : N"
apply (unfold absdiff_def)
apply (rule add_commute)
apply (tactic {* typechk_tac [thm "diff_typing"] *})
done

(*If a+b=0 then a=0.   Surprisingly tedious*)
lemma add_eq0_lemma: "[| a:N;  b:N |] ==> ?c : PROD u: Eq(N,a#+b,0) .  Eq(N,a,0)"
apply (tactic {* NE_tac "a" 1 *})
apply (rule_tac [3] replace_type)
apply (tactic "arith_rew_tac []")
apply (tactic "intr_tac []") (*strips remaining PRODs*)
apply (rule_tac [2] zero_ne_succ [THEN FE])
apply (erule_tac [3] EqE [THEN sym_elem])
apply (tactic {* typechk_tac [thm "add_typing"] *})
done

(*Version of above with the premise  a+b=0.
  Again, resolution instantiates variables in ProdE *)
lemma add_eq0: "[| a:N;  b:N;  a #+ b = 0 : N |] ==> a = 0 : N"
apply (rule EqE)
apply (rule add_eq0_lemma [THEN ProdE])
apply (rule_tac [3] EqI)
apply (tactic "typechk_tac []")
done

(*Here is a lemma to infer a-b=0 and b-a=0 from a|-|b=0, below. *)
lemma absdiff_eq0_lem:
    "[| a:N;  b:N;  a |-| b = 0 : N |] ==>
     ?a : SUM v: Eq(N, a-b, 0) . Eq(N, b-a, 0)"
apply (unfold absdiff_def)
apply (tactic "intr_tac []")
apply (tactic eqintr_tac)
apply (rule_tac [2] add_eq0)
apply (rule add_eq0)
apply (rule_tac [6] add_commute [THEN trans_elem])
apply (tactic {* typechk_tac [thm "diff_typing"] *})
done

(*if  a |-| b = 0  then  a = b
  proof: a-b=0 and b-a=0, so b = a+(b-a) = a+0 = a*)
lemma absdiff_eq0: "[| a |-| b = 0 : N;  a:N;  b:N |] ==> a = b : N"
apply (rule EqE)
apply (rule absdiff_eq0_lem [THEN SumE])
apply (tactic "TRYALL assume_tac")
apply (tactic eqintr_tac)
apply (rule add_diff_inverse [THEN sym_elem, THEN trans_elem])
apply (rule_tac [3] EqE, tactic "assume_tac 3")
apply (tactic {* hyp_arith_rew_tac [thm "add_0_right"] *})
done


subsection {* Remainder and Quotient *}

(*typing of remainder: short and long versions*)

lemma mod_typing: "[| a:N;  b:N |] ==> a mod b : N"
apply (unfold mod_def)
apply (tactic {* typechk_tac [thm "absdiff_typing"] *})
done

lemma mod_typingL: "[| a=c:N;  b=d:N |] ==> a mod b = c mod d : N"
apply (unfold mod_def)
apply (tactic {* equal_tac [thm "absdiff_typingL"] *})
done


(*computation for  mod : 0 and successor cases*)

lemma modC0: "b:N ==> 0 mod b = 0 : N"
apply (unfold mod_def)
apply (tactic {* rew_tac [thm "absdiff_typing"] *})
done

lemma modC_succ:
"[| a:N; b:N |] ==> succ(a) mod b = rec(succ(a mod b) |-| b, 0, %x y. succ(a mod b)) : N"
apply (unfold mod_def)
apply (tactic {* rew_tac [thm "absdiff_typing"] *})
done


(*typing of quotient: short and long versions*)

lemma div_typing: "[| a:N;  b:N |] ==> a div b : N"
apply (unfold div_def)
apply (tactic {* typechk_tac [thm "absdiff_typing", thm "mod_typing"] *})
done

lemma div_typingL: "[| a=c:N;  b=d:N |] ==> a div b = c div d : N"
apply (unfold div_def)
apply (tactic {* equal_tac [thm "absdiff_typingL", thm "mod_typingL"] *})
done

lemmas div_typing_rls = mod_typing div_typing absdiff_typing


(*computation for quotient: 0 and successor cases*)

lemma divC0: "b:N ==> 0 div b = 0 : N"
apply (unfold div_def)
apply (tactic {* rew_tac [thm "mod_typing", thm "absdiff_typing"] *})
done

lemma divC_succ:
 "[| a:N;  b:N |] ==> succ(a) div b =
     rec(succ(a) mod b, succ(a div b), %x y. a div b) : N"
apply (unfold div_def)
apply (tactic {* rew_tac [thm "mod_typing"] *})
done


(*Version of above with same condition as the  mod  one*)
lemma divC_succ2: "[| a:N;  b:N |] ==>
     succ(a) div b =rec(succ(a mod b) |-| b, succ(a div b), %x y. a div b) : N"
apply (rule divC_succ [THEN trans_elem])
apply (tactic {* rew_tac (thms "div_typing_rls" @ [thm "modC_succ"]) *})
apply (tactic {* NE_tac "succ (a mod b) |-|b" 1 *})
apply (tactic {* rew_tac [thm "mod_typing", thm "div_typing", thm "absdiff_typing"] *})
done

(*for case analysis on whether a number is 0 or a successor*)
lemma iszero_decidable: "a:N ==> rec(a, inl(eq), %ka kb. inr(<ka, eq>)) :
                      Eq(N,a,0) + (SUM x:N. Eq(N,a, succ(x)))"
apply (tactic {* NE_tac "a" 1 *})
apply (rule_tac [3] PlusI_inr)
apply (rule_tac [2] PlusI_inl)
apply (tactic eqintr_tac)
apply (tactic "equal_tac []")
done

(*Main Result.  Holds when b is 0 since   a mod 0 = a     and    a div 0 = 0  *)
lemma mod_div_equality: "[| a:N;  b:N |] ==> a mod b  #+  (a div b) #* b = a : N"
apply (tactic {* NE_tac "a" 1 *})
apply (tactic {* arith_rew_tac (thms "div_typing_rls" @
  [thm "modC0", thm "modC_succ", thm "divC0", thm "divC_succ2"]) *})
apply (rule EqE)
(*case analysis on   succ(u mod b)|-|b  *)
apply (rule_tac a1 = "succ (u mod b) |-| b" in iszero_decidable [THEN PlusE])
apply (erule_tac [3] SumE)
apply (tactic {* hyp_arith_rew_tac (thms "div_typing_rls" @
  [thm "modC0", thm "modC_succ", thm "divC0", thm "divC_succ2"]) *})
(*Replace one occurence of  b  by succ(u mod b).  Clumsy!*)
apply (rule add_typingL [THEN trans_elem])
apply (erule EqE [THEN absdiff_eq0, THEN sym_elem])
apply (rule_tac [3] refl_elem)
apply (tactic {* hyp_arith_rew_tac (thms "div_typing_rls") *})
done

end
