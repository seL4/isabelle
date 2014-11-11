(*  Title:      CTT/Arith.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section {* Elementary arithmetic *}

theory Arith
imports Bool
begin

subsection {* Arithmetic operators and their definitions *}

definition
  add :: "[i,i]\<Rightarrow>i"   (infixr "#+" 65) where
  "a#+b == rec(a, b, \<lambda>u v. succ(v))"

definition
  diff :: "[i,i]\<Rightarrow>i"   (infixr "-" 65) where
  "a-b == rec(b, a, \<lambda>u v. rec(v, 0, \<lambda>x y. x))"

definition
  absdiff :: "[i,i]\<Rightarrow>i"   (infixr "|-|" 65) where
  "a|-|b == (a-b) #+ (b-a)"

definition
  mult :: "[i,i]\<Rightarrow>i"   (infixr "#*" 70) where
  "a#*b == rec(a, 0, \<lambda>u v. b #+ v)"

definition
  mod :: "[i,i]\<Rightarrow>i"   (infixr "mod" 70) where
  "a mod b == rec(a, 0, %u v. rec(succ(v) |-| b, 0, %x y. succ(v)))"

definition
  div :: "[i,i]\<Rightarrow>i"   (infixr "div" 70) where
  "a div b == rec(a, 0, \<lambda>u v. rec(succ(u) mod b, succ(v), \<lambda>x y. v))"


notation (xsymbols)
  mult  (infixr "#\<times>" 70)

notation (HTML output)
  mult (infixr "#\<times>" 70)


lemmas arith_defs = add_def diff_def absdiff_def mult_def mod_def div_def


subsection {* Proofs about elementary arithmetic: addition, multiplication, etc. *}

(** Addition *)

(*typing of add: short and long versions*)

lemma add_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #+ b : N"
apply (unfold arith_defs)
apply typechk
done

lemma add_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a #+ b = c #+ d : N"
apply (unfold arith_defs)
apply equal
done


(*computation for add: 0 and successor cases*)

lemma addC0: "b:N \<Longrightarrow> 0 #+ b = b : N"
apply (unfold arith_defs)
apply rew
done

lemma addC_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> succ(a) #+ b = succ(a #+ b) : N"
apply (unfold arith_defs)
apply rew
done


(** Multiplication *)

(*typing of mult: short and long versions*)

lemma mult_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #* b : N"
apply (unfold arith_defs)
apply (typechk add_typing)
done

lemma mult_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a #* b = c #* d : N"
apply (unfold arith_defs)
apply (equal add_typingL)
done

(*computation for mult: 0 and successor cases*)

lemma multC0: "b:N \<Longrightarrow> 0 #* b = 0 : N"
apply (unfold arith_defs)
apply rew
done

lemma multC_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> succ(a) #* b = b #+ (a #* b) : N"
apply (unfold arith_defs)
apply rew
done


(** Difference *)

(*typing of difference*)

lemma diff_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a - b : N"
apply (unfold arith_defs)
apply typechk
done

lemma diff_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a - b = c - d : N"
apply (unfold arith_defs)
apply equal
done


(*computation for difference: 0 and successor cases*)

lemma diffC0: "a:N \<Longrightarrow> a - 0 = a : N"
apply (unfold arith_defs)
apply rew
done

(*Note: rec(a, 0, \<lambda>z w.z) is pred(a). *)

lemma diff_0_eq_0: "b:N \<Longrightarrow> 0 - b = 0 : N"
apply (unfold arith_defs)
apply (NE b)
apply hyp_rew
done


(*Essential to simplify FIRST!!  (Else we get a critical pair)
  succ(a) - succ(b) rewrites to   pred(succ(a) - b)  *)
lemma diff_succ_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> succ(a) - succ(b) = a - b : N"
apply (unfold arith_defs)
apply hyp_rew
apply (NE b)
apply hyp_rew
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
  val refl              = @{thm refl_elem}
  val sym               = @{thm sym_elem}
  val trans             = @{thm trans_elem}
  val refl_red          = @{thm refl_red}
  val trans_red         = @{thm trans_red}
  val red_if_equal      = @{thm red_if_equal}
  val default_rls       = @{thms arithC_rls} @ @{thms comp_rls}
  val routine_tac       = routine_tac (@{thms arith_typing_rls} @ @{thms routine_rls})
  end

structure Arith_simp = TSimpFun (Arith_simp_data)

local val congr_rls = @{thms congr_rls} in

fun arith_rew_tac ctxt prems = make_rew_tac ctxt
  (Arith_simp.norm_tac ctxt (congr_rls, prems))

fun hyp_arith_rew_tac ctxt prems = make_rew_tac ctxt
  (Arith_simp.cond_norm_tac ctxt (prove_cond_tac, congr_rls, prems))

end
*}

method_setup arith_rew = {*
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (arith_rew_tac ctxt ths))
*}

method_setup hyp_arith_rew = {*
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (hyp_arith_rew_tac ctxt ths))
*}


subsection {* Addition *}

(*Associative law for addition*)
lemma add_assoc: "\<lbrakk>a:N; b:N; c:N\<rbrakk> \<Longrightarrow> (a #+ b) #+ c = a #+ (b #+ c) : N"
apply (NE a)
apply hyp_arith_rew
done


(*Commutative law for addition.  Can be proved using three inductions.
  Must simplify after first induction!  Orientation of rewrites is delicate*)
lemma add_commute: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #+ b = b #+ a : N"
apply (NE a)
apply hyp_arith_rew
apply (rule sym_elem)
prefer 2
apply (NE b)
prefer 4
apply (NE b)
apply hyp_arith_rew
done


subsection {* Multiplication *}

(*right annihilation in product*)
lemma mult_0_right: "a:N \<Longrightarrow> a #* 0 = 0 : N"
apply (NE a)
apply hyp_arith_rew
done

(*right successor law for multiplication*)
lemma mult_succ_right: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #* succ(b) = a #+ (a #* b) : N"
apply (NE a)
apply (hyp_arith_rew add_assoc [THEN sym_elem])
apply (assumption | rule add_commute mult_typingL add_typingL intrL_rls refl_elem)+
done

(*Commutative law for multiplication*)
lemma mult_commute: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #* b = b #* a : N"
apply (NE a)
apply (hyp_arith_rew mult_0_right mult_succ_right)
done

(*addition distributes over multiplication*)
lemma add_mult_distrib: "\<lbrakk>a:N; b:N; c:N\<rbrakk> \<Longrightarrow> (a #+ b) #* c = (a #* c) #+ (b #* c) : N"
apply (NE a)
apply (hyp_arith_rew add_assoc [THEN sym_elem])
done

(*Associative law for multiplication*)
lemma mult_assoc: "\<lbrakk>a:N; b:N; c:N\<rbrakk> \<Longrightarrow> (a #* b) #* c = a #* (b #* c) : N"
apply (NE a)
apply (hyp_arith_rew add_mult_distrib)
done


subsection {* Difference *}

text {*
Difference on natural numbers, without negative numbers
  a - b = 0  iff  a<=b    a - b = succ(c) iff a>b   *}

lemma diff_self_eq_0: "a:N \<Longrightarrow> a - a = 0 : N"
apply (NE a)
apply hyp_arith_rew
done


lemma add_0_right: "\<lbrakk>c : N; 0 : N; c : N\<rbrakk> \<Longrightarrow> c #+ 0 = c : N"
  by (rule addC0 [THEN [3] add_commute [THEN trans_elem]])

(*Addition is the inverse of subtraction: if b<=x then b#+(x-b) = x.
  An example of induction over a quantified formula (a product).
  Uses rewriting with a quantified, implicative inductive hypothesis.*)
schematic_lemma add_diff_inverse_lemma:
  "b:N \<Longrightarrow> ?a : PROD x:N. Eq(N, b-x, 0) --> Eq(N, b #+ (x-b), x)"
apply (NE b)
(*strip one "universal quantifier" but not the "implication"*)
apply (rule_tac [3] intr_rls)
(*case analysis on x in
    (succ(u) <= x) --> (succ(u)#+(x-succ(u)) = x) *)
prefer 4
apply (NE x)
apply assumption
(*Prepare for simplification of types -- the antecedent succ(u)<=x *)
apply (rule_tac [2] replace_type)
apply (rule_tac [1] replace_type)
apply arith_rew
(*Solves first 0 goal, simplifies others.  Two sugbgoals remain.
  Both follow by rewriting, (2) using quantified induction hyp*)
apply intr (*strips remaining PRODs*)
apply (hyp_arith_rew add_0_right)
apply assumption
done


(*Version of above with premise   b-a=0   i.e.    a >= b.
  Using ProdE does not work -- for ?B(?a) is ambiguous.
  Instead, add_diff_inverse_lemma states the desired induction scheme
    the use of RS below instantiates Vars in ProdE automatically. *)
lemma add_diff_inverse: "\<lbrakk>a:N; b:N; b - a = 0 : N\<rbrakk> \<Longrightarrow> b #+ (a-b) = a : N"
apply (rule EqE)
apply (rule add_diff_inverse_lemma [THEN ProdE, THEN ProdE])
apply (assumption | rule EqI)+
done


subsection {* Absolute difference *}

(*typing of absolute difference: short and long versions*)

lemma absdiff_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a |-| b : N"
apply (unfold arith_defs)
apply typechk
done

lemma absdiff_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a |-| b = c |-| d : N"
apply (unfold arith_defs)
apply equal
done

lemma absdiff_self_eq_0: "a:N \<Longrightarrow> a |-| a = 0 : N"
apply (unfold absdiff_def)
apply (arith_rew diff_self_eq_0)
done

lemma absdiffC0: "a:N \<Longrightarrow> 0 |-| a = a : N"
apply (unfold absdiff_def)
apply hyp_arith_rew
done


lemma absdiff_succ_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> succ(a) |-| succ(b)  =  a |-| b : N"
apply (unfold absdiff_def)
apply hyp_arith_rew
done

(*Note how easy using commutative laws can be?  ...not always... *)
lemma absdiff_commute: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a |-| b = b |-| a : N"
apply (unfold absdiff_def)
apply (rule add_commute)
apply (typechk diff_typing)
done

(*If a+b=0 then a=0.   Surprisingly tedious*)
schematic_lemma add_eq0_lemma: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> ?c : PROD u: Eq(N,a#+b,0) .  Eq(N,a,0)"
apply (NE a)
apply (rule_tac [3] replace_type)
apply arith_rew
apply intr (*strips remaining PRODs*)
apply (rule_tac [2] zero_ne_succ [THEN FE])
apply (erule_tac [3] EqE [THEN sym_elem])
apply (typechk add_typing)
done

(*Version of above with the premise  a+b=0.
  Again, resolution instantiates variables in ProdE *)
lemma add_eq0: "\<lbrakk>a:N; b:N; a #+ b = 0 : N\<rbrakk> \<Longrightarrow> a = 0 : N"
apply (rule EqE)
apply (rule add_eq0_lemma [THEN ProdE])
apply (rule_tac [3] EqI)
apply typechk
done

(*Here is a lemma to infer a-b=0 and b-a=0 from a|-|b=0, below. *)
schematic_lemma absdiff_eq0_lem:
  "\<lbrakk>a:N; b:N; a |-| b = 0 : N\<rbrakk> \<Longrightarrow> ?a : SUM v: Eq(N, a-b, 0) . Eq(N, b-a, 0)"
apply (unfold absdiff_def)
apply intr
apply eqintr
apply (rule_tac [2] add_eq0)
apply (rule add_eq0)
apply (rule_tac [6] add_commute [THEN trans_elem])
apply (typechk diff_typing)
done

(*if  a |-| b = 0  then  a = b
  proof: a-b=0 and b-a=0, so b = a+(b-a) = a+0 = a*)
lemma absdiff_eq0: "\<lbrakk>a |-| b = 0 : N; a:N; b:N\<rbrakk> \<Longrightarrow> a = b : N"
apply (rule EqE)
apply (rule absdiff_eq0_lem [THEN SumE])
apply eqintr
apply (rule add_diff_inverse [THEN sym_elem, THEN trans_elem])
apply (erule_tac [3] EqE)
apply (hyp_arith_rew add_0_right)
done


subsection {* Remainder and Quotient *}

(*typing of remainder: short and long versions*)

lemma mod_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a mod b : N"
apply (unfold mod_def)
apply (typechk absdiff_typing)
done

lemma mod_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a mod b = c mod d : N"
apply (unfold mod_def)
apply (equal absdiff_typingL)
done


(*computation for  mod : 0 and successor cases*)

lemma modC0: "b:N \<Longrightarrow> 0 mod b = 0 : N"
apply (unfold mod_def)
apply (rew absdiff_typing)
done

lemma modC_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow>
  succ(a) mod b = rec(succ(a mod b) |-| b, 0, \<lambda>x y. succ(a mod b)) : N"
apply (unfold mod_def)
apply (rew absdiff_typing)
done


(*typing of quotient: short and long versions*)

lemma div_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a div b : N"
apply (unfold div_def)
apply (typechk absdiff_typing mod_typing)
done

lemma div_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a div b = c div d : N"
apply (unfold div_def)
apply (equal absdiff_typingL mod_typingL)
done

lemmas div_typing_rls = mod_typing div_typing absdiff_typing


(*computation for quotient: 0 and successor cases*)

lemma divC0: "b:N \<Longrightarrow> 0 div b = 0 : N"
apply (unfold div_def)
apply (rew mod_typing absdiff_typing)
done

lemma divC_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow>
  succ(a) div b = rec(succ(a) mod b, succ(a div b), \<lambda>x y. a div b) : N"
apply (unfold div_def)
apply (rew mod_typing)
done


(*Version of above with same condition as the  mod  one*)
lemma divC_succ2: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow>
  succ(a) div b =rec(succ(a mod b) |-| b, succ(a div b), \<lambda>x y. a div b) : N"
apply (rule divC_succ [THEN trans_elem])
apply (rew div_typing_rls modC_succ)
apply (NE "succ (a mod b) |-|b")
apply (rew mod_typing div_typing absdiff_typing)
done

(*for case analysis on whether a number is 0 or a successor*)
lemma iszero_decidable: "a:N \<Longrightarrow> rec(a, inl(eq), \<lambda>ka kb. inr(<ka, eq>)) :
                      Eq(N,a,0) + (SUM x:N. Eq(N,a, succ(x)))"
apply (NE a)
apply (rule_tac [3] PlusI_inr)
apply (rule_tac [2] PlusI_inl)
apply eqintr
apply equal
done

(*Main Result.  Holds when b is 0 since   a mod 0 = a     and    a div 0 = 0  *)
lemma mod_div_equality: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a mod b #+ (a div b) #* b = a : N"
apply (NE a)
apply (arith_rew div_typing_rls modC0 modC_succ divC0 divC_succ2)
apply (rule EqE)
(*case analysis on   succ(u mod b)|-|b  *)
apply (rule_tac a1 = "succ (u mod b) |-| b" in iszero_decidable [THEN PlusE])
apply (erule_tac [3] SumE)
apply (hyp_arith_rew div_typing_rls modC0 modC_succ divC0 divC_succ2)
(*Replace one occurrence of  b  by succ(u mod b).  Clumsy!*)
apply (rule add_typingL [THEN trans_elem])
apply (erule EqE [THEN absdiff_eq0, THEN sym_elem])
apply (rule_tac [3] refl_elem)
apply (hyp_arith_rew div_typing_rls)
done

end
