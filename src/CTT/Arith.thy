(*  Title:      CTT/Arith.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>Elementary arithmetic\<close>

theory Arith
  imports Bool
begin

subsection \<open>Arithmetic operators and their definitions\<close>

definition add :: "[i,i]\<Rightarrow>i"   (infixr "#+" 65)
  where "a#+b \<equiv> rec(a, b, \<lambda>u v. succ(v))"

definition diff :: "[i,i]\<Rightarrow>i"   (infixr "-" 65)
  where "a-b \<equiv> rec(b, a, \<lambda>u v. rec(v, 0, \<lambda>x y. x))"

definition absdiff :: "[i,i]\<Rightarrow>i"   (infixr "|-|" 65)
  where "a|-|b \<equiv> (a-b) #+ (b-a)"

definition mult :: "[i,i]\<Rightarrow>i"   (infixr "#*" 70)
  where "a#*b \<equiv> rec(a, 0, \<lambda>u v. b #+ v)"

definition mod :: "[i,i]\<Rightarrow>i"   (infixr "mod" 70)
  where "a mod b \<equiv> rec(a, 0, \<lambda>u v. rec(succ(v) |-| b, 0, \<lambda>x y. succ(v)))"

definition div :: "[i,i]\<Rightarrow>i"   (infixr "div" 70)
  where "a div b \<equiv> rec(a, 0, \<lambda>u v. rec(succ(u) mod b, succ(v), \<lambda>x y. v))"

lemmas arith_defs = add_def diff_def absdiff_def mult_def mod_def div_def


subsection \<open>Proofs about elementary arithmetic: addition, multiplication, etc.\<close>

subsubsection \<open>Addition\<close>

text \<open>Typing of \<open>add\<close>: short and long versions.\<close>

lemma add_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #+ b : N"
  unfolding arith_defs by typechk

lemma add_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a #+ b = c #+ d : N"
  unfolding arith_defs by equal


text \<open>Computation for \<open>add\<close>: 0 and successor cases.\<close>

lemma addC0: "b:N \<Longrightarrow> 0 #+ b = b : N"
  unfolding arith_defs by rew

lemma addC_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> succ(a) #+ b = succ(a #+ b) : N"
  unfolding arith_defs by rew


subsubsection \<open>Multiplication\<close>

text \<open>Typing of \<open>mult\<close>: short and long versions.\<close>

lemma mult_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #* b : N"
  unfolding arith_defs by (typechk add_typing)

lemma mult_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a #* b = c #* d : N"
  unfolding arith_defs by (equal add_typingL)


text \<open>Computation for \<open>mult\<close>: 0 and successor cases.\<close>

lemma multC0: "b:N \<Longrightarrow> 0 #* b = 0 : N"
  unfolding arith_defs by rew

lemma multC_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> succ(a) #* b = b #+ (a #* b) : N"
  unfolding arith_defs by rew


subsubsection \<open>Difference\<close>

text \<open>Typing of difference.\<close>

lemma diff_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a - b : N"
  unfolding arith_defs by typechk

lemma diff_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a - b = c - d : N"
  unfolding arith_defs by equal


text \<open>Computation for difference: 0 and successor cases.\<close>

lemma diffC0: "a:N \<Longrightarrow> a - 0 = a : N"
  unfolding arith_defs by rew

text \<open>Note: \<open>rec(a, 0, \<lambda>z w.z)\<close> is \<open>pred(a).\<close>\<close>

lemma diff_0_eq_0: "b:N \<Longrightarrow> 0 - b = 0 : N"
  unfolding arith_defs
  apply (NE b)
    apply hyp_rew
  done

text \<open>
  Essential to simplify FIRST!!  (Else we get a critical pair)
  \<open>succ(a) - succ(b)\<close> rewrites to \<open>pred(succ(a) - b)\<close>.
\<close>
lemma diff_succ_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> succ(a) - succ(b) = a - b : N"
  unfolding arith_defs
  apply hyp_rew
  apply (NE b)
    apply hyp_rew
  done


subsection \<open>Simplification\<close>

lemmas arith_typing_rls = add_typing mult_typing diff_typing
  and arith_congr_rls = add_typingL mult_typingL diff_typingL

lemmas congr_rls = arith_congr_rls intrL2_rls elimL_rls

lemmas arithC_rls =
  addC0 addC_succ
  multC0 multC_succ
  diffC0 diff_0_eq_0 diff_succ_succ

ML \<open>
  structure Arith_simp = TSimpFun(
    val refl = @{thm refl_elem}
    val sym = @{thm sym_elem}
    val trans = @{thm trans_elem}
    val refl_red = @{thm refl_red}
    val trans_red = @{thm trans_red}
    val red_if_equal = @{thm red_if_equal}
    val default_rls = @{thms arithC_rls comp_rls}
    val routine_tac = routine_tac @{thms arith_typing_rls routine_rls}
  )

  fun arith_rew_tac ctxt prems =
    make_rew_tac ctxt (Arith_simp.norm_tac ctxt (@{thms congr_rls}, prems))

  fun hyp_arith_rew_tac ctxt prems =
    make_rew_tac ctxt
      (Arith_simp.cond_norm_tac ctxt (prove_cond_tac ctxt, @{thms congr_rls}, prems))
\<close>

method_setup arith_rew = \<open>
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (arith_rew_tac ctxt ths))
\<close>

method_setup hyp_arith_rew = \<open>
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (hyp_arith_rew_tac ctxt ths))
\<close>


subsection \<open>Addition\<close>

text \<open>Associative law for addition.\<close>
lemma add_assoc: "\<lbrakk>a:N; b:N; c:N\<rbrakk> \<Longrightarrow> (a #+ b) #+ c = a #+ (b #+ c) : N"
  apply (NE a)
    apply hyp_arith_rew
  done

text \<open>Commutative law for addition.  Can be proved using three inductions.
  Must simplify after first induction!  Orientation of rewrites is delicate.\<close>
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


subsection \<open>Multiplication\<close>

text \<open>Right annihilation in product.\<close>
lemma mult_0_right: "a:N \<Longrightarrow> a #* 0 = 0 : N"
  apply (NE a)
    apply hyp_arith_rew
  done

text \<open>Right successor law for multiplication.\<close>
lemma mult_succ_right: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #* succ(b) = a #+ (a #* b) : N"
  apply (NE a)
    apply (hyp_arith_rew add_assoc [THEN sym_elem])
  apply (assumption | rule add_commute mult_typingL add_typingL intrL_rls refl_elem)+
  done

text \<open>Commutative law for multiplication.\<close>
lemma mult_commute: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a #* b = b #* a : N"
  apply (NE a)
    apply (hyp_arith_rew mult_0_right mult_succ_right)
  done

text \<open>Addition distributes over multiplication.\<close>
lemma add_mult_distrib: "\<lbrakk>a:N; b:N; c:N\<rbrakk> \<Longrightarrow> (a #+ b) #* c = (a #* c) #+ (b #* c) : N"
  apply (NE a)
    apply (hyp_arith_rew add_assoc [THEN sym_elem])
  done

text \<open>Associative law for multiplication.\<close>
lemma mult_assoc: "\<lbrakk>a:N; b:N; c:N\<rbrakk> \<Longrightarrow> (a #* b) #* c = a #* (b #* c) : N"
  apply (NE a)
    apply (hyp_arith_rew add_mult_distrib)
  done


subsection \<open>Difference\<close>

text \<open>
  Difference on natural numbers, without negative numbers
  \<^item> \<open>a - b = 0\<close>  iff  \<open>a \<le> b\<close>
  \<^item> \<open>a - b = succ(c)\<close> iff \<open>a > b\<close>
\<close>

lemma diff_self_eq_0: "a:N \<Longrightarrow> a - a = 0 : N"
  apply (NE a)
    apply hyp_arith_rew
  done


lemma add_0_right: "\<lbrakk>c : N; 0 : N; c : N\<rbrakk> \<Longrightarrow> c #+ 0 = c : N"
  by (rule addC0 [THEN [3] add_commute [THEN trans_elem]])

text \<open>
  Addition is the inverse of subtraction: if \<open>b \<le> x\<close> then \<open>b #+ (x - b) = x\<close>.
  An example of induction over a quantified formula (a product).
  Uses rewriting with a quantified, implicative inductive hypothesis.
\<close>
schematic_goal add_diff_inverse_lemma:
  "b:N \<Longrightarrow> ?a : \<Prod>x:N. Eq(N, b-x, 0) \<longrightarrow> Eq(N, b #+ (x-b), x)"
  apply (NE b)
    \<comment> \<open>strip one "universal quantifier" but not the "implication"\<close>
    apply (rule_tac [3] intr_rls)
    \<comment> \<open>case analysis on \<open>x\<close> in \<open>succ(u) \<le> x \<longrightarrow> succ(u) #+ (x - succ(u)) = x\<close>\<close>
     prefer 4
     apply (NE x)
       apply assumption
    \<comment> \<open>Prepare for simplification of types -- the antecedent \<open>succ(u) \<le> x\<close>\<close>
      apply (rule_tac [2] replace_type)
       apply (rule_tac [1] replace_type)
        apply arith_rew
    \<comment> \<open>Solves first 0 goal, simplifies others.  Two sugbgoals remain.
    Both follow by rewriting, (2) using quantified induction hyp.\<close>
   apply intr \<comment> \<open>strips remaining \<open>\<Prod>\<close>s\<close>
    apply (hyp_arith_rew add_0_right)
  apply assumption
  done

text \<open>
  Version of above with premise \<open>b - a = 0\<close> i.e. \<open>a \<ge> b\<close>.
  Using @{thm ProdE} does not work -- for \<open>?B(?a)\<close> is ambiguous.
  Instead, @{thm add_diff_inverse_lemma} states the desired induction scheme;
  the use of \<open>THEN\<close> below instantiates Vars in @{thm ProdE} automatically.
\<close>
lemma add_diff_inverse: "\<lbrakk>a:N; b:N; b - a = 0 : N\<rbrakk> \<Longrightarrow> b #+ (a-b) = a : N"
  apply (rule EqE)
  apply (rule add_diff_inverse_lemma [THEN ProdE, THEN ProdE])
    apply (assumption | rule EqI)+
  done


subsection \<open>Absolute difference\<close>

text \<open>Typing of absolute difference: short and long versions.\<close>

lemma absdiff_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a |-| b : N"
  unfolding arith_defs by typechk

lemma absdiff_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a |-| b = c |-| d : N"
  unfolding arith_defs by equal

lemma absdiff_self_eq_0: "a:N \<Longrightarrow> a |-| a = 0 : N"
  unfolding absdiff_def by (arith_rew diff_self_eq_0)

lemma absdiffC0: "a:N \<Longrightarrow> 0 |-| a = a : N"
  unfolding absdiff_def by hyp_arith_rew

lemma absdiff_succ_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> succ(a) |-| succ(b)  =  a |-| b : N"
  unfolding absdiff_def by hyp_arith_rew

text \<open>Note how easy using commutative laws can be?  ...not always...\<close>
lemma absdiff_commute: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a |-| b = b |-| a : N"
  unfolding absdiff_def
  apply (rule add_commute)
   apply (typechk diff_typing)
  done

text \<open>If \<open>a + b = 0\<close> then \<open>a = 0\<close>. Surprisingly tedious.\<close>
schematic_goal add_eq0_lemma: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> ?c : Eq(N,a#+b,0) \<longrightarrow> Eq(N,a,0)"
  apply (NE a)
    apply (rule_tac [3] replace_type)
     apply arith_rew
  apply intr  \<comment> \<open>strips remaining \<open>\<Prod>\<close>s\<close>
   apply (rule_tac [2] zero_ne_succ [THEN FE])
     apply (erule_tac [3] EqE [THEN sym_elem])
    apply (typechk add_typing)
  done

text \<open>
  Version of above with the premise \<open>a + b = 0\<close>.
  Again, resolution instantiates variables in @{thm ProdE}.
\<close>
lemma add_eq0: "\<lbrakk>a:N; b:N; a #+ b = 0 : N\<rbrakk> \<Longrightarrow> a = 0 : N"
  apply (rule EqE)
  apply (rule add_eq0_lemma [THEN ProdE])
    apply (rule_tac [3] EqI)
    apply typechk
  done

text \<open>Here is a lemma to infer \<open>a - b = 0\<close> and \<open>b - a = 0\<close> from \<open>a |-| b = 0\<close>, below.\<close>
schematic_goal absdiff_eq0_lem:
  "\<lbrakk>a:N; b:N; a |-| b = 0 : N\<rbrakk> \<Longrightarrow> ?a : Eq(N, a-b, 0) \<times> Eq(N, b-a, 0)"
  apply (unfold absdiff_def)
  apply intr
   apply eqintr
   apply (rule_tac [2] add_eq0)
     apply (rule add_eq0)
       apply (rule_tac [6] add_commute [THEN trans_elem])
         apply (typechk diff_typing)
  done

text \<open>If \<open>a |-| b = 0\<close> then \<open>a = b\<close>
  proof: \<open>a - b = 0\<close> and \<open>b - a = 0\<close>, so \<open>b = a + (b - a) = a + 0 = a\<close>.
\<close>
lemma absdiff_eq0: "\<lbrakk>a |-| b = 0 : N; a:N; b:N\<rbrakk> \<Longrightarrow> a = b : N"
  apply (rule EqE)
  apply (rule absdiff_eq0_lem [THEN SumE])
     apply eqintr
  apply (rule add_diff_inverse [THEN sym_elem, THEN trans_elem])
     apply (erule_tac [3] EqE)
    apply (hyp_arith_rew add_0_right)
  done


subsection \<open>Remainder and Quotient\<close>

text \<open>Typing of remainder: short and long versions.\<close>

lemma mod_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a mod b : N"
  unfolding mod_def by (typechk absdiff_typing)

lemma mod_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a mod b = c mod d : N"
  unfolding mod_def by (equal absdiff_typingL)


text \<open>Computation for \<open>mod\<close>: 0 and successor cases.\<close>

lemma modC0: "b:N \<Longrightarrow> 0 mod b = 0 : N"
  unfolding mod_def by (rew absdiff_typing)

lemma modC_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow>
  succ(a) mod b = rec(succ(a mod b) |-| b, 0, \<lambda>x y. succ(a mod b)) : N"
  unfolding mod_def by (rew absdiff_typing)


text \<open>Typing of quotient: short and long versions.\<close>

lemma div_typing: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a div b : N"
  unfolding div_def by (typechk absdiff_typing mod_typing)

lemma div_typingL: "\<lbrakk>a = c:N; b = d:N\<rbrakk> \<Longrightarrow> a div b = c div d : N"
  unfolding div_def by (equal absdiff_typingL mod_typingL)

lemmas div_typing_rls = mod_typing div_typing absdiff_typing


text \<open>Computation for quotient: 0 and successor cases.\<close>

lemma divC0: "b:N \<Longrightarrow> 0 div b = 0 : N"
  unfolding div_def by (rew mod_typing absdiff_typing)

lemma divC_succ: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow>
  succ(a) div b = rec(succ(a) mod b, succ(a div b), \<lambda>x y. a div b) : N"
  unfolding div_def by (rew mod_typing)


text \<open>Version of above with same condition as the \<open>mod\<close> one.\<close>
lemma divC_succ2: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow>
  succ(a) div b =rec(succ(a mod b) |-| b, succ(a div b), \<lambda>x y. a div b) : N"
  apply (rule divC_succ [THEN trans_elem])
    apply (rew div_typing_rls modC_succ)
  apply (NE "succ (a mod b) |-|b")
    apply (rew mod_typing div_typing absdiff_typing)
  done

text \<open>For case analysis on whether a number is 0 or a successor.\<close>
lemma iszero_decidable: "a:N \<Longrightarrow> rec(a, inl(eq), \<lambda>ka kb. inr(<ka, eq>)) :
  Eq(N,a,0) + (\<Sum>x:N. Eq(N,a, succ(x)))"
  apply (NE a)
    apply (rule_tac [3] PlusI_inr)
     apply (rule_tac [2] PlusI_inl)
      apply eqintr
     apply equal
  done

text \<open>Main Result. Holds when \<open>b\<close> is 0 since \<open>a mod 0 = a\<close> and \<open>a div 0 = 0\<close>.\<close>
lemma mod_div_equality: "\<lbrakk>a:N; b:N\<rbrakk> \<Longrightarrow> a mod b #+ (a div b) #* b = a : N"
  apply (NE a)
    apply (arith_rew div_typing_rls modC0 modC_succ divC0 divC_succ2)
  apply (rule EqE)
    \<comment> \<open>case analysis on \<open>succ(u mod b) |-| b\<close>\<close>
  apply (rule_tac a1 = "succ (u mod b) |-| b" in iszero_decidable [THEN PlusE])
    apply (erule_tac [3] SumE)
    apply (hyp_arith_rew div_typing_rls modC0 modC_succ divC0 divC_succ2)
    \<comment> \<open>Replace one occurrence of \<open>b\<close> by \<open>succ(u mod b)\<close>. Clumsy!\<close>
  apply (rule add_typingL [THEN trans_elem])
    apply (erule EqE [THEN absdiff_eq0, THEN sym_elem])
     apply (rule_tac [3] refl_elem)
     apply (hyp_arith_rew div_typing_rls)
  done

end
