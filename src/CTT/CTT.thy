(*  Title:      CTT/CTT.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Constructive Type Theory\<close>

theory CTT
imports Pure
begin

ML_file "~~/src/Provers/typedsimp.ML"
setup Pure_Thy.old_appl_syntax_setup

typedecl i
typedecl t
typedecl o

consts
  \<comment> \<open>Types\<close>
  F         :: "t"
  T         :: "t"          \<comment> \<open>\<open>F\<close> is empty, \<open>T\<close> contains one element\<close>
  contr     :: "i\<Rightarrow>i"
  tt        :: "i"
  \<comment> \<open>Natural numbers\<close>
  N         :: "t"
  succ      :: "i\<Rightarrow>i"
  rec       :: "[i, i, [i,i]\<Rightarrow>i] \<Rightarrow> i"
  \<comment> \<open>Unions\<close>
  inl       :: "i\<Rightarrow>i"
  inr       :: "i\<Rightarrow>i"
  "when"    :: "[i, i\<Rightarrow>i, i\<Rightarrow>i]\<Rightarrow>i"
  \<comment> \<open>General Sum and Binary Product\<close>
  Sum       :: "[t, i\<Rightarrow>t]\<Rightarrow>t"
  fst       :: "i\<Rightarrow>i"
  snd       :: "i\<Rightarrow>i"
  split     :: "[i, [i,i]\<Rightarrow>i] \<Rightarrow>i"
  \<comment> \<open>General Product and Function Space\<close>
  Prod      :: "[t, i\<Rightarrow>t]\<Rightarrow>t"
  \<comment> \<open>Types\<close>
  Plus      :: "[t,t]\<Rightarrow>t"           (infixr "+" 40)
  \<comment> \<open>Equality type\<close>
  Eq        :: "[t,i,i]\<Rightarrow>t"
  eq        :: "i"
  \<comment> \<open>Judgements\<close>
  Type      :: "t \<Rightarrow> prop"          ("(_ type)" [10] 5)
  Eqtype    :: "[t,t]\<Rightarrow>prop"        ("(_ =/ _)" [10,10] 5)
  Elem      :: "[i, t]\<Rightarrow>prop"       ("(_ /: _)" [10,10] 5)
  Eqelem    :: "[i,i,t]\<Rightarrow>prop"      ("(_ =/ _ :/ _)" [10,10,10] 5)
  Reduce    :: "[i,i]\<Rightarrow>prop"        ("Reduce[_,_]")

  \<comment> \<open>Types\<close>

  \<comment> \<open>Functions\<close>
  lambda    :: "(i \<Rightarrow> i) \<Rightarrow> i"      (binder "\<^bold>\<lambda>" 10)
  app       :: "[i,i]\<Rightarrow>i"           (infixl "`" 60)
  \<comment> \<open>Natural numbers\<close>
  Zero      :: "i"                  ("0")
  \<comment> \<open>Pairing\<close>
  pair      :: "[i,i]\<Rightarrow>i"           ("(1<_,/_>)")

syntax
  "_PROD"   :: "[idt,t,t]\<Rightarrow>t"       ("(3\<Prod>_:_./ _)" 10)
  "_SUM"    :: "[idt,t,t]\<Rightarrow>t"       ("(3\<Sum>_:_./ _)" 10)
translations
  "\<Prod>x:A. B" \<rightleftharpoons> "CONST Prod(A, \<lambda>x. B)"
  "\<Sum>x:A. B" \<rightleftharpoons> "CONST Sum(A, \<lambda>x. B)"

abbreviation Arrow :: "[t,t]\<Rightarrow>t"  (infixr "\<longrightarrow>" 30)
  where "A \<longrightarrow> B \<equiv> \<Prod>_:A. B"

abbreviation Times :: "[t,t]\<Rightarrow>t"  (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_:A. B"

text \<open>
  Reduction: a weaker notion than equality;  a hack for simplification.
  \<open>Reduce[a,b]\<close> means either that \<open>a = b : A\<close> for some \<open>A\<close> or else
    that \<open>a\<close> and \<open>b\<close> are textually identical.

  Does not verify \<open>a:A\<close>!  Sound because only \<open>trans_red\<close> uses a \<open>Reduce\<close>
  premise. No new theorems can be proved about the standard judgements.
\<close>
axiomatization
where
  refl_red: "\<And>a. Reduce[a,a]" and
  red_if_equal: "\<And>a b A. a = b : A \<Longrightarrow> Reduce[a,b]" and
  trans_red: "\<And>a b c A. \<lbrakk>a = b : A; Reduce[b,c]\<rbrakk> \<Longrightarrow> a = c : A" and

  \<comment> \<open>Reflexivity\<close>

  refl_type: "\<And>A. A type \<Longrightarrow> A = A" and
  refl_elem: "\<And>a A. a : A \<Longrightarrow> a = a : A" and

  \<comment> \<open>Symmetry\<close>

  sym_type:  "\<And>A B. A = B \<Longrightarrow> B = A" and
  sym_elem:  "\<And>a b A. a = b : A \<Longrightarrow> b = a : A" and

  \<comment> \<open>Transitivity\<close>

  trans_type:   "\<And>A B C. \<lbrakk>A = B; B = C\<rbrakk> \<Longrightarrow> A = C" and
  trans_elem:   "\<And>a b c A. \<lbrakk>a = b : A; b = c : A\<rbrakk> \<Longrightarrow> a = c : A" and

  equal_types:  "\<And>a A B. \<lbrakk>a : A; A = B\<rbrakk> \<Longrightarrow> a : B" and
  equal_typesL: "\<And>a b A B. \<lbrakk>a = b : A; A = B\<rbrakk> \<Longrightarrow> a = b : B" and

  \<comment> \<open>Substitution\<close>

  subst_type:   "\<And>a A B. \<lbrakk>a : A; \<And>z. z:A \<Longrightarrow> B(z) type\<rbrakk> \<Longrightarrow> B(a) type" and
  subst_typeL:  "\<And>a c A B D. \<lbrakk>a = c : A; \<And>z. z:A \<Longrightarrow> B(z) = D(z)\<rbrakk> \<Longrightarrow> B(a) = D(c)" and

  subst_elem:   "\<And>a b A B. \<lbrakk>a : A; \<And>z. z:A \<Longrightarrow> b(z):B(z)\<rbrakk> \<Longrightarrow> b(a):B(a)" and
  subst_elemL:
    "\<And>a b c d A B. \<lbrakk>a = c : A; \<And>z. z:A \<Longrightarrow> b(z)=d(z) : B(z)\<rbrakk> \<Longrightarrow> b(a)=d(c) : B(a)" and


  \<comment> \<open>The type \<open>N\<close> -- natural numbers\<close>

  NF: "N type" and
  NI0: "0 : N" and
  NI_succ: "\<And>a. a : N \<Longrightarrow> succ(a) : N" and
  NI_succL:  "\<And>a b. a = b : N \<Longrightarrow> succ(a) = succ(b) : N" and

  NE:
   "\<And>p a b C. \<lbrakk>p: N; a: C(0); \<And>u v. \<lbrakk>u: N; v: C(u)\<rbrakk> \<Longrightarrow> b(u,v): C(succ(u))\<rbrakk>
   \<Longrightarrow> rec(p, a, \<lambda>u v. b(u,v)) : C(p)" and

  NEL:
   "\<And>p q a b c d C. \<lbrakk>p = q : N; a = c : C(0);
      \<And>u v. \<lbrakk>u: N; v: C(u)\<rbrakk> \<Longrightarrow> b(u,v) = d(u,v): C(succ(u))\<rbrakk>
   \<Longrightarrow> rec(p, a, \<lambda>u v. b(u,v)) = rec(q,c,d) : C(p)" and

  NC0:
   "\<And>a b C. \<lbrakk>a: C(0); \<And>u v. \<lbrakk>u: N; v: C(u)\<rbrakk> \<Longrightarrow> b(u,v): C(succ(u))\<rbrakk>
   \<Longrightarrow> rec(0, a, \<lambda>u v. b(u,v)) = a : C(0)" and

  NC_succ:
   "\<And>p a b C. \<lbrakk>p: N;  a: C(0); \<And>u v. \<lbrakk>u: N; v: C(u)\<rbrakk> \<Longrightarrow> b(u,v): C(succ(u))\<rbrakk> \<Longrightarrow>
   rec(succ(p), a, \<lambda>u v. b(u,v)) = b(p, rec(p, a, \<lambda>u v. b(u,v))) : C(succ(p))" and

  \<comment> \<open>The fourth Peano axiom.  See page 91 of Martin-Löf's book.\<close>
  zero_ne_succ: "\<And>a. \<lbrakk>a: N; 0 = succ(a) : N\<rbrakk> \<Longrightarrow> 0: F" and


  \<comment> \<open>The Product of a family of types\<close>

  ProdF: "\<And>A B. \<lbrakk>A type; \<And>x. x:A \<Longrightarrow> B(x) type\<rbrakk> \<Longrightarrow> \<Prod>x:A. B(x) type" and

  ProdFL:
    "\<And>A B C D. \<lbrakk>A = C; \<And>x. x:A \<Longrightarrow> B(x) = D(x)\<rbrakk> \<Longrightarrow> \<Prod>x:A. B(x) = \<Prod>x:C. D(x)" and

  ProdI:
    "\<And>b A B. \<lbrakk>A type; \<And>x. x:A \<Longrightarrow> b(x):B(x)\<rbrakk> \<Longrightarrow> \<^bold>\<lambda>x. b(x) : \<Prod>x:A. B(x)" and

  ProdIL: "\<And>b c A B. \<lbrakk>A type; \<And>x. x:A \<Longrightarrow> b(x) = c(x) : B(x)\<rbrakk> \<Longrightarrow>
    \<^bold>\<lambda>x. b(x) = \<^bold>\<lambda>x. c(x) : \<Prod>x:A. B(x)" and

  ProdE:  "\<And>p a A B. \<lbrakk>p : \<Prod>x:A. B(x); a : A\<rbrakk> \<Longrightarrow> p`a : B(a)" and
  ProdEL: "\<And>p q a b A B. \<lbrakk>p = q: \<Prod>x:A. B(x); a = b : A\<rbrakk> \<Longrightarrow> p`a = q`b : B(a)" and

  ProdC: "\<And>a b A B. \<lbrakk>a : A; \<And>x. x:A \<Longrightarrow> b(x) : B(x)\<rbrakk> \<Longrightarrow> (\<^bold>\<lambda>x. b(x)) ` a = b(a) : B(a)" and

  ProdC2: "\<And>p A B. p : \<Prod>x:A. B(x) \<Longrightarrow> (\<^bold>\<lambda>x. p`x) = p : \<Prod>x:A. B(x)" and


  \<comment> \<open>The Sum of a family of types\<close>

  SumF:  "\<And>A B. \<lbrakk>A type; \<And>x. x:A \<Longrightarrow> B(x) type\<rbrakk> \<Longrightarrow> \<Sum>x:A. B(x) type" and
  SumFL: "\<And>A B C D. \<lbrakk>A = C; \<And>x. x:A \<Longrightarrow> B(x) = D(x)\<rbrakk> \<Longrightarrow> \<Sum>x:A. B(x) = \<Sum>x:C. D(x)" and

  SumI:  "\<And>a b A B. \<lbrakk>a : A; b : B(a)\<rbrakk> \<Longrightarrow> <a,b> : \<Sum>x:A. B(x)" and
  SumIL: "\<And>a b c d A B. \<lbrakk> a = c : A; b = d : B(a)\<rbrakk> \<Longrightarrow> <a,b> = <c,d> : \<Sum>x:A. B(x)" and

  SumE: "\<And>p c A B C. \<lbrakk>p: \<Sum>x:A. B(x); \<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> c(x,y): C(<x,y>)\<rbrakk>
    \<Longrightarrow> split(p, \<lambda>x y. c(x,y)) : C(p)" and

  SumEL: "\<And>p q c d A B C. \<lbrakk>p = q : \<Sum>x:A. B(x);
      \<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> c(x,y)=d(x,y): C(<x,y>)\<rbrakk>
    \<Longrightarrow> split(p, \<lambda>x y. c(x,y)) = split(q, \<lambda>x y. d(x,y)) : C(p)" and

  SumC: "\<And>a b c A B C. \<lbrakk>a: A;  b: B(a); \<And>x y. \<lbrakk>x:A; y:B(x)\<rbrakk> \<Longrightarrow> c(x,y): C(<x,y>)\<rbrakk>
    \<Longrightarrow> split(<a,b>, \<lambda>x y. c(x,y)) = c(a,b) : C(<a,b>)" and

  fst_def:   "\<And>a. fst(a) \<equiv> split(a, \<lambda>x y. x)" and
  snd_def:   "\<And>a. snd(a) \<equiv> split(a, \<lambda>x y. y)" and


  \<comment> \<open>The sum of two types\<close>

  PlusF: "\<And>A B. \<lbrakk>A type; B type\<rbrakk> \<Longrightarrow> A+B type" and
  PlusFL: "\<And>A B C D. \<lbrakk>A = C; B = D\<rbrakk> \<Longrightarrow> A+B = C+D" and

  PlusI_inl: "\<And>a A B. \<lbrakk>a : A; B type\<rbrakk> \<Longrightarrow> inl(a) : A+B" and
  PlusI_inlL: "\<And>a c A B. \<lbrakk>a = c : A; B type\<rbrakk> \<Longrightarrow> inl(a) = inl(c) : A+B" and

  PlusI_inr: "\<And>b A B. \<lbrakk>A type; b : B\<rbrakk> \<Longrightarrow> inr(b) : A+B" and
  PlusI_inrL: "\<And>b d A B. \<lbrakk>A type; b = d : B\<rbrakk> \<Longrightarrow> inr(b) = inr(d) : A+B" and

  PlusE:
    "\<And>p c d A B C. \<lbrakk>p: A+B;
      \<And>x. x:A \<Longrightarrow> c(x): C(inl(x));
      \<And>y. y:B \<Longrightarrow> d(y): C(inr(y)) \<rbrakk> \<Longrightarrow> when(p, \<lambda>x. c(x), \<lambda>y. d(y)) : C(p)" and

  PlusEL:
    "\<And>p q c d e f A B C. \<lbrakk>p = q : A+B;
      \<And>x. x: A \<Longrightarrow> c(x) = e(x) : C(inl(x));
      \<And>y. y: B \<Longrightarrow> d(y) = f(y) : C(inr(y))\<rbrakk>
    \<Longrightarrow> when(p, \<lambda>x. c(x), \<lambda>y. d(y)) = when(q, \<lambda>x. e(x), \<lambda>y. f(y)) : C(p)" and

  PlusC_inl:
    "\<And>a c d A B C. \<lbrakk>a: A;
      \<And>x. x:A \<Longrightarrow> c(x): C(inl(x));
      \<And>y. y:B \<Longrightarrow> d(y): C(inr(y)) \<rbrakk>
    \<Longrightarrow> when(inl(a), \<lambda>x. c(x), \<lambda>y. d(y)) = c(a) : C(inl(a))" and

  PlusC_inr:
    "\<And>b c d A B C. \<lbrakk>b: B;
      \<And>x. x:A \<Longrightarrow> c(x): C(inl(x));
      \<And>y. y:B \<Longrightarrow> d(y): C(inr(y))\<rbrakk>
    \<Longrightarrow> when(inr(b), \<lambda>x. c(x), \<lambda>y. d(y)) = d(b) : C(inr(b))" and


  \<comment> \<open>The type \<open>Eq\<close>\<close>

  EqF: "\<And>a b A. \<lbrakk>A type; a : A; b : A\<rbrakk> \<Longrightarrow> Eq(A,a,b) type" and
  EqFL: "\<And>a b c d A B. \<lbrakk>A = B; a = c : A; b = d : A\<rbrakk> \<Longrightarrow> Eq(A,a,b) = Eq(B,c,d)" and
  EqI: "\<And>a b A. a = b : A \<Longrightarrow> eq : Eq(A,a,b)" and
  EqE: "\<And>p a b A. p : Eq(A,a,b) \<Longrightarrow> a = b : A" and

  \<comment> \<open>By equality of types, can prove \<open>C(p)\<close> from \<open>C(eq)\<close>, an elimination rule\<close>
  EqC: "\<And>p a b A. p : Eq(A,a,b) \<Longrightarrow> p = eq : Eq(A,a,b)" and


  \<comment> \<open>The type \<open>F\<close>\<close>

  FF: "F type" and
  FE: "\<And>p C. \<lbrakk>p: F; C type\<rbrakk> \<Longrightarrow> contr(p) : C" and
  FEL: "\<And>p q C. \<lbrakk>p = q : F; C type\<rbrakk> \<Longrightarrow> contr(p) = contr(q) : C" and


  \<comment> \<open>The type T\<close>
  \<comment> \<open>
    Martin-Löf's book (page 68) discusses elimination and computation.
    Elimination can be derived by computation and equality of types,
    but with an extra premise \<open>C(x)\<close> type \<open>x:T\<close>.
    Also computation can be derived from elimination.
  \<close>

  TF: "T type" and
  TI: "tt : T" and
  TE: "\<And>p c C. \<lbrakk>p : T; c : C(tt)\<rbrakk> \<Longrightarrow> c : C(p)" and
  TEL: "\<And>p q c d C. \<lbrakk>p = q : T; c = d : C(tt)\<rbrakk> \<Longrightarrow> c = d : C(p)" and
  TC: "\<And>p. p : T \<Longrightarrow> p = tt : T"


subsection "Tactics and derived rules for Constructive Type Theory"

text \<open>Formation rules.\<close>
lemmas form_rls = NF ProdF SumF PlusF EqF FF TF
  and formL_rls = ProdFL SumFL PlusFL EqFL

text \<open>
  Introduction rules. OMITTED:
  \<^item> \<open>EqI\<close>, because its premise is an \<open>eqelem\<close>, not an \<open>elem\<close>.
\<close>
lemmas intr_rls = NI0 NI_succ ProdI SumI PlusI_inl PlusI_inr TI
  and intrL_rls = NI_succL ProdIL SumIL PlusI_inlL PlusI_inrL

text \<open>
  Elimination rules. OMITTED:
  \<^item> \<open>EqE\<close>, because its conclusion is an \<open>eqelem\<close>, not an \<open>elem\<close>
  \<^item> \<open>TE\<close>, because it does not involve a constructor.
\<close>
lemmas elim_rls = NE ProdE SumE PlusE FE
  and elimL_rls = NEL ProdEL SumEL PlusEL FEL

text \<open>OMITTED: \<open>eqC\<close> are \<open>TC\<close> because they make rewriting loop: \<open>p = un = un = \<dots>\<close>\<close>
lemmas comp_rls = NC0 NC_succ ProdC SumC PlusC_inl PlusC_inr

text \<open>Rules with conclusion \<open>a:A\<close>, an elem judgement.\<close>
lemmas element_rls = intr_rls elim_rls

text \<open>Definitions are (meta)equality axioms.\<close>
lemmas basic_defs = fst_def snd_def

text \<open>Compare with standard version: \<open>B\<close> is applied to UNSIMPLIFIED expression!\<close>
lemma SumIL2: "\<lbrakk>c = a : A; d = b : B(a)\<rbrakk> \<Longrightarrow> <c,d> = <a,b> : Sum(A,B)"
  apply (rule sym_elem)
  apply (rule SumIL)
   apply (rule_tac [!] sym_elem)
   apply assumption+
  done

lemmas intrL2_rls = NI_succL ProdIL SumIL2 PlusI_inlL PlusI_inrL

text \<open>
  Exploit \<open>p:Prod(A,B)\<close> to create the assumption \<open>z:B(a)\<close>.
  A more natural form of product elimination.
\<close>
lemma subst_prodE:
  assumes "p: Prod(A,B)"
    and "a: A"
    and "\<And>z. z: B(a) \<Longrightarrow> c(z): C(z)"
  shows "c(p`a): C(p`a)"
  by (rule assms ProdE)+


subsection \<open>Tactics for type checking\<close>

ML \<open>
local

fun is_rigid_elem (Const(@{const_name Elem},_) $ a $ _) = not(is_Var (head_of a))
  | is_rigid_elem (Const(@{const_name Eqelem},_) $ a $ _ $ _) = not(is_Var (head_of a))
  | is_rigid_elem (Const(@{const_name Type},_) $ a) = not(is_Var (head_of a))
  | is_rigid_elem _ = false

in

(*Try solving a:A or a=b:A by assumption provided a is rigid!*)
fun test_assume_tac ctxt = SUBGOAL (fn (prem, i) =>
  if is_rigid_elem (Logic.strip_assums_concl prem)
  then assume_tac ctxt i else no_tac)

fun ASSUME ctxt tf i = test_assume_tac ctxt i  ORELSE  tf i

end
\<close>

text \<open>
  For simplification: type formation and checking,
  but no equalities between terms.
\<close>
lemmas routine_rls = form_rls formL_rls refl_type element_rls

ML \<open>
fun routine_tac rls ctxt prems =
  ASSUME ctxt (filt_resolve_from_net_tac ctxt 4 (Tactic.build_net (prems @ rls)));

(*Solve all subgoals "A type" using formation rules. *)
val form_net = Tactic.build_net @{thms form_rls};
fun form_tac ctxt =
  REPEAT_FIRST (ASSUME ctxt (filt_resolve_from_net_tac ctxt 1 form_net));

(*Type checking: solve a:A (a rigid, A flexible) by intro and elim rules. *)
fun typechk_tac ctxt thms =
  let val tac =
    filt_resolve_from_net_tac ctxt 3
      (Tactic.build_net (thms @ @{thms form_rls} @ @{thms element_rls}))
  in  REPEAT_FIRST (ASSUME ctxt tac)  end

(*Solve a:A (a flexible, A rigid) by introduction rules.
  Cannot use stringtrees (filt_resolve_tac) since
  goals like ?a:SUM(A,B) have a trivial head-string *)
fun intr_tac ctxt thms =
  let val tac =
    filt_resolve_from_net_tac ctxt 1
      (Tactic.build_net (thms @ @{thms form_rls} @ @{thms intr_rls}))
  in  REPEAT_FIRST (ASSUME ctxt tac)  end

(*Equality proving: solve a=b:A (where a is rigid) by long rules. *)
fun equal_tac ctxt thms =
  REPEAT_FIRST
    (ASSUME ctxt
      (filt_resolve_from_net_tac ctxt 3
        (Tactic.build_net (thms @ @{thms form_rls element_rls intrL_rls elimL_rls refl_elem}))))
\<close>

method_setup form = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (form_tac ctxt))\<close>
method_setup typechk = \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (typechk_tac ctxt ths))\<close>
method_setup intr = \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (intr_tac ctxt ths))\<close>
method_setup equal = \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (equal_tac ctxt ths))\<close>


subsection \<open>Simplification\<close>

text \<open>To simplify the type in a goal.\<close>
lemma replace_type: "\<lbrakk>B = A; a : A\<rbrakk> \<Longrightarrow> a : B"
  apply (rule equal_types)
   apply (rule_tac [2] sym_type)
   apply assumption+
  done

text \<open>Simplify the parameter of a unary type operator.\<close>
lemma subst_eqtyparg:
  assumes 1: "a=c : A"
    and 2: "\<And>z. z:A \<Longrightarrow> B(z) type"
  shows "B(a) = B(c)"
  apply (rule subst_typeL)
   apply (rule_tac [2] refl_type)
   apply (rule 1)
  apply (erule 2)
  done

text \<open>Simplification rules for Constructive Type Theory.\<close>
lemmas reduction_rls = comp_rls [THEN trans_elem]

ML \<open>
(*Converts each goal "e : Eq(A,a,b)" into "a=b:A" for simplification.
  Uses other intro rules to avoid changing flexible goals.*)
val eqintr_net = Tactic.build_net @{thms EqI intr_rls}
fun eqintr_tac ctxt =
  REPEAT_FIRST (ASSUME ctxt (filt_resolve_from_net_tac ctxt 1 eqintr_net))

(** Tactics that instantiate CTT-rules.
    Vars in the given terms will be incremented!
    The (rtac EqE i) lets them apply to equality judgements. **)

fun NE_tac ctxt sp i =
  TRY (resolve_tac ctxt @{thms EqE} i) THEN
  Rule_Insts.res_inst_tac ctxt [((("p", 0), Position.none), sp)] [] @{thm NE} i

fun SumE_tac ctxt sp i =
  TRY (resolve_tac ctxt @{thms EqE} i) THEN
  Rule_Insts.res_inst_tac ctxt [((("p", 0), Position.none), sp)] [] @{thm SumE} i

fun PlusE_tac ctxt sp i =
  TRY (resolve_tac ctxt @{thms EqE} i) THEN
  Rule_Insts.res_inst_tac ctxt [((("p", 0), Position.none), sp)] [] @{thm PlusE} i

(** Predicate logic reasoning, WITH THINNING!!  Procedures adapted from NJ. **)

(*Finds f:Prod(A,B) and a:A in the assumptions, concludes there is z:B(a) *)
fun add_mp_tac ctxt i =
  resolve_tac ctxt @{thms subst_prodE} i  THEN  assume_tac ctxt i  THEN  assume_tac ctxt i

(*Finds P\<longrightarrow>Q and P in the assumptions, replaces implication by Q *)
fun mp_tac ctxt i = eresolve_tac ctxt @{thms subst_prodE} i  THEN  assume_tac ctxt i

(*"safe" when regarded as predicate calculus rules*)
val safe_brls = sort (make_ord lessb)
    [ (true, @{thm FE}), (true,asm_rl),
      (false, @{thm ProdI}), (true, @{thm SumE}), (true, @{thm PlusE}) ]

val unsafe_brls =
    [ (false, @{thm PlusI_inl}), (false, @{thm PlusI_inr}), (false, @{thm SumI}),
      (true, @{thm subst_prodE}) ]

(*0 subgoals vs 1 or more*)
val (safe0_brls, safep_brls) =
    List.partition (curry (op =) 0 o subgoals_of_brl) safe_brls

fun safestep_tac ctxt thms i =
    form_tac ctxt ORELSE
    resolve_tac ctxt thms i  ORELSE
    biresolve_tac ctxt safe0_brls i  ORELSE  mp_tac ctxt i  ORELSE
    DETERM (biresolve_tac ctxt safep_brls i)

fun safe_tac ctxt thms i = DEPTH_SOLVE_1 (safestep_tac ctxt thms i)

fun step_tac ctxt thms = safestep_tac ctxt thms  ORELSE'  biresolve_tac ctxt unsafe_brls

(*Fails unless it solves the goal!*)
fun pc_tac ctxt thms = DEPTH_SOLVE_1 o (step_tac ctxt thms)
\<close>

method_setup eqintr = \<open>Scan.succeed (SIMPLE_METHOD o eqintr_tac)\<close>
method_setup NE = \<open>
  Scan.lift Args.embedded_inner_syntax >> (fn s => fn ctxt => SIMPLE_METHOD' (NE_tac ctxt s))
\<close>
method_setup pc = \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (pc_tac ctxt ths))\<close>
method_setup add_mp = \<open>Scan.succeed (SIMPLE_METHOD' o add_mp_tac)\<close>

ML_file "rew.ML"
method_setup rew = \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (rew_tac ctxt ths))\<close>
method_setup hyp_rew = \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD (hyp_rew_tac ctxt ths))\<close>


subsection \<open>The elimination rules for fst/snd\<close>

lemma SumE_fst: "p : Sum(A,B) \<Longrightarrow> fst(p) : A"
  apply (unfold basic_defs)
  apply (erule SumE)
  apply assumption
  done

text \<open>The first premise must be \<open>p:Sum(A,B)\<close>!!.\<close>
lemma SumE_snd:
  assumes major: "p: Sum(A,B)"
    and "A type"
    and "\<And>x. x:A \<Longrightarrow> B(x) type"
  shows "snd(p) : B(fst(p))"
  apply (unfold basic_defs)
  apply (rule major [THEN SumE])
  apply (rule SumC [THEN subst_eqtyparg, THEN replace_type])
      apply (typechk assms)
  done

end
