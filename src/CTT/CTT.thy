(*  Title:      CTT/CTT.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

theory CTT
imports Pure
begin

section \<open>Constructive Type Theory: axiomatic basis\<close>

ML_file \<open>~~/src/Provers/typedsimp.ML\<close>
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
  \<comment> \<open>Martin-Löf's book (page 68) discusses elimination and computation.
    Elimination can be derived by computation and equality of types,
    but with an extra premise \<open>C(x)\<close> type \<open>x:T\<close>.
    Also computation can be derived from elimination.\<close>

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
  by (rule sym_elem) (rule SumIL; rule sym_elem)

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

fun is_rigid_elem \<^Const_>\<open>Elem for a _\<close> = not(is_Var (head_of a))
  | is_rigid_elem \<^Const_>\<open>Eqelem for a _ _\<close> = not(is_Var (head_of a))
  | is_rigid_elem \<^Const_>\<open>Type for a\<close> = not(is_Var (head_of a))
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

ML_file \<open>rew.ML\<close>
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


section \<open>The two-element type (booleans and conditionals)\<close>

definition Bool :: "t"
  where "Bool \<equiv> T+T"

definition true :: "i"
  where "true \<equiv> inl(tt)"

definition false :: "i"
  where "false \<equiv> inr(tt)"

definition cond :: "[i,i,i]\<Rightarrow>i"
  where "cond(a,b,c) \<equiv> when(a, \<lambda>_. b, \<lambda>_. c)"

lemmas bool_defs = Bool_def true_def false_def cond_def


subsection \<open>Derivation of rules for the type \<open>Bool\<close>\<close>

text \<open>Formation rule.\<close>
lemma boolF: "Bool type"
  unfolding bool_defs by typechk

text \<open>Introduction rules for \<open>true\<close>, \<open>false\<close>.\<close>

lemma boolI_true: "true : Bool"
  unfolding bool_defs by typechk

lemma boolI_false: "false : Bool"
  unfolding bool_defs by typechk

text \<open>Elimination rule: typing of \<open>cond\<close>.\<close>
lemma boolE: "\<lbrakk>p:Bool; a : C(true); b : C(false)\<rbrakk> \<Longrightarrow> cond(p,a,b) : C(p)"
  unfolding bool_defs
  apply (typechk; erule TE)
   apply typechk
  done

lemma boolEL: "\<lbrakk>p = q : Bool; a = c : C(true); b = d : C(false)\<rbrakk>
  \<Longrightarrow> cond(p,a,b) = cond(q,c,d) : C(p)"
  unfolding bool_defs
  apply (rule PlusEL)
    apply (erule asm_rl refl_elem [THEN TEL])+
  done

text \<open>Computation rules for \<open>true\<close>, \<open>false\<close>.\<close>

lemma boolC_true: "\<lbrakk>a : C(true); b : C(false)\<rbrakk> \<Longrightarrow> cond(true,a,b) = a : C(true)"
  unfolding bool_defs
  apply (rule comp_rls)
    apply typechk
   apply (erule_tac [!] TE)
   apply typechk
  done

lemma boolC_false: "\<lbrakk>a : C(true); b : C(false)\<rbrakk> \<Longrightarrow> cond(false,a,b) = b : C(false)"
  unfolding bool_defs
  apply (rule comp_rls)
    apply typechk
   apply (erule_tac [!] TE)
   apply typechk
  done

section \<open>Elementary arithmetic\<close>

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
