(*  Title:      CTT/ctt.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Constructive Type Theory
*)

CTT = Pure +

types
  i
  t
  o

arities
   i,t,o :: logic

consts
  (*Types*)
  F,T       :: "t"          (*F is empty, T contains one element*)
  contr     :: "i=>i"
  tt        :: "i"
  (*Natural numbers*)
  N         :: "t"
  succ      :: "i=>i"
  rec       :: "[i, i, [i,i]=>i] => i"
  (*Unions*)
  inl,inr   :: "i=>i"
  when      :: "[i, i=>i, i=>i]=>i"
  (*General Sum and Binary Product*)
  Sum       :: "[t, i=>t]=>t"
  fst,snd   :: "i=>i"
  split     :: "[i, [i,i]=>i] =>i"
  (*General Product and Function Space*)
  Prod      :: "[t, i=>t]=>t"
  (*Equality type*)
  Eq        :: "[t,i,i]=>t"
  eq        :: "i"
  (*Judgements*)
  Type      :: "t => prop"          ("(_ type)" [10] 5)
  Eqtype    :: "[t,t]=>prop"        ("(_ =/ _)" [10,10] 5)
  Elem      :: "[i, t]=>prop"       ("(_ /: _)" [10,10] 5)
  Eqelem    :: "[i,i,t]=>prop"      ("(_ =/ _ :/ _)" [10,10,10] 5)
  Reduce    :: "[i,i]=>prop"        ("Reduce[_,_]")
  (*Types*)
  "@PROD"   :: "[idt,t,t]=>t"       ("(3PROD _:_./ _)" 10)
  "@SUM"    :: "[idt,t,t]=>t"       ("(3SUM _:_./ _)" 10)
  "+"       :: "[t,t]=>t"           (infixr 40)
  (*Invisible infixes!*)
  "@-->"    :: "[t,t]=>t"           ("(_ -->/ _)" [31,30] 30)
  "@*"      :: "[t,t]=>t"           ("(_ */ _)" [51,50] 50)
  (*Functions*)
  lambda    :: "(i => i) => i"      (binder "lam " 10)
  "`"       :: "[i,i]=>i"           (infixl 60)
  (*Natural numbers*)
  "0"       :: "i"                  ("0")
  (*Pairing*)
  pair      :: "[i,i]=>i"           ("(1<_,/_>)")

translations
  "PROD x:A. B" => "Prod(A, %x. B)"
  "A --> B"     => "Prod(A, _K(B))"
  "SUM x:A. B"  => "Sum(A, %x. B)"
  "A * B"       => "Sum(A, _K(B))"

syntax (xsymbols)
  "@-->"    :: "[t,t]=>t"           ("(_ \\<longrightarrow>/ _)" [31,30] 30)
  "@*"      :: "[t,t]=>t"           ("(_ \\<times>/ _)"          [51,50] 50)
  Elem      :: "[i, t]=>prop"       ("(_ /\\<in> _)" [10,10] 5)
  Eqelem    :: "[i,i,t]=>prop"      ("(2_ =/ _ \\<in>/ _)" [10,10,10] 5)
  "@SUM"    :: "[idt,t,t] => t"     ("(3\\<Sigma> _\\<in>_./ _)" 10)
  "@PROD"   :: "[idt,t,t] => t"     ("(3\\<Pi> _\\<in>_./ _)"    10)
  "lam "    :: "[idts, i] => i"     ("(3\\<lambda>\\<lambda>_./ _)" 10)

rules

  (*Reduction: a weaker notion than equality;  a hack for simplification.
    Reduce[a,b] means either that  a=b:A  for some A or else that "a" and "b"
    are textually identical.*)

  (*does not verify a:A!  Sound because only trans_red uses a Reduce premise
    No new theorems can be proved about the standard judgements.*)
  refl_red "Reduce[a,a]"
  red_if_equal "a = b : A ==> Reduce[a,b]"
  trans_red "[| a = b : A;  Reduce[b,c] |] ==> a = c : A"

  (*Reflexivity*)

  refl_type "A type ==> A = A"
  refl_elem "a : A ==> a = a : A"

  (*Symmetry*)

  sym_type  "A = B ==> B = A"
  sym_elem  "a = b : A ==> b = a : A"

  (*Transitivity*)

  trans_type   "[| A = B;  B = C |] ==> A = C"
  trans_elem   "[| a = b : A;  b = c : A |] ==> a = c : A"

  equal_types  "[| a : A;  A = B |] ==> a : B"
  equal_typesL "[| a = b : A;  A = B |] ==> a = b : B"

  (*Substitution*)

  subst_type   "[| a : A;  !!z. z:A ==> B(z) type |] ==> B(a) type"
  subst_typeL  "[| a = c : A;  !!z. z:A ==> B(z) = D(z) |] ==> B(a) = D(c)"

  subst_elem   "[| a : A;  !!z. z:A ==> b(z):B(z) |] ==> b(a):B(a)"
  subst_elemL
    "[| a=c : A;  !!z. z:A ==> b(z)=d(z) : B(z) |] ==> b(a)=d(c) : B(a)"


  (*The type N -- natural numbers*)

  NF "N type"
  NI0 "0 : N"
  NI_succ "a : N ==> succ(a) : N"
  NI_succL  "a = b : N ==> succ(a) = succ(b) : N"

  NE
   "[| p: N;  a: C(0);  !!u v. [| u: N; v: C(u) |] ==> b(u,v): C(succ(u)) |] 
   ==> rec(p, a, %u v. b(u,v)) : C(p)"

  NEL
   "[| p = q : N;  a = c : C(0);  
      !!u v. [| u: N; v: C(u) |] ==> b(u,v) = d(u,v): C(succ(u)) |] 
   ==> rec(p, a, %u v. b(u,v)) = rec(q,c,d) : C(p)"

  NC0
   "[| a: C(0);  !!u v. [| u: N; v: C(u) |] ==> b(u,v): C(succ(u)) |] 
   ==> rec(0, a, %u v. b(u,v)) = a : C(0)"

  NC_succ
   "[| p: N;  a: C(0);  
       !!u v. [| u: N; v: C(u) |] ==> b(u,v): C(succ(u)) |] ==>  
   rec(succ(p), a, %u v. b(u,v)) = b(p, rec(p, a, %u v. b(u,v))) : C(succ(p))"

  (*The fourth Peano axiom.  See page 91 of Martin-Lof's book*)
  zero_ne_succ
    "[| a: N;  0 = succ(a) : N |] ==> 0: F"


  (*The Product of a family of types*)

  ProdF  "[| A type; !!x. x:A ==> B(x) type |] ==> PROD x:A. B(x) type"

  ProdFL
   "[| A = C;  !!x. x:A ==> B(x) = D(x) |] ==> 
   PROD x:A. B(x) = PROD x:C. D(x)"

  ProdI
   "[| A type;  !!x. x:A ==> b(x):B(x)|] ==> lam x. b(x) : PROD x:A. B(x)"

  ProdIL
   "[| A type;  !!x. x:A ==> b(x) = c(x) : B(x)|] ==> 
   lam x. b(x) = lam x. c(x) : PROD x:A. B(x)"

  ProdE  "[| p : PROD x:A. B(x);  a : A |] ==> p`a : B(a)"
  ProdEL "[| p=q: PROD x:A. B(x);  a=b : A |] ==> p`a = q`b : B(a)"

  ProdC
   "[| a : A;  !!x. x:A ==> b(x) : B(x)|] ==> 
   (lam x. b(x)) ` a = b(a) : B(a)"

  ProdC2
   "p : PROD x:A. B(x) ==> (lam x. p`x) = p : PROD x:A. B(x)"


  (*The Sum of a family of types*)

  SumF  "[| A type;  !!x. x:A ==> B(x) type |] ==> SUM x:A. B(x) type"
  SumFL
    "[| A = C;  !!x. x:A ==> B(x) = D(x) |] ==> SUM x:A. B(x) = SUM x:C. D(x)"

  SumI  "[| a : A;  b : B(a) |] ==> <a,b> : SUM x:A. B(x)"
  SumIL "[| a=c:A;  b=d:B(a) |] ==> <a,b> = <c,d> : SUM x:A. B(x)"

  SumE
    "[| p: SUM x:A. B(x);  !!x y. [| x:A; y:B(x) |] ==> c(x,y): C(<x,y>) |] 
    ==> split(p, %x y. c(x,y)) : C(p)"

  SumEL
    "[| p=q : SUM x:A. B(x); 
       !!x y. [| x:A; y:B(x) |] ==> c(x,y)=d(x,y): C(<x,y>)|] 
    ==> split(p, %x y. c(x,y)) = split(q, % x y. d(x,y)) : C(p)"

  SumC
    "[| a: A;  b: B(a);  !!x y. [| x:A; y:B(x) |] ==> c(x,y): C(<x,y>) |] 
    ==> split(<a,b>, %x y. c(x,y)) = c(a,b) : C(<a,b>)"

  fst_def   "fst(a) == split(a, %x y. x)"
  snd_def   "snd(a) == split(a, %x y. y)"


  (*The sum of two types*)

  PlusF   "[| A type;  B type |] ==> A+B type"
  PlusFL  "[| A = C;  B = D |] ==> A+B = C+D"

  PlusI_inl   "[| a : A;  B type |] ==> inl(a) : A+B"
  PlusI_inlL "[| a = c : A;  B type |] ==> inl(a) = inl(c) : A+B"

  PlusI_inr   "[| A type;  b : B |] ==> inr(b) : A+B"
  PlusI_inrL "[| A type;  b = d : B |] ==> inr(b) = inr(d) : A+B"

  PlusE
    "[| p: A+B;  !!x. x:A ==> c(x): C(inl(x));  
                !!y. y:B ==> d(y): C(inr(y)) |] 
    ==> when(p, %x. c(x), %y. d(y)) : C(p)"

  PlusEL
    "[| p = q : A+B;  !!x. x: A ==> c(x) = e(x) : C(inl(x));   
                     !!y. y: B ==> d(y) = f(y) : C(inr(y)) |] 
    ==> when(p, %x. c(x), %y. d(y)) = when(q, %x. e(x), %y. f(y)) : C(p)"

  PlusC_inl
    "[| a: A;  !!x. x:A ==> c(x): C(inl(x));  
              !!y. y:B ==> d(y): C(inr(y)) |] 
    ==> when(inl(a), %x. c(x), %y. d(y)) = c(a) : C(inl(a))"

  PlusC_inr
    "[| b: B;  !!x. x:A ==> c(x): C(inl(x));  
              !!y. y:B ==> d(y): C(inr(y)) |] 
    ==> when(inr(b), %x. c(x), %y. d(y)) = d(b) : C(inr(b))"


  (*The type Eq*)

  EqF    "[| A type;  a : A;  b : A |] ==> Eq(A,a,b) type"
  EqFL "[| A=B;  a=c: A;  b=d : A |] ==> Eq(A,a,b) = Eq(B,c,d)"
  EqI "a = b : A ==> eq : Eq(A,a,b)"
  EqE "p : Eq(A,a,b) ==> a = b : A"

  (*By equality of types, can prove C(p) from C(eq), an elimination rule*)
  EqC "p : Eq(A,a,b) ==> p = eq : Eq(A,a,b)"

  (*The type F*)

  FF "F type"
  FE "[| p: F;  C type |] ==> contr(p) : C"
  FEL  "[| p = q : F;  C type |] ==> contr(p) = contr(q) : C"

  (*The type T
     Martin-Lof's book (page 68) discusses elimination and computation.
     Elimination can be derived by computation and equality of types,
     but with an extra premise C(x) type x:T.
     Also computation can be derived from elimination. *)

  TF "T type"
  TI "tt : T"
  TE "[| p : T;  c : C(tt) |] ==> c : C(p)"
  TEL "[| p = q : T;  c = d : C(tt) |] ==> c = d : C(p)"
  TC "p : T ==> p = tt : T"
end


ML

val print_translation =
  [("Prod", dependent_tr' ("@PROD", "@-->")),
   ("Sum", dependent_tr' ("@SUM", "@*"))];

