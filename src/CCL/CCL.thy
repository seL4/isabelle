(*  Title: 	CCL/ccl.thy
    ID:         $Id$
    Author: 	Martin Coen
    Copyright   1993  University of Cambridge

Classical Computational Logic for Untyped Lambda Calculus with reduction to 
weak head-normal form.

Based on FOL extended with set collection, a primitive higher-order logic.
HOL is too strong - descriptions prevent a type of programs being defined
which contains only executable terms.
*)

CCL = Gfp +

classes prog < term

default prog

types i

arities 
      i          :: prog
      fun        :: (prog,prog)prog

consts
  (*** Evaluation Judgement ***)
  "--->"      ::       "[i,i]=>prop"          (infixl 20)

  (*** Bisimulations for pre-order and equality ***)
  "[="        ::       "['a,'a]=>o"           (infixl 50)
  SIM         ::       "[i,i,i set]=>o"
  POgen,EQgen ::       "i set => i set"
  PO,EQ       ::       "i set"

  (*** Term Formers ***)
  true,false  ::       "i"
  pair        ::       "[i,i]=>i"             ("(1<_,/_>)")
  lambda      ::       "(i=>i)=>i"            (binder "lam " 55)
  case        ::       "[i,i,i,[i,i]=>i,(i=>i)=>i]=>i"
  "`"         ::       "[i,i]=>i"             (infixl 56)
  bot         ::       "i"
  fix         ::       "(i=>i)=>i"

  (*** Defined Predicates ***)
  Trm,Dvg     ::       "i => o"

rules

  (******* EVALUATION SEMANTICS *******)

  (**  This is the evaluation semantics from which the axioms below were derived.  **)
  (**  It is included here just as an evaluator for FUN and has no influence on    **)
  (**  inference in the theory CCL.                                                **)

  trueV       "true ---> true"
  falseV      "false ---> false"
  pairV       "<a,b> ---> <a,b>"
  lamV        "lam x.b(x) ---> lam x.b(x)"
  caseVtrue   "[| t ---> true;  d ---> c |] ==> case(t,d,e,f,g) ---> c"
  caseVfalse  "[| t ---> false;  e ---> c |] ==> case(t,d,e,f,g) ---> c"
  caseVpair   "[| t ---> <a,b>;  f(a,b) ---> c |] ==> case(t,d,e,f,g) ---> c"
  caseVlam    "[| t ---> lam x.b(x);  g(b) ---> c |] ==> case(t,d,e,f,g) ---> c"

  (*** Properties of evaluation: note that "t ---> c" impies that c is canonical ***)

  canonical  "[| t ---> c; c==true ==> u--->v; 
                          c==false ==> u--->v; 
                    !!a b.c==<a,b> ==> u--->v; 
                      !!f.c==lam x.f(x) ==> u--->v |] ==> 
             u--->v"

  (* Should be derivable - but probably a bitch! *)
  substitute "[| a==a'; t(a)--->c(a) |] ==> t(a')--->c(a')"

  (************** LOGIC ***************)

  (*** Definitions used in the following rules ***)

  apply_def     "f ` t == case(f,bot,bot,%x y.bot,%u.u(t))"
  bot_def         "bot == (lam x.x`x)`(lam x.x`x)"
  fix_def      "fix(f) == (lam x.f(x`x))`(lam x.f(x`x))"

  (*  The pre-order ([=) is defined as a simulation, and behavioural equivalence (=) *)
  (*  as a bisimulation.  They can both be expressed as (bi)simulations up to        *)
  (*  behavioural equivalence (ie the relations PO and EQ defined below).            *)

  SIM_def
  "SIM(t,t',R) ==  (t=true & t'=true) | (t=false & t'=false) | 
                  (EX a a' b b'.t=<a,b> & t'=<a',b'> & <a,a'> : R & <b,b'> : R) | 
                  (EX f f'.t=lam x.f(x) & t'=lam x.f'(x) & (ALL x.<f(x),f'(x)> : R))"

  POgen_def  "POgen(R) == {p. EX t t'. p=<t,t'> & (t = bot | SIM(t,t',R))}"
  EQgen_def  "EQgen(R) == {p. EX t t'. p=<t,t'> & (t = bot & t' = bot | SIM(t,t',R))}"

  PO_def    "PO == gfp(POgen)"
  EQ_def    "EQ == gfp(EQgen)"

  (*** Rules ***)

  (** Partial Order **)

  po_refl        "a [= a"
  po_trans       "[| a [= b;  b [= c |] ==> a [= c"
  po_cong        "a [= b ==> f(a) [= f(b)"

  (* Extend definition of [= to program fragments of higher type *)
  po_abstractn   "(!!x. f(x) [= g(x)) ==> (%x.f(x)) [= (%x.g(x))"

  (** Equality - equivalence axioms inherited from FOL.thy   **)
  (**          - congruence of "=" is axiomatised implicitly **)

  eq_iff         "t = t' <-> t [= t' & t' [= t"

  (** Properties of canonical values given by greatest fixed point definitions **)
 
  PO_iff         "t [= t' <-> <t,t'> : PO"
  EQ_iff         "t =  t' <-> <t,t'> : EQ"

  (** Behaviour of non-canonical terms (ie case) given by the following beta-rules **)

  caseBtrue            "case(true,d,e,f,g) = d"
  caseBfalse          "case(false,d,e,f,g) = e"
  caseBpair           "case(<a,b>,d,e,f,g) = f(a,b)"
  caseBlam       "case(lam x.b(x),d,e,f,g) = g(b)"
  caseBbot              "case(bot,d,e,f,g) = bot"            (* strictness *)

  (** The theory is non-trivial **)
  distinctness   "~ lam x.b(x) = bot"

  (*** Definitions of Termination and Divergence ***)

  Dvg_def  "Dvg(t) == t = bot"
  Trm_def  "Trm(t) == ~ Dvg(t)"

end


(*
Would be interesting to build a similar theory for a typed programming language:
    ie.     true :: bool,      fix :: ('a=>'a)=>'a  etc......

This is starting to look like LCF.
What are the advantages of this approach?   
        - less axiomatic                                            
        - wfd induction / coinduction and fixed point induction available
           
*)
