(*  Title: 	HOL/IMP/Com.thy
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Arithmetic expressions, Boolean expressions, Commands

And their Operational semantics
*)

Com = Arith +

(** Arithmetic expressions **)
types loc
      state = "loc => nat"
      n2n = "nat => nat"
      n2n2n = "nat => nat => nat"

arities loc :: term

datatype
  aexp = N nat
       | X loc
       | Op1 n2n aexp
       | Op2 n2n2n aexp aexp

(** Evaluation of arithmetic expressions **)
consts  evala    :: "(aexp*state*nat)set"
       "@evala"  :: "[aexp,state,nat] => bool" ("<_,_>/ -a-> _"  [0,0,50] 50)
translations
    "<ae,sig> -a-> n" == "(ae,sig,n) : evala"
inductive "evala"
  intrs 
    N   "<N(n),s> -a-> n"
    X  	"<X(x),s> -a-> s(x)"
    Op1 "<e,s> -a-> n ==> <Op1 f e,s> -a-> f(n)"
    Op2 "[| <e0,s> -a-> n0;  <e1,s>  -a-> n1 |] \
\           ==> <Op2 f e0 e1,s> -a-> f n0 n1"

types n2n2b = "[nat,nat] => bool"

(** Boolean expressions **)

datatype
  bexp = true
       | false
       | ROp  n2n2b aexp aexp
       | noti bexp
       | andi bexp bexp 	(infixl 60)
       | ori  bexp bexp 	(infixl 60)

(** Evaluation of boolean expressions **)
consts evalb	:: "(bexp*state*bool)set"	
       "@evalb" :: "[bexp,state,bool] => bool" ("<_,_>/ -b-> _"  [0,0,50] 50)

translations
    "<be,sig> -b-> b" == "(be,sig,b) : evalb"

inductive "evalb"
 intrs (*avoid clash with ML constructors true, false*)
    tru   "<true,s> -b-> True"
    fls   "<false,s> -b-> False"
    ROp   "[| <a0,s> -a-> n0; <a1,s> -a-> n1 |] \
\	   ==> <ROp f a0 a1,s> -b-> f n0 n1"
    noti  "<b,s> -b-> w ==> <noti(b),s> -b-> (~w)"
    andi  "[| <b0,s> -b-> w0; <b1,s> -b-> w1 |] \
\          ==> <b0 andi b1,s> -b-> (w0 & w1)"
    ori   "[| <b0,s> -b-> w0; <b1,s> -b-> w1 |] \
\	    ==> <b0 ori b1,s> -b-> (w0 | w1)"

(** Commands **)

datatype
  com = skip
      | ":="   loc aexp	         (infixl  60)
      | semic  com com	         ("_; _"  [60, 60] 10)
      | whileC bexp com	         ("while _ do _"  60)
      | ifC    bexp com com	 ("ifc _ then _ else _"  60)

(** Execution of commands **)
consts  evalc    :: "(com*state*state)set"
        "@evalc" :: "[com,state,state] => bool" ("<_,_>/ -c-> _" [0,0,50] 50)
	"assign" :: "[state,nat,loc] => state"  ("_[_'/_]"       [95,0,0] 95)

translations
       "<ce,sig> -c-> s" == "(ce,sig,s) : evalc"

rules 
	assign_def	"s[m/x] == (%y. if y=x then m else s y)"

inductive "evalc"
  intrs
    skip    "<skip,s> -c-> s"

    assign  "<a,s> -a-> m ==> <x := a,s> -c-> s[m/x]"

    semi    "[| <c0,s> -c-> s2; <c1,s2> -c-> s1 |] \
\            ==> <c0 ; c1, s> -c-> s1"

    ifcTrue "[| <b,s> -b-> True; <c0,s> -c-> s1 |] \
\            ==> <ifc b then c0 else c1, s> -c-> s1"

    ifcFalse "[| <b,s> -b-> False; <c1,s> -c-> s1 |] \
\             ==> <ifc b then c0 else c1, s> -c-> s1"

    whileFalse "<b, s> -b-> False ==> <while b do c,s> -c-> s"

    whileTrue  "[| <b,s> -b-> True; <c,s> -c-> s2; \
\                  <while b do c, s2> -c-> s1 |] \
\               ==> <while b do c, s> -c-> s1 "
 
end
