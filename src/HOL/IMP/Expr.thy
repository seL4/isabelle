(*  Title:      HOL/IMP/Expr.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Copyright   1994 TUM

Arithmetic expressions and Boolean expressions.
Not used in the rest of the language, but included for completeness.
*)

Expr = Arith +

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
       "@evala"  :: [aexp,state,nat] => bool ("<_,_>/ -a-> _"  [0,0,50] 50)
translations
    "<ae,sig> -a-> n" == "(ae,sig,n) : evala"
inductive "evala"
  intrs 
    N   "<N(n),s> -a-> n"
    X   "<X(x),s> -a-> s(x)"
    Op1 "<e,s> -a-> n ==> <Op1 f e,s> -a-> f(n)"
    Op2 "[| <e0,s> -a-> n0;  <e1,s>  -a-> n1 |] 
           ==> <Op2 f e0 e1,s> -a-> f n0 n1"

types n2n2b = "[nat,nat] => bool"

(** Boolean expressions **)

datatype
  bexp = true
       | false
       | ROp  n2n2b aexp aexp
       | noti bexp
       | andi bexp bexp         (infixl 60)
       | ori  bexp bexp         (infixl 60)

(** Evaluation of boolean expressions **)
consts evalb    :: "(bexp*state*bool)set"       
       "@evalb" :: [bexp,state,bool] => bool ("<_,_>/ -b-> _"  [0,0,50] 50)

translations
    "<be,sig> -b-> b" == "(be,sig,b) : evalb"

inductive "evalb"
 intrs (*avoid clash with ML constructors true, false*)
    tru   "<true,s> -b-> True"
    fls   "<false,s> -b-> False"
    ROp   "[| <a0,s> -a-> n0; <a1,s> -a-> n1 |] 
           ==> <ROp f a0 a1,s> -b-> f n0 n1"
    noti  "<b,s> -b-> w ==> <noti(b),s> -b-> (~w)"
    andi  "[| <b0,s> -b-> w0; <b1,s> -b-> w1 |] 
          ==> <b0 andi b1,s> -b-> (w0 & w1)"
    ori   "[| <b0,s> -b-> w0; <b1,s> -b-> w1 |] 
            ==> <b0 ori b1,s> -b-> (w0 | w1)"

(** Denotational semantics of arithemtic and boolean expressions **)
consts
  A     :: aexp => state => nat
  B     :: bexp => state => bool

primrec A aexp
  A_nat "A(N(n)) = (%s. n)"
  A_loc "A(X(x)) = (%s. s(x))" 
  A_op1 "A(Op1 f a) = (%s. f(A a s))"
  A_op2 "A(Op2 f a0 a1) = (%s. f (A a0 s) (A a1 s))"

primrec B bexp
  B_true  "B(true) = (%s. True)"
  B_false "B(false) = (%s. False)"
  B_op    "B(ROp f a0 a1) = (%s. f (A a0 s) (A a1 s))" 
  B_not   "B(noti(b)) = (%s. ~(B b s))"
  B_and   "B(b0 andi b1) = (%s. (B b0 s) & (B b1 s))"
  B_or    "B(b0 ori b1) = (%s. (B b0 s) | (B b1 s))"

end
