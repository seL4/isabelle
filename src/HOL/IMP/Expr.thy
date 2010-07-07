(*  Title:      HOL/IMP/Expr.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Copyright   1994 TUM
*)

header "Expressions"

theory Expr imports Main begin

text {*
  Arithmetic expressions and Boolean expressions.
  Not used in the rest of the language, but included for completeness.
*}

subsection "Arithmetic expressions"
typedecl loc

types
  state = "loc => nat"

datatype
  aexp = N nat
       | X loc
       | Op1 "nat => nat" aexp
       | Op2 "nat => nat => nat" aexp aexp

subsection "Evaluation of arithmetic expressions"

inductive
  evala :: "[aexp*state,nat] => bool"  (infixl "-a->" 50)
where
  N:   "(N(n),s) -a-> n"
| X:   "(X(x),s) -a-> s(x)"
| Op1: "(e,s) -a-> n ==> (Op1 f e,s) -a-> f(n)"
| Op2: "[| (e0,s) -a-> n0;  (e1,s)  -a-> n1 |]
        ==> (Op2 f e0 e1,s) -a-> f n0 n1"

lemmas [intro] = N X Op1 Op2


subsection "Boolean expressions"

datatype
  bexp = true
       | false
       | ROp  "nat => nat => bool" aexp aexp
       | noti bexp
       | andi bexp bexp         (infixl "andi" 60)
       | ori  bexp bexp         (infixl "ori" 60)

subsection "Evaluation of boolean expressions"

inductive
  evalb :: "[bexp*state,bool] => bool"  (infixl "-b->" 50)
  -- "avoid clash with ML constructors true, false"
where
  tru:   "(true,s) -b-> True"
| fls:   "(false,s) -b-> False"
| ROp:   "[| (a0,s) -a-> n0; (a1,s) -a-> n1 |]
          ==> (ROp f a0 a1,s) -b-> f n0 n1"
| noti:  "(b,s) -b-> w ==> (noti(b),s) -b-> (~w)"
| andi:  "[| (b0,s) -b-> w0; (b1,s) -b-> w1 |]
          ==> (b0 andi b1,s) -b-> (w0 & w1)"
| ori:   "[| (b0,s) -b-> w0; (b1,s) -b-> w1 |]
          ==> (b0 ori b1,s) -b-> (w0 | w1)"

lemmas [intro] = tru fls ROp noti andi ori

subsection "Denotational semantics of arithmetic and boolean expressions"

primrec A :: "aexp => state => nat"
where
  "A(N(n)) = (%s. n)"
| "A(X(x)) = (%s. s(x))"
| "A(Op1 f a) = (%s. f(A a s))"
| "A(Op2 f a0 a1) = (%s. f (A a0 s) (A a1 s))"

primrec B :: "bexp => state => bool"
where
  "B(true) = (%s. True)"
| "B(false) = (%s. False)"
| "B(ROp f a0 a1) = (%s. f (A a0 s) (A a1 s))"
| "B(noti(b)) = (%s. ~(B b s))"
| "B(b0 andi b1) = (%s. (B b0 s) & (B b1 s))"
| "B(b0 ori b1) = (%s. (B b0 s) | (B b1 s))"

inductive_simps
  evala_simps [simp]:
  "(N(n),s) -a-> n'" 
  "(X(x),sigma) -a-> i"
  "(Op1 f e,sigma) -a-> i"
  "(Op2 f a1 a2,sigma) -a-> i"
  "((true,sigma) -b-> w)"
  "((false,sigma) -b-> w)"
  "((ROp f a0 a1,sigma) -b-> w)"
  "((noti(b),sigma) -b-> w)"
  "((b0 andi b1,sigma) -b-> w)"
  "((b0 ori b1,sigma) -b-> w)"


lemma aexp_iff: "((a,s) -a-> n) = (A a s = n)"
  by (induct a arbitrary: n) auto

lemma bexp_iff:
  "((b,s) -b-> w) = (B b s = w)"
  by (induct b arbitrary: w) (auto simp add: aexp_iff)

end
