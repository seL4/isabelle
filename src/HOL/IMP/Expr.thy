(*  Title:      HOL/IMP/Expr.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Copyright   1994 TUM
*)

header "Expressions"

theory Expr = Datatype:

text {*
  Arithmetic expressions and Boolean expressions.
  Not used in the rest of the language, but included for completeness.
*}

subsection "Arithmetic expressions"
typedecl loc 

types
  state = "loc => nat"
  n2n = "nat => nat"
  n2n2n = "nat => nat => nat"

datatype
  aexp = N nat
       | X loc
       | Op1 n2n aexp
       | Op2 n2n2n aexp aexp

subsection "Evaluation of arithmetic expressions"
consts  evala    :: "((aexp*state) * nat) set"
       "-a->"    :: "[aexp*state,nat] => bool"         (infixl 50)
translations
    "aesig -a-> n" == "(aesig,n) : evala"
inductive evala
  intros 
  N:   "(N(n),s) -a-> n"
  X:   "(X(x),s) -a-> s(x)"
  Op1: "(e,s) -a-> n ==> (Op1 f e,s) -a-> f(n)"
  Op2: "[| (e0,s) -a-> n0;  (e1,s)  -a-> n1 |] 
        ==> (Op2 f e0 e1,s) -a-> f n0 n1"

lemmas [intro] = N X Op1 Op2

types n2n2b = "[nat,nat] => bool"

subsection "Boolean expressions"

datatype
  bexp = true
       | false
       | ROp  n2n2b aexp aexp
       | noti bexp
       | andi bexp bexp         (infixl 60)
       | ori  bexp bexp         (infixl 60)

subsection "Evaluation of boolean expressions"
consts evalb    :: "((bexp*state) * bool)set"       
       "-b->"   :: "[bexp*state,bool] => bool"         (infixl 50)

translations
    "besig -b-> b" == "(besig,b) : evalb"

inductive evalb
  -- "avoid clash with ML constructors true, false"
  intros
  tru:   "(true,s) -b-> True"
  fls:   "(false,s) -b-> False"
  ROp:   "[| (a0,s) -a-> n0; (a1,s) -a-> n1 |] 
          ==> (ROp f a0 a1,s) -b-> f n0 n1"
  noti:  "(b,s) -b-> w ==> (noti(b),s) -b-> (~w)"
  andi:  "[| (b0,s) -b-> w0; (b1,s) -b-> w1 |] 
          ==> (b0 andi b1,s) -b-> (w0 & w1)"
  ori:   "[| (b0,s) -b-> w0; (b1,s) -b-> w1 |] 
          ==> (b0 ori b1,s) -b-> (w0 | w1)"

lemmas [intro] = tru fls ROp noti andi ori

subsection "Denotational semantics of arithmetic and boolean expressions"
consts
  A     :: "aexp => state => nat"
  B     :: "bexp => state => bool"

primrec
  "A(N(n)) = (%s. n)"
  "A(X(x)) = (%s. s(x))"
  "A(Op1 f a) = (%s. f(A a s))"
  "A(Op2 f a0 a1) = (%s. f (A a0 s) (A a1 s))"

primrec
  "B(true) = (%s. True)"
  "B(false) = (%s. False)"
  "B(ROp f a0 a1) = (%s. f (A a0 s) (A a1 s))"
  "B(noti(b)) = (%s. ~(B b s))"
  "B(b0 andi b1) = (%s. (B b0 s) & (B b1 s))"
  "B(b0 ori b1) = (%s. (B b0 s) | (B b1 s))"

lemma [simp]: "(N(n),s) -a-> n' = (n = n')"
  by (rule,cases set: evala) auto

lemma [simp]: "(X(x),sigma) -a-> i = (i = sigma x)" 
  by (rule,cases set: evala) auto

lemma	[simp]: 
  "(Op1 f e,sigma) -a-> i = (\<exists>n. i = f n \<and> (e,sigma) -a-> n)" 
  by (rule,cases set: evala) auto

lemma [simp]:
  "(Op2 f a1 a2,sigma) -a-> i = 
  (\<exists>n0 n1. i = f n0 n1 \<and> (a1, sigma) -a-> n0 \<and> (a2, sigma) -a-> n1)"
  by (rule,cases set: evala) auto

lemma [simp]: "((true,sigma) -b-> w) = (w=True)" 
  by (rule,cases set: evalb) auto

lemma [simp]:
  "((false,sigma) -b-> w) = (w=False)" 
  by (rule,cases set: evalb) auto

lemma [simp]:
  "((ROp f a0 a1,sigma) -b-> w) =   
  (? m. (a0,sigma) -a-> m & (? n. (a1,sigma) -a-> n & w = f m n))" 
  by (rule,cases set: evalb) auto

lemma [simp]:  
  "((noti(b),sigma) -b-> w) = (? x. (b,sigma) -b-> x & w = (~x))" 
  by (rule,cases set: evalb) auto

lemma [simp]:
  "((b0 andi b1,sigma) -b-> w) =   
  (? x. (b0,sigma) -b-> x & (? y. (b1,sigma) -b-> y & w = (x&y)))" 
  by (rule,cases set: evalb) auto

lemma [simp]:  
  "((b0 ori b1,sigma) -b-> w) =   
  (? x. (b0,sigma) -b-> x & (? y. (b1,sigma) -b-> y & w = (x|y)))" 
  by (rule,cases set: evalb) auto


lemma aexp_iff [rule_format (no_asm)]: 
  "!n. ((a,s) -a-> n) = (A a s = n)"
  apply (induct_tac "a")
  apply auto
  done

lemma bexp_iff [rule_format (no_asm)]: 
  "!w. ((b,s) -b-> w) = (B b s = w)"
  apply (induct_tac "b")
  apply (auto simp add: aexp_iff)
  done

end

