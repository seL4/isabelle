(*  Title:      FOL/IFOL.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Intuitionistic first-order logic.
*)

IFOL = Pure +

global

classes
  term < logic

default
  term

types
  o

arities
  o :: logic


consts

  Trueprop      :: o => prop                    ("(_)" 5)
  True, False   :: o

  (* Connectives *)

  "="           :: ['a, 'a] => o                (infixl 50)

  Not           :: o => o                       ("~ _" [40] 40)
  "&"           :: [o, o] => o                  (infixr 35)
  "|"           :: [o, o] => o                  (infixr 30)
  "-->"         :: [o, o] => o                  (infixr 25)
  "<->"         :: [o, o] => o                  (infixr 25)

  (* Quantifiers *)

  All           :: ('a => o) => o               (binder "ALL " 10)
  Ex            :: ('a => o) => o               (binder "EX " 10)
  Ex1           :: ('a => o) => o               (binder "EX! " 10)



syntax
  "~="          :: ['a, 'a] => o                (infixl 50)

translations
  "x ~= y"      == "~ (x = y)"

syntax (symbols)
  Not           :: o => o                       ("\\<not> _" [40] 40)
  "op &"        :: [o, o] => o                  (infixr "\\<and>" 35)
  "op |"        :: [o, o] => o                  (infixr "\\<or>" 30)
  "op -->"      :: [o, o] => o                  (infixr "\\<midarrow>\\<rightarrow>" 25)
  "op <->"      :: [o, o] => o                  (infixr "\\<leftarrow>\\<rightarrow>" 25)
  "ALL "        :: [idts, o] => o               ("(3\\<forall>_./ _)" [0, 10] 10)
  "EX "         :: [idts, o] => o               ("(3\\<exists>_./ _)" [0, 10] 10)
  "EX! "        :: [idts, o] => o               ("(3\\<exists>!_./ _)" [0, 10] 10)
  "op ~="       :: ['a, 'a] => o                (infixl "\\<noteq>" 50)


local

rules

  (* Equality *)

  refl          "a=a"
  subst         "[| a=b;  P(a) |] ==> P(b)"

  (* Propositional logic *)

  conjI         "[| P;  Q |] ==> P&Q"
  conjunct1     "P&Q ==> P"
  conjunct2     "P&Q ==> Q"

  disjI1        "P ==> P|Q"
  disjI2        "Q ==> P|Q"
  disjE         "[| P|Q;  P ==> R;  Q ==> R |] ==> R"

  impI          "(P ==> Q) ==> P-->Q"
  mp            "[| P-->Q;  P |] ==> Q"

  FalseE        "False ==> P"

  (* Definitions *)

  True_def      "True  == False-->False"
  not_def       "~P    == P-->False"
  iff_def       "P<->Q == (P-->Q) & (Q-->P)"

  (* Unique existence *)

  ex1_def       "EX! x. P(x) == EX x. P(x) & (ALL y. P(y) --> y=x)"

  (* Quantifiers *)

  allI          "(!!x. P(x)) ==> (ALL x. P(x))"
  spec          "(ALL x. P(x)) ==> P(x)"

  exI           "P(x) ==> (EX x. P(x))"
  exE           "[| EX x. P(x);  !!x. P(x) ==> R |] ==> R"

  (* Reflection *)

  eq_reflection   "(x=y)   ==> (x==y)"
  iff_reflection  "(P<->Q) ==> (P==Q)"

end


ML val thy_data = [Simplifier.simpset_thy_data];
