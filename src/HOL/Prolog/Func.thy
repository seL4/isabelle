(*  Title:    HOL/Prolog/Func.thy
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

header {* Untyped functional language, with call by value semantics *}

theory Func
imports HOHH Algebras
begin

typedecl tm

consts
  abs     :: "(tm => tm) => tm"
  app     :: "tm => tm => tm"

  cond    :: "tm => tm => tm => tm"
  "fix"   :: "(tm => tm) => tm"

  true    :: tm
  false   :: tm
  "and"   :: "tm => tm => tm"       (infixr "and" 999)
  eq      :: "tm => tm => tm"       (infixr "eq" 999)

  Z       :: tm                     ("Z")
  S       :: "tm => tm"
(*
        "++", "--",
        "**"    :: tm => tm => tm       (infixr 999)
*)
        eval    :: "[tm, tm] => bool"

instance tm :: plus ..
instance tm :: minus ..
instance tm :: times ..

axioms   eval: "

eval (abs RR) (abs RR)..
eval (app F X) V :- eval F (abs R) & eval X U & eval (R U) V..

eval (cond P L1 R1) D1 :- eval P true  & eval L1 D1..
eval (cond P L2 R2) D2 :- eval P false & eval R2 D2..
eval (fix G) W   :- eval (G (fix G)) W..

eval true  true ..
eval false false..
eval (P and Q) true  :- eval P true  & eval Q true ..
eval (P and Q) false :- eval P false | eval Q false..
eval (A1 eq B1) true  :- eval A1 C1 & eval B1 C1..
eval (A2 eq B2) false :- True..

eval Z Z..
eval (S N) (S M) :- eval N M..
eval ( Z    + M) K     :- eval      M  K..
eval ((S N) + M) (S K) :- eval (N + M) K..
eval (N     - Z) K     :- eval  N      K..
eval ((S N) - (S M)) K :- eval (N- M)  K..
eval ( Z    * M) Z..
eval ((S N) * M) K :- eval (N * M) L & eval (L + M) K"


lemmas prog_Func = eval

lemma "eval ((S (S Z)) + (S Z)) ?X"
  apply (prolog prog_Func)
  done

lemma "eval (app (fix (%fact. abs(%n. cond (n eq Z) (S Z)
                        (n * (app fact (n - (S Z))))))) (S (S (S Z)))) ?X"
  apply (prolog prog_Func)
  done

end
