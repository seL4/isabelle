(*  Title:    HOL/Prolog/Func.thy
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

section \<open>Untyped functional language, with call by value semantics\<close>

theory Func
imports HOHH
begin

typedecl tm

axiomatization
  abs     :: "(tm \<Rightarrow> tm) \<Rightarrow> tm" and
  app     :: "tm \<Rightarrow> tm \<Rightarrow> tm" and

  cond    :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" and
  "fix"   :: "(tm \<Rightarrow> tm) \<Rightarrow> tm" and

  true    :: tm and
  false   :: tm and
  "and"   :: "tm \<Rightarrow> tm \<Rightarrow> tm"       (infixr \<open>and\<close> 999) and
  eq      :: "tm \<Rightarrow> tm \<Rightarrow> tm"       (infixr \<open>eq\<close> 999) and

  Z       :: tm                     (\<open>Z\<close>) and
  S       :: "tm \<Rightarrow> tm" and

  plus    :: "tm \<Rightarrow> tm \<Rightarrow> tm"       (infixl \<open>+\<close> 65) and
  minus   :: "tm \<Rightarrow> tm \<Rightarrow> tm"       (infixl \<open>-\<close> 65) and
  times   :: "tm \<Rightarrow> tm \<Rightarrow> tm"       (infixl \<open>*\<close> 70) and

  eval    :: "tm \<Rightarrow> tm \<Rightarrow> bool" where

eval: "

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

schematic_goal "eval ((S (S Z)) + (S Z)) ?X"
  apply (prolog prog_Func)
  done

schematic_goal "eval (app (fix (%fact. abs(%n. cond (n eq Z) (S Z)
                        (n * (app fact (n - (S Z))))))) (S (S (S Z)))) ?X"
  apply (prolog prog_Func)
  done

end
