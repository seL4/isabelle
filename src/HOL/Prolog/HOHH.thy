(*  Title:    HOL/Prolog/HOHH.thy
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

section \<open>Higher-order hereditary Harrop formulas\<close>

theory HOHH
imports HOL.HOL
begin

ML_file \<open>prolog.ML\<close>

method_setup ptac =
  \<open>Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (Prolog.ptac ctxt thms))\<close>
  "basic Lambda Prolog interpreter"

method_setup prolog =
  \<open>Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD (Prolog.prolog_tac ctxt thms))\<close>
  "Lambda Prolog interpreter"

consts

(* D-formulas (programs):  D ::= !x. D | D .. D | D :- G | A            *)
  Dand        :: "[bool, bool] => bool"         (infixr \<open>..\<close> 28)
  Dif        :: "[bool, bool] => bool"         (infixl \<open>:-\<close> 29)

(* G-formulas (goals):     G ::= A | G & G | G | G | ? x. G
                               | True | !x. G | D => G                  *)
(*Dand'         :: "[bool, bool] => bool"         (infixr "," 35)*)
  Dimp          :: "[bool, bool] => bool"         (infixr \<open>=>\<close> 27)

translations

  "D :- G"      =>      "G --> D"
  "D1 .. D2"    =>      "D1 & D2"
(*"G1 , G2"     =>      "G1 & G2"*)
  "D => G"      =>      "D --> G"

end
