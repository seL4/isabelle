(*  Title:      Sequents/ILL.thy
    ID:         $Id$
    Author:     Sara Kalvala and Valeria de Paiva
    Copyright   1995  University of Cambridge
*)

theory ILL
imports Sequents
begin

consts
  Trueprop       :: "two_seqi"

  tens :: "[o, o] => o"        (infixr "><" 35)
  limp :: "[o, o] => o"        (infixr "-o" 45)
  liff :: "[o, o] => o"        (infixr "o-o" 45)
  FShriek :: "o => o"          ("! _" [100] 1000)
  lconj :: "[o, o] => o"       (infixr "&&" 35)
  ldisj :: "[o, o] => o"       (infixr "++" 35)
  zero :: "o"                  ("0")
  top :: "o"                   ("1")
  eye :: "o"                   ("I")
  aneg :: "o=>o"               ("~_")


  (* context manipulation *)

 Context      :: "two_seqi"

  (* promotion rule *)

  PromAux :: "three_seqi"

syntax
  "@Trueprop" :: "single_seqe" ("((_)/ |- (_))" [6,6] 5)
  "@Context"  :: "two_seqe"   ("((_)/ :=: (_))" [6,6] 5)
  "@PromAux"  :: "three_seqe" ("promaux {_||_||_}")

parse_translation {*
  [("@Trueprop", single_tr "Trueprop"),
   ("@Context", two_seq_tr "Context"),
   ("@PromAux", three_seq_tr "PromAux")] *}

print_translation {*
  [("Trueprop", single_tr' "@Trueprop"),
   ("Context", two_seq_tr'"@Context"),
   ("PromAux", three_seq_tr'"@PromAux")] *}

defs

liff_def:        "P o-o Q == (P -o Q) >< (Q -o P)"

aneg_def:        "~A == A -o 0"


axioms

identity:        "P |- P"

zerol:           "$G, 0, $H |- A"

  (* RULES THAT DO NOT DIVIDE CONTEXT *)

derelict:   "$F, A, $G |- C ==> $F, !A, $G |- C"
  (* unfortunately, this one removes !A  *)

contract:  "$F, !A, !A, $G |- C ==> $F, !A, $G |- C"

weaken:     "$F, $G |- C ==> $G, !A, $F |- C"
  (* weak form of weakening, in practice just to clean context *)
  (* weaken and contract not needed (CHECK)  *)

promote2:        "promaux{ || $H || B} ==> $H |- !B"
promote1:        "promaux{!A, $G || $H || B}
                  ==> promaux {$G || $H, !A || B}"
promote0:        "$G |- A ==> promaux {$G || || A}"



tensl:     "$H, A, B, $G |- C ==> $H, A >< B, $G |- C"

impr:      "A, $F |- B ==> $F |- A -o B"

conjr:           "[| $F |- A ;
                 $F |- B |]
                ==> $F |- (A && B)"

conjll:          "$G, A, $H |- C ==> $G, A && B, $H |- C"

conjlr:          "$G, B, $H |- C ==> $G, A && B, $H |- C"

disjrl:          "$G |- A ==> $G |- A ++ B"
disjrr:          "$G |- B ==> $G |- A ++ B"
disjl:           "[| $G, A, $H |- C ;
                     $G, B, $H |- C |]
                 ==> $G, A ++ B, $H |- C"


      (* RULES THAT DIVIDE CONTEXT *)

tensr:           "[| $F, $J :=: $G;
                     $F |- A ;
                     $J |- B     |]
                     ==> $G |- A >< B"

impl:            "[| $G, $F :=: $J, $H ;
                     B, $F |- C ;
                        $G |- A |]
                     ==> $J, A -o B, $H |- C"


cut: " [| $J1, $H1, $J2, $H3, $J3, $H2, $J4, $H4 :=: $F ;
          $H1, $H2, $H3, $H4 |- A ;
          $J1, $J2, A, $J3, $J4 |- B |]  ==> $F |- B"


  (* CONTEXT RULES *)

context1:     "$G :=: $G"
context2:     "$F, $G :=: $H, !A, $G ==> $F, A, $G :=: $H, !A, $G"
context3:     "$F, $G :=: $H, $J ==> $F, A, $G :=: $H, A, $J"
context4a:    "$F :=: $H, $G ==> $F :=: $H, !A, $G"
context4b:    "$F, $H :=: $G ==> $F, !A, $H :=: $G"
context5:     "$F, $G :=: $H ==> $G, $F :=: $H"


ML {*

val lazy_cs = empty_pack
  add_safes [thm "tensl", thm "conjr", thm "disjl", thm "promote0",
    thm "context2", thm "context3"]
  add_unsafes [thm "identity", thm "zerol", thm "conjll", thm "conjlr",
    thm "disjrl", thm "disjrr", thm "impr", thm "tensr", thm "impl",
    thm "derelict", thm "weaken", thm "promote1", thm "promote2",
    thm "context1", thm "context4a", thm "context4b"];

local
  val promote0 = thm "promote0"
  val promote1 = thm "promote1"
  val promote2 = thm "promote2"
in

fun prom_tac n = REPEAT (resolve_tac [promote0,promote1,promote2] n)

end
*}

method_setup best_lazy =
  {* Method.no_args (SIMPLE_METHOD' (best_tac lazy_cs)) *}
  "lazy classical reasoning"

lemma aux_impl: "$F, $G |- A ==> $F, !(A -o B), $G |- B"
  apply (rule derelict)
  apply (rule impl)
  apply (rule_tac [2] identity)
  apply (rule context1)
  apply assumption
  done

lemma conj_lemma: " $F, !A, !B, $G |- C ==> $F, !(A && B), $G |- C"
  apply (rule contract)
  apply (rule_tac A = " (!A) >< (!B) " in cut)
  apply (rule_tac [2] tensr)
  prefer 3
  apply (subgoal_tac "! (A && B) |- !A")
  apply assumption
  apply best_lazy
  prefer 3
  apply (subgoal_tac "! (A && B) |- !B")
  apply assumption
  apply best_lazy
  apply (rule_tac [2] context1)
  apply (rule_tac [2] tensl)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context3)
  apply (rule context1)
  done

lemma impr_contract: "!A, !A, $G |- B ==> $G |- (!A) -o B"
  apply (rule impr)
  apply (rule contract)
  apply assumption
  done

lemma impr_contr_der: "A, !A, $G |- B ==> $G |- (!A) -o B"
  apply (rule impr)
  apply (rule contract)
  apply (rule derelict)
  apply assumption
  done

lemma contrad1: "$F, (!B) -o 0, $G, !B, $H |- A"
  apply (rule impl)
  apply (rule_tac [3] identity)
  apply (rule context3)
  apply (rule context1)
  apply (rule zerol)
  done


lemma contrad2: "$F, !B, $G, (!B) -o 0, $H |- A"
  apply (rule impl)
  apply (rule_tac [3] identity)
  apply (rule context3)
  apply (rule context1)
  apply (rule zerol)
  done

lemma ll_mp: "A -o B, A |- B"
  apply (rule impl)
  apply (rule_tac [2] identity)
  apply (rule_tac [2] identity)
  apply (rule context1)
  done

lemma mp_rule1: "$F, B, $G, $H |- C ==> $F, A, $G, A -o B, $H |- C"
  apply (rule_tac A = "B" in cut)
  apply (rule_tac [2] ll_mp)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context3)
  apply (rule context1)
  done

lemma mp_rule2: "$F, B, $G, $H |- C ==> $F, A -o B, $G, A, $H |- C"
  apply (rule_tac A = "B" in cut)
  apply (rule_tac [2] ll_mp)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context3)
  apply (rule context1)
  done

lemma or_to_and: "!((!(A ++ B)) -o 0) |- !( ((!A) -o 0) && ((!B) -o 0))"
  by best_lazy

lemma o_a_rule: "$F, !( ((!A) -o 0) && ((!B) -o 0)), $G |- C ==>  
          $F, !((!(A ++ B)) -o 0), $G |- C"
  apply (rule cut)
  apply (rule_tac [2] or_to_and)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context1)
  done

lemma conj_imp: "((!A) -o C) ++ ((!B) -o C) |- (!(A && B)) -o C"
  apply (rule impr)
  apply (rule conj_lemma)
  apply (rule disjl)
  apply (rule mp_rule1, best_lazy)+
  done

lemma not_imp: "!A, !((!B) -o 0) |- (!((!A) -o B)) -o 0"
  by best_lazy

lemma a_not_a: "!A -o (!A -o 0) |- !A -o 0"
  apply (rule impr)
  apply (rule contract)
  apply (rule impl)
  apply (rule_tac [3] identity)
  apply (rule context1)
  apply best_lazy
  done

lemma a_not_a_rule: "$J1, !A -o 0, $J2 |- B ==> $J1, !A -o (!A -o 0), $J2 |- B"
  apply (rule_tac A = "!A -o 0" in cut)
  apply (rule_tac [2] a_not_a)
  prefer 2 apply (assumption)
  apply best_lazy
  done

ML {*

val safe_cs = lazy_cs add_safes [thm "conj_lemma", thm "ll_mp", thm "contrad1",
                                 thm "contrad2", thm "mp_rule1", thm "mp_rule2", thm "o_a_rule",
                                 thm "a_not_a_rule"]
                      add_unsafes [thm "aux_impl"];

val power_cs = safe_cs add_unsafes [thm "impr_contr_der"];
*}


method_setup best_safe =
  {* Method.no_args (SIMPLE_METHOD' (best_tac safe_cs)) *} ""

method_setup best_power =
  {* Method.no_args (SIMPLE_METHOD' (best_tac power_cs)) *} ""


(* Some examples from Troelstra and van Dalen *)

lemma "!((!A) -o ((!B) -o 0)) |- (!(A && B)) -o 0"
  by best_safe

lemma "!((!(A && B)) -o 0) |- !((!A) -o ((!B) -o 0))"
  by best_safe

lemma "!( (!((! ((!A) -o B) ) -o 0)) -o 0) |-
        (!A) -o ( (!  ((!B) -o 0)) -o 0)"
  by best_safe

lemma "!(  (!A) -o ( (!  ((!B) -o 0)) -o 0) ) |-
          (!((! ((!A) -o B) ) -o 0)) -o 0"
  by best_power

end
