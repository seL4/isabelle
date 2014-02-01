(*  Title:      Sequents/ILL.thy
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
  "_Trueprop" :: "single_seqe" ("((_)/ |- (_))" [6,6] 5)
  "_Context"  :: "two_seqe"   ("((_)/ :=: (_))" [6,6] 5)
  "_PromAux"  :: "three_seqe" ("promaux {_||_||_}")

parse_translation {*
  [(@{syntax_const "_Trueprop"}, K (single_tr @{const_syntax Trueprop})),
   (@{syntax_const "_Context"}, K (two_seq_tr @{const_syntax Context})),
   (@{syntax_const "_PromAux"}, K (three_seq_tr @{const_syntax PromAux}))]
*}

print_translation {*
  [(@{const_syntax Trueprop}, K (single_tr' @{syntax_const "_Trueprop"})),
   (@{const_syntax Context}, K (two_seq_tr' @{syntax_const "_Context"})),
   (@{const_syntax PromAux}, K (three_seq_tr' @{syntax_const "_PromAux"}))]
*}

defs

liff_def:        "P o-o Q == (P -o Q) >< (Q -o P)"

aneg_def:        "~A == A -o 0"


axiomatization where

identity:        "P |- P" and

zerol:           "$G, 0, $H |- A" and

  (* RULES THAT DO NOT DIVIDE CONTEXT *)

derelict:   "$F, A, $G |- C ==> $F, !A, $G |- C" and
  (* unfortunately, this one removes !A  *)

contract:  "$F, !A, !A, $G |- C ==> $F, !A, $G |- C" and

weaken:     "$F, $G |- C ==> $G, !A, $F |- C" and
  (* weak form of weakening, in practice just to clean context *)
  (* weaken and contract not needed (CHECK)  *)

promote2:        "promaux{ || $H || B} ==> $H |- !B" and
promote1:        "promaux{!A, $G || $H || B}
                  ==> promaux {$G || $H, !A || B}" and
promote0:        "$G |- A ==> promaux {$G || || A}" and



tensl:     "$H, A, B, $G |- C ==> $H, A >< B, $G |- C" and

impr:      "A, $F |- B ==> $F |- A -o B" and

conjr:           "[| $F |- A ;
                 $F |- B |]
                ==> $F |- (A && B)" and

conjll:          "$G, A, $H |- C ==> $G, A && B, $H |- C" and

conjlr:          "$G, B, $H |- C ==> $G, A && B, $H |- C" and

disjrl:          "$G |- A ==> $G |- A ++ B" and
disjrr:          "$G |- B ==> $G |- A ++ B" and
disjl:           "[| $G, A, $H |- C ;
                     $G, B, $H |- C |]
                 ==> $G, A ++ B, $H |- C" and


      (* RULES THAT DIVIDE CONTEXT *)

tensr:           "[| $F, $J :=: $G;
                     $F |- A ;
                     $J |- B     |]
                     ==> $G |- A >< B" and

impl:            "[| $G, $F :=: $J, $H ;
                     B, $F |- C ;
                        $G |- A |]
                     ==> $J, A -o B, $H |- C" and


cut: " [| $J1, $H1, $J2, $H3, $J3, $H2, $J4, $H4 :=: $F ;
          $H1, $H2, $H3, $H4 |- A ;
          $J1, $J2, A, $J3, $J4 |- B |]  ==> $F |- B" and


  (* CONTEXT RULES *)

context1:     "$G :=: $G" and
context2:     "$F, $G :=: $H, !A, $G ==> $F, A, $G :=: $H, !A, $G" and
context3:     "$F, $G :=: $H, $J ==> $F, A, $G :=: $H, A, $J" and
context4a:    "$F :=: $H, $G ==> $F :=: $H, !A, $G" and
context4b:    "$F, $H :=: $G ==> $F, !A, $H :=: $G" and
context5:     "$F, $G :=: $H ==> $G, $F :=: $H"


ML {*
  val lazy_pack =
    Cla.put_pack Cla.empty_pack @{context}
    |> fold_rev Cla.add_safe @{thms tensl conjr disjl promote0 context2 context3}
    |> fold_rev Cla.add_unsafe @{thms
      identity zerol conjll conjlr
      disjrl disjrr impr tensr impl
      derelict weaken promote1 promote2
      context1 context4a context4b}
    |> Cla.get_pack;
  
  fun promote_tac i =
    REPEAT (resolve_tac @{thms promote0 promote1 promote2} i);
*}

method_setup best_lazy = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.best_tac (Cla.put_pack lazy_pack ctxt)))
*} "lazy classical reasoning"

lemma aux_impl: "$F, $G |- A \<Longrightarrow> $F, !(A -o B), $G |- B"
  apply (rule derelict)
  apply (rule impl)
  apply (rule_tac [2] identity)
  apply (rule context1)
  apply assumption
  done

lemma conj_lemma: " $F, !A, !B, $G |- C \<Longrightarrow> $F, !(A && B), $G |- C"
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

lemma impr_contract: "!A, !A, $G |- B \<Longrightarrow> $G |- (!A) -o B"
  apply (rule impr)
  apply (rule contract)
  apply assumption
  done

lemma impr_contr_der: "A, !A, $G |- B \<Longrightarrow> $G |- (!A) -o B"
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

lemma mp_rule1: "$F, B, $G, $H |- C \<Longrightarrow> $F, A, $G, A -o B, $H |- C"
  apply (rule_tac A = "B" in cut)
  apply (rule_tac [2] ll_mp)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context3)
  apply (rule context1)
  done

lemma mp_rule2: "$F, B, $G, $H |- C \<Longrightarrow> $F, A -o B, $G, A, $H |- C"
  apply (rule_tac A = "B" in cut)
  apply (rule_tac [2] ll_mp)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context3)
  apply (rule context1)
  done

lemma or_to_and: "!((!(A ++ B)) -o 0) |- !( ((!A) -o 0) && ((!B) -o 0))"
  by best_lazy

lemma o_a_rule: "$F, !( ((!A) -o 0) && ((!B) -o 0)), $G |- C \<Longrightarrow>
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

lemma a_not_a_rule: "$J1, !A -o 0, $J2 |- B \<Longrightarrow> $J1, !A -o (!A -o 0), $J2 |- B"
  apply (rule_tac A = "!A -o 0" in cut)
  apply (rule_tac [2] a_not_a)
  prefer 2 apply (assumption)
  apply best_lazy
  done

ML {*
  val safe_pack =
    Cla.put_pack lazy_pack @{context}
    |> fold_rev Cla.add_safe @{thms conj_lemma ll_mp contrad1
        contrad2 mp_rule1 mp_rule2 o_a_rule a_not_a_rule}
    |> Cla.add_unsafe @{thm aux_impl}
    |> Cla.get_pack;

  val power_pack =
    Cla.put_pack safe_pack @{context}
    |> Cla.add_unsafe @{thm impr_contr_der}
    |> Cla.get_pack;
*}


method_setup best_safe =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.best_tac (Cla.put_pack safe_pack ctxt))) *}

method_setup best_power =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.best_tac (Cla.put_pack power_pack ctxt))) *}


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
