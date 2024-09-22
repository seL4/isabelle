(*  Title:      Sequents/ILL.thy
    Author:     Sara Kalvala and Valeria de Paiva
    Copyright   1995  University of Cambridge
*)

theory ILL
imports Sequents
begin

consts
  Trueprop       :: "two_seqi"

  tens :: "[o, o] \<Rightarrow> o"        (infixr \<open>><\<close> 35)
  limp :: "[o, o] \<Rightarrow> o"        (infixr \<open>-o\<close> 45)
  FShriek :: "o \<Rightarrow> o"          (\<open>! _\<close> [100] 1000)
  lconj :: "[o, o] \<Rightarrow> o"       (infixr \<open>&&\<close> 35)
  ldisj :: "[o, o] \<Rightarrow> o"       (infixr \<open>++\<close> 35)
  zero :: "o"                  (\<open>0\<close>)
  top :: "o"                   (\<open>1\<close>)
  eye :: "o"                   (\<open>I\<close>)


  (* context manipulation *)

 Context      :: "two_seqi"

  (* promotion rule *)

  PromAux :: "three_seqi"

syntax
  "_Trueprop" :: "single_seqe" (\<open>(\<open>notation=judgment\<close>(_)/ \<turnstile> (_))\<close> [6,6] 5)
  "_Context"  :: "two_seqe"   (\<open>(\<open>notation=\<open>infix Context\<close>\<close>(_)/ :=: (_))\<close> [6,6] 5)
  "_PromAux"  :: "three_seqe" (\<open>promaux {_||_||_}\<close>)

parse_translation \<open>
  [(\<^syntax_const>\<open>_Trueprop\<close>, K (single_tr \<^const_syntax>\<open>Trueprop\<close>)),
   (\<^syntax_const>\<open>_Context\<close>, K (two_seq_tr \<^const_syntax>\<open>Context\<close>)),
   (\<^syntax_const>\<open>_PromAux\<close>, K (three_seq_tr \<^const_syntax>\<open>PromAux\<close>))]
\<close>

print_translation \<open>
  [(\<^const_syntax>\<open>Trueprop\<close>, K (single_tr' \<^syntax_const>\<open>_Trueprop\<close>)),
   (\<^const_syntax>\<open>Context\<close>, K (two_seq_tr' \<^syntax_const>\<open>_Context\<close>)),
   (\<^const_syntax>\<open>PromAux\<close>, K (three_seq_tr' \<^syntax_const>\<open>_PromAux\<close>))]
\<close>

definition liff :: "[o, o] \<Rightarrow> o"  (infixr \<open>o-o\<close> 45)
  where "P o-o Q == (P -o Q) >< (Q -o P)"

definition aneg :: "o\<Rightarrow>o"  (\<open>~_\<close>)
  where "~A == A -o 0"


axiomatization where

identity:        "P \<turnstile> P" and

zerol:           "$G, 0, $H \<turnstile> A" and

  (* RULES THAT DO NOT DIVIDE CONTEXT *)

derelict:   "$F, A, $G \<turnstile> C \<Longrightarrow> $F, !A, $G \<turnstile> C" and
  (* unfortunately, this one removes !A  *)

contract:  "$F, !A, !A, $G \<turnstile> C \<Longrightarrow> $F, !A, $G \<turnstile> C" and

weaken:     "$F, $G \<turnstile> C \<Longrightarrow> $G, !A, $F \<turnstile> C" and
  (* weak form of weakening, in practice just to clean context *)
  (* weaken and contract not needed (CHECK)  *)

promote2:        "promaux{ || $H || B} \<Longrightarrow> $H \<turnstile> !B" and
promote1:        "promaux{!A, $G || $H || B}
                  \<Longrightarrow> promaux {$G || $H, !A || B}" and
promote0:        "$G \<turnstile> A \<Longrightarrow> promaux {$G || || A}" and



tensl:     "$H, A, B, $G \<turnstile> C \<Longrightarrow> $H, A >< B, $G \<turnstile> C" and

impr:      "A, $F \<turnstile> B \<Longrightarrow> $F \<turnstile> A -o B" and

conjr:           "\<lbrakk>$F \<turnstile> A ;
                 $F \<turnstile> B\<rbrakk>
                \<Longrightarrow> $F \<turnstile> (A && B)" and

conjll:          "$G, A, $H \<turnstile> C \<Longrightarrow> $G, A && B, $H \<turnstile> C" and

conjlr:          "$G, B, $H \<turnstile> C \<Longrightarrow> $G, A && B, $H \<turnstile> C" and

disjrl:          "$G \<turnstile> A \<Longrightarrow> $G \<turnstile> A ++ B" and
disjrr:          "$G \<turnstile> B \<Longrightarrow> $G \<turnstile> A ++ B" and
disjl:           "\<lbrakk>$G, A, $H \<turnstile> C ;
                   $G, B, $H \<turnstile> C\<rbrakk>
                 \<Longrightarrow> $G, A ++ B, $H \<turnstile> C" and


      (* RULES THAT DIVIDE CONTEXT *)

tensr:           "\<lbrakk>$F, $J :=: $G;
                   $F \<turnstile> A ;
                   $J \<turnstile> B\<rbrakk>
                     \<Longrightarrow> $G \<turnstile> A >< B" and

impl:            "\<lbrakk>$G, $F :=: $J, $H ;
                   B, $F \<turnstile> C ;
                   $G \<turnstile> A\<rbrakk>
                     \<Longrightarrow> $J, A -o B, $H \<turnstile> C" and


cut: "\<lbrakk> $J1, $H1, $J2, $H3, $J3, $H2, $J4, $H4 :=: $F ;
        $H1, $H2, $H3, $H4 \<turnstile> A ;
        $J1, $J2, A, $J3, $J4 \<turnstile> B\<rbrakk> \<Longrightarrow> $F \<turnstile> B" and


  (* CONTEXT RULES *)

context1:     "$G :=: $G" and
context2:     "$F, $G :=: $H, !A, $G \<Longrightarrow> $F, A, $G :=: $H, !A, $G" and
context3:     "$F, $G :=: $H, $J \<Longrightarrow> $F, A, $G :=: $H, A, $J" and
context4a:    "$F :=: $H, $G \<Longrightarrow> $F :=: $H, !A, $G" and
context4b:    "$F, $H :=: $G \<Longrightarrow> $F, !A, $H :=: $G" and
context5:     "$F, $G :=: $H \<Longrightarrow> $G, $F :=: $H"

text "declarations for lazy classical reasoning:"
lemmas [safe] =
  context3
  context2
  promote0
  disjl
  conjr
  tensl
lemmas [unsafe] =
  context4b
  context4a
  context1
  promote2
  promote1
  weaken
  derelict
  impl
  tensr
  impr
  disjrr
  disjrl
  conjlr
  conjll
  zerol
  identity

lemma aux_impl: "$F, $G \<turnstile> A \<Longrightarrow> $F, !(A -o B), $G \<turnstile> B"
  apply (rule derelict)
  apply (rule impl)
  apply (rule_tac [2] identity)
  apply (rule context1)
  apply assumption
  done

lemma conj_lemma: " $F, !A, !B, $G \<turnstile> C \<Longrightarrow> $F, !(A && B), $G \<turnstile> C"
  apply (rule contract)
  apply (rule_tac A = " (!A) >< (!B) " in cut)
  apply (rule_tac [2] tensr)
  prefer 3
  apply (subgoal_tac "! (A && B) \<turnstile> !A")
  apply assumption
  apply best
  prefer 3
  apply (subgoal_tac "! (A && B) \<turnstile> !B")
  apply assumption
  apply best
  apply (rule_tac [2] context1)
  apply (rule_tac [2] tensl)
  prefer 2 apply assumption
  apply (rule context3)
  apply (rule context3)
  apply (rule context1)
  done

lemma impr_contract: "!A, !A, $G \<turnstile> B \<Longrightarrow> $G \<turnstile> (!A) -o B"
  apply (rule impr)
  apply (rule contract)
  apply assumption
  done

lemma impr_contr_der: "A, !A, $G \<turnstile> B \<Longrightarrow> $G \<turnstile> (!A) -o B"
  apply (rule impr)
  apply (rule contract)
  apply (rule derelict)
  apply assumption
  done

lemma contrad1: "$F, (!B) -o 0, $G, !B, $H \<turnstile> A"
  apply (rule impl)
  apply (rule_tac [3] identity)
  apply (rule context3)
  apply (rule context1)
  apply (rule zerol)
  done


lemma contrad2: "$F, !B, $G, (!B) -o 0, $H \<turnstile> A"
  apply (rule impl)
  apply (rule_tac [3] identity)
  apply (rule context3)
  apply (rule context1)
  apply (rule zerol)
  done

lemma ll_mp: "A -o B, A \<turnstile> B"
  apply (rule impl)
  apply (rule_tac [2] identity)
  apply (rule_tac [2] identity)
  apply (rule context1)
  done

lemma mp_rule1: "$F, B, $G, $H \<turnstile> C \<Longrightarrow> $F, A, $G, A -o B, $H \<turnstile> C"
  apply (rule_tac A = "B" in cut)
  apply (rule_tac [2] ll_mp)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context3)
  apply (rule context1)
  done

lemma mp_rule2: "$F, B, $G, $H \<turnstile> C \<Longrightarrow> $F, A -o B, $G, A, $H \<turnstile> C"
  apply (rule_tac A = "B" in cut)
  apply (rule_tac [2] ll_mp)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context3)
  apply (rule context1)
  done

lemma or_to_and: "!((!(A ++ B)) -o 0) \<turnstile> !( ((!A) -o 0) && ((!B) -o 0))"
  by best

lemma o_a_rule: "$F, !( ((!A) -o 0) && ((!B) -o 0)), $G \<turnstile> C \<Longrightarrow>
          $F, !((!(A ++ B)) -o 0), $G \<turnstile> C"
  apply (rule cut)
  apply (rule_tac [2] or_to_and)
  prefer 2 apply (assumption)
  apply (rule context3)
  apply (rule context1)
  done

lemma conj_imp: "((!A) -o C) ++ ((!B) -o C) \<turnstile> (!(A && B)) -o C"
  apply (rule impr)
  apply (rule conj_lemma)
  apply (rule disjl)
  apply (rule mp_rule1, best)+
  done

lemma not_imp: "!A, !((!B) -o 0) \<turnstile> (!((!A) -o B)) -o 0"
  by best

lemma a_not_a: "!A -o (!A -o 0) \<turnstile> !A -o 0"
  apply (rule impr)
  apply (rule contract)
  apply (rule impl)
  apply (rule_tac [3] identity)
  apply (rule context1)
  apply best
  done

lemma a_not_a_rule: "$J1, !A -o 0, $J2 \<turnstile> B \<Longrightarrow> $J1, !A -o (!A -o 0), $J2 \<turnstile> B"
  apply (rule_tac A = "!A -o 0" in cut)
  apply (rule_tac [2] a_not_a)
  prefer 2 apply assumption
  apply best
  done

ML \<open>
  val safe_pack =
    \<^context>
    |> fold_rev Cla.add_safe @{thms conj_lemma ll_mp contrad1
        contrad2 mp_rule1 mp_rule2 o_a_rule a_not_a_rule}
    |> Cla.add_unsafe @{thm aux_impl}
    |> Cla.get_pack;

  val power_pack =
    Cla.put_pack safe_pack \<^context>
    |> Cla.add_unsafe @{thm impr_contr_der}
    |> Cla.get_pack;
\<close>

method_setup best_safe =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.best_tac (Cla.put_pack safe_pack ctxt)))\<close>

method_setup best_power =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.best_tac (Cla.put_pack power_pack ctxt)))\<close>


(* Some examples from Troelstra and van Dalen *)

lemma "!((!A) -o ((!B) -o 0)) \<turnstile> (!(A && B)) -o 0"
  by best_safe

lemma "!((!(A && B)) -o 0) \<turnstile> !((!A) -o ((!B) -o 0))"
  by best_safe

lemma "!( (!((! ((!A) -o B) ) -o 0)) -o 0) \<turnstile>
        (!A) -o ( (!  ((!B) -o 0)) -o 0)"
  by best_safe

lemma "!(  (!A) -o ( (!  ((!B) -o 0)) -o 0) ) \<turnstile>
          (!((! ((!A) -o B) ) -o 0)) -o 0"
  by best_power

end
