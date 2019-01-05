(*  Title:      HOL/UNITY/Simple/NSP_Bad.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Original file is ../Auth/NS_Public_Bad
*)

section\<open>Analyzing the Needham-Schroeder Public-Key Protocol in UNITY\<close>

theory NSP_Bad imports "HOL-Auth.Public" "../UNITY_Main" begin

text\<open>This is the flawed version, vulnerable to Lowe's attack.
From page 260 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989).
\<close>

type_synonym state = "event list"

  (*The spy MAY say anything he CAN say.  We do not expect him to
    invent new nonces here, but he can also use NS1.  Common to
    all similar protocols.*)
definition
  Fake :: "(state*state) set"
  where "Fake = {(s,s').
              \<exists>B X. s' = Says Spy B X # s
                    & X \<in> synth (analz (spies s))}"

  (*The numeric suffixes on A identify the rule*)

  (*Alice initiates a protocol run, sending a nonce to Bob*)
definition
  NS1 :: "(state*state) set"
  where "NS1 = {(s1,s').
             \<exists>A1 B NA.
                 s' = Says A1 B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A1\<rbrace>) # s1
               & Nonce NA \<notin> used s1}"

  (*Bob responds to Alice's message with a further nonce*)
definition
  NS2 :: "(state*state) set"
  where "NS2 = {(s2,s').
             \<exists>A' A2 B NA NB.
                 s' = Says B A2 (Crypt (pubK A2) \<lbrace>Nonce NA, Nonce NB\<rbrace>) # s2
               & Says A' B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A2\<rbrace>) \<in> set s2
               & Nonce NB \<notin> used s2}"

  (*Alice proves her existence by sending NB back to Bob.*)
definition
  NS3 :: "(state*state) set"
  where "NS3 = {(s3,s').
             \<exists>A3 B' B NA NB.
                 s' = Says A3 B (Crypt (pubK B) (Nonce NB)) # s3
               & Says A3  B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A3\<rbrace>) \<in> set s3
               & Says B' A3 (Crypt (pubK A3) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set s3}"


definition Nprg :: "state program" where
    (*Initial trace is empty*)
    "Nprg = mk_total_program({[]}, {Fake, NS1, NS2, NS3}, UNIV)"

declare spies_partsEs [elim]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]

text\<open>For other theories, e.g. Mutex and Lift, using [iff] slows proofs down.
  Here, it facilitates re-use of the Auth proofs.\<close>

declare Fake_def [THEN def_act_simp, iff]
declare NS1_def [THEN def_act_simp, iff]
declare NS2_def [THEN def_act_simp, iff]
declare NS3_def [THEN def_act_simp, iff]

declare Nprg_def [THEN def_prg_Init, simp]


text\<open>A "possibility property": there are traces that reach the end.
  Replace by LEADSTO proof!\<close>
lemma "A \<noteq> B ==>
       \<exists>NB. \<exists>s \<in> reachable Nprg. Says A B (Crypt (pubK B) (Nonce NB)) \<in> set s"
apply (intro exI bexI)
apply (rule_tac [2] act = "totalize_act NS3" in reachable.Acts)
apply (rule_tac [3] act = "totalize_act NS2" in reachable.Acts)
apply (rule_tac [4] act = "totalize_act NS1" in reachable.Acts)
apply (rule_tac [5] reachable.Init)
apply (simp_all (no_asm_simp) add: Nprg_def totalize_act_def)
apply auto
done


subsection\<open>Inductive Proofs about \<^term>\<open>ns_public\<close>\<close>

lemma ns_constrainsI:
     "(!!act s s'. [| act \<in> {Id, Fake, NS1, NS2, NS3};
                      (s,s') \<in> act;  s \<in> A |] ==> s' \<in> A')
      ==> Nprg \<in> A co A'"
apply (simp add: Nprg_def mk_total_program_def)
apply (rule constrainsI, auto)
done


text\<open>This ML code does the inductions directly.\<close>
ML\<open>
fun ns_constrains_tac ctxt i =
  SELECT_GOAL
    (EVERY
     [REPEAT (eresolve_tac ctxt @{thms Always_ConstrainsI} 1),
      REPEAT (resolve_tac ctxt [@{thm StableI}, @{thm stableI}, @{thm constrains_imp_Constrains}] 1),
      resolve_tac ctxt @{thms ns_constrainsI} 1,
      full_simp_tac ctxt 1,
      REPEAT (FIRSTGOAL (eresolve_tac ctxt [disjE])),
      ALLGOALS (clarify_tac (ctxt delrules [impI, @{thm impCE}])),
      REPEAT (FIRSTGOAL (analz_mono_contra_tac ctxt)),
      ALLGOALS (asm_simp_tac ctxt)]) i;

(*Tactic for proving secrecy theorems*)
fun ns_induct_tac ctxt =
  (SELECT_GOAL o EVERY)
     [resolve_tac ctxt @{thms AlwaysI} 1,
      force_tac ctxt 1,
      (*"reachable" gets in here*)
      resolve_tac ctxt [@{thm Always_reachable} RS @{thm Always_ConstrainsI} RS @{thm StableI}] 1,
      ns_constrains_tac ctxt 1];
\<close>

method_setup ns_induct = \<open>
    Scan.succeed (SIMPLE_METHOD' o ns_induct_tac)\<close>
    "for inductive reasoning about the Needham-Schroeder protocol"

text\<open>Converts invariants into statements about reachable states\<close>
lemmas Always_Collect_reachableD =
     Always_includes_reachable [THEN subsetD, THEN CollectD]

text\<open>Spy never sees another agent's private key! (unless it's bad at start)\<close>
lemma Spy_see_priK:
     "Nprg \<in> Always {s. (Key (priK A) \<in> parts (spies s)) = (A \<in> bad)}"
apply ns_induct
apply blast
done
declare Spy_see_priK [THEN Always_Collect_reachableD, simp]

lemma Spy_analz_priK:
     "Nprg \<in> Always {s. (Key (priK A) \<in> analz (spies s)) = (A \<in> bad)}"
by (rule Always_reachable [THEN Always_weaken], auto)
declare Spy_analz_priK [THEN Always_Collect_reachableD, simp]


subsection\<open>Authenticity properties obtained from NS2\<close>

text\<open>It is impossible to re-use a nonce in both NS1 and NS2 provided the
     nonce is secret.  (Honest users generate fresh nonces.)\<close>
lemma no_nonce_NS1_NS2:
 "Nprg
  \<in> Always {s. Crypt (pubK C) \<lbrace>NA', Nonce NA\<rbrace> \<in> parts (spies s) -->
                Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies s) -->
                Nonce NA \<in> analz (spies s)}"
apply ns_induct
apply (blast intro: analz_insertI)+
done

text\<open>Adding it to the claset slows down proofs...\<close>
lemmas no_nonce_NS1_NS2_reachable =
       no_nonce_NS1_NS2 [THEN Always_Collect_reachableD, rule_format]


text\<open>Unicity for NS1: nonce NA identifies agents A and B\<close>
lemma unique_NA_lemma:
     "Nprg
  \<in> Always {s. Nonce NA \<notin> analz (spies s) -->
                Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts(spies s) -->
                Crypt(pubK B') \<lbrace>Nonce NA, Agent A'\<rbrace> \<in> parts(spies s) -->
                A=A' & B=B'}"
apply ns_induct
apply auto
txt\<open>Fake, NS1 are non-trivial\<close>
done

text\<open>Unicity for NS1: nonce NA identifies agents A and B\<close>
lemma unique_NA:
     "[| Crypt(pubK B)  \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts(spies s);
         Crypt(pubK B') \<lbrace>Nonce NA, Agent A'\<rbrace> \<in> parts(spies s);
         Nonce NA \<notin> analz (spies s);
         s \<in> reachable Nprg |]
      ==> A=A' & B=B'"
by (blast dest: unique_NA_lemma [THEN Always_Collect_reachableD])


text\<open>Secrecy: Spy does not see the nonce sent in msg NS1 if A and B are secure\<close>
lemma Spy_not_see_NA:
     "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Says A B (Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set s
                  --> Nonce NA \<notin> analz (spies s)}"
apply ns_induct
txt\<open>NS3\<close>
prefer 4 apply (blast intro: no_nonce_NS1_NS2_reachable)
txt\<open>NS2\<close>
prefer 3 apply (blast dest: unique_NA)
txt\<open>NS1\<close>
prefer 2 apply blast
txt\<open>Fake\<close>
apply spy_analz
done


text\<open>Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.\<close>
lemma A_trusts_NS2:
 "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Says A B (Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set s &
                  Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts (knows Spy s)
         --> Says B A (Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set s}"
  (*insert an invariant for use in some of the subgoals*)
apply (insert Spy_not_see_NA [of A B NA], simp, ns_induct)
apply (auto dest: unique_NA)
done


text\<open>If the encrypted message appears then it originated with Alice in NS1\<close>
lemma B_trusts_NS1:
     "Nprg \<in> Always
              {s. Nonce NA \<notin> analz (spies s) -->
                  Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies s)
         --> Says A B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set s}"
apply ns_induct
apply blast
done


subsection\<open>Authenticity properties obtained from NS2\<close>

text\<open>Unicity for NS2: nonce NB identifies nonce NA and agent A.
   Proof closely follows that of \<open>unique_NA\<close>.\<close>
lemma unique_NB_lemma:
 "Nprg
  \<in> Always {s. Nonce NB \<notin> analz (spies s)  -->
                Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts (spies s) -->
                Crypt(pubK A') \<lbrace>Nonce NA', Nonce NB\<rbrace> \<in> parts(spies s) -->
                A=A' & NA=NA'}"
apply ns_induct
apply auto
txt\<open>Fake, NS2 are non-trivial\<close>
done

lemma unique_NB:
     "[| Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts(spies s);
         Crypt(pubK A') \<lbrace>Nonce NA', Nonce NB\<rbrace> \<in> parts(spies s);
         Nonce NB \<notin> analz (spies s);
         s \<in> reachable Nprg |]
      ==> A=A' & NA=NA'"
apply (blast dest: unique_NB_lemma [THEN Always_Collect_reachableD])
done


text\<open>NB remains secret PROVIDED Alice never responds with round 3\<close>
lemma Spy_not_see_NB:
     "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set s &
                  (\<forall>C. Says A C (Crypt (pubK C) (Nonce NB)) \<notin> set s)
                  --> Nonce NB \<notin> analz (spies s)}"
apply ns_induct
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt\<open>NS3: because NB determines A\<close>
prefer 4 apply (blast dest: unique_NB)
txt\<open>NS2: by freshness and unicity of NB\<close>
prefer 3 apply (blast intro: no_nonce_NS1_NS2_reachable)
txt\<open>NS1: by freshness\<close>
prefer 2 apply blast
txt\<open>Fake\<close>
apply spy_analz
done



text\<open>Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3--to somebody....\<close>
lemma B_trusts_NS3:
     "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Crypt (pubK B) (Nonce NB) \<in> parts (spies s) &
                  Says B A  (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set s
                  --> (\<exists>C. Says A C (Crypt (pubK C) (Nonce NB)) \<in> set s)}"
  (*insert an invariant for use in some of the subgoals*)
apply (insert Spy_not_see_NB [of A B NA NB], simp, ns_induct)
apply (simp_all (no_asm_simp) add: ex_disj_distrib)
apply auto
txt\<open>NS3: because NB determines A. This use of \<open>unique_NB\<close> is robust.\<close>
apply (blast intro: unique_NB [THEN conjunct1])
done


text\<open>Can we strengthen the secrecy theorem?  NO\<close>
lemma "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set s
                  --> Nonce NB \<notin> analz (spies s)}"
apply ns_induct
apply auto
txt\<open>Fake\<close>
apply spy_analz
txt\<open>NS2: by freshness and unicity of NB\<close>
 apply (blast intro: no_nonce_NS1_NS2_reachable)
txt\<open>NS3: unicity of NB identifies A and NA, but not B\<close>
apply (frule_tac A'=A in Says_imp_spies [THEN parts.Inj, THEN unique_NB])
apply (erule Says_imp_spies [THEN parts.Inj], auto)
apply (rename_tac s B' C)
txt\<open>This is the attack!
@{subgoals[display,indent=0,margin=65]}
\<close>
oops


(*
THIS IS THE ATTACK!
[| A \<notin> bad; B \<notin> bad |]
==> Nprg
   \<in> Always
       {s. Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set s -->
           Nonce NB \<notin> analz (knows Spy s)}
 1. !!s B' C.
       [| A \<notin> bad; B \<notin> bad; s \<in> reachable Nprg
          Says A C (Crypt (pubK C) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set s;
          Says B' A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set s;
          C \<in> bad; Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set s;
          Nonce NB \<notin> analz (knows Spy s) |]
       ==> False
*)

end
