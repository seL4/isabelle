(*  Title:      HOL/Auth/NSP_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

ML{*add_path "$ISABELLE_HOME/src/HOL/Auth"*}

Original file is ../Auth/NS_Public_Bad
*)

header{*Analyzing the Needham-Schroeder Public-Key Protocol in UNITY*}

theory NSP_Bad = Public + UNITY_Main:

text{*This is the flawed version, vulnerable to Lowe's attack.
From page 260 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989).
*}

types state = "event list"

constdefs

  (*The spy MAY say anything he CAN say.  We do not expect him to
    invent new nonces here, but he can also use NS1.  Common to
    all similar protocols.*)
  Fake :: "(state*state) set"
    "Fake == {(s,s').
	      \<exists>B X. s' = Says Spy B X # s
		    & X \<in> synth (analz (spies s))}"

  (*The numeric suffixes on A identify the rule*)

  (*Alice initiates a protocol run, sending a nonce to Bob*)
  NS1 :: "(state*state) set"
    "NS1 == {(s1,s').
	     \<exists>A1 B NA.
	         s' = Says A1 B (Crypt (pubK B) {|Nonce NA, Agent A1|}) # s1
	       & Nonce NA \<notin> used s1}"

  (*Bob responds to Alice's message with a further nonce*)
  NS2 :: "(state*state) set"
    "NS2 == {(s2,s').
	     \<exists>A' A2 B NA NB.
	         s' = Says B A2 (Crypt (pubK A2) {|Nonce NA, Nonce NB|}) # s2
               & Says A' B (Crypt (pubK B) {|Nonce NA, Agent A2|}) \<in> set s2
	       & Nonce NB \<notin> used s2}"

  (*Alice proves her existence by sending NB back to Bob.*)
  NS3 :: "(state*state) set"
    "NS3 == {(s3,s').
	     \<exists>A3 B' B NA NB.
	         s' = Says A3 B (Crypt (pubK B) (Nonce NB)) # s3
               & Says A3  B (Crypt (pubK B) {|Nonce NA, Agent A3|}) \<in> set s3
	       & Says B' A3 (Crypt (pubK A3) {|Nonce NA, Nonce NB|}) \<in> set s3}"


constdefs
  Nprg :: "state program"
    (*Initial trace is empty*)
    "Nprg == mk_total_program({[]}, {Fake, NS1, NS2, NS3}, UNIV)"

declare spies_partsEs [elim]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]

text{*For other theories, e.g. Mutex and Lift, using [iff] slows proofs down.
  Here, it facilitates re-use of the Auth proofs.*}

declare Fake_def [THEN def_act_simp, iff]
declare NS1_def [THEN def_act_simp, iff]
declare NS2_def [THEN def_act_simp, iff]
declare NS3_def [THEN def_act_simp, iff]

declare Nprg_def [THEN def_prg_Init, simp]


text{*A "possibility property": there are traces that reach the end.
  Replace by LEADSTO proof!*}
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


subsection{*Inductive Proofs about @{term ns_public}*}

lemma ns_constrainsI:
     "(!!act s s'. [| act \<in> {Id, Fake, NS1, NS2, NS3};
                      (s,s') \<in> act;  s \<in> A |] ==> s' \<in> A')
      ==> Nprg \<in> A co A'"
apply (simp add: Nprg_def mk_total_program_def)
apply (rule constrainsI, auto)
done


text{*This ML code does the inductions directly.*}
ML{*
val ns_constrainsI = thm "ns_constrainsI";

fun ns_constrains_tac(cs,ss) i =
   SELECT_GOAL
      (EVERY [REPEAT (etac Always_ConstrainsI 1),
	      REPEAT (resolve_tac [StableI, stableI,
				   constrains_imp_Constrains] 1),
	      rtac ns_constrainsI 1,
	      full_simp_tac ss 1,
	      REPEAT (FIRSTGOAL (etac disjE)),
	      ALLGOALS (clarify_tac (cs delrules [impI,impCE])),
	      REPEAT (FIRSTGOAL analz_mono_contra_tac),
	      ALLGOALS (asm_simp_tac ss)]) i;

(*Tactic for proving secrecy theorems*)
fun ns_induct_tac(cs,ss) =
  (SELECT_GOAL o EVERY)
     [rtac AlwaysI 1,
      force_tac (cs,ss) 1,
      (*"reachable" gets in here*)
      rtac (Always_reachable RS Always_ConstrainsI RS StableI) 1,
      ns_constrains_tac(cs,ss) 1];
*}

method_setup ns_induct = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            ns_induct_tac (Classical.get_local_claset ctxt,
                               Simplifier.get_local_simpset ctxt) 1)) *}
    "for inductive reasoning about the Needham-Schroeder protocol"

text{*Converts invariants into statements about reachable states*}
lemmas Always_Collect_reachableD =
     Always_includes_reachable [THEN subsetD, THEN CollectD]

text{*Spy never sees another agent's private key! (unless it's bad at start)*}
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


subsection{*Authenticity properties obtained from NS2*}

text{*It is impossible to re-use a nonce in both NS1 and NS2 provided the
     nonce is secret.  (Honest users generate fresh nonces.)*}
lemma no_nonce_NS1_NS2:
 "Nprg
  \<in> Always {s. Crypt (pubK C) {|NA', Nonce NA|} \<in> parts (spies s) -->
                Crypt (pubK B) {|Nonce NA, Agent A|} \<in> parts (spies s) -->
                Nonce NA \<in> analz (spies s)}"
apply ns_induct
apply (blast intro: analz_insertI)+
done

text{*Adding it to the claset slows down proofs...*}
lemmas no_nonce_NS1_NS2_reachable =
       no_nonce_NS1_NS2 [THEN Always_Collect_reachableD, rule_format]


text{*Unicity for NS1: nonce NA identifies agents A and B*}
lemma unique_NA_lemma:
     "Nprg
  \<in> Always {s. Nonce NA \<notin> analz (spies s) -->
                Crypt(pubK B) {|Nonce NA, Agent A|} \<in> parts(spies s) -->
                Crypt(pubK B') {|Nonce NA, Agent A'|} \<in> parts(spies s) -->
                A=A' & B=B'}"
apply ns_induct
apply auto
txt{*Fake, NS1 are non-trivial*}
done

text{*Unicity for NS1: nonce NA identifies agents A and B*}
lemma unique_NA:
     "[| Crypt(pubK B)  {|Nonce NA, Agent A|} \<in> parts(spies s);
         Crypt(pubK B') {|Nonce NA, Agent A'|} \<in> parts(spies s);
         Nonce NA \<notin> analz (spies s);
         s \<in> reachable Nprg |]
      ==> A=A' & B=B'"
by (blast dest: unique_NA_lemma [THEN Always_Collect_reachableD])


text{*Secrecy: Spy does not see the nonce sent in msg NS1 if A and B are secure*}
lemma Spy_not_see_NA:
     "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Says A B (Crypt(pubK B) {|Nonce NA, Agent A|}) \<in> set s
                  --> Nonce NA \<notin> analz (spies s)}"
apply ns_induct
txt{*NS3*}
prefer 4 apply (blast intro: no_nonce_NS1_NS2_reachable)
txt{*NS2*}
prefer 3 apply (blast dest: unique_NA)
txt{*NS1*}
prefer 2 apply blast
txt{*Fake*}
apply spy_analz
done


text{*Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.*}
lemma A_trusts_NS2:
 "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Says A B (Crypt(pubK B) {|Nonce NA, Agent A|}) \<in> set s &
                  Crypt(pubK A) {|Nonce NA, Nonce NB|} \<in> parts (knows Spy s)
         --> Says B A (Crypt(pubK A) {|Nonce NA, Nonce NB|}) \<in> set s}"
  (*insert an invariant for use in some of the subgoals*)
apply (insert Spy_not_see_NA [of A B NA], simp, ns_induct)
apply (auto dest: unique_NA)
done


text{*If the encrypted message appears then it originated with Alice in NS1*}
lemma B_trusts_NS1:
     "Nprg \<in> Always
              {s. Nonce NA \<notin> analz (spies s) -->
                  Crypt (pubK B) {|Nonce NA, Agent A|} \<in> parts (spies s)
         --> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) \<in> set s}"
apply ns_induct
apply blast
done


subsection{*Authenticity properties obtained from NS2*}

text{*Unicity for NS2: nonce NB identifies nonce NA and agent A.
   Proof closely follows that of @{text unique_NA}.*}
lemma unique_NB_lemma:
 "Nprg
  \<in> Always {s. Nonce NB \<notin> analz (spies s)  -->
                Crypt (pubK A) {|Nonce NA, Nonce NB|} \<in> parts (spies s) -->
                Crypt(pubK A'){|Nonce NA', Nonce NB|} \<in> parts(spies s) -->
                A=A' & NA=NA'}"
apply ns_induct
apply auto
txt{*Fake, NS2 are non-trivial*}
done

lemma unique_NB:
     "[| Crypt(pubK A) {|Nonce NA, Nonce NB|} \<in> parts(spies s);
         Crypt(pubK A'){|Nonce NA', Nonce NB|} \<in> parts(spies s);
         Nonce NB \<notin> analz (spies s);
         s \<in> reachable Nprg |]
      ==> A=A' & NA=NA'"
apply (blast dest: unique_NB_lemma [THEN Always_Collect_reachableD])
done


text{*NB remains secret PROVIDED Alice never responds with round 3*}
lemma Spy_not_see_NB:
     "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) \<in> set s &
                  (ALL C. Says A C (Crypt (pubK C) (Nonce NB)) \<notin> set s)
                  --> Nonce NB \<notin> analz (spies s)}"
apply ns_induct
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt{*NS3: because NB determines A*}
prefer 4 apply (blast dest: unique_NB)
txt{*NS2: by freshness and unicity of NB*}
prefer 3 apply (blast intro: no_nonce_NS1_NS2_reachable)
txt{*NS1: by freshness*}
prefer 2 apply blast
txt{*Fake*}
apply spy_analz
done



text{*Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3--to somebody....*}
lemma B_trusts_NS3:
     "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Crypt (pubK B) (Nonce NB) \<in> parts (spies s) &
                  Says B A  (Crypt (pubK A) {|Nonce NA, Nonce NB|}) \<in> set s
                  --> (\<exists>C. Says A C (Crypt (pubK C) (Nonce NB)) \<in> set s)}"
  (*insert an invariant for use in some of the subgoals*)
apply (insert Spy_not_see_NB [of A B NA NB], simp, ns_induct)
apply (simp_all (no_asm_simp) add: ex_disj_distrib)
apply auto
txt{*NS3: because NB determines A. This use of @{text unique_NB} is robust.*}
apply (blast intro: unique_NB [THEN conjunct1])
done


text{*Can we strengthen the secrecy theorem?  NO*}
lemma "[| A \<notin> bad;  B \<notin> bad |]
  ==> Nprg \<in> Always
              {s. Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) \<in> set s
                  --> Nonce NB \<notin> analz (spies s)}"
apply ns_induct
apply auto
txt{*Fake*}
apply spy_analz
txt{*NS2: by freshness and unicity of NB*}
 apply (blast intro: no_nonce_NS1_NS2_reachable)
txt{*NS3: unicity of NB identifies A and NA, but not B*}
apply (frule_tac A'=A in Says_imp_spies [THEN parts.Inj, THEN unique_NB])
apply (erule Says_imp_spies [THEN parts.Inj], auto)
apply (rename_tac s B' C)
txt{*This is the attack!
@{subgoals[display,indent=0,margin=65]}
*}
oops


(*
THIS IS THE ATTACK!
[| A \<notin> bad; B \<notin> bad |]
==> Nprg
   \<in> Always
       {s. Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) \<in> set s -->
           Nonce NB \<notin> analz (knows Spy s)}
 1. !!s B' C.
       [| A \<notin> bad; B \<notin> bad; s \<in> reachable Nprg
          Says A C (Crypt (pubK C) {|Nonce NA, Agent A|}) \<in> set s;
          Says B' A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) \<in> set s;
          C \<in> bad; Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) \<in> set s;
          Nonce NB \<notin> analz (knows Spy s) |]
       ==> False
*)

end
