(*  Title:      HOL/Auth/Recur
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "recur" for the Recursive Authentication protocol.
*)

theory Recur = Shared:

(*End marker for message bundles*)
syntax        END :: "msg"
translations "END" == "Number 0"

(*Two session keys are distributed to each agent except for the initiator,
        who receives one.
  Perhaps the two session keys could be bundled into a single message.
*)
consts     respond :: "event list => (msg*msg*key)set"
inductive "respond evs" (*Server's response to the nested message*)
  intros
   One:  "Key KAB \<notin> used evs
          ==> (Hash[Key(shrK A)] {|Agent A, Agent B, Nonce NA, END|},
               {|Crypt (shrK A) {|Key KAB, Agent B, Nonce NA|}, END|},
               KAB)   \<in> respond evs"

    (*The most recent session key is passed up to the caller*)
   Cons: "[| (PA, RA, KAB) \<in> respond evs;
             Key KBC \<notin> used evs;  Key KBC \<notin> parts {RA};
             PA = Hash[Key(shrK A)] {|Agent A, Agent B, Nonce NA, P|} |]
          ==> (Hash[Key(shrK B)] {|Agent B, Agent C, Nonce NB, PA|},
               {|Crypt (shrK B) {|Key KBC, Agent C, Nonce NB|},
                 Crypt (shrK B) {|Key KAB, Agent A, Nonce NB|},
                 RA|},
               KBC)
              \<in> respond evs"


(*Induction over "respond" can be difficult due to the complexity of the
  subgoals.  Set "responses" captures the general form of certificates.
*)
consts     responses :: "event list => msg set"
inductive "responses evs"
  intros
    (*Server terminates lists*)
   Nil:  "END \<in> responses evs"

   Cons: "[| RA \<in> responses evs;  Key KAB \<notin> used evs |]
          ==> {|Crypt (shrK B) {|Key KAB, Agent A, Nonce NB|},
                RA|}  \<in> responses evs"


consts     recur   :: "event list set"
inductive "recur"
  intros
         (*Initial trace is empty*)
   Nil:  "[] \<in> recur"

         (*The spy MAY say anything he CAN say.  Common to
           all similar protocols.*)
   Fake: "[| evsf \<in> recur;  X \<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \<in> recur"

         (*Alice initiates a protocol run.
           END is a placeholder to terminate the nesting.*)
   RA1:  "[| evs1: recur;  Nonce NA \<notin> used evs1 |]
          ==> Says A B (Hash[Key(shrK A)] {|Agent A, Agent B, Nonce NA, END|})
              # evs1 \<in> recur"

         (*Bob's response to Alice's message.  C might be the Server.
           We omit PA = {|XA, Agent A, Agent B, Nonce NA, P|} because
           it complicates proofs, so B may respond to any message at all!*)
   RA2:  "[| evs2: recur;  Nonce NB \<notin> used evs2;
             Says A' B PA \<in> set evs2 |]
          ==> Says B C (Hash[Key(shrK B)] {|Agent B, Agent C, Nonce NB, PA|})
              # evs2 \<in> recur"

         (*The Server receives Bob's message and prepares a response.*)
   RA3:  "[| evs3: recur;  Says B' Server PB \<in> set evs3;
             (PB,RB,K) \<in> respond evs3 |]
          ==> Says Server B RB # evs3 \<in> recur"

         (*Bob receives the returned message and compares the Nonces with
           those in the message he previously sent the Server.*)
   RA4:  "[| evs4: recur;
             Says B  C {|XH, Agent B, Agent C, Nonce NB,
                         XA, Agent A, Agent B, Nonce NA, P|} \<in> set evs4;
             Says C' B {|Crypt (shrK B) {|Key KBC, Agent C, Nonce NB|},
                         Crypt (shrK B) {|Key KAB, Agent A, Nonce NB|},
                         RA|} \<in> set evs4 |]
          ==> Says B A RA # evs4 \<in> recur"

   (*No "oops" message can easily be expressed.  Each session key is
     associated--in two separate messages--with two nonces.  This is
     one try, but it isn't that useful.  Re domino attack, note that
     Recur.ML proves that each session key is secure provided the two
     peers are, even if there are compromised agents elsewhere in
     the chain.  Oops cases proved using parts_cut, Key_in_keysFor_parts,
     etc.

   Oops:  "[| evso: recur;  Says Server B RB \<in> set evso;
	      RB \<in> responses evs';  Key K \<in> parts {RB} |]
           ==> Notes Spy {|Key K, RB|} # evso \<in> recur"
  *)


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]


(** Possibility properties: traces that reach the end
        ONE theorem would be more elegant and faster!
        By induction on a list of agents (no repetitions)
**)


(*Simplest case: Alice goes directly to the server*)
lemma "\<exists>K NA. \<exists>evs \<in> recur.
   Says Server A {|Crypt (shrK A) {|Key K, Agent Server, Nonce NA|},
                   END|}  \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] recur.Nil [THEN recur.RA1, 
                               THEN recur.RA3 [OF _ _ respond.One]])
apply possibility
done


(*Case two: Alice, Bob and the server*)
lemma "\<exists>K. \<exists>NA. \<exists>evs \<in> recur.
        Says B A {|Crypt (shrK A) {|Key K, Agent B, Nonce NA|},
                   END|}  \<in> set evs"
apply (cut_tac Nonce_supply2 Key_supply2)
apply clarify
apply (intro exI bexI)
apply (rule_tac [2] 
          recur.Nil [THEN recur.RA1, 
                     THEN recur.RA2,
                     THEN recur.RA3 [OF _ _ respond.One [THEN respond.Cons]],
                     THEN recur.RA4])
apply (tactic "basic_possibility_tac")
apply (tactic
      "DEPTH_SOLVE (eresolve_tac [asm_rl, less_not_refl2, less_not_refl3] 1)")
done

(*Case three: Alice, Bob, Charlie and the server
  Rather slow (16 seconds) to run every time...
lemma "\<exists>K. \<exists>NA. \<exists>evs \<in> recur.
        Says B A {|Crypt (shrK A) {|Key K, Agent B, Nonce NA|},
                   END|}  \<in> set evs"
apply (tactic "cut_facts_tac [Nonce_supply3, Key_supply3] 1")
apply clarify
apply (intro exI bexI)
apply (rule_tac [2] 
          recur.Nil [THEN recur.RA1, 
                     THEN recur.RA2, THEN recur.RA2,
                     THEN recur.RA3 
                          [OF _ _ respond.One 
                                  [THEN respond.Cons, THEN respond.Cons]],
                     THEN recur.RA4, THEN recur.RA4])
apply (tactic "basic_possibility_tac")
apply (tactic
      "DEPTH_SOLVE (swap_res_tac [refl, conjI, disjCI] 1 ORELSE \
\                   eresolve_tac [asm_rl, less_not_refl2, less_not_refl3] 1)")
done
*)

(**** Inductive proofs about recur ****)

lemma respond_imp_not_used: "(PA,RB,KAB) \<in> respond evs ==> Key KAB \<notin> used evs"
by (erule respond.induct, simp_all)

lemma Key_in_parts_respond [rule_format]:
   "[| Key K \<in> parts {RB};  (PB,RB,K') \<in> respond evs |] ==> Key K \<notin> used evs"
apply (erule rev_mp, erule respond.induct)
apply (auto dest: Key_not_used respond_imp_not_used)
done

(*Simple inductive reasoning about responses*)
lemma respond_imp_responses:
     "(PA,RB,KAB) \<in> respond evs ==> RB \<in> responses evs"
apply (erule respond.induct)
apply (blast intro!: respond_imp_not_used responses.intros)+
done


(** For reasoning about the encrypted portion of messages **)

lemmas RA2_analz_spies = Says_imp_spies [THEN analz.Inj]

lemma RA4_analz_spies:
     "Says C' B {|Crypt K X, X', RA|} \<in> set evs ==> RA \<in> analz (spies evs)"
by blast


(*RA2_analz... and RA4_analz... let us treat those cases using the same
  argument as for the Fake case.  This is possible for most, but not all,
  proofs: Fake does not invent new nonces (as in RA2), and of course Fake
  messages originate from the Spy. *)

lemmas RA2_parts_spies =  RA2_analz_spies [THEN analz_into_parts]
lemmas RA4_parts_spies =  RA4_analz_spies [THEN analz_into_parts]


(** Theorems of the form X \<notin> parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(** Spy never sees another agent's shared key! (unless it's bad at start) **)

lemma Spy_see_shrK [simp]:
     "evs \<in> recur ==> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule recur.induct)
apply auto
(*RA3.  It's ugly to call auto twice, but it seems necessary.*)
apply (auto dest: Key_in_parts_respond simp add: parts_insert_spies)
done

lemma Spy_analz_shrK [simp]:
     "evs \<in> recur ==> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[|Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> recur|] ==> A \<in> bad"
by (blast dest: Spy_see_shrK)


(*** Proofs involving analz ***)

(** Session keys are not used to encrypt other session keys **)

(*Version for "responses" relation.  Handles case RA3 in the theorem below.
  Note that it holds for *any* set H (not just "spies evs")
  satisfying the inductive hypothesis.*)
lemma resp_analz_image_freshK_lemma:
     "[| RB \<in> responses evs;
         \<forall>K KK. KK \<subseteq> - (range shrK) -->
                   (Key K \<in> analz (Key`KK Un H)) =
                   (K \<in> KK | Key K \<in> analz H) |]
     ==> \<forall>K KK. KK \<subseteq> - (range shrK) -->
                   (Key K \<in> analz (insert RB (Key`KK Un H))) =
                   (K \<in> KK | Key K \<in> analz (insert RB H))"
by (erule responses.induct,
    simp_all del: image_insert
	     add: analz_image_freshK_simps)


(*Version for the protocol.  Proof is almost trivial, thanks to the lemma.*)
lemma raw_analz_image_freshK:
 "evs \<in> recur ==>
   \<forall>K KK. KK \<subseteq> - (range shrK) -->
          (Key K \<in> analz (Key`KK Un (spies evs))) =
          (K \<in> KK | Key K \<in> analz (spies evs))"
apply (erule recur.induct)
apply (drule_tac [4] RA2_analz_spies,
       drule_tac [5] respond_imp_responses,
       drule_tac [6] RA4_analz_spies)
apply analz_freshK
apply spy_analz
(*RA3*)
apply (simp_all add: resp_analz_image_freshK_lemma)
done


(*Instance of the lemma with H replaced by (spies evs):
   [| RB \<in> responses evs;  evs \<in> recur; |]
   ==> KK \<subseteq> - (range shrK) -->
       Key K \<in> analz (insert RB (Key`KK Un spies evs)) =
       (K \<in> KK | Key K \<in> analz (insert RB (spies evs)))
*)
lemmas resp_analz_image_freshK =  
       resp_analz_image_freshK_lemma [OF _ raw_analz_image_freshK]

lemma analz_insert_freshK:
     "[| evs \<in> recur;  KAB \<notin> range shrK |]
      ==> Key K \<in> analz (insert (Key KAB) (spies evs)) =
          (K = KAB | Key K \<in> analz (spies evs))"
by (simp del: image_insert
         add: analz_image_freshK_simps raw_analz_image_freshK)


(*Everything that's hashed is already in past traffic. *)
lemma Hash_imp_body:
     "[| Hash {|Key(shrK A), X|} \<in> parts (spies evs);
         evs \<in> recur;  A \<notin> bad |] ==> X \<in> parts (spies evs)"
apply (erule rev_mp)
apply (erule recur.induct,
       drule_tac [6] RA4_parts_spies,
       drule_tac [5] respond_imp_responses,
       drule_tac [4] RA2_parts_spies)
(*RA3 requires a further induction*)
apply (erule_tac [5] responses.induct)
apply simp_all
(*Nil*)
apply force
(*Fake*)
apply (blast intro: parts_insertI)
done


(** The Nonce NA uniquely identifies A's message.
    This theorem applies to steps RA1 and RA2!

  Unicity is not used in other proofs but is desirable in its own right.
**)

lemma unique_NA:
  "[| Hash {|Key(shrK A), Agent A, B, NA, P|} \<in> parts (spies evs);
      Hash {|Key(shrK A), Agent A, B',NA, P'|} \<in> parts (spies evs);
      evs \<in> recur;  A \<notin> bad |]
    ==> B=B' & P=P'"
apply (erule rev_mp, erule rev_mp)
apply (erule recur.induct,
       drule_tac [5] respond_imp_responses)
apply (force, simp_all)
(*Fake*)
apply blast
apply (erule_tac [3] responses.induct)
(*RA1,2: creation of new Nonce*)
apply simp_all
apply (blast dest!: Hash_imp_body)+
done


(*** Lemmas concerning the Server's response
      (relations "respond" and "responses")
***)

lemma shrK_in_analz_respond [simp]:
     "[| RB \<in> responses evs;  evs \<in> recur |]
  ==> (Key (shrK B) \<in> analz (insert RB (spies evs))) = (B:bad)"
by (erule responses.induct,
    simp_all del: image_insert
             add: analz_image_freshK_simps resp_analz_image_freshK)


lemma resp_analz_insert_lemma:
     "[| Key K \<in> analz (insert RB H);
         \<forall>K KK. KK \<subseteq> - (range shrK) -->
                   (Key K \<in> analz (Key`KK Un H)) =
                   (K \<in> KK | Key K \<in> analz H);
         RB \<in> responses evs |]
     ==> (Key K \<in> parts{RB} | Key K \<in> analz H)"
apply (erule rev_mp, erule responses.induct)
apply (simp_all del: image_insert
             add: analz_image_freshK_simps resp_analz_image_freshK_lemma)
(*Simplification using two distinct treatments of "image"*)
apply (simp add: parts_insert2)
apply blast
done

lemmas resp_analz_insert =
       resp_analz_insert_lemma [OF _ raw_analz_image_freshK]

(*The last key returned by respond indeed appears in a certificate*)
lemma respond_certificate:
     "(Hash[Key(shrK A)] {|Agent A, B, NA, P|}, RA, K) \<in> respond evs
      ==> Crypt (shrK A) {|Key K, B, NA|} \<in> parts {RA}"
apply (ind_cases "(X, RA, K) \<in> respond evs")
apply simp_all
done

(*This unicity proof differs from all the others in the HOL/Auth directory.
  The conclusion isn't quite unicity but duplicity, in that there are two
  possibilities.  Also, the presence of two different matching messages in
  the inductive step complicates the case analysis.  Unusually for such proofs,
  the quantifiers appear to be necessary.*)
lemma unique_lemma [rule_format]:
     "(PB,RB,KXY) \<in> respond evs ==>
      \<forall>A B N. Crypt (shrK A) {|Key K, Agent B, N|} \<in> parts {RB} -->
      (\<forall>A' B' N'. Crypt (shrK A') {|Key K, Agent B', N'|} \<in> parts {RB} -->
      (A'=A & B'=B) | (A'=B & B'=A))"
apply (erule respond.induct)
apply (simp_all add: all_conj_distrib)
apply (blast dest: respond_certificate)
done

lemma unique_session_keys:
     "[| Crypt (shrK A) {|Key K, Agent B, N|} \<in> parts {RB};
         Crypt (shrK A') {|Key K, Agent B', N'|} \<in> parts {RB};
         (PB,RB,KXY) \<in> respond evs |]
      ==> (A'=A & B'=B) | (A'=B & B'=A)"
by (rule unique_lemma, auto)


(** Crucial secrecy property: Spy does not see the keys sent in msg RA3
    Does not in itself guarantee security: an attack could violate
    the premises, e.g. by having A=Spy **)

lemma respond_Spy_not_see_session_key [rule_format]:
     "[| (PB,RB,KAB) \<in> respond evs;  evs \<in> recur |]
      ==> \<forall>A A' N. A \<notin> bad & A' \<notin> bad -->
          Crypt (shrK A) {|Key K, Agent A', N|} \<in> parts{RB} -->
          Key K \<notin> analz (insert RB (spies evs))"
apply (erule respond.induct)
apply (frule_tac [2] respond_imp_responses)
apply (frule_tac [2] respond_imp_not_used)
apply (simp_all del: image_insert
                add: analz_image_freshK_simps split_ifs shrK_in_analz_respond
                     resp_analz_image_freshK parts_insert2)
apply (simp_all add: ex_disj_distrib)
(** LEVEL 5 **)
(*Base case of respond*)
apply blast
(*Inductive step of respond*)
apply (intro allI conjI impI)
apply simp_all
(*by unicity, either B=Aa or B=A', a contradiction if B \<in> bad*)
apply (blast dest: unique_session_keys [OF _ respond_certificate])
apply (blast dest!: respond_certificate)
apply (blast dest!: resp_analz_insert)
done


lemma Spy_not_see_session_key:
     "[| Crypt (shrK A) {|Key K, Agent A', N|} \<in> parts (spies evs);
         A \<notin> bad;  A' \<notin> bad;  evs \<in> recur |]
      ==> Key K \<notin> analz (spies evs)"
apply (erule rev_mp)
apply (erule recur.induct)
apply (drule_tac [4] RA2_analz_spies,
       frule_tac [5] respond_imp_responses,
       drule_tac [6] RA4_analz_spies,
       simp_all add: split_ifs analz_insert_eq analz_insert_freshK)
(*Base*)
apply force
(*Fake*)
apply spy_analz
(*RA2*)
apply blast 
(*RA3 remains*)
apply (simp add: parts_insert_spies)
(*Now we split into two cases.  A single blast could do it, but it would take
  a CPU minute.*)
apply (safe del: impCE)
(*RA3, case 1: use lemma previously proved by induction*)
apply (blast elim: rev_notE [OF _ respond_Spy_not_see_session_key])
(*RA3, case 2: K is an old key*)
apply (blast dest: resp_analz_insert dest: Key_in_parts_respond)
(*RA4*)
apply blast 
done

(**** Authenticity properties for Agents ****)

(*The response never contains Hashes*)
lemma Hash_in_parts_respond:
     "[| Hash {|Key (shrK B), M|} \<in> parts (insert RB H);
         (PB,RB,K) \<in> respond evs |]
      ==> Hash {|Key (shrK B), M|} \<in> parts H"
apply (erule rev_mp)
apply (erule respond_imp_responses [THEN responses.induct])
apply auto
done

(*Only RA1 or RA2 can have caused such a part of a message to appear.
  This result is of no use to B, who cannot verify the Hash.  Moreover,
  it can say nothing about how recent A's message is.  It might later be
  used to prove B's presence to A at the run's conclusion.*)
lemma Hash_auth_sender [rule_format]:
     "[| Hash {|Key(shrK A), Agent A, Agent B, NA, P|} \<in> parts(spies evs);
         A \<notin> bad;  evs \<in> recur |]
      ==> Says A B (Hash[Key(shrK A)] {|Agent A, Agent B, NA, P|}) \<in> set evs"
apply (unfold HPair_def)
apply (erule rev_mp)
apply (erule recur.induct,
       drule_tac [6] RA4_parts_spies,
       drule_tac [4] RA2_parts_spies,
       simp_all)
(*Nil*)
apply force
(*Fake, RA3*)
apply (blast dest: Hash_in_parts_respond)+
done

(** These two results subsume (for all agents) the guarantees proved
    separately for A and B in the Otway-Rees protocol.
**)


(*Certificates can only originate with the Server.*)
lemma Cert_imp_Server_msg:
     "[| Crypt (shrK A) Y \<in> parts (spies evs);
         A \<notin> bad;  evs \<in> recur |]
      ==> \<exists>C RC. Says Server C RC \<in> set evs  &
                   Crypt (shrK A) Y \<in> parts {RC}"
apply (erule rev_mp, erule recur.induct, simp_all)
(*Nil*)
apply force
(*Fake*)
apply blast
(*RA1*)
apply blast
(*RA2: it cannot be a new Nonce, contradiction.*)
apply blast
(*RA3*) (*Pity that the proof is so brittle: this step requires the rewriting,
          which however would break all other steps.*)
apply (simp add: parts_insert_spies, blast)
(*RA4*)
apply blast
done

end
