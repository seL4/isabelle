(*  Title:      HOL/Auth/NS_Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_shared" for Needham-Schroeder Shared-Key protocol.

From page 247 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

theory NS_Shared = Shared:

consts  ns_shared   :: "event list set"
inductive "ns_shared"
 intros
	(*Initial trace is empty*)
  Nil:  "[] \\<in> ns_shared"
	(*The spy MAY say anything he CAN say.  We do not expect him to
	  invent new nonces here, but he can also use NS1.  Common to
	  all similar protocols.*)
  Fake: "\\<lbrakk>evsf \\<in> ns_shared;  X \\<in> synth (analz (spies evsf))\\<rbrakk>
	 \\<Longrightarrow> Says Spy B X # evsf \\<in> ns_shared"

	(*Alice initiates a protocol run, requesting to talk to any B*)
  NS1:  "\\<lbrakk>evs1 \\<in> ns_shared;  Nonce NA \\<notin> used evs1\\<rbrakk>
	 \\<Longrightarrow> Says A Server \\<lbrace>Agent A, Agent B, Nonce NA\\<rbrace> # evs1  \\<in>  ns_shared"

	(*Server's response to Alice's message.
	  !! It may respond more than once to A's request !!
	  Server doesn't know who the true sender is, hence the A' in
	      the sender field.*)
  NS2:  "\\<lbrakk>evs2 \\<in> ns_shared;  Key KAB \\<notin> used evs2;
	  Says A' Server \\<lbrace>Agent A, Agent B, Nonce NA\\<rbrace> \\<in> set evs2\\<rbrakk>
	 \\<Longrightarrow> Says Server A
	       (Crypt (shrK A)
		  \\<lbrace>Nonce NA, Agent B, Key KAB,
		    (Crypt (shrK B) \\<lbrace>Key KAB, Agent A\\<rbrace>)\\<rbrace>)
	       # evs2 \\<in> ns_shared"

	 (*We can't assume S=Server.  Agent A "remembers" her nonce.
	   Need A \\<noteq> Server because we allow messages to self.*)
  NS3:  "\\<lbrakk>evs3 \\<in> ns_shared;  A \\<noteq> Server;
	  Says S A (Crypt (shrK A) \\<lbrace>Nonce NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs3;
	  Says A Server \\<lbrace>Agent A, Agent B, Nonce NA\\<rbrace> \\<in> set evs3\\<rbrakk>
	 \\<Longrightarrow> Says A B X # evs3 \\<in> ns_shared"

	(*Bob's nonce exchange.  He does not know who the message came
	  from, but responds to A because she is mentioned inside.*)
  NS4:  "\\<lbrakk>evs4 \\<in> ns_shared;  Nonce NB \\<notin> used evs4;
	  Says A' B (Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace>) \\<in> set evs4\\<rbrakk>
	 \\<Longrightarrow> Says B A (Crypt K (Nonce NB)) # evs4 \\<in> ns_shared"

	(*Alice responds with Nonce NB if she has seen the key before.
	  Maybe should somehow check Nonce NA again.
	  We do NOT send NB-1 or similar as the Spy cannot spoof such things.
	  Letting the Spy add or subtract 1 lets him send all nonces.
	  Instead we distinguish the messages by sending the nonce twice.*)
  NS5:  "\\<lbrakk>evs5 \\<in> ns_shared;
	  Says B' A (Crypt K (Nonce NB)) \\<in> set evs5;
	  Says S  A (Crypt (shrK A) \\<lbrace>Nonce NA, Agent B, Key K, X\\<rbrace>)
	    \\<in> set evs5\\<rbrakk>
	 \\<Longrightarrow> Says A B (Crypt K \\<lbrace>Nonce NB, Nonce NB\\<rbrace>) # evs5 \\<in> ns_shared"

	(*This message models possible leaks of session keys.
	  The two Nonces identify the protocol run: the rule insists upon
	  the true senders in order to make them accurate.*)
  Oops: "\\<lbrakk>evso \\<in> ns_shared;  Says B A (Crypt K (Nonce NB)) \\<in> set evso;
	  Says Server A (Crypt (shrK A) \\<lbrace>Nonce NA, Agent B, Key K, X\\<rbrace>)
	      \\<in> set evso\\<rbrakk>
	 \\<Longrightarrow> Notes Spy \\<lbrace>Nonce NA, Nonce NB, Key K\\<rbrace> # evso \\<in> ns_shared"


declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body  [dest]
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]
declare image_eq_UN [simp]  (*accelerates proofs involving nested images*)


(*A "possibility property": there are traces that reach the end*)
lemma "A \\<noteq> Server \\<Longrightarrow> \\<exists>N K. \\<exists>evs \\<in> ns_shared.
                              Says A B (Crypt K \\<lbrace>Nonce N, Nonce N\\<rbrace>) \\<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] ns_shared.Nil
       [THEN ns_shared.NS1, THEN ns_shared.NS2, THEN ns_shared.NS3,
	THEN ns_shared.NS4, THEN ns_shared.NS5])
apply possibility
done

(*This version is similar, while instantiating ?K and ?N to epsilon-terms
lemma "A \\<noteq> Server \\<Longrightarrow> \\<exists>evs \\<in> ns_shared.
                Says A B (Crypt ?K \\<lbrace>Nonce ?N, Nonce ?N\\<rbrace>) \\<in> set evs"
*)


(**** Inductive proofs about ns_shared ****)

(** Forwarding lemmas, to aid simplification **)

(*For reasoning about the encrypted portion of message NS3*)
lemma NS3_msg_in_parts_spies:
     "Says S A (Crypt KA \\<lbrace>N, B, K, X\\<rbrace>) \\<in> set evs \\<Longrightarrow> X \\<in> parts (spies evs)"
by blast

(*For reasoning about the Oops message*)
lemma Oops_parts_spies:
     "Says Server A (Crypt (shrK A) \\<lbrace>NA, B, K, X\\<rbrace>) \\<in> set evs
            \\<Longrightarrow> K \\<in> parts (spies evs)"
by blast

(** Theorems of the form X \\<notin> parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's bad at start)*)
lemma Spy_see_shrK [simp]:
     "evs \\<in> ns_shared \\<Longrightarrow> (Key (shrK A) \\<in> parts (spies evs)) = (A \\<in> bad)"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply simp_all
apply blast+;
done

lemma Spy_analz_shrK [simp]:
     "evs \\<in> ns_shared \\<Longrightarrow> (Key (shrK A) \\<in> analz (spies evs)) = (A \\<in> bad)"
by auto


(*Nobody can have used non-existent keys!*)
lemma new_keys_not_used [rule_format, simp]:
    "evs \\<in> ns_shared \\<Longrightarrow> Key K \\<notin> used evs \\<longrightarrow> K \\<notin> keysFor (parts (spies evs))"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply simp_all
(*Fake, NS2, NS4, NS5*)
apply (blast dest!: keysFor_parts_insert)+
done


(** Lemmas concerning the form of items passed in messages **)

(*Describes the form of K, X and K' when the Server sends this message.*)
lemma Says_Server_message_form:
     "\\<lbrakk>Says Server A (Crypt K' \\<lbrace>N, Agent B, Key K, X\\<rbrace>) \\<in> set evs;
       evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> K \\<notin> range shrK \\<and>
          X = (Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace>) \\<and>
          K' = shrK A"
by (erule rev_mp, erule ns_shared.induct, auto)


(*If the encrypted message appears then it originated with the Server*)
lemma A_trusts_NS2:
     "\\<lbrakk>Crypt (shrK A) \\<lbrace>NA, Agent B, Key K, X\\<rbrace> \\<in> parts (spies evs);
       A \\<notin> bad;  evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> Says Server A (Crypt (shrK A) \\<lbrace>NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs"
apply (erule rev_mp)
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply auto
done

lemma cert_A_form:
     "\\<lbrakk>Crypt (shrK A) \\<lbrace>NA, Agent B, Key K, X\\<rbrace> \\<in> parts (spies evs);
       A \\<notin> bad;  evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> K \\<notin> range shrK \\<and>  X = (Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace>)"
by (blast dest!: A_trusts_NS2 Says_Server_message_form)

(*EITHER describes the form of X when the following message is sent,
  OR     reduces it to the Fake case.
  Use Says_Server_message_form if applicable.*)
lemma Says_S_message_form:
     "\\<lbrakk>Says S A (Crypt (shrK A) \\<lbrace>Nonce NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs;
       evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> (K \\<notin> range shrK \\<and> X = (Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace>))
          \\<or> X \\<in> analz (spies evs)"
by (blast dest: Says_imp_knows_Spy cert_A_form analz.Inj)


(*Alternative version also provable
lemma Says_S_message_form2:
  "\\<lbrakk>Says S A (Crypt (shrK A) \\<lbrace>Nonce NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs;
    evs \\<in> ns_shared\\<rbrakk>
   \\<Longrightarrow> Says Server A (Crypt (shrK A) \\<lbrace>Nonce NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs
       \\<or> X \\<in> analz (spies evs)"
apply (case_tac "A \\<in> bad")
apply (force dest!: Says_imp_knows_Spy [THEN analz.Inj]);
by (blast dest!: A_trusts_NS2 Says_Server_message_form)
*)


(****
 SESSION KEY COMPROMISE THEOREM.  To prove theorems of the form

  Key K \\<in> analz (insert (Key KAB) (spies evs)) \\<Longrightarrow>
  Key K \\<in> analz (spies evs)

 A more general formula must be proved inductively.
****)

(*NOT useful in this form, but it says that session keys are not used
  to encrypt messages containing other keys, in the actual protocol.
  We require that agents should behave like this subsequently also.*)
lemma  "\\<lbrakk>evs \\<in> ns_shared;  Kab \\<notin> range shrK\\<rbrakk> \\<Longrightarrow>
         (Crypt KAB X) \\<in> parts (spies evs) \\<and>
         Key K \\<in> parts {X} \\<longrightarrow> Key K \\<in> parts (spies evs)"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply simp_all
(*Fake*)
apply (blast dest: parts_insert_subset_Un)
(*Base, NS4 and NS5*)
apply auto
done


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)

lemma analz_image_freshK [rule_format]:
 "evs \\<in> ns_shared \\<Longrightarrow>
   \\<forall>K KK. KK \\<subseteq> - (range shrK) \\<longrightarrow>
             (Key K \\<in> analz (Key`KK \\<union> (spies evs))) =
             (K \\<in> KK \\<or> Key K \\<in> analz (spies evs))"
apply (erule ns_shared.induct, force)
apply (drule_tac [7] Says_Server_message_form)
apply (erule_tac [4] Says_S_message_form [THEN disjE])
apply analz_freshK
apply spy_analz
done


lemma analz_insert_freshK:
     "\\<lbrakk>evs \\<in> ns_shared;  KAB \\<notin> range shrK\\<rbrakk> \\<Longrightarrow>
       (Key K \\<in> analz (insert (Key KAB) (spies evs))) =
       (K = KAB \\<or> Key K \\<in> analz (spies evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


(** The session key K uniquely identifies the message **)

(*In messages of this form, the session key uniquely identifies the rest*)
lemma unique_session_keys:
     "\\<lbrakk>Says Server A (Crypt (shrK A) \\<lbrace>NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs;
       Says Server A' (Crypt (shrK A') \\<lbrace>NA', Agent B', Key K, X'\\<rbrace>) \\<in> set evs;
       evs \\<in> ns_shared\\<rbrakk> \\<Longrightarrow> A=A' \\<and> NA=NA' \\<and> B=B' \\<and> X = X'"
apply (erule rev_mp, erule rev_mp, erule ns_shared.induct)
apply simp_all
apply blast+
done


(** Crucial secrecy property: Spy does not see the keys sent in msg NS2 **)

(*Beware of [rule_format] and the universal quantifier!*)
lemma secrecy_lemma:
     "\\<lbrakk>Says Server A (Crypt (shrK A) \\<lbrace>NA, Agent B, Key K,
                                      Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace>\\<rbrace>)
              \\<in> set evs;
         A \\<notin> bad;  B \\<notin> bad;  evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> (\\<forall>NB. Notes Spy \\<lbrace>NA, NB, Key K\\<rbrace> \\<notin> set evs) \\<longrightarrow>
         Key K \\<notin> analz (spies evs)"
apply (erule rev_mp)
apply (erule ns_shared.induct, force)
apply (frule_tac [7] Says_Server_message_form)
apply (frule_tac [4] Says_S_message_form)
apply (erule_tac [5] disjE)
apply (simp_all add: analz_insert_eq analz_insert_freshK pushes split_ifs)
apply spy_analz  (*Fake*)
apply blast      (*NS2*)
(*NS3, Server sub-case*) (**LEVEL 8 **)
apply (blast dest!: Crypt_Spy_analz_bad A_trusts_NS2
	     dest:  Says_imp_knows_Spy analz.Inj unique_session_keys)
(*NS3, Spy sub-case; also Oops*)
apply (blast dest: unique_session_keys)+
done



(*Final version: Server's message in the most abstract form*)
lemma Spy_not_see_encrypted_key:
     "\\<lbrakk>Says Server A (Crypt K' \\<lbrace>NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs;
       \\<forall>NB. Notes Spy \\<lbrace>NA, NB, Key K\\<rbrace> \\<notin> set evs;
       A \\<notin> bad;  B \\<notin> bad;  evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> Key K \\<notin> analz (spies evs)"
by (blast dest: Says_Server_message_form secrecy_lemma)


(**** Guarantees available at various stages of protocol ***)

(*If the encrypted message appears then it originated with the Server*)
lemma B_trusts_NS3:
     "\\<lbrakk>Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace> \\<in> parts (spies evs);
       B \\<notin> bad;  evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> \\<exists>NA. Says Server A
               (Crypt (shrK A) \\<lbrace>NA, Agent B, Key K,
                                 Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace>\\<rbrace>)
              \\<in> set evs"
apply (erule rev_mp)
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply auto
done


lemma A_trusts_NS4_lemma [rule_format]:
   "evs \\<in> ns_shared \\<Longrightarrow>
      Key K \\<notin> analz (spies evs) \\<longrightarrow>
      Says Server A (Crypt (shrK A) \\<lbrace>NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs \\<longrightarrow>
      Crypt K (Nonce NB) \\<in> parts (spies evs) \\<longrightarrow>
      Says B A (Crypt K (Nonce NB)) \\<in> set evs"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply (analz_mono_contra, simp_all)
apply blast     (*Fake*)
(*NS2: contradiction from the assumptions
  Key K \\<notin> used evs2  and Crypt K (Nonce NB) \\<in> parts (spies evs2) *)
apply (force dest!: Crypt_imp_keysFor)
apply blast     (*NS3*)
(*NS4*)
apply (blast dest!: B_trusts_NS3
	     dest: Says_imp_knows_Spy [THEN analz.Inj]
                   Crypt_Spy_analz_bad unique_session_keys)
done

(*This version no longer assumes that K is secure*)
lemma A_trusts_NS4:
     "\\<lbrakk>Crypt K (Nonce NB) \\<in> parts (spies evs);
       Crypt (shrK A) \\<lbrace>NA, Agent B, Key K, X\\<rbrace> \\<in> parts (spies evs);
       \\<forall>NB. Notes Spy \\<lbrace>NA, NB, Key K\\<rbrace> \\<notin> set evs;
       A \\<notin> bad;  B \\<notin> bad;  evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> Says B A (Crypt K (Nonce NB)) \\<in> set evs"
by (blast intro: A_trusts_NS4_lemma
          dest: A_trusts_NS2 Spy_not_see_encrypted_key)

(*If the session key has been used in NS4 then somebody has forwarded
  component X in some instance of NS4.  Perhaps an interesting property,
  but not needed (after all) for the proofs below.*)
theorem NS4_implies_NS3 [rule_format]:
  "evs \\<in> ns_shared \\<Longrightarrow>
     Key K \\<notin> analz (spies evs) \\<longrightarrow>
     Says Server A (Crypt (shrK A) \\<lbrace>NA, Agent B, Key K, X\\<rbrace>) \\<in> set evs \\<longrightarrow>
     Crypt K (Nonce NB) \\<in> parts (spies evs) \\<longrightarrow>
     (\\<exists>A'. Says A' B X \\<in> set evs)"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply analz_mono_contra
apply (simp_all add: ex_disj_distrib)
apply blast  (*Fake*)
apply (blast dest!: new_keys_not_used Crypt_imp_keysFor)  (*NS2*)
apply blast  (*NS3*)
(*NS4*)
apply (blast dest!: B_trusts_NS3
	     dest: Says_imp_knows_Spy [THEN analz.Inj]
                   unique_session_keys Crypt_Spy_analz_bad)
done


lemma B_trusts_NS5_lemma [rule_format]:
  "\\<lbrakk>B \\<notin> bad;  evs \\<in> ns_shared\\<rbrakk> \\<Longrightarrow>
     Key K \\<notin> analz (spies evs) \\<longrightarrow>
     Says Server A
	  (Crypt (shrK A) \\<lbrace>NA, Agent B, Key K,
			    Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace>\\<rbrace>) \\<in> set evs \\<longrightarrow>
     Crypt K \\<lbrace>Nonce NB, Nonce NB\\<rbrace> \\<in> parts (spies evs) \\<longrightarrow>
     Says A B (Crypt K \\<lbrace>Nonce NB, Nonce NB\\<rbrace>) \\<in> set evs"
apply (erule ns_shared.induct, force, drule_tac [4] NS3_msg_in_parts_spies)
apply analz_mono_contra
apply simp_all
apply blast  (*Fake*)
apply (blast dest!: new_keys_not_used Crypt_imp_keysFor)  (*NS2*)
apply (blast dest!: cert_A_form) (*NS3*)
(*NS5*)
apply (blast dest!: A_trusts_NS2
	     dest: Says_imp_knows_Spy [THEN analz.Inj]
                   unique_session_keys Crypt_Spy_analz_bad)
done


(*Very strong Oops condition reveals protocol's weakness*)
lemma B_trusts_NS5:
     "\\<lbrakk>Crypt K \\<lbrace>Nonce NB, Nonce NB\\<rbrace> \\<in> parts (spies evs);
       Crypt (shrK B) \\<lbrace>Key K, Agent A\\<rbrace> \\<in> parts (spies evs);
       \\<forall>NA NB. Notes Spy \\<lbrace>NA, NB, Key K\\<rbrace> \\<notin> set evs;
       A \\<notin> bad;  B \\<notin> bad;  evs \\<in> ns_shared\\<rbrakk>
      \\<Longrightarrow> Says A B (Crypt K \\<lbrace>Nonce NB, Nonce NB\\<rbrace>) \\<in> set evs"
by (blast intro: B_trusts_NS5_lemma
          dest: B_trusts_NS3 Spy_not_see_encrypted_key)

end
