(*  Title:      HOL/Auth/Kerberos_BAN
    ID:         $Id$
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Kerberos protocol, BAN version.

From page 251 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)

  Confidentiality (secrecy) and authentication properties rely on 
  temporal checks: strong guarantees in a little abstracted - but
  very realistic - model (see .thy).

Tidied and converted to Isar by lcp.
*)

theory Kerberos_BAN = Shared:

(* Temporal modelization: session keys can be leaked 
                          ONLY when they have expired *)

syntax
    CT :: "event list=>nat"
    Expired :: "[nat, event list] => bool"
    RecentAuth :: "[nat, event list] => bool"

consts

    (*Duration of the session key*)
    SesKeyLife   :: nat

    (*Duration of the authenticator*)
    AutLife :: nat

text{*The ticket should remain fresh for two journeys on the network at least*}
specification (SesKeyLife)
  SesKeyLife_LB [iff]: "2 \<le> SesKeyLife"
    by blast

text{*The authenticator only for one journey*}
specification (AutLife)
  AutLife_LB [iff]:    "Suc 0 \<le> AutLife"
    by blast


translations
   "CT" == "length"
  
   "Expired T evs" == "SesKeyLife + T < CT evs"

   "RecentAuth T evs" == "CT evs \<le> AutLife + T"

consts  kerberos_ban   :: "event list set"
inductive "kerberos_ban"
 intros 

   Nil:  "[] \<in> kerberos_ban"

   Fake: "[| evsf \<in> kerberos_ban;  X \<in> synth (analz (spies evsf)) |]
	  ==> Says Spy B X # evsf \<in> kerberos_ban"


   Kb1:  "[| evs1 \<in> kerberos_ban |]
	  ==> Says A Server {|Agent A, Agent B|} # evs1
		\<in>  kerberos_ban"


   Kb2:  "[| evs2 \<in> kerberos_ban;  Key KAB \<notin> used evs2;
	     Says A' Server {|Agent A, Agent B|} \<in> set evs2 |]
	  ==> Says Server A 
		(Crypt (shrK A)
		   {|Number (CT evs2), Agent B, Key KAB,  
		    (Crypt (shrK B) {|Number (CT evs2), Agent A, Key KAB|})|}) 
		# evs2 \<in> kerberos_ban"


   Kb3:  "[| evs3 \<in> kerberos_ban;  
	     Says S A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}) 
	       \<in> set evs3;
	     Says A Server {|Agent A, Agent B|} \<in> set evs3;
	     ~ Expired Ts evs3 |]
	  ==> Says A B {|X, Crypt K {|Agent A, Number (CT evs3)|} |} 
	       # evs3 \<in> kerberos_ban"


   Kb4:  "[| evs4 \<in> kerberos_ban;  
	     Says A' B {|(Crypt (shrK B) {|Number Ts, Agent A, Key K|}), 
			 (Crypt K {|Agent A, Number Ta|}) |}: set evs4;
	     ~ Expired Ts evs4;  RecentAuth Ta evs4 |]
	  ==> Says B A (Crypt K (Number Ta)) # evs4
		\<in> kerberos_ban"

	(*Old session keys may become compromised*)
   Oops: "[| evso \<in> kerberos_ban;  
	     Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|})
	       \<in> set evso;
	     Expired Ts evso |]
	  ==> Notes Spy {|Number Ts, Key K|} # evso \<in> kerberos_ban"


declare Says_imp_knows_Spy [THEN parts.Inj, dest] 
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

(*A "possibility property": there are traces that reach the end.*)
lemma "Key K \<notin> used []
       ==> \<exists>Timestamp. \<exists>evs \<in> kerberos_ban.     
             Says B A (Crypt K (Number Timestamp))  
                  \<in> set evs"
apply (cut_tac SesKeyLife_LB)
apply (intro exI bexI)
apply (rule_tac [2] 
           kerberos_ban.Nil [THEN kerberos_ban.Kb1, THEN kerberos_ban.Kb2, 
                             THEN kerberos_ban.Kb3, THEN kerberos_ban.Kb4])
apply (possibility, simp_all (no_asm_simp) add: used_Cons)
done


(**** Inductive proofs about kerberos_ban ****)

(*Forwarding Lemma for reasoning about the encrypted portion of message Kb3*)
lemma Kb3_msg_in_parts_spies:
     "Says S A (Crypt KA {|Timestamp, B, K, X|}) \<in> set evs  
      ==> X \<in> parts (spies evs)"
by blast
                              
lemma Oops_parts_spies:
     "Says Server A (Crypt (shrK A) {|Timestamp, B, K, X|}) \<in> set evs  
      ==> K \<in> parts (spies evs)"
by blast


(*Spy never sees another agent's shared key! (unless it's bad at start)*)
lemma Spy_see_shrK [simp]:
     "evs \<in> kerberos_ban ==> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule kerberos_ban.induct) 
apply (frule_tac [7] Oops_parts_spies) 
apply (frule_tac [5] Kb3_msg_in_parts_spies, simp_all)  
apply blast+
done


lemma Spy_analz_shrK [simp]:
     "evs \<in> kerberos_ban ==> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
apply auto
done


lemma Spy_see_shrK_D [dest!]:
     "[| Key (shrK A) \<in> parts (spies evs);        
                evs \<in> kerberos_ban |] ==> A:bad"
apply (blast dest: Spy_see_shrK)
done

lemmas Spy_analz_shrK_D = analz_subset_parts [THEN subsetD, THEN Spy_see_shrK_D,  dest!]


(*Nobody can have used non-existent keys!*)
lemma new_keys_not_used [rule_format, simp]:
     "evs \<in> kerberos_ban ==>       
       Key K \<notin> used evs --> K \<notin> keysFor (parts (spies evs))"
apply (erule kerberos_ban.induct) 
apply (frule_tac [7] Oops_parts_spies) 
apply (frule_tac [5] Kb3_msg_in_parts_spies, simp_all)  
(*Fake*)
apply (force dest!: keysFor_parts_insert)
(*Kb2, Kb3, Kb4*)
apply blast+
done

(** Lemmas concerning the form of items passed in messages **)

(*Describes the form of K, X and K' when the Server sends this message.*)
lemma Says_Server_message_form:
     "[| Says Server A (Crypt K' {|Number Ts, Agent B, Key K, X|})   
         \<in> set evs; evs \<in> kerberos_ban |]                            
      ==> K \<notin> range shrK &                                          
          X = (Crypt (shrK B) {|Number Ts, Agent A, Key K|}) &       
          K' = shrK A"
apply (erule rev_mp)
apply (erule kerberos_ban.induct, auto)
done


(*If the encrypted message appears then it originated with the Server
  PROVIDED that A is NOT compromised!

  This shows implicitly the FRESHNESS OF THE SESSION KEY to A
*)
lemma A_trusts_K_by_Kb2:
     "[| Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}  
           \<in> parts (spies evs);                           
         A \<notin> bad;  evs \<in> kerberos_ban |]                 
       ==> Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|})  
             \<in> set evs"
apply (erule rev_mp)
apply (erule kerberos_ban.induct) 
apply (frule_tac [7] Oops_parts_spies) 
apply (frule_tac [5] Kb3_msg_in_parts_spies, simp_all)  
apply blast
done


(*If the TICKET appears then it originated with the Server*)
(*FRESHNESS OF THE SESSION KEY to B*)
lemma B_trusts_K_by_Kb3:
     "[| Crypt (shrK B) {|Number Ts, Agent A, Key K|} \<in> parts (spies evs);  
         B \<notin> bad;  evs \<in> kerberos_ban |]                         
       ==> Says Server A                                          
            (Crypt (shrK A) {|Number Ts, Agent B, Key K,                    
                          Crypt (shrK B) {|Number Ts, Agent A, Key K|}|})   
           \<in> set evs"
apply (erule rev_mp)
apply (erule kerberos_ban.induct) 
apply (frule_tac [7] Oops_parts_spies) 
apply (frule_tac [5] Kb3_msg_in_parts_spies, simp_all)  
apply blast
done


(*EITHER describes the form of X when the following message is sent, 
  OR     reduces it to the Fake case.
  Use Says_Server_message_form if applicable.*)
lemma Says_S_message_form:
     "[| Says S A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|})      
            \<in> set evs;                                                   
         evs \<in> kerberos_ban |]                                           
 ==> (K \<notin> range shrK & X = (Crypt (shrK B) {|Number Ts, Agent A, Key K|})) 
          | X \<in> analz (spies evs)"
apply (case_tac "A \<in> bad")
apply (force dest!: Says_imp_spies [THEN analz.Inj])
apply (frule Says_imp_spies [THEN parts.Inj])
apply (blast dest!: A_trusts_K_by_Kb2 Says_Server_message_form)
done



(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (spies evs)) ==>
  Key K \<in> analz (spies evs)

 A more general formula must be proved inductively.

****)


(** Session keys are not used to encrypt other session keys **)

lemma analz_image_freshK [rule_format (no_asm)]:
     "evs \<in> kerberos_ban ==>                           
   \<forall>K KK. KK \<subseteq> - (range shrK) -->                  
          (Key K \<in> analz (Key`KK Un (spies evs))) =   
          (K \<in> KK | Key K \<in> analz (spies evs))"
apply (erule kerberos_ban.induct)
apply (drule_tac [7] Says_Server_message_form)
apply (erule_tac [5] Says_S_message_form [THEN disjE], analz_freshK, spy_analz)
done



lemma analz_insert_freshK:
     "[| evs \<in> kerberos_ban;  KAB \<notin> range shrK |] ==>      
      (Key K \<in> analz (insert (Key KAB) (spies evs))) =        
      (K = KAB | Key K \<in> analz (spies evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


(** The session key K uniquely identifies the message **)

lemma unique_session_keys:
     "[| Says Server A                                     
           (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}) \<in> set evs;   
         Says Server A'                                    
          (Crypt (shrK A') {|Number Ts', Agent B', Key K, X'|}) \<in> set evs; 
         evs \<in> kerberos_ban |] ==> A=A' & Ts=Ts' & B=B' & X = X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos_ban.induct) 
apply (frule_tac [7] Oops_parts_spies) 
apply (frule_tac [5] Kb3_msg_in_parts_spies, simp_all)  
(*Kb2: it can't be a new key*)
apply blast
done


(** Lemma: the session key sent in msg Kb2 would be EXPIRED
    if the spy could see it!
**)

lemma lemma2 [rule_format (no_asm)]:
     "[| A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos_ban |]            
  ==> Says Server A                                             
          (Crypt (shrK A) {|Number Ts, Agent B, Key K,          
                            Crypt (shrK B) {|Number Ts, Agent A, Key K|}|}) 
         \<in> set evs -->                                          
      Key K \<in> analz (spies evs) --> Expired Ts evs"
apply (erule kerberos_ban.induct)
apply (frule_tac [7] Says_Server_message_form)
apply (frule_tac [5] Says_S_message_form [THEN disjE])
apply (simp_all (no_asm_simp) add: less_SucI analz_insert_eq analz_insert_freshK pushes)
txt{*Fake*}
apply spy_analz
txt{*Kb2*}
apply (blast intro: parts_insertI less_SucI)
txt{*Kb3*}
apply (case_tac "Aa \<in> bad")
 prefer 2 apply (blast dest: A_trusts_K_by_Kb2 unique_session_keys)
apply (blast dest: Says_imp_spies [THEN analz.Inj] Crypt_Spy_analz_bad elim!: MPair_analz intro: less_SucI)
txt{*Oops: PROOF FAILED if addIs below*}
apply (blast dest: unique_session_keys intro!: less_SucI)
done


(** CONFIDENTIALITY for the SERVER:
                     Spy does not see the keys sent in msg Kb2 
                     as long as they have NOT EXPIRED
**)
lemma Confidentiality_S:
     "[| Says Server A                                            
          (Crypt K' {|Number T, Agent B, Key K, X|}) \<in> set evs;   
         ~ Expired T evs;                                         
         A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos_ban                 
      |] ==> Key K \<notin> analz (spies evs)"
apply (frule Says_Server_message_form, assumption)
apply (blast intro: lemma2)
done

(**** THE COUNTERPART OF CONFIDENTIALITY 
      [|...; Expired Ts evs; ...|] ==> Key K \<in> analz (spies evs)
      WOULD HOLD ONLY IF AN OOPS OCCURRED! ---> Nothing to prove!   ****)


(** CONFIDENTIALITY for ALICE: **)
(** Also A_trusts_K_by_Kb2 RS Confidentiality_S **)
lemma Confidentiality_A:
     "[| Crypt (shrK A) {|Number T, Agent B, Key K, X|} \<in> parts (spies evs); 
         ~ Expired T evs;           
         A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos_ban                 
      |] ==> Key K \<notin> analz (spies evs)"
apply (blast dest!: A_trusts_K_by_Kb2 Confidentiality_S)
done


(** CONFIDENTIALITY for BOB: **)
(** Also B_trusts_K_by_Kb3 RS Confidentiality_S **)
lemma Confidentiality_B:
     "[| Crypt (shrK B) {|Number Tk, Agent A, Key K|}  
          \<in> parts (spies evs);               
        ~ Expired Tk evs;           
        A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos_ban                 
      |] ==> Key K \<notin> analz (spies evs)"
apply (blast dest!: B_trusts_K_by_Kb3 Confidentiality_S)
done


lemma lemma_B [rule_format]:
     "[| B \<notin> bad;  evs \<in> kerberos_ban |]                         
      ==> Key K \<notin> analz (spies evs) -->                     
          Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|})  
          \<in> set evs -->                                              
          Crypt K (Number Ta) \<in> parts (spies evs) -->         
          Says B A (Crypt K (Number Ta)) \<in> set evs"
apply (erule kerberos_ban.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] Says_S_message_form)
apply (drule_tac [6] Kb3_msg_in_parts_spies, analz_mono_contra)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt{*Fake*}
apply blast
txt{*Kb2*}
apply (force dest: Crypt_imp_invKey_keysFor) 
txt{*Kb4*}
apply (blast dest: B_trusts_K_by_Kb3 unique_session_keys 
                   Says_imp_spies [THEN analz.Inj] Crypt_Spy_analz_bad)
done


(*AUTHENTICATION OF B TO A*)
lemma Authentication_B:
     "[| Crypt K (Number Ta) \<in> parts (spies evs);            
         Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}     
         \<in> parts (spies evs);                                
         ~ Expired Ts evs;                                   
         A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos_ban |]         
      ==> Says B A (Crypt K (Number Ta)) \<in> set evs"
by (blast dest!: A_trusts_K_by_Kb2
          intro!: lemma_B elim!: Confidentiality_S [THEN [2] rev_notE])



lemma lemma_A [rule_format]:
     "[| A \<notin> bad; B \<notin> bad; evs \<in> kerberos_ban |] 
      ==>           
         Key K \<notin> analz (spies evs) -->          
         Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|})   
         \<in> set evs -->   
          Crypt K {|Agent A, Number Ta|} \<in> parts (spies evs) --> 
         Says A B {|X, Crypt K {|Agent A, Number Ta|}|}   
             \<in> set evs"
apply (erule kerberos_ban.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] Says_S_message_form)
apply (frule_tac [6] Kb3_msg_in_parts_spies, analz_mono_contra)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt{*Fake*}
apply blast
txt{*Kb2*}
apply (force dest: Crypt_imp_invKey_keysFor) 
txt{*Kb3*}
apply (blast dest: A_trusts_K_by_Kb2 unique_session_keys)
done


(*AUTHENTICATION OF A TO B*)
lemma Authentication_A:
     "[| Crypt K {|Agent A, Number Ta|} \<in> parts (spies evs);   
         Crypt (shrK B) {|Number Ts, Agent A, Key K|}          
         \<in> parts (spies evs);                                  
         ~ Expired Ts evs;                                     
         A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos_ban |]           
      ==> Says A B {|Crypt (shrK B) {|Number Ts, Agent A, Key K|},      
                     Crypt K {|Agent A, Number Ta|}|} \<in> set evs"
by (blast dest!: B_trusts_K_by_Kb3
          intro!: lemma_A 
          elim!: Confidentiality_S [THEN [2] rev_notE])

end
