(*  Title:      HOL/Auth/NS_Public_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_public" for the Needham-Schroeder Public-Key protocol.
Flawed version, vulnerable to Lowe's attack.

From page 260 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

theory NS_Public_Bad = Public:

consts  ns_public  :: "event list set"

inductive ns_public
  intros 
         (*Initial trace is empty*)
   Nil:  "[] \<in> ns_public"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
   Fake: "\<lbrakk>evsf \<in> ns_public;  X \<in> synth (analz (spies evsf))\<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> ns_public"

         (*Alice initiates a protocol run, sending a nonce to Bob*)
   NS1:  "\<lbrakk>evs1 \<in> ns_public;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>)
                # evs1  \<in>  ns_public"

         (*Bob responds to Alice's message with a further nonce*)
   NS2:  "\<lbrakk>evs2 \<in> ns_public;  Nonce NB \<notin> used evs2;
           Says A' B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>)
                # evs2  \<in>  ns_public"

         (*Alice proves her existence by sending NB back to Bob.*)
   NS3:  "\<lbrakk>evs3 \<in> ns_public;
           Says A  B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
           Says B' A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubK B) (Nonce NB)) # evs3 \<in> ns_public"

declare knows_Spy_partsEs [elim]
declare analz_subset_parts [THEN subsetD, dest]
declare Fake_parts_insert [THEN subsetD, dest]
declare image_eq_UN [simp]  (*accelerates proofs involving nested images*)

(*A "possibility property": there are traces that reach the end*)
lemma "\<exists>NB. \<exists>evs \<in> ns_public. Says A B (Crypt (pubK B) (Nonce NB)) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] ns_public.Nil [THEN ns_public.NS1, THEN ns_public.NS2, 
                                   THEN ns_public.NS3])
by possibility


(**** Inductive proofs about ns_public ****)

(** Theorems of the form X \<notin> parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's bad at start)*)
lemma Spy_see_priK [simp]: 
      "evs \<in> ns_public \<Longrightarrow> (Key (priK A) \<in> parts (spies evs)) = (A \<in> bad)"
by (erule ns_public.induct, auto)

lemma Spy_analz_priK [simp]: 
      "evs \<in> ns_public \<Longrightarrow> (Key (priK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto


(*** Authenticity properties obtained from NS2 ***)

(*It is impossible to re-use a nonce in both NS1 and NS2, provided the nonce
  is secret.  (Honest users generate fresh nonces.)*)
lemma no_nonce_NS1_NS2 [rule_format]: 
      "evs \<in> ns_public 
       \<Longrightarrow> Crypt (pubK C) \<lbrace>NA', Nonce NA\<rbrace> \<in> parts (spies evs) \<longrightarrow>
           Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies evs) \<longrightarrow>  
           Nonce NA \<in> analz (spies evs)"
apply (erule ns_public.induct, simp_all)
apply (blast intro: analz_insertI)+
done


(*Unicity for NS1: nonce NA identifies agents A and B*)
lemma unique_NA: 
     "\<lbrakk>Crypt(pubK B)  \<lbrace>Nonce NA, Agent A \<rbrace> \<in> parts(spies evs);  
       Crypt(pubK B') \<lbrace>Nonce NA, Agent A'\<rbrace> \<in> parts(spies evs);  
       Nonce NA \<notin> analz (spies evs); evs \<in> ns_public\<rbrakk>
      \<Longrightarrow> A=A' \<and> B=B'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)   
apply (erule ns_public.induct, simp_all)
(*Fake, NS1*)
apply (blast intro!: analz_insertI)+
done


(*Secrecy: Spy does not see the nonce sent in msg NS1 if A and B are secure
  The major premise "Says A B ..." makes it a dest-rule, so we use
  (erule rev_mp) rather than rule_format. *)
theorem Spy_not_see_NA: 
      "\<lbrakk>Says A B (Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
       \<Longrightarrow> Nonce NA \<notin> analz (spies evs)"
apply (erule rev_mp)   
apply (erule ns_public.induct, simp_all, spy_analz)
apply (blast dest: unique_NA intro: no_nonce_NS1_NS2)+
done


(*Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.*)
lemma A_trusts_NS2_lemma [rule_format]: 
   "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
    \<Longrightarrow> Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts (spies evs) \<longrightarrow>
	Says A B (Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs \<longrightarrow>
	Says B A (Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs"
apply (erule ns_public.induct)
apply (auto dest: Spy_not_see_NA unique_NA)
done

theorem A_trusts_NS2: 
     "\<lbrakk>Says A  B (Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs;   
       Says B' A (Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
      \<Longrightarrow> Says B A (Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs"
by (blast intro: A_trusts_NS2_lemma)


(*If the encrypted message appears then it originated with Alice in NS1*)
lemma B_trusts_NS1 [rule_format]:
     "evs \<in> ns_public                                         
      \<Longrightarrow> Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies evs) \<longrightarrow>
	  Nonce NA \<notin> analz (spies evs) \<longrightarrow>
	  Says A B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs"
apply (erule ns_public.induct, simp_all)
(*Fake*)
apply (blast intro!: analz_insertI)
done



(*** Authenticity properties obtained from NS2 ***)

(*Unicity for NS2: nonce NB identifies nonce NA and agent A
  [proof closely follows that for unique_NA] *)
lemma unique_NB [dest]: 
     "\<lbrakk>Crypt(pubK A)  \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts(spies evs);
       Crypt(pubK A') \<lbrace>Nonce NA', Nonce NB\<rbrace> \<in> parts(spies evs);
       Nonce NB \<notin> analz (spies evs); evs \<in> ns_public\<rbrakk>
     \<Longrightarrow> A=A' \<and> NA=NA'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)   
apply (erule ns_public.induct, simp_all)
(*Fake, NS2*)
apply (blast intro!: analz_insertI)+
done


(*NB remains secret PROVIDED Alice never responds with round 3*)
theorem Spy_not_see_NB [dest]:
     "\<lbrakk>Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;   
       \<forall>C. Says A C (Crypt (pubK C) (Nonce NB)) \<notin> set evs;       
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                      
     \<Longrightarrow> Nonce NB \<notin> analz (spies evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule ns_public.induct, simp_all, spy_analz)
apply (simp_all add: all_conj_distrib) (*speeds up the next step*)
apply (blast intro: no_nonce_NS1_NS2)+
done


(*Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3--to somebody....*)

lemma B_trusts_NS3_lemma [rule_format]:
     "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                    
      \<Longrightarrow> Crypt (pubK B) (Nonce NB) \<in> parts (spies evs) \<longrightarrow>
          Says B A  (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs \<longrightarrow>
          (\<exists>C. Says A C (Crypt (pubK C) (Nonce NB)) \<in> set evs)"
apply (erule ns_public.induct, auto)
by (blast intro: no_nonce_NS1_NS2)+

theorem B_trusts_NS3:
     "\<lbrakk>Says B A  (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;
       Says A' B (Crypt (pubK B) (Nonce NB)) \<in> set evs;             
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                    
      \<Longrightarrow> \<exists>C. Says A C (Crypt (pubK C) (Nonce NB)) \<in> set evs"
by (blast intro: B_trusts_NS3_lemma)


(*Can we strengthen the secrecy theorem Spy_not_see_NB?  NO*)
lemma "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>            
       \<Longrightarrow> Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs  
           \<longrightarrow> Nonce NB \<notin> analz (spies evs)"
apply (erule ns_public.induct, simp_all, spy_analz)
(*NS1: by freshness*)
apply blast
(*NS2: by freshness and unicity of NB*)
apply (blast intro: no_nonce_NS1_NS2)
(*NS3: unicity of NB identifies A and NA, but not B*)
apply clarify
apply (frule_tac A' = A in 
       Says_imp_knows_Spy [THEN parts.Inj, THEN unique_NB], auto)
apply (rename_tac C B' evs3)
oops

(*
THIS IS THE ATTACK!
Level 8
!!evs. \<lbrakk>A \<notin> bad; B \<notin> bad; evs \<in> ns_public\<rbrakk>
       \<Longrightarrow> Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs \<longrightarrow>
           Nonce NB \<notin> analz (spies evs)
 1. !!C B' evs3.
       \<lbrakk>A \<notin> bad; B \<notin> bad; evs3 \<in> ns_public
        Says A C (Crypt (pubK C) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
        Says B' A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3; 
        C \<in> bad;
        Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3;
        Nonce NB \<notin> analz (spies evs3)\<rbrakk>
       \<Longrightarrow> False
*)

end
