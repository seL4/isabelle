(*  Title:      HOL/Auth/WooLam
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "woolam" for the Woo-Lam protocol.

Simplified version from page 11 of
  Abadi and Needham.  Prudent Engineering Practice for Cryptographic Protocols.
  IEEE Trans. S.E. 22(1), 1996, pages 6-15.

Note: this differs from the Woo-Lam protocol discussed by Lowe in his paper
  Some New Attacks upon Security Protocols.
  Computer Security Foundations Workshop, 1996.
*)

WooLam = Shared + 

consts  woolam  :: event list set
inductive woolam
  intrs 
         (*Initial trace is empty*)
    Nil  "[] \\<in> woolam"

         (** These rules allow agents to send messages to themselves **)

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evsf \\<in> woolam;  X \\<in> synth (analz (spies evsf)) |]
          ==> Says Spy B X  # evsf \\<in> woolam"

         (*Alice initiates a protocol run*)
    WL1  "[| evs1 \\<in> woolam |]
          ==> Says A B (Agent A) # evs1 \\<in> woolam"

         (*Bob responds to Alice's message with a challenge.*)
    WL2  "[| evs2 \\<in> woolam;  Says A' B (Agent A) \\<in> set evs2 |]
          ==> Says B A (Nonce NB) # evs2 \\<in> woolam"

         (*Alice responds to Bob's challenge by encrypting NB with her key.
           B is *not* properly determined -- Alice essentially broadcasts
           her reply.*)
    WL3  "[| evs3 \\<in> woolam;
             Says A  B (Agent A)  \\<in> set evs3;
             Says B' A (Nonce NB) \\<in> set evs3 |]
          ==> Says A B (Crypt (shrK A) (Nonce NB)) # evs3 \\<in> woolam"

         (*Bob forwards Alice's response to the Server.  NOTE: usually
           the messages are shown in chronological order, for clarity.
           But here, exchanging the two events would cause the lemma
           WL4_analz_spies to pick up the wrong assumption!*)
    WL4  "[| evs4 \\<in> woolam;  
             Says A'  B X         \\<in> set evs4;
             Says A'' B (Agent A) \\<in> set evs4 |]
          ==> Says B Server {|Agent A, Agent B, X|} # evs4 \\<in> woolam"

         (*Server decrypts Alice's response for Bob.*)
    WL5  "[| evs5 \\<in> woolam;  
             Says B' Server {|Agent A, Agent B, Crypt (shrK A) (Nonce NB)|}
               \\<in> set evs5 |]
          ==> Says Server B (Crypt (shrK B) {|Agent A, Nonce NB|})
                 # evs5 \\<in> woolam"

end
