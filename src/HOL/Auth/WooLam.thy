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

consts  woolam   :: "agent set => event list set"
inductive "woolam lost"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: woolam lost"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: woolam lost;  B ~= Spy;  
             X: synth (analz (sees lost Spy evs)) |]
          ==> Says Spy B X  # evs : woolam lost"

         (*Alice initiates a protocol run*)
    WL1  "[| evs: woolam lost;  A ~= B |]
          ==> Says A B (Agent A) # evs : woolam lost"

         (*Bob responds to Alice's message with a challenge.*)
    WL2  "[| evs: woolam lost;  A ~= B;
             Says A' B (Agent A) : set_of_list evs |]
          ==> Says B A (Nonce (newN evs)) # evs : woolam lost"

         (*Alice responds to Bob's challenge by encrypting NB with her key.
           B is *not* properly determined -- Alice essentially broadcasts
           her reply.*)
    WL3  "[| evs: woolam lost;  A ~= B;
             Says B' A (Nonce NB) : set_of_list evs;
             Says A  B (Agent A)  : set_of_list evs |]
          ==> Says A B (Crypt (Nonce NB) (shrK A)) # evs : woolam lost"

         (*Bob forwards Alice's response to the Server.*)
    WL4  "[| evs: woolam lost;  B ~= Server;  
             Says A'  B X         : set_of_list evs;
             Says A'' B (Agent A) : set_of_list evs |]
          ==> Says B Server {|Agent A, Agent B, X|} # evs : woolam lost"

         (*Server decrypts Alice's response for Bob.*)
    WL5  "[| evs: woolam lost;  B ~= Server;
             Says B' Server {|Agent A, Agent B, Crypt (Nonce NB) (shrK A)|}
               : set_of_list evs |]
          ==> Says Server B (Crypt {|Agent A, Nonce NB|} (shrK B))
                 # evs : woolam lost"

end
