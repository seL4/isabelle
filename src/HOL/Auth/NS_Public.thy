(*  Title:      HOL/Auth/NS_Public
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_public" for the Needham-Schroeder Public-Key protocol.
Version incorporating Lowe's fix (inclusion of B's identify in round 2).
*)

NS_Public = Public + 

consts  lost    :: agent set        (*No need for it to be a variable*)
	ns_public  :: event list set
inductive ns_public
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: ns_public"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: ns_public;  B ~= Spy;  
             X: synth (analz (sees lost Spy evs)) |]
          ==> Says Spy B X  # evs : ns_public"

         (*Alice initiates a protocol run, sending a nonce to Bob*)
    NS1  "[| evs: ns_public;  A ~= B;  Nonce NA ~: used evs |]
          ==> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|})
                 # evs  :  ns_public"

         (*Bob responds to Alice's message with a further nonce*)
    NS2  "[| evs: ns_public;  A ~= B;  Nonce NB ~: used evs;
             Says A' B (Crypt (pubK B) {|Nonce NA, Agent A|})
               : set_of_list evs |]
          ==> Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|})
                # evs  :  ns_public"

         (*Alice proves her existence by sending NB back to Bob.*)
    NS3  "[| evs: ns_public;  A ~= B;
             Says B' A (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|})
               : set_of_list evs;
             Says A  B (Crypt (pubK B) {|Nonce NA, Agent A|})
               : set_of_list evs |]
          ==> Says A B (Crypt (pubK B) (Nonce NB)) # evs : ns_public"

  (**Oops message??**)

rules
  (*Spy has access to his own key for spoof messages*)
  Spy_in_lost "Spy: lost"

end
