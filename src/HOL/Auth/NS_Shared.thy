(*  Title:      HOL/Auth/NS_Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_shared" for Needham-Schroeder Shared-Key protocol.

From page 247 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

NS_Shared = Shared + 

consts  ns_shared   :: event list set
inductive "ns_shared"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: ns_shared"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: ns_shared;  B ~= Spy;  
             X: synth (analz (spies evs)) |]
          ==> Says Spy B X # evs : ns_shared"

         (*Alice initiates a protocol run, requesting to talk to any B*)
    NS1  "[| evs1: ns_shared;  A ~= Server;  Nonce NA ~: used evs1 |]
          ==> Says A Server {|Agent A, Agent B, Nonce NA|} # evs1
                :  ns_shared"

         (*Server's response to Alice's message.
           !! It may respond more than once to A's request !!
	   Server doesn't know who the true sender is, hence the A' in
               the sender field.*)
    NS2  "[| evs2: ns_shared;  A ~= B;  A ~= Server;  Key KAB ~: used evs2;
             Says A' Server {|Agent A, Agent B, Nonce NA|} : set evs2 |]
          ==> Says Server A 
                (Crypt (shrK A)
                   {|Nonce NA, Agent B, Key KAB,
                     (Crypt (shrK B) {|Key KAB, Agent A|})|}) 
                # evs2 : ns_shared"

          (*We can't assume S=Server.  Agent A "remembers" her nonce.
            Can inductively show A ~= Server*)
    NS3  "[| evs3: ns_shared;  A ~= B;
             Says S A (Crypt (shrK A) {|Nonce NA, Agent B, Key K, X|}) 
               : set evs3;
             Says A Server {|Agent A, Agent B, Nonce NA|} : set evs3 |]
          ==> Says A B X # evs3 : ns_shared"

         (*Bob's nonce exchange.  He does not know who the message came
           from, but responds to A because she is mentioned inside.*)
    NS4  "[| evs4: ns_shared;  A ~= B;  Nonce NB ~: used evs4;
             Says A' B (Crypt (shrK B) {|Key K, Agent A|}) : set evs4 |]
          ==> Says B A (Crypt K (Nonce NB)) # evs4
                : ns_shared"

         (*Alice responds with Nonce NB if she has seen the key before.
           Maybe should somehow check Nonce NA again.
           We do NOT send NB-1 or similar as the Spy cannot spoof such things.
           Letting the Spy add or subtract 1 lets him send ALL nonces.
           Instead we distinguish the messages by sending the nonce twice.*)
    NS5  "[| evs5: ns_shared;  A ~= B;  
             Says B' A (Crypt K (Nonce NB)) : set evs5;
             Says S  A (Crypt (shrK A) {|Nonce NA, Agent B, Key K, X|})
               : set evs5 |]
          ==> Says A B (Crypt K {|Nonce NB, Nonce NB|}) # evs5 : ns_shared"
  
         (*This message models possible leaks of session keys.
           The two Nonces identify the protocol run: the rule insists upon
           the true senders in order to make them accurate.*)
    Oops "[| evso: ns_shared;  A ~= Spy;
             Says B A (Crypt K (Nonce NB)) : set evso;
             Says Server A (Crypt (shrK A) {|Nonce NA, Agent B, Key K, X|})
               : set evso |]
          ==> Says A Spy {|Nonce NA, Nonce NB, Key K|} # evso : ns_shared"

end
