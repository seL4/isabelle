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

consts  ns_shared   :: "event list set"
inductive ns_shared
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: ns_shared"

         (*The enemy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: ns_shared;  B ~= Enemy;  X: synth (analz (sees Enemy evs)) |]
          ==> Says Enemy B X # evs : ns_shared"

         (*Alice initiates a protocol run, requesting to talk to any B*)
    NS1  "[| evs: ns_shared;  A ~= Server |]
          ==> Says A Server {|Agent A, Agent B, Nonce (newN evs)|} # evs
                 : ns_shared"

         (*Server's response to Alice's message.
           !! It may respond more than once to A's request !!
	   Server doesn't know who the true sender is, hence the A' in
               the sender field.*)
    NS2  "[| evs: ns_shared;  A ~= B;  A ~= Server;
             Says A' Server {|Agent A, Agent B, Nonce NA|} : set_of_list evs |]
          ==> Says Server A 
                  (Crypt {|Nonce NA, Agent B, Key (newK evs),   
                           (Crypt {|Key (newK evs), Agent A|} (shrK B))|}
                   (shrK A)) # evs : ns_shared"

          (*We can't assume S=Server.  Agent A "remembers" her nonce.
            May assume WLOG that she is NOT the Enemy: the Fake rule
            covers this case.  Can inductively show A ~= Server*)
    NS3  "[| evs: ns_shared;  A ~= B;
             Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A)) 
               : set_of_list evs;
             A = Friend i;
             Says A Server {|Agent A, Agent B, Nonce NA|} : set_of_list evs |]
          ==> Says A B X # evs : ns_shared"

         (*Bob's nonce exchange.  He does not know who the message came
           from, but responds to A because she is mentioned inside.*)
    NS4  "[| evs: ns_shared;  A ~= B;  
             Says A' B (Crypt {|Key K, Agent A|} (shrK B)) : set_of_list evs |]
          ==> Says B A (Crypt (Nonce (newN evs)) K) # evs : ns_shared"

         (*Alice responds with the Nonce, if she has seen the key before.
           We do NOT use N-1 or similar as the Enemy cannot spoof such things.
           Allowing the Enemy to add or subtract 1 allows him to send ALL
               nonces.  Instead we distinguish the messages by sending the
               nonce twice.*)
    NS5  "[| evs: ns_shared;  A ~= B;  
             Says B' A (Crypt (Nonce N) K) : set_of_list evs;
             Says S  A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A))
               : set_of_list evs |]
          ==> Says A B (Crypt {|Nonce N, Nonce N|} K) # evs : ns_shared"

end
