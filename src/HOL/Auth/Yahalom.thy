(*  Title:      HOL/Auth/OtwayRees
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "yahalom" for the Yahalom protocol.

From page 257 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

OtwayRees = Shared + 

consts  yahalom   :: "event list set"
inductive yahalom
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: yahalom"

         (*The enemy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: yahalom;  B ~= Enemy;  X: synth (analz (sees Enemy evs)) |]
          ==> Says Enemy B X  # evs : yahalom"

         (*Alice initiates a protocol run*)
    YM1  "[| evs: yahalom;  A ~= B |]
          ==> Says A B {|Nonce (newN evs), Agent A |} # evs : yahalom"

         (*Bob's response to Alice's message.  Bob doesn't know who 
	   the sender is, hence the A' in the sender field.
           We modify the published protocol by NOT encrypting NB.*)
    YM2  "[| evs: yahalom;  B ~= Server;
             Says A' B {|Nonce NA, Agent A|} : set_of_list evs |]
          ==> Says B Server 
                  {|Agent B, 
                    Crypt {|Agent A, Nonce NA, Nonce (newN evs)|} (shrK B)|}
                 # evs : yahalom"

         (*The Server receives Bob's message.  He responds by sending a
            new session key to Alice, with a packet for forwarding to Bob.*)
    YM3  "[| evs: yahalom;  B ~= Server;
             Says B' Server 
                  {|Nonce NA, Agent A, Agent B, 
                    Crypt {|Nonce NA, Agent A, Agent B|} (shrK A), 
                    Nonce NB, 
                    Crypt {|Nonce NA, Agent A, Agent B|} (shrK B)|}
               : set_of_list evs |]
          ==> Says Server B 
                  {|Nonce NA, 
                    Crypt {|Nonce NA, Key (newK evs)|} (shrK A),
                    Crypt {|Nonce NB, Key (newK evs)|} (shrK B)|}
                 # evs : yahalom"

         (*Bob receives the Server's (?) message and compares the Nonces with
	   those in the message he previously sent the Server.*)
    YM4  "[| evs: yahalom;  A ~= B;  
             Says S B {|Nonce NA, X, Crypt {|Nonce NB, Key K|} (shrK B)|}
               : set_of_list evs;
             Says B Server {|Nonce NA, Agent A, Agent B, X', Nonce NB, X''|}
               : set_of_list evs |]
          ==> (Says B A {|Nonce NA, X|}) # evs : yahalom"

         (*Alice checks her Nonce, then sends a dummy message to Bob,
           using the new session key.*)
    YM5  "[| evs: yahalom;  
             Says B' A {|Nonce NA, Crypt {|Nonce NA, Key K|} (shrK A)|}
               : set_of_list evs;
             Says A  B {|Nonce NA, Agent A, Agent B, X|} : set_of_list evs |]
          ==> Says A B (Crypt (Agent A) K)  # evs : yahalom"

end
