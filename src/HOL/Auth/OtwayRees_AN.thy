(*  Title:      HOL/Auth/OtwayRees
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

Simplified version with minimal encryption but explicit messages

Note that the formalization does not even assume that nonces are fresh.
This is because the protocol does not rely on uniqueness of nonces for
security, only for freshness, and the proof script does not prove freshness
properties.

From page 11 of
  Abadi and Needham.  Prudent Engineering Practice for Cryptographic Protocols.
  IEEE Trans. SE 22 (1), 1996
*)

OtwayRees_AN = Shared + 

consts  otway   :: agent set => event list set
inductive "otway lost"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: otway lost"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: otway lost;  B ~= Spy;  
             X: synth (analz (sees lost Spy evs)) |]
          ==> Says Spy B X  # evs : otway lost"

         (*Alice initiates a protocol run*)
    OR1  "[| evs: otway lost;  A ~= B;  B ~= Server |]
          ==> Says A B {|Agent A, Agent B, Nonce NA|} # evs : otway lost"

         (*Bob's response to Alice's message.  Bob doesn't know who 
	   the sender is, hence the A' in the sender field.*)
    OR2  "[| evs: otway lost;  B ~= Server;
             Says A' B {|Agent A, Agent B, Nonce NA|} : set_of_list evs |]
          ==> Says B Server {|Agent A, Agent B, Nonce NA, Nonce NB|}
                 # evs : otway lost"

         (*The Server receives Bob's message.  Then he sends a new
           session key to Bob with a packet for forwarding to Alice.*)
    OR3  "[| evs: otway lost;  B ~= Server;  A ~= B;  Key KAB ~: used evs;
             Says B' Server {|Agent A, Agent B, Nonce NA, Nonce NB|}
               : set_of_list evs |]
          ==> Says Server B 
               {|Crypt (shrK A) {|Nonce NA, Agent A, Agent B, Key KAB|},
                 Crypt (shrK B) {|Nonce NB, Agent A, Agent B, Key KAB|}|}
              # evs : otway lost"

         (*Bob receives the Server's (?) message and compares the Nonces with
	   those in the message he previously sent the Server.*)
    OR4  "[| evs: otway lost;  A ~= B;
             Says B Server {|Agent A, Agent B, Nonce NA, Nonce NB|}
               : set_of_list evs;
             Says S B {|X, Crypt(shrK B){|Nonce NB, Agent A, Agent B, Key K|}|}
               : set_of_list evs |]
          ==> Says B A X # evs : otway lost"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.  B is not assumed to know shrK A.*)
    Oops "[| evs: otway lost;  B ~= Spy;
             Says Server B 
                      {|Crypt (shrK A) {|Nonce NA, Agent A, Agent B, Key K|}, 
                        Crypt (shrK B) {|Nonce NB, Agent A, Agent B, Key K|}|}
               : set_of_list evs |]
          ==> Says B Spy {|Nonce NA, Nonce NB, Key K|} # evs : otway lost"

end
