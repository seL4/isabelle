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

consts  otway   :: event list set
inductive "otway"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: otway"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs \\<in> otway;  X \\<in> synth (analz (knows Spy evs)) |]
          ==> Says Spy B X  # evs \\<in> otway"

         (*A message that has been sent can be received by the
           intended recipient.*)
    Reception "[| evsr \\<in> otway;  Says A B X \\<in>set evsr |]
               ==> Gets B X # evsr \\<in> otway"

         (*Alice initiates a protocol run*)
    OR1  "[| evs1 \\<in> otway |]
          ==> Says A B {|Agent A, Agent B, Nonce NA|} # evs1 \\<in> otway"

         (*Bob's response to Alice's message.*)
    OR2  "[| evs2 \\<in> otway;  
             Gets B {|Agent A, Agent B, Nonce NA|} \\<in>set evs2 |]
          ==> Says B Server {|Agent A, Agent B, Nonce NA, Nonce NB|}
                 # evs2 \\<in> otway"

         (*The Server receives Bob's message.  Then he sends a new
           session key to Bob with a packet for forwarding to Alice.*)
    OR3  "[| evs3 \\<in> otway;  Key KAB \\<notin> used evs3;
             Gets Server {|Agent A, Agent B, Nonce NA, Nonce NB|}
               \\<in>set evs3 |]
          ==> Says Server B 
               {|Crypt (shrK A) {|Nonce NA, Agent A, Agent B, Key KAB|},
                 Crypt (shrK B) {|Nonce NB, Agent A, Agent B, Key KAB|}|}
              # evs3 \\<in> otway"

         (*Bob receives the Server's (?) message and compares the Nonces with
	   those in the message he previously sent the Server.
           Need B ~= Server because we allow messages to self.*)
    OR4  "[| evs4 \\<in> otway;  B ~= Server; 
             Says B Server {|Agent A, Agent B, Nonce NA, Nonce NB|} \\<in>set evs4;
             Gets B {|X, Crypt(shrK B){|Nonce NB,Agent A,Agent B,Key K|}|}
               \\<in>set evs4 |]
          ==> Says B A X # evs4 \\<in> otway"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.  B is not assumed to know shrK A.*)
    Oops "[| evso \\<in> otway;  
             Says Server B 
                      {|Crypt (shrK A) {|Nonce NA, Agent A, Agent B, Key K|}, 
                        Crypt (shrK B) {|Nonce NB, Agent A, Agent B, Key K|}|}
               \\<in>set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso \\<in> otway"

end
