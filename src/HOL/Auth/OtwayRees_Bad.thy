(*  Title:      HOL/Auth/OtwayRees_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

The FAULTY version omitting encryption of Nonce NB, as suggested on page 247 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

OtwayRees_Bad = Shared + 

consts  otway   :: event list set

inductive otway
  intrs 
         (*Initial trace is empty*)
    Nil  "[] \\<in> otway"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evsf \\<in> otway;  X \\<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \\<in> otway"

         (*A message that has been sent can be received by the
           intended recipient.*)
    Reception "[| evsr \\<in> otway;  Says A B X \\<in> set evsr |]
               ==> Gets B X # evsr \\<in> otway"

         (*Alice initiates a protocol run*)
    OR1  "[| evs1 \\<in> otway;  Nonce NA \\<notin> used evs1 |]
          ==> Says A B {|Nonce NA, Agent A, Agent B, 
                         Crypt (shrK A) {|Nonce NA, Agent A, Agent B|} |} 
                 # evs1 \\<in> otway"

         (*Bob's response to Alice's message. 
           This variant of the protocol does NOT encrypt NB.*)
    OR2  "[| evs2 \\<in> otway;  Nonce NB \\<notin> used evs2;
             Gets B {|Nonce NA, Agent A, Agent B, X|} \\<in> set evs2 |]
          ==> Says B Server 
                  {|Nonce NA, Agent A, Agent B, X, Nonce NB,
                    Crypt (shrK B) {|Nonce NA, Agent A, Agent B|}|}
                 # evs2 \\<in> otway"

         (*The Server receives Bob's message and checks that the three NAs
           match.  Then he sends a new session key to Bob with a packet for
           forwarding to Alice.*)
    OR3  "[| evs3 \\<in> otway;  Key KAB \\<notin> used evs3;
             Gets Server 
                  {|Nonce NA, Agent A, Agent B, 
                    Crypt (shrK A) {|Nonce NA, Agent A, Agent B|}, 
                    Nonce NB, 
                    Crypt (shrK B) {|Nonce NA, Agent A, Agent B|}|}
               \\<in> set evs3 |]
          ==> Says Server B 
                  {|Nonce NA, 
                    Crypt (shrK A) {|Nonce NA, Key KAB|},
                    Crypt (shrK B) {|Nonce NB, Key KAB|}|}
                 # evs3 \\<in> otway"

         (*Bob receives the Server's (?) message and compares the Nonces with
	   those in the message he previously sent the Server.
           Need B ~= Server because we allow messages to self.*)
    OR4  "[| evs4 \\<in> otway;  B ~= Server;
             Says B Server {|Nonce NA, Agent A, Agent B, X', Nonce NB,
                             Crypt (shrK B) {|Nonce NA, Agent A, Agent B|}|}
               \\<in> set evs4;
             Gets B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               \\<in> set evs4 |]
          ==> Says B A {|Nonce NA, X|} # evs4 \\<in> otway"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.*)
    Oops "[| evso \\<in> otway;  
             Says Server B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               \\<in> set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso \\<in> otway"

end
