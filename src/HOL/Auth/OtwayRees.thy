(*  
Inductive relation "otway" for the Otway-Rees protocol
extended by Gets primitive.

Version that encrypts Nonce NB

*)

OtwayRees = Shared + 


consts  otway   :: event list set
inductive "otway"
  intrs 
         (*Initial trace is empty*)
    Nil  "[] \\<in> otway"

         (** These rules allow agents to send messages to themselves **)

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evsf \\<in> otway;  X \\<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf : otway"

         (*A message that has been sent can be received by the
           intended recipient.*)
    Reception "[| evsr \\<in> otway;  Says A B X : set evsr |]
               ==> Gets B X # evsr : otway"

         (*Alice initiates a protocol run*)
    OR1  "[| evs1 \\<in> otway;  Nonce NA \\<notin> used evs1 |]
          ==> Says A B {|Nonce NA, Agent A, Agent B, 
                         Crypt (shrK A) {|Nonce NA, Agent A, Agent B|} |} 
                 # evs1 : otway"

         (*Bob's response to Alice's message.  Note that NB is encrypted.*)
    OR2  "[| evs2 \\<in> otway;  Nonce NB \\<notin> used evs2;
             Gets B {|Nonce NA, Agent A, Agent B, X|} : set evs2 |]
          ==> Says B Server 
                  {|Nonce NA, Agent A, Agent B, X, 
                    Crypt (shrK B)
                      {|Nonce NA, Nonce NB, Agent A, Agent B|}|}
                 # evs2 : otway"

         (*The Server receives Bob's message and checks that the three NAs
           match.  Then he sends a new session key to Bob with a packet for
           forwarding to Alice.*)
    OR3  "[| evs3 \\<in> otway;  Key KAB \\<notin> used evs3;
             Gets Server 
                  {|Nonce NA, Agent A, Agent B, 
                    Crypt (shrK A) {|Nonce NA, Agent A, Agent B|}, 
                    Crypt (shrK B) {|Nonce NA, Nonce NB, Agent A, Agent B|}|}
               : set evs3 |]
          ==> Says Server B 
                  {|Nonce NA, 
                    Crypt (shrK A) {|Nonce NA, Key KAB|},
                    Crypt (shrK B) {|Nonce NB, Key KAB|}|}
                 # evs3 : otway"

         (*Bob receives the Server's (?) message and compares the Nonces with
	   those in the message he previously sent the Server.
           Need B \\<noteq> Server because we allow messages to self.*)
    OR4  "[| evs4 \\<in> otway;  B \\<noteq> Server;
             Says B Server {|Nonce NA, Agent A, Agent B, X', 
                             Crypt (shrK B)
                                   {|Nonce NA, Nonce NB, Agent A, Agent B|}|}
               : set evs4;
             Gets B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               : set evs4 |]
          ==> Says B A {|Nonce NA, X|} # evs4 : otway"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.*)
    Oops "[| evso \\<in> otway;  
             Says Server B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               : set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso : otway"

end
