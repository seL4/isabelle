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

consts  lost    :: agent set        (*No need for it to be a variable*)
	otway   :: event list set

inductive otway
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: otway"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: otway;  B ~= Spy;  X: synth (analz (sees lost Spy evs)) |]
          ==> Says Spy B X  # evs : otway"

         (*Alice initiates a protocol run*)
    OR1  "[| evs: otway;  A ~= B;  B ~= Server |]
          ==> Says A B {|Nonce (newN evs), Agent A, Agent B, 
                         Crypt {|Nonce (newN evs), Agent A, Agent B|} 
                               (shrK A) |} 
                 # evs : otway"

         (*Bob's response to Alice's message.  Bob doesn't know who 
	   the sender is, hence the A' in the sender field.
           We modify the published protocol by NOT encrypting NB.*)
    OR2  "[| evs: otway;  B ~= Server;
             Says A' B {|Nonce NA, Agent A, Agent B, X|} : set_of_list evs |]
          ==> Says B Server 
                  {|Nonce NA, Agent A, Agent B, X, Nonce (newN evs), 
                    Crypt {|Nonce NA, Agent A, Agent B|} (shrK B)|}
                 # evs : otway"

         (*The Server receives Bob's message and checks that the three NAs
           match.  Then he sends a new session key to Bob with a packet for
           forwarding to Alice.*)
    OR3  "[| evs: otway;  B ~= Server;
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
                 # evs : otway"

         (*Bob receives the Server's (?) message and compares the Nonces with
	   those in the message he previously sent the Server.*)
    OR4  "[| evs: otway;  A ~= B;
             Says S B {|Nonce NA, X, Crypt {|Nonce NB, Key K|} (shrK B)|}
               : set_of_list evs;
             Says B Server {|Nonce NA, Agent A, Agent B, X', Nonce NB, X''|}
               : set_of_list evs |]
          ==> Says B A {|Nonce NA, X|} # evs : otway"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.*)
    Oops "[| evs: otway;  B ~= Spy;
             Says Server B {|Nonce NA, X, Crypt {|Nonce NB, Key K|} (shrK B)|}
               : set_of_list evs |]
          ==> Says B Spy {|Nonce NA, Nonce NB, Key K|} # evs : otway"

end
