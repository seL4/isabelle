(*  Title:      HOL/Auth/Yahalom
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "yahalom" for the Yahalom protocol.

From page 257 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

Yahalom = Shared + 

consts  yahalom   :: event list set
inductive "yahalom"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: yahalom"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: yahalom;  B ~= Spy;  
             X: synth (analz (spies evs)) |]
          ==> Says Spy B X  # evs : yahalom"

         (*Alice initiates a protocol run*)
    YM1  "[| evs1: yahalom;  A ~= B;  Nonce NA ~: used evs1 |]
          ==> Says A B {|Agent A, Nonce NA|} # evs1 : yahalom"

         (*Bob's response to Alice's message.  Bob doesn't know who 
	   the sender is, hence the A' in the sender field.*)
    YM2  "[| evs2: yahalom;  B ~= Server;  Nonce NB ~: used evs2;
             Says A' B {|Agent A, Nonce NA|} : set evs2 |]
          ==> Says B Server 
                  {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
                # evs2 : yahalom"

         (*The Server receives Bob's message.  He responds by sending a
            new session key to Alice, with a packet for forwarding to Bob.*)
    YM3  "[| evs3: yahalom;  A ~= Server;  Key KAB ~: used evs3;
             Says B' Server 
                  {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
               : set evs3 |]
          ==> Says Server A
                   {|Crypt (shrK A) {|Agent B, Key KAB, Nonce NA, Nonce NB|},
                     Crypt (shrK B) {|Agent A, Key KAB|}|}
                # evs3 : yahalom"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.*)
    YM4  "[| evs4: yahalom;  A ~= Server;  
             Says S A {|Crypt (shrK A) {|Agent B, Key K, Nonce NA, Nonce NB|},
                        X|}  : set evs4;
             Says A B {|Agent A, Nonce NA|} : set evs4 |]
          ==> Says A B {|X, Crypt K (Nonce NB)|} # evs4 : yahalom"

         (*This message models possible leaks of session keys.  The Nonces
           identify the protocol run.  Quoting Server here ensures they are
           correct.*)
    Oops "[| evso: yahalom;  A ~= Spy;
             Says Server A {|Crypt (shrK A)
                                   {|Agent B, Key K, Nonce NA, Nonce NB|},
                             X|}  : set evso |]
          ==> Says A Spy {|Nonce NA, Nonce NB, Key K|} # evso : yahalom"


constdefs 
  KeyWithNonce :: [key, nat, event list] => bool
  "KeyWithNonce K NB evs ==
     EX A B na X. 
       Says Server A {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB|}, X|} 
         : set evs"

end
