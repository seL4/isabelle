(*  Title:      HOL/Auth/Yahalom2
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "yahalom" for the Yahalom protocol, Variant 2.

This version trades encryption of NB for additional explicitness in YM3.
Also in YM3, care is taken to make the two certificates distinct.

From page 259 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

Yahalom2 = Shared + 

consts  yahalom   :: event list set
inductive "yahalom"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: yahalom"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: yahalom;  X: synth (analz (knows Spy evs)) |]
          ==> Says Spy B X  # evs : yahalom"

         (*A message that has been sent can be received by the
           intended recipient.*)
    Reception "[| evsr: yahalom;  Says A B X : set evsr |]
               ==> Gets B X # evsr : yahalom"

         (*Alice initiates a protocol run*)
    YM1  "[| evs1: yahalom;  Nonce NA ~: used evs1 |]
          ==> Says A B {|Agent A, Nonce NA|} # evs1 : yahalom"

         (*Bob's response to Alice's message.*)
    YM2  "[| evs2: yahalom;  Nonce NB ~: used evs2;
             Gets B {|Agent A, Nonce NA|} : set evs2 |]
          ==> Says B Server 
                  {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|}
                # evs2 : yahalom"

         (*The Server receives Bob's message.  He responds by sending a
           new session key to Alice, with a certificate for forwarding to Bob.
           Both agents are quoted in the 2nd certificate to prevent attacks!*)
    YM3  "[| evs3: yahalom;  Key KAB ~: used evs3;
             Gets Server {|Agent B, Nonce NB,
			   Crypt (shrK B) {|Agent A, Nonce NA|}|}
               : set evs3 |]
          ==> Says Server A
               {|Nonce NB, 
                 Crypt (shrK A) {|Agent B, Key KAB, Nonce NA|},
                 Crypt (shrK B) {|Agent A, Agent B, Key KAB, Nonce NB|}|}
                 # evs3 : yahalom"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.*)
    YM4  "[| evs4: yahalom;  
             Gets A {|Nonce NB, Crypt (shrK A) {|Agent B, Key K, Nonce NA|},
                      X|}  : set evs4;
             Says A B {|Agent A, Nonce NA|} : set evs4 |]
          ==> Says A B {|X, Crypt K (Nonce NB)|} # evs4 : yahalom"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.  Quoting Server here ensures they are
           correct. *)
    Oops "[| evso: yahalom;  
             Says Server A {|Nonce NB, 
                             Crypt (shrK A) {|Agent B, Key K, Nonce NA|},
                             X|}  : set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso : yahalom"

end
