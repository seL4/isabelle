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
    Nil  "[] \\<in> yahalom"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evsf \\<in> yahalom;  X \\<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \\<in> yahalom"

         (*A message that has been sent can be received by the
           intended recipient.*)
    Reception "[| evsr \\<in> yahalom;  Says A B X \\<in> set evsr |]
               ==> Gets B X # evsr \\<in> yahalom"

         (*Alice initiates a protocol run*)
    YM1  "[| evs1 \\<in> yahalom;  Nonce NA \\<notin> used evs1 |]
          ==> Says A B {|Agent A, Nonce NA|} # evs1 \\<in> yahalom"

         (*Bob's response to Alice's message.*)
    YM2  "[| evs2 \\<in> yahalom;  Nonce NB \\<notin> used evs2;
             Gets B {|Agent A, Nonce NA|} \\<in> set evs2 |]
          ==> Says B Server 
                  {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
                # evs2 \\<in> yahalom"

         (*The Server receives Bob's message.  He responds by sending a
            new session key to Alice, with a packet for forwarding to Bob.*)
    YM3  "[| evs3 \\<in> yahalom;  Key KAB \\<notin> used evs3;
             Gets Server 
                  {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
               \\<in> set evs3 |]
          ==> Says Server A
                   {|Crypt (shrK A) {|Agent B, Key KAB, Nonce NA, Nonce NB|},
                     Crypt (shrK B) {|Agent A, Key KAB|}|}
                # evs3 \\<in> yahalom"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.  The premise
           A \\<noteq> Server is needed to prove Says_Server_not_range.*)
    YM4  "[| evs4 \\<in> yahalom;  A \\<noteq> Server;
             Gets A {|Crypt(shrK A) {|Agent B, Key K, Nonce NA, Nonce NB|}, X|}
                \\<in> set evs4;
             Says A B {|Agent A, Nonce NA|} \\<in> set evs4 |]
          ==> Says A B {|X, Crypt K (Nonce NB)|} # evs4 \\<in> yahalom"

         (*This message models possible leaks of session keys.  The Nonces
           identify the protocol run.  Quoting Server here ensures they are
           correct.*)
    Oops "[| evso \\<in> yahalom;  
             Says Server A {|Crypt (shrK A)
                                   {|Agent B, Key K, Nonce NA, Nonce NB|},
                             X|}  \\<in> set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso \\<in> yahalom"


constdefs 
  KeyWithNonce :: [key, nat, event list] => bool
  "KeyWithNonce K NB evs ==
     \\<exists>A B na X. 
       Says Server A {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB|}, X|} 
         \\<in> set evs"

end
