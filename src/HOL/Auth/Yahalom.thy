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

consts  yahalom   :: agent set => event list set
inductive "yahalom lost"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: yahalom lost"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: yahalom lost;  B ~= Spy;  
             X: synth (analz (sees lost Spy evs)) |]
          ==> Says Spy B X  # evs : yahalom lost"

         (*Alice initiates a protocol run*)
    YM1  "[| evs: yahalom lost;  A ~= B |]
          ==> Says A B {|Agent A, Nonce (newN(length evs))|} # evs
                : yahalom lost"

         (*Bob's response to Alice's message.  Bob doesn't know who 
	   the sender is, hence the A' in the sender field.*)
    YM2  "[| evs: yahalom lost;  B ~= Server;
             Says A' B {|Agent A, Nonce NA|} : set_of_list evs |]
          ==> Says B Server 
                  {|Agent B, 
                    Crypt (shrK B)
                      {|Agent A, Nonce NA, Nonce (newN(length evs))|}|}
                 # evs : yahalom lost"

         (*The Server receives Bob's message.  He responds by sending a
            new session key to Alice, with a packet for forwarding to Bob.*)
    YM3  "[| evs: yahalom lost;  A ~= Server;
             Says B' Server 
                  {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
               : set_of_list evs |]
          ==> Says Server A
                  {|Crypt (shrK A) {|Agent B, Key (newK(length evs)), 
                            Nonce NA, Nonce NB|},
                    Crypt (shrK B) {|Agent A, Key (newK(length evs))|}|}
                 # evs : yahalom lost"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.*)
    YM4  "[| evs: yahalom lost;  A ~= Server;  A ~= B;  
             Says S A {|Crypt (shrK A) {|Agent B, Key K, Nonce NA, Nonce NB|},
                        X|}  : set_of_list evs;
             Says A B {|Agent A, Nonce NA|} : set_of_list evs |]
          ==> Says A B {|X, Crypt K (Nonce NB)|} # evs : yahalom lost"

         (*This message models possible leaks of session keys.  The Nonces
           identify the protocol run.  Quoting Server here ensures they are
           correct.*)
    Oops "[| evs: yahalom lost;  A ~= Spy;
             Says Server A {|Crypt (shrK A)
                                   {|Agent B, Key K, Nonce NA, Nonce NB|},
                             X|}  : set_of_list evs |]
          ==> Says A Spy {|Nonce NA, Nonce NB, Key K|} # evs : yahalom lost"

end
