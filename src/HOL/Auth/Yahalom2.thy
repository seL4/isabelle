(*  Title:      HOL/Auth/Yahalom
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "yahalom" for the Yahalom protocol, Variant 2.

This version trades encryption of NB for additional explicitness in YM3.

From page 259 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

Yahalom2 = Shared + 

consts  yahalom   :: "agent set => event list set"
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
          ==> Says A B {|Agent A, Nonce (newN evs)|} # evs : yahalom lost"

         (*Bob's response to Alice's message.  Bob doesn't know who 
	   the sender is, hence the A' in the sender field.*)
    YM2  "[| evs: yahalom lost;  B ~= Server;
             Says A' B {|Agent A, Nonce NA|} : set_of_list evs |]
          ==> Says B Server 
                  {|Agent B, Nonce (newN evs), 
                    Crypt {|Agent A, Nonce NA|} (shrK B)|}
                 # evs : yahalom lost"

         (*The Server receives Bob's message.  He responds by sending a
            new session key to Alice, with a packet for forwarding to Bob.*)
    YM3  "[| evs: yahalom lost;  A ~= Server;
             Says B' Server 
                  {|Agent B, Nonce NB, Crypt {|Agent A, Nonce NA|} (shrK B)|}
               : set_of_list evs |]
          ==> Says Server A
               {|Nonce NB, 
                 Crypt {|Agent B, Key (newK evs), Nonce NA|} (shrK A),
                 Crypt {|Agent A, Key (newK evs), Nonce NB, Nonce NB|} (shrK B)|}
                 # evs : yahalom lost"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.*)
    YM4  "[| evs: yahalom lost;  A ~= B;  
             Says S A {|Nonce NB, Crypt {|Agent B, Key K, Nonce NA|} (shrK A),
                        X|}
               : set_of_list evs;
             Says A B {|Agent A, Nonce NA|} : set_of_list evs |]
          ==> Says A B {|X, Crypt (Nonce NB) K|} # evs : yahalom lost"

         (*This message models possible leaks of session keys.  The Nonce NA
           identifies the protocol run.  We can't be sure about NB.*)
    Revl "[| evs: yahalom lost;  A ~= Spy;
             Says S A {|Nonce NB, Crypt {|Agent B, Key K, Nonce NA|} (shrK A),
                        X|}
               : set_of_list evs |]
          ==> Says A Spy {|Nonce NA, Key K|} # evs : yahalom lost"

end
