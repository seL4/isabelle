(*  Title:      HOL/Auth/Recur
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "recur" for the Recursive Authentication protocol.
*)

Recur = Shared +

(*Two session keys are distributed to each agent except for the initiator,
        who receives one.
  Perhaps the two session keys could be bundled into a single message.
*)
consts     respond :: "event list => (msg*msg*key)set"
inductive "respond evs" (*Server's response to the nested message*)
  intrs
    (*The message "Agent Server" marks the end of a list.*)
    One  "[| A ~= Server;  Key KAB ~: used evs |]
          ==> (Hash[Key(shrK A)] {|Agent A, Agent B, Nonce NA, Agent Server|}, 
               {|Crypt (shrK A) {|Key KAB, Agent B, Nonce NA|}, Agent Server|},
               KAB)   : respond evs"

    (*The most recent session key is passed up to the caller*)
    Cons "[| (PA, RA, KAB) : respond evs;  
             Key KBC ~: used evs;  Key KBC ~: parts {RA};
             PA = Hash[Key(shrK A)] {|Agent A, Agent B, Nonce NA, P|};
             B ~= Server |]
          ==> (Hash[Key(shrK B)] {|Agent B, Agent C, Nonce NB, PA|}, 
               {|Crypt (shrK B) {|Key KBC, Agent C, Nonce NB|}, 
                 Crypt (shrK B) {|Key KAB, Agent A, Nonce NB|},
                 RA|},
               KBC)
              : respond evs"


(*Induction over "respond" can be difficult due to the complexity of the
  subgoals.  Set "responses" captures the general form of certificates.
*)
consts     responses :: event list => msg set
inductive "responses evs"       
  intrs
    (*Server terminates lists*)
    Nil  "Agent Server : responses evs"

    Cons "[| RA : responses evs;  Key KAB ~: used evs |]
          ==> {|Crypt (shrK B) {|Key KAB, Agent A, Nonce NB|},
                RA|}  : responses evs"


consts     recur   :: event list set
inductive "recur"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: recur"

         (*The spy MAY say anything he CAN say.  Common to
           all similar protocols.*)
    Fake "[| evs: recur;  B ~= Spy;  
             X: synth (analz (spies evs)) |]
          ==> Says Spy B X  # evs : recur"

         (*Alice initiates a protocol run.
           "Agent Server" is just a placeholder, to terminate the nesting.*)
    RA1  "[| evs1: recur;  A ~= B;  A ~= Server;  Nonce NA ~: used evs1 |]
          ==> Says A B 
                (Hash[Key(shrK A)] 
                 {|Agent A, Agent B, Nonce NA, Agent Server|})
              # evs1 : recur"

         (*Bob's response to Alice's message.  C might be the Server.
           XA should be the Hash of the remaining components with KA, but
                Bob cannot check that.
           P is the previous recur message from Alice's caller.
           NOTE: existing proofs don't need PA and are complicated by its
                presence!  See parts_Fake_tac.*)
    RA2  "[| evs2: recur;  B ~= C;  B ~= Server;  Nonce NB ~: used evs2;
             Says A' B PA : set evs2;  
             PA = {|XA, Agent A, Agent B, Nonce NA, P|} |]
          ==> Says B C (Hash[Key(shrK B)] {|Agent B, Agent C, Nonce NB, PA|})
              # evs2 : recur"

         (*The Server receives Bob's message and prepares a response.*)
    RA3  "[| evs3: recur;  B ~= Server;
             Says B' Server PB : set evs3;
             (PB,RB,K) : respond evs3 |]
          ==> Says Server B RB # evs3 : recur"

         (*Bob receives the returned message and compares the Nonces with
           those in the message he previously sent the Server.*)
    RA4  "[| evs4: recur;  A ~= B;  
             Says B  C {|XH, Agent B, Agent C, Nonce NB, 
                         XA, Agent A, Agent B, Nonce NA, P|} : set evs4;
             Says C' B {|Crypt (shrK B) {|Key KBC, Agent C, Nonce NB|}, 
                         Crypt (shrK B) {|Key KAB, Agent A, Nonce NB|}, 
                         RA|} : set evs4 |]
          ==> Says B A RA # evs4 : recur"

(**No "oops" message can easily be expressed.  Each session key is
   associated--in two separate messages--with two nonces.
***)
end
