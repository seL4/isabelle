(*  Title:      HOL/Auth/Recur
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "recur" for the Recursive Authentication protocol.
*)

Recur = HPair + Shared +

syntax
  newK2    :: "nat*nat => key"

translations
  "newK2 x"  == "newK(nPair x)"

(*Two session keys are distributed to each agent except for the initiator,
	who receives one.
  Perhaps the two session keys could be bundled into a single message.
*)
consts     respond :: "nat => (nat*msg*msg)set"
inductive "respond i"	(*Server's response to the nested message*)
  intrs
    (*The message "Agent Server" marks the end of a list.*)

    One  "A ~= Server
          ==> (j, HPair (Key(shrK A)) 
                        {|Agent A, Agent B, Nonce NA, Agent Server|}, 
                  {|Agent A, 
                    Crypt (shrK A) {|Key(newK2(i,j)), Agent B, Nonce NA|}, 
                    Agent Server|})
              : respond i"

    (*newK2(i,Suc j) is the key for A & B; newK2(i,j) is the key for B & C*)
    Cons "[| (Suc j, PA, RA) : respond i;
             PA = HPair (Key(shrK A)) {|Agent A, Agent B, Nonce NA, P|};
             B ~= Server |]
          ==> (j, HPair (Key(shrK B)) {|Agent B, Agent C, Nonce NB, PA|}, 
                  {|Agent B, 
                    Crypt (shrK B) {|Key(newK2(i,Suc j)), Agent A, Nonce NB|},
                    Agent B, 
                    Crypt (shrK B) {|Key(newK2(i,j)), Agent C, Nonce NB|}, 
                    RA|})
              : respond i"


(*Induction over "respond" can be difficult due to the complexity of the
  subgoals.  The "responses" relation formalizes the general form of its
  third component.
*)
consts     responses :: nat => msg set
inductive "responses i" 	
  intrs
    (*Server terminates lists*)
    Nil  "Agent Server : responses i"

    Cons "RA : responses i
          ==> {|Agent B, 
                Crypt (shrK B) {|Key(newK2(i,k)), Agent A, Nonce NB|},
                RA|}  : responses i"


consts     recur   :: agent set => event list set
inductive "recur lost"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: recur lost"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: recur lost;  B ~= Spy;  
             X: synth (analz (sees lost Spy evs)) |]
          ==> Says Spy B X  # evs : recur lost"

         (*Alice initiates a protocol run.
           "Agent Server" is just a placeholder, to terminate the nesting.*)
    RA1  "[| evs: recur lost;  A ~= B;  A ~= Server |]
          ==> Says A B 
                (HPair (Key(shrK A)) 
                 {|Agent A, Agent B, Nonce(newN(length evs)), Agent Server|})
              # evs : recur lost"

         (*Bob's response to Alice's message.  C might be the Server.
           XA should be the Hash of the remaining components with KA, but
		Bob cannot check that.
           P is the previous recur message from Alice's caller.*)
    RA2  "[| evs: recur lost;  B ~= C;  B ~= Server;
             Says A' B PA : set_of_list evs;  
             PA = {|XA, Agent A, Agent B, Nonce NA, P|} |]
          ==> Says B C 
                (HPair (Key(shrK B))
                 {|Agent B, Agent C, Nonce (newN(length evs)), PA|})
              # evs : recur lost"

         (*The Server receives and decodes Bob's message.  Then he generates
           a new session key and a response.*)
    RA3  "[| evs: recur lost;  B ~= Server;
             Says B' Server PB : set_of_list evs;
             (0,PB,RB) : respond (length evs) |]
          ==> Says Server B RB # evs : recur lost"

         (*Bob receives the returned message and compares the Nonces with
	   those in the message he previously sent the Server.*)
    RA4  "[| evs: recur lost;  A ~= B;  
             Says C' B {|Agent B, 
                         Crypt (shrK B) {|Key KAB, Agent A, Nonce NB|}, 
                         Agent B, 
                         Crypt (shrK B) {|Key KAC, Agent C, Nonce NB|}, RA|}
               : set_of_list evs;
             Says B  C {|XH, Agent B, Agent C, Nonce NB, 
                         XA, Agent A, Agent B, Nonce NA, P|} 
               : set_of_list evs |]
          ==> Says B A RA # evs : recur lost"

(**No "oops" message can readily be expressed, since each session key is
   associated--in two separate messages--with two nonces.
***)
end
