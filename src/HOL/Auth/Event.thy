(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatype of events;
inductive relation "traces" for Needham-Schroeder (shared keys)

INTERLEAVING?  See defn of "traces"

WHAT ABOUT ASYMMETRIC KEYS?  NOBODY'S PRIVATE KEY CAN EQUAL SOMEBODY ELSE'S
  PUBLIC KEY...
*)

Event = Message + List + 

consts
  publicKey    :: agent => key
  shrK    :: agent => key  (*symmetric keys*)

rules
  isSym_shrK "isSymKey (shrK A)"

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: agent => msg set

primrec initState agent
        (*Server knows all keys; other agents know only their own*)
  initState_Server  "initState Server     = Key `` range shrK"
  initState_Friend  "initState (Friend i) = {Key (shrK (Friend i))}"
  initState_Spy   "initState Spy  = {Key (shrK Spy)}"

(**
For asymmetric keys: server knows all public and private keys,
  others know their private key and perhaps all public keys  
**)

datatype  (*Messages, and components of agent stores*)
  event = Says agent agent msg
        | Notes agent msg

consts  
  sees1 :: [agent, event] => msg set

primrec sees1 event
           (*First agent recalls all that it says, but NOT everything
             that is sent to it; it must note such things if/when received*)
  sees1_Says  "sees1 A (Says A' B X)  = (if A:{A',Spy} then {X} else {})"
          (*part of A's internal state*)
  sees1_Notes "sees1 A (Notes A' X)   = (if A=A' then {X} else {})"

consts  
  sees :: [agent, event list] => msg set

primrec sees list
        (*Initial knowledge includes all public keys and own private key*)
  sees_Nil  "sees A []       = initState A"
  sees_Cons "sees A (ev#evs) = sees1 A ev Un sees A evs"


constdefs
  knownBy :: [event list, msg] => agent set
  "knownBy evs X == {A. X: analz (sees A evs)}"


(*Agents generate "random" nonces.  Different traces always yield
  different nonces.  Same applies for keys.*)
(*newK NEEDS AN ARGUMENT TO ALLOW ASYMMETRIC KEYS.
  NEED AXIOM SAYING THAT NEW KEYS CANNOT EQUAL THE INVERSE OF A PREVIOUS KEY*)
consts
  newN :: "event list => nat"
  newK :: "event list => key"

rules
  inj_shrK "inj shrK"

  inj_newN   "inj(newN)"
  fresh_newN "Nonce (newN evs) ~: parts (initState B)" 

  inj_newK   "inj(newK)"
  fresh_newK "Key (newK evs) ~: parts (initState B)" 
  isSym_newK "isSymKey (newK evs)"


(*Needham-Schroeder Shared-Key protocol (from BAN paper, page 247)*)
consts  traces   :: "event list set"
inductive traces
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: traces"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: traces;  B ~= Spy;  X: synth (analz (sees Spy evs))
          |] ==> (Says Spy B X) # evs : traces"

         (*Alice initiates a protocol run*)
    NS1  "[| evs: traces;  A ~= Server
          |] ==> (Says A Server {|Agent A, Agent B, Nonce (newN evs)|}) 
                 # evs : traces"

         (*Server's response to Alice's message.
           !! It may respond more than once to A's request !!
	   Server doesn't know who the true sender is, hence the A' in
               the sender field.*)
    NS2  "[| evs: traces;  A ~= B;  A ~= Server;
             (Says A' Server {|Agent A, Agent B, Nonce NA|}) : set_of_list evs
          |] ==> (Says Server A 
                  (Crypt {|Nonce NA, Agent B, Key (newK evs),   
                           (Crypt {|Key (newK evs), Agent A|} (shrK B))|}
                   (shrK A))) # evs : traces"

          (*We can't assume S=Server.  Agent A "remembers" her nonce.
            May assume WLOG that she is NOT the Spy: the Fake rule
            covers this case.  Can inductively show A ~= Server*)
    NS3  "[| evs: traces;  A ~= B;
             (Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A))) 
               : set_of_list evs;
             A = Friend i;
             (Says A Server {|Agent A, Agent B, Nonce NA|}) : set_of_list evs
          |] ==> (Says A B X) # evs : traces"

         (*Bob's nonce exchange.  He does not know who the message came
           from, but responds to A because she is mentioned inside.*)
    NS4  "[| evs: traces;  A ~= B;  
             (Says A' B (Crypt {|Key K, Agent A|} (shrK B))) 
               : set_of_list evs
          |] ==> (Says B A (Crypt (Nonce (newN evs)) K)) # evs : traces"

         (*Alice responds with (Suc N), if she has seen the key before.*)
    NS5  "[| evs: traces;  A ~= B;  
             (Says B' A (Crypt (Nonce N) K)) : set_of_list evs;
             (Says S  A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A))) 
               : set_of_list evs
          |] ==> (Says A B (Crypt (Nonce (Suc N)) K)) # evs : traces"

end
