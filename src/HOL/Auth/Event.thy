(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatype of events;
inductive relation "traces" for Needham-Schroeder (shared keys)

WHAT ABOUT ASYMMETRIC KEYS?  NOBODY'S PRIVATE KEY CAN EQUAL SOMEBODY ELSE'S
  PUBLIC KEY...
*)

Event = Message + List + 

consts
  publicKey    :: agent => key
  serverKey    :: agent => key	(*symmetric keys*)

rules
  isSym_serverKey "isSymKey (serverKey A)"

consts	(*Initial states of agents -- parameter of the construction*)
  initState :: agent => msg set

primrec initState agent
	(*Server knows all keys; other agents know only their own*)
  initState_Server  "initState Server     = range (Key o serverKey)"
  initState_Friend  "initState (Friend i) = {Key (serverKey (Friend i))}"
  initState_Enemy   "initState Enemy  = {Key (serverKey Enemy)}"

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
  sees1_Says  "sees1 A (Says A' B X)  = (if A:{A',Enemy} then {X} else {})"
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
  "knownBy evs X == {A. X: analyze (sees A evs)}"


(*Agents generate "random" nonces.  Different agents always generate
  different nonces.  Different traces also yield different nonces.  Same
  applies for keys.*)
(*newK NEEDS AN ARGUMENT TO ALLOW ASYMMETRIC KEYS.  REMOVE AGENT ARGUMENT?
  NEED AXIOM SAYING THAT NEW KEYS CANNOT EQUAL THE INVERSE OF A PREVIOUS KEY*)
consts
  newN :: "agent * event list => nat"
  newK :: "agent * event list => key"

rules
  inj_serverKey "inj serverKey"

  inj_newN   "inj(newN)"
  fresh_newN "Nonce (newN(A,evs)) ~: parts (initState B)" 

  inj_newK   "inj(newK)"
  fresh_newK "Key (newK(A,evs)) ~: parts (initState B)" 
  isSym_newK "isSymKey (newK(A,evs))"


consts  traces   :: "event list set"
inductive traces
  intrs 
    Nil  "[]: traces"

    (*The enemy MAY say anything he CAN say.  We do not expect him to
      invent new nonces here, but he can also use NS1.*)
    Fake "[| evs: traces;  X: synthesize(analyze(sees Enemy evs))
          |] ==> (Says Enemy B X) # evs : traces"

    NS1  "[| evs: traces;  A ~= Server
          |] ==> (Says A Server {|Agent A, Agent B, Nonce (newN(A,evs))|}) 
                 # evs : traces"

    NS2  "[| evs: traces;  
             evs = (Says A Server {|Agent A, Agent B, Nonce NA|}) # evs'
          |] ==> (Says Server A 
                       (Crypt {|Agent A, Agent B, 
                                Key (newK(Server,evs)), Nonce NA|}
                              (serverKey A))) # evs : traces"
end
