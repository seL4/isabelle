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
  serverKey    :: agent => key  (*symmetric keys*)

rules
  isSym_serverKey "isSymKey (serverKey A)"

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: agent => msg set

primrec initState agent
        (*Server knows all keys; other agents know only their own*)
  initState_Server  "initState Server     = Key `` range serverKey"
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
  "knownBy evs X == {A. X: analz (sees A evs)}"


(*Agents generate "random" nonces.  Different traces always yield
  different nonces.  Same applies for keys.*)
(*newK NEEDS AN ARGUMENT TO ALLOW ASYMMETRIC KEYS.
  NEED AXIOM SAYING THAT NEW KEYS CANNOT EQUAL THE INVERSE OF A PREVIOUS KEY*)
consts
  newN :: "event list => nat"
  newK :: "event list => key"

rules
  inj_serverKey "inj serverKey"

  inj_newN   "inj(newN)"
  fresh_newN "Nonce (newN evs) ~: parts (initState B)" 

  inj_newK   "inj(newK)"
  fresh_newK "Key (newK evs) ~: parts (initState B)" 
  isSym_newK "isSymKey (newK evs)"


(*NS3 DOESN'T ALLOW INTERLEAVING -- that is, it only responds to the
  MOST RECENT message.*)

consts  traces   :: "event list set"
inductive traces
  intrs 
    Nil  "[]: traces"

    (*The enemy MAY say anything he CAN say.  We do not expect him to
      invent new nonces here, but he can also use NS1.*)
    Fake "[| evs: traces;  B ~= Enemy;  
             X: synth(analz(sees Enemy evs))
          |] ==> (Says Enemy B X) # evs : traces"

    NS1  "[| evs: traces;  A ~= Server
          |] ==> (Says A Server {|Agent A, Agent B, Nonce (newN evs)|}) 
                 # evs : traces"

          (*We can't trust the sender field, hence the A' in it.
            This allows the Server to respond more than once to A's
            request...*)
    NS2  "[| evs: traces;  A ~= B;  A ~= Server;
             (Says A' Server {|Agent A, Agent B, Nonce NA|}) : set_of_list evs
          |] ==> (Says Server A 
                  (Crypt {|Nonce NA, Agent B, Key (newK evs),   
                           (Crypt {|Key (newK evs), Agent A|} (serverKey B))|}
                   (serverKey A))) # evs : traces"

           (*We can't assume S=Server.  Agent A "remembers" her nonce.
             May assume WLOG that she is NOT the Enemy: the Fake rule
             covers this case.  Can inductively show A ~= Server*)
    NS3  "[| evs: traces;  A ~= B;
             (Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey A))) 
               : set_of_list evs;
             A = Friend i;
             (Says A Server {|Agent A, Agent B, Nonce NA|}) : set_of_list evs
          |] ==> (Says A B X) # evs : traces"

(*Initial version of NS2 had 

        {|Agent A, Agent B, Key (newK evs), Nonce NA|}

  for the encrypted part; the version above is LESS explicit, hence
  HARDER to prove.  Also it is precisely as in the BAN paper.
*)

end
