(*  Title:      HOL/Auth/Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 

IS THE Notes constructor needed??
*)

Shared = Message + List + 

consts
  shrK    :: agent => key  (*symmetric keys*)

rules
  isSym_shrK "isSymKey (shrK A)"

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: agent => msg set

primrec initState agent
        (*Server knows all keys; other agents know only their own*)
  initState_Server  "initState Server     = Key `` range shrK"
  initState_Friend  "initState (Friend i) = {Key (shrK (Friend i))}"
  initState_Enemy   "initState Enemy  = {Key (shrK Enemy)}"

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


(*Agents generate "random" nonces.  Different traces always yield
  different nonces.  Same applies for keys.*)
consts
  newN :: "event list => nat"
  newK :: "event list => key"

rules
  inj_shrK "inj shrK"

  inj_newN   "inj newN"
  fresh_newN "Nonce (newN evs) ~: parts (initState B)" 

  inj_newK   "inj newK"
  fresh_newK "Key (newK evs) ~: parts (initState B)" 
  isSym_newK "isSymKey (newK evs)"

end
