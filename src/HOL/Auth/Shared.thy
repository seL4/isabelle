(*  Title:      HOL/Auth/Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 
*)

Shared = Message + List + Finite +

consts
  shrK    :: agent => key  (*symmetric keys*)

rules
  isSym_keys "isSymKey K"	(*All keys are symmetric*)
  inj_shrK   "inj shrK"		(*No two agents have the same long-term key*)

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: [agent set, agent] => msg set

primrec initState agent
        (*Server knows all long-term keys; other agents know only their own*)
  initState_Server  "initState lost Server     = Key `` range shrK"
  initState_Friend  "initState lost (Friend i) = {Key (shrK (Friend i))}"
  initState_Spy     "initState lost Spy        = Key``shrK``lost"


datatype  (*Messages, and components of agent stores*)
  event = Says agent agent msg

consts  
  sees1 :: [agent, event] => msg set

primrec sees1 event
           (*Spy reads all traffic whether addressed to him or not*)
  sees1_Says  "sees1 A (Says A' B X)  = (if A:{B,Spy} then {X} else {})"

consts  
  sees :: [agent set, agent, event list] => msg set

primrec sees list
  sees_Nil  "sees lost A []       = initState lost A"
  sees_Cons "sees lost A (ev#evs) = sees1 A ev Un sees lost A evs"


constdefs
  (*Set of items that might be visible to somebody: complement of the set
        of fresh items*)
  used :: event list => msg set
    "used evs == parts (UN lost B. sees lost B evs)"


rules
  (*Unlike the corresponding property of nonces, this cannot be proved.
    We have infinitely many agents and there is nothing to stop their
    long-term keys from exhausting all the natural numbers.  The axiom
    assumes that their keys are dispersed so as to leave room for infinitely
    many fresh session keys.  We could, alternatively, restrict agents to
    an unspecified finite number.*)
  Key_supply_ax  "finite KK ==> EX K. K ~: KK & Key K ~: used evs"

end
