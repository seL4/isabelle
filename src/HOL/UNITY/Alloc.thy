(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator

CONSIDER CHANGING "sum" to work on type "int", not "nat"
  --then can use subtraction in spec (1),
  --but need invariants that values are non-negative
*)

Alloc = Follows + Extend + PPROD +

(*Duplicated from HOL/ex/NatSum.thy.
  Maybe type should be  [nat=>int, nat] => int**)
consts sum     :: [nat=>nat, nat] => nat
primrec 
  "sum f 0 = 0"
  "sum f (Suc n) = f(n) + sum f n"


(*This function merely sums the elements of a list*)
consts tokens     :: nat list => nat
primrec 
  "tokens [] = 0"
  "tokens (x#xs) = x + tokens xs"


consts
  NbT      :: nat       (*Number of tokens in system*)
  Nclients :: nat       (*Number of clients*)


record clientState =
  giv :: nat list   (*client's INPUT history:  tokens GRANTED*)
  ask :: nat list   (*client's OUTPUT history: tokens REQUESTED*)
  rel :: nat list   (*client's OUTPUT history: tokens RELEASED*)

record allocState =
  allocGiv :: nat => nat list   (*allocator's local copy of "giv" for i*)
  allocAsk :: nat => nat list   (*allocator's local copy of "ask" for i*)
  allocRel :: nat => nat list   (*allocator's local copy of "rel" for i*)

record systemState = allocState +
  client :: nat => clientState  (*states of all clients*)


constdefs

(** Resource allocation system specification **)

  (*spec (1)*)
  system_safety :: systemState program set
    "system_safety ==
     Always {s. sum (%i. (tokens o giv o sub i o client) s) Nclients
	        <= NbT + sum (%i. (tokens o rel o sub i o client) s) Nclients}"

  (*spec (2)*)
  system_progress :: systemState program set
    "system_progress == INT i : lessThan Nclients.
			INT h. 
			  {s. h <= (ask o sub i o client)s} LeadsTo
			  {s. h pfixLe (giv o sub i o client) s}"

  system_spec :: systemState program set
    "system_spec == system_safety Int system_progress"

(** Client specification (required) ***)

  (*spec (3) PROBABLY REQUIRES A LOCALTO PRECONDITION*)
  client_increasing :: clientState program set
    "client_increasing ==
         UNIV guarantees Increasing ask Int Increasing rel"

  (*spec (4)*)
  client_bounded :: clientState program set
    "client_bounded ==
         UNIV guarantees Always {s. ALL elt : set (ask s). elt <= NbT}"

  (*spec (5)*)
  client_progress :: clientState program set
    "client_progress ==
	 Increasing giv
	 guarantees
	 (INT h. {s. h <= giv s & h pfixGe ask s}
		 LeadsTo
		 {s. tokens h <= (tokens o rel) s})"

  client_spec :: clientState program set
    "client_spec == client_increasing Int client_bounded Int client_progress"

(** Allocator specification (required) ***)

  (*spec (6)  PROBABLY REQUIRES A LOCALTO PRECONDITION*)
  alloc_increasing :: allocState program set
    "alloc_increasing ==
	 UNIV
         guarantees
	 (INT i : lessThan Nclients. Increasing (sub i o allocAsk))"

  (*spec (7)*)
  alloc_safety :: allocState program set
    "alloc_safety ==
	 (INT i : lessThan Nclients. Increasing (sub i o allocRel))
         guarantees
	 Always {s. sum (%i. (tokens o sub i o allocGiv) s) Nclients
	         <= NbT + sum (%i. (tokens o sub i o allocRel) s) Nclients}"

  (*spec (8)*)
  alloc_progress :: allocState program set
    "alloc_progress ==
	 (INT i : lessThan Nclients. Increasing (sub i o allocAsk) Int
	                             Increasing (sub i o allocRel))
         Int
         Always {s. ALL i : lessThan Nclients.
		    ALL k : lessThan (length (allocAsk s i)).
		    allocAsk s i ! k <= NbT}
         Int
         (INT i : lessThan Nclients. 
	  INT h. {s. h <= (sub i o allocGiv)s & h pfixGe (sub i o allocAsk)s}
		  LeadsTo {s. tokens h <= (tokens o sub i o allocRel)s})
         guarantees
	     (INT i : lessThan Nclients.
	      INT h. {s. h <= (sub i o allocAsk) s} LeadsTo
	             {s. h pfixLe (sub i o allocGiv) s})"

  alloc_spec :: allocState program set
    "alloc_spec == alloc_increasing Int alloc_safety Int alloc_progress"

(** Network specification ***)

  (*spec (9.1)*)
  network_ask :: systemState program set
    "network_ask == INT i : lessThan Nclients.
                    Increasing (ask o sub i o client)
                    guarantees
                    ((sub i o allocAsk) Fols (ask o sub i o client))"

  (*spec (9.2)*)
  network_giv :: systemState program set
    "network_giv == INT i : lessThan Nclients.
                    Increasing (sub i o allocGiv)
                    guarantees
                    ((giv o sub i o client) Fols (sub i o allocGiv))"

  (*spec (9.3)*)
  network_rel :: systemState program set
    "network_rel == INT i : lessThan Nclients.
                    Increasing (rel o sub i o client)
                    guarantees
                    ((sub i o allocRel) Fols (rel o sub i o client))"

  network_spec :: systemState program set
    "network_spec == network_ask Int network_giv Int network_rel"


(** State mappings **)
  sysOfAlloc :: "(allocState * (nat => clientState)) => systemState"
    "sysOfAlloc == %(s,y). (| allocGiv = allocGiv s,
			      allocAsk = allocAsk s,
			      allocRel = allocRel s,
			      client   = y |)"
(***    "sysOfAlloc == %(s,y). s(|client := y|)"  TYPE DOESN'T CHANGE***)


  sysOfClient :: "((nat => clientState) * allocState ) => systemState"
    "sysOfClient == %(x,y). sysOfAlloc(y,x)"


locale System =
  fixes 
    Alloc   :: allocState program
    Client  :: clientState program
    Network :: systemState program
    System  :: systemState program
  
  assumes
    Alloc   "Alloc   : alloc_spec"
    Client  "Client  : client_spec"
    Network "Network : network_spec"

  defines
    System_def
      "System == (extend sysOfAlloc Alloc)
                 Join
                 (extend sysOfClient (plam x: lessThan Nclients. Client))
                 Join
                 Network"
end
