(*  Title:      HOL/UNITY/Alloc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Specification of Chandy and Charpentier's Allocator
*)

Alloc = AllocBase + PPROD +

(** State definitions.  OUTPUT variables are locals **)

record clientState =
  giv :: nat list   (*client's INPUT history:  tokens GRANTED*)
  ask :: nat list   (*client's OUTPUT history: tokens REQUESTED*)
  rel :: nat list   (*client's OUTPUT history: tokens RELEASED*)

record 'a clientState_d =
  clientState +
  dummy :: 'a       (*dummy field for new variables*)

constdefs
  (*DUPLICATED FROM Client.thy, but with "tok" removed*)
  (*Maybe want a special theory section to declare such maps*)
  non_dummy :: 'a clientState_d => clientState
    "non_dummy s == (|giv = giv s, ask = ask s, rel = rel s|)"

  (*Renaming map to put a Client into the standard form*)
  client_map :: "'a clientState_d => clientState*'a"
    "client_map == funPair non_dummy dummy"

  
record allocState =
  allocGiv :: nat => nat list   (*OUTPUT history: source of "giv" for i*)
  allocAsk :: nat => nat list   (*INPUT: allocator's copy of "ask" for i*)
  allocRel :: nat => nat list   (*INPUT: allocator's copy of "rel" for i*)

record 'a allocState_d =
  allocState +
  dummy    :: 'a                (*dummy field for new variables*)

record 'a systemState =
  allocState +
  client :: nat => clientState  (*states of all clients*)
  dummy  :: 'a                  (*dummy field for new variables*)


constdefs

(** Resource allocation system specification **)

  (*spec (1)*)
  system_safety :: 'a systemState program set
    "system_safety ==
     Always {s. (\\<Sum>i: lessThan Nclients. (tokens o giv o sub i o client)s)
     <= NbT + (\\<Sum>i: lessThan Nclients. (tokens o rel o sub i o client)s)}"

  (*spec (2)*)
  system_progress :: 'a systemState program set
    "system_progress == INT i : lessThan Nclients.
			INT h. 
			  {s. h <= (ask o sub i o client)s} LeadsTo
			  {s. h pfixLe (giv o sub i o client) s}"

  system_spec :: 'a systemState program set
    "system_spec == system_safety Int system_progress"

(** Client specification (required) ***)

  (*spec (3)*)
  client_increasing :: 'a clientState_d program set
    "client_increasing ==
         UNIV guarantees  Increasing ask Int Increasing rel"

  (*spec (4)*)
  client_bounded :: 'a clientState_d program set
    "client_bounded ==
         UNIV guarantees  Always {s. ALL elt : set (ask s). elt <= NbT}"

  (*spec (5)*)
  client_progress :: 'a clientState_d program set
    "client_progress ==
	 Increasing giv  guarantees
	 (INT h. {s. h <= giv s & h pfixGe ask s}
		 LeadsTo {s. tokens h <= (tokens o rel) s})"

  (*spec: preserves part*)
  client_preserves :: 'a clientState_d program set
    "client_preserves == preserves giv Int preserves clientState_d.dummy"

  (*environmental constraints*)
  client_allowed_acts :: 'a clientState_d program set
    "client_allowed_acts ==
       {F. AllowedActs F =
	    insert Id (UNION (preserves (funPair rel ask)) Acts)}"

  client_spec :: 'a clientState_d program set
    "client_spec == client_increasing Int client_bounded Int client_progress
                    Int client_allowed_acts Int client_preserves"

(** Allocator specification (required) ***)

  (*spec (6)*)
  alloc_increasing :: 'a allocState_d program set
    "alloc_increasing ==
	 UNIV  guarantees
	 (INT i : lessThan Nclients. Increasing (sub i o allocGiv))"

  (*spec (7)*)
  alloc_safety :: 'a allocState_d program set
    "alloc_safety ==
	 (INT i : lessThan Nclients. Increasing (sub i o allocRel))
         guarantees
	 Always {s. (\\<Sum>i: lessThan Nclients. (tokens o sub i o allocGiv)s)
         <= NbT + (\\<Sum>i: lessThan Nclients. (tokens o sub i o allocRel)s)}"

  (*spec (8)*)
  alloc_progress :: 'a allocState_d program set
    "alloc_progress ==
	 (INT i : lessThan Nclients. Increasing (sub i o allocAsk) Int
	                             Increasing (sub i o allocRel))
         Int
         Always {s. ALL i<Nclients.
		     ALL elt : set ((sub i o allocAsk) s). elt <= NbT}
         Int
         (INT i : lessThan Nclients. 
	  INT h. {s. h <= (sub i o allocGiv)s & h pfixGe (sub i o allocAsk)s}
		 LeadsTo
	         {s. tokens h <= (tokens o sub i o allocRel)s})
         guarantees
	     (INT i : lessThan Nclients.
	      INT h. {s. h <= (sub i o allocAsk) s}
	             LeadsTo
	             {s. h pfixLe (sub i o allocGiv) s})"

  (*NOTE: to follow the original paper, the formula above should have had
	INT h. {s. h i <= (sub i o allocGiv)s & h i pfixGe (sub i o allocAsk)s}
	       LeadsTo
	       {s. tokens h i <= (tokens o sub i o allocRel)s})
    thus h should have been a function variable.  However, only h i is ever
    looked at.*)

  (*spec: preserves part*)
  alloc_preserves :: 'a allocState_d program set
    "alloc_preserves == preserves allocRel Int preserves allocAsk Int
                        preserves allocState_d.dummy"
  
  (*environmental constraints*)
  alloc_allowed_acts :: 'a allocState_d program set
    "alloc_allowed_acts ==
       {F. AllowedActs F =
	    insert Id (UNION (preserves allocGiv) Acts)}"

  alloc_spec :: 'a allocState_d program set
    "alloc_spec == alloc_increasing Int alloc_safety Int alloc_progress Int
                   alloc_allowed_acts Int alloc_preserves"

(** Network specification ***)

  (*spec (9.1)*)
  network_ask :: 'a systemState program set
    "network_ask == INT i : lessThan Nclients.
			Increasing (ask o sub i o client)  guarantees
			((sub i o allocAsk) Fols (ask o sub i o client))"

  (*spec (9.2)*)
  network_giv :: 'a systemState program set
    "network_giv == INT i : lessThan Nclients.
			Increasing (sub i o allocGiv)
			guarantees
			((giv o sub i o client) Fols (sub i o allocGiv))"

  (*spec (9.3)*)
  network_rel :: 'a systemState program set
    "network_rel == INT i : lessThan Nclients.
			Increasing (rel o sub i o client)
			guarantees
			((sub i o allocRel) Fols (rel o sub i o client))"

  (*spec: preserves part*)
  network_preserves :: 'a systemState program set
    "network_preserves ==
       preserves allocGiv  Int
       (INT i : lessThan Nclients. preserves (rel o sub i o client)  Int
                                   preserves (ask o sub i o client))"
  
  (*environmental constraints*)
  network_allowed_acts :: 'a systemState program set
    "network_allowed_acts ==
       {F. AllowedActs F =
           insert Id
	    (UNION (preserves allocRel Int
		    (INT i: lessThan Nclients. preserves(giv o sub i o client)))
		  Acts)}"

  network_spec :: 'a systemState program set
    "network_spec == network_ask Int network_giv Int
                     network_rel Int network_allowed_acts Int
                     network_preserves"


(** State mappings **)
  sysOfAlloc :: "((nat => clientState) * 'a) allocState_d => 'a systemState"
    "sysOfAlloc == %s. let (cl,xtr) = allocState_d.dummy s
                       in (| allocGiv = allocGiv s,
			     allocAsk = allocAsk s,
			     allocRel = allocRel s,
			     client   = cl,
			     dummy    = xtr|)"


  sysOfClient :: "(nat => clientState) * 'a allocState_d => 'a systemState"
    "sysOfClient == %(cl,al). (| allocGiv = allocGiv al,
			         allocAsk = allocAsk al,
			         allocRel = allocRel al,
			         client   = cl,
			         systemState.dummy = allocState_d.dummy al|)"

consts 
    Alloc   :: 'a allocState_d program
    Client  :: 'a clientState_d program
    Network :: 'a systemState program
    System  :: 'a systemState program
  
rules
    Alloc   "Alloc   : alloc_spec"
    Client  "Client  : client_spec"
    Network "Network : network_spec"

defs
    System_def
      "System == rename sysOfAlloc Alloc Join Network Join
                 (rename sysOfClient
		  (plam x: lessThan Nclients. rename client_map Client))"


(**
locale System =
  fixes 
    Alloc   :: 'a allocState_d program
    Client  :: 'a clientState_d program
    Network :: 'a systemState program
    System  :: 'a systemState program

  assumes
    Alloc   "Alloc   : alloc_spec"
    Client  "Client  : client_spec"
    Network "Network : network_spec"

  defines
    System_def
      "System == rename sysOfAlloc Alloc
                 Join
                 Network
                 Join
                 (rename sysOfClient
		  (plam x: lessThan Nclients. rename client_map Client))"
**)


end
