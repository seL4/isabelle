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

record 'a clientState_u =
  clientState +
  extra :: 'a       (*dummy field for new variables*)

constdefs
  (*DUPLICATED FROM Client.thy, but with "tok" removed*)
  (*Maybe want a special theory section to declare such maps*)
  non_extra :: 'a clientState_u => clientState
    "non_extra s == (|giv = giv s, ask = ask s, rel = rel s|)"

  (*Renaming map to put a Client into the standard form*)
  client_map :: "'a clientState_u => clientState*'a"
    "client_map == funPair non_extra extra"

  
record allocState =
  allocGiv :: nat => nat list   (*OUTPUT history: source of "giv" for i*)
  allocAsk :: nat => nat list   (*INPUT: allocator's copy of "ask" for i*)
  allocRel :: nat => nat list   (*INPUT: allocator's copy of "rel" for i*)

record 'a allocState_u =
  allocState +
  extra    :: 'a                (*dummy field for new variables*)

record 'a systemState =
  allocState +
  client :: nat => clientState  (*states of all clients*)
  extra  :: 'a                  (*dummy field for new variables*)


constdefs

(** Resource allocation system specification **)

  (*spec (1)*)
  system_safety :: 'a systemState program set
    "system_safety ==
     Always {s. sum_below (%i. (tokens o giv o sub i o client) s) Nclients
        <= NbT + sum_below (%i. (tokens o rel o sub i o client) s) Nclients}"

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
  client_increasing :: 'a clientState_u program set
    "client_increasing ==
         UNIV guarantees[funPair rel ask]
         Increasing ask Int Increasing rel"

  (*spec (4)*)
  client_bounded :: 'a clientState_u program set
    "client_bounded ==
         UNIV guarantees[ask]
         Always {s. ALL elt : set (ask s). elt <= NbT}"

  (*spec (5)*)
  client_progress :: 'a clientState_u program set
    "client_progress ==
	 Increasing giv
	 guarantees[funPair rel ask]
	 (INT h. {s. h <= giv s & h pfixGe ask s}
		 LeadsTo {s. tokens h <= (tokens o rel) s})"

  (*spec: preserves part*)
    client_preserves :: 'a clientState_u program set
    "client_preserves == preserves (funPair giv clientState_u.extra)"

  client_spec :: 'a clientState_u program set
    "client_spec == client_increasing Int client_bounded Int client_progress
                    Int client_preserves"

(** Allocator specification (required) ***)

  (*spec (6)*)
  alloc_increasing :: 'a allocState_u program set
    "alloc_increasing ==
	 UNIV
         guarantees[allocGiv]
	 (INT i : lessThan Nclients. Increasing (sub i o allocGiv))"

  (*spec (7)*)
  alloc_safety :: 'a allocState_u program set
    "alloc_safety ==
	 (INT i : lessThan Nclients. Increasing (sub i o allocRel))
         guarantees[allocGiv]
	 Always {s. sum_below (%i. (tokens o sub i o allocGiv) s) Nclients
	      <= NbT + sum_below (%i. (tokens o sub i o allocRel) s) Nclients}"

  (*spec (8)*)
  alloc_progress :: 'a allocState_u program set
    "alloc_progress ==
	 (INT i : lessThan Nclients. Increasing (sub i o allocAsk) Int
	                             Increasing (sub i o allocRel))
         Int
         Always {s. ALL i. i<Nclients -->
		     (ALL elt : set ((sub i o allocAsk) s). elt <= NbT)}
         Int
         (INT i : lessThan Nclients. 
	  INT h. {s. h <= (sub i o allocGiv)s & h pfixGe (sub i o allocAsk)s}
		 LeadsTo
	         {s. tokens h <= (tokens o sub i o allocRel)s})
         guarantees[allocGiv]
	     (INT i : lessThan Nclients.
	      INT h. {s. h <= (sub i o allocAsk) s}
	             LeadsTo
	             {s. h pfixLe (sub i o allocGiv) s})"

  (*spec: preserves part*)
    alloc_preserves :: 'a allocState_u program set
    "alloc_preserves == preserves (funPair allocRel
				   (funPair allocAsk allocState_u.extra))"
  
  alloc_spec :: 'a allocState_u program set
    "alloc_spec == alloc_increasing Int alloc_safety Int alloc_progress Int
                   alloc_preserves"

(** Network specification ***)

  (*spec (9.1)*)
  network_ask :: 'a systemState program set
    "network_ask == INT i : lessThan Nclients.
			Increasing (ask o sub i o client)
			guarantees[allocAsk]
			((sub i o allocAsk) Fols (ask o sub i o client))"

  (*spec (9.2)*)
  network_giv :: 'a systemState program set
    "network_giv == INT i : lessThan Nclients.
			Increasing (sub i o allocGiv)
			guarantees[giv o sub i o client]
			((giv o sub i o client) Fols (sub i o allocGiv))"

  (*spec (9.3)*)
  network_rel :: 'a systemState program set
    "network_rel == INT i : lessThan Nclients.
			Increasing (rel o sub i o client)
			guarantees[allocRel]
			((sub i o allocRel) Fols (rel o sub i o client))"

  (*spec: preserves part*)
    network_preserves :: 'a systemState program set
    "network_preserves == preserves allocGiv  Int
                          (INT i : lessThan Nclients.
                           preserves (funPair rel ask o sub i o client))"
  
  network_spec :: 'a systemState program set
    "network_spec == network_ask Int network_giv Int
                     network_rel Int network_preserves"


(** State mappings **)
  sysOfAlloc :: "((nat => clientState) * 'a) allocState_u => 'a systemState"
    "sysOfAlloc == %s. let (cl,xtr) = allocState_u.extra s
                       in (| allocGiv = allocGiv s,
			     allocAsk = allocAsk s,
			     allocRel = allocRel s,
			     client   = cl,
			     extra    = xtr|)"


  sysOfClient :: "(nat => clientState) * 'a allocState_u => 'a systemState"
    "sysOfClient == %(cl,al). (| allocGiv = allocGiv al,
			         allocAsk = allocAsk al,
			         allocRel = allocRel al,
			         client   = cl,
			         systemState.extra = allocState_u.extra al|)"

consts 
    Alloc   :: 'a allocState_u program
    Client  :: 'a clientState_u program
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
    Alloc   :: 'a allocState_u program
    Client  :: 'a clientState_u program
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
