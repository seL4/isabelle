(*  Title:      HOL/UNITY/AllocImpl
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Implementation of a multiple-client allocator from a single-client allocator
*)

AllocImpl = AllocBase + Follows + PPROD + 


(** State definitions.  OUTPUT variables are locals **)

(*Type variable 'b is the type of items being merged*)
record 'b merge =
  In   :: nat => 'b list   (*merge's INPUT histories: streams to merge*)
  Out  :: 'b list          (*merge's OUTPUT history: merged items*)
  iOut :: nat list         (*merge's OUTPUT history: origins of merged items*)

record ('a,'b) merge_d =
  'b merge +
  dummy :: 'a       (*dummy field for new variables*)

constdefs
  non_dummy :: ('a,'b) merge_d => 'b merge
    "non_dummy s == (|In = In s, Out = Out s, iOut = iOut s|)"

record 'b distr =
  In  :: 'b list          (*items to distribute*)
  iIn :: nat list         (*destinations of items to distribute*)
  Out :: nat => 'b list   (*distributed items*)

record ('a,'b) distr_d =
  'b distr +
  dummy :: 'a       (*dummy field for new variables*)

record allocState =
  giv :: nat list   (*OUTPUT history: source of tokens*)
  ask :: nat list   (*INPUT: tokens requested from allocator*)
  rel :: nat list   (*INPUT: tokens released to allocator*)

record 'a allocState_d =
  allocState +
  dummy    :: 'a                (*dummy field for new variables*)

record 'a systemState =
  allocState +
  mergeRel :: nat merge
  mergeAsk :: nat merge
  distr    :: nat distr
  dummy    :: 'a                  (*dummy field for new variables*)


constdefs

(** Merge specification (the number of inputs is Nclients) ***)

  (*spec (10)*)
  merge_increasing :: ('a,'b) merge_d program set
    "merge_increasing ==
         UNIV guarantees[funPair merge.Out merge.iOut]
         (Increasing merge.Out) Int (Increasing merge.iOut)"

  (*spec (11)*)
  merge_eqOut :: ('a,'b) merge_d program set
    "merge_eqOut ==
         UNIV guarantees[funPair merge.Out merge.iOut]
         Always {s. length (merge.Out s) = length (merge.iOut s)}"

  (*spec (12)*)
  merge_bounded :: ('a,'b) merge_d program set
    "merge_bounded ==
         UNIV guarantees[merge.iOut]
         Always {s. ALL elt : set (merge.iOut s). elt < Nclients}"

  (*spec (13)*)
  merge_follows :: ('a,'b) merge_d program set
    "merge_follows ==
	 (INT i : lessThan Nclients. Increasing (sub i o merge.In))
	 guarantees[funPair merge.Out merge.iOut]
	 (INT i : lessThan Nclients. 
	  (%s. sublist (merge.Out s) 
                       {k. k < size(merge.iOut s) & merge.iOut s! k = i})
	  Fols (sub i o merge.In))"

  (*spec: preserves part*)
    merge_preserves :: ('a,'b) merge_d program set
    "merge_preserves == preserves (funPair merge.In merge_d.dummy)"

  merge_spec :: ('a,'b) merge_d program set
    "merge_spec == merge_increasing Int merge_eqOut Int merge_bounded Int
                   merge_follows Int merge_preserves"

(** Distributor specification (the number of outputs is Nclients) ***)

  (*spec (14)*)
  distr_follows :: ('a,'b) distr_d program set
    "distr_follows ==
	 Increasing distr.In Int Increasing distr.iIn Int
	 Always {s. ALL elt : set (distr.iIn s). elt < Nclients}
	 guarantees[distr.Out]
	 (INT i : lessThan Nclients. 
	  (sub i o distr.Out) Fols
	  (%s. sublist (distr.In s) 
                       {k. k < size(distr.iIn s) & distr.iIn s ! k = i}))"


(** Single-client allocator specification (required) ***)

  (*spec (18)*)
  alloc_increasing :: 'a allocState_d program set
    "alloc_increasing == UNIV guarantees[giv] Increasing giv"

  (*spec (19)*)
  alloc_safety :: 'a allocState_d program set
    "alloc_safety ==
	 Increasing rel
         guarantees[giv] Always {s. tokens (giv s) <= NbT + tokens (rel s)}"

  (*spec (20)*)
  alloc_progress :: 'a allocState_d program set
    "alloc_progress ==
	 Increasing ask Int Increasing rel Int
         Always {s. ALL elt : set (ask s). elt <= NbT}
         Int
         (INT h. {s. h <= giv s & h pfixGe (ask s)}
		 LeadsTo
	         {s. tokens h <= tokens (rel s)})
         guarantees[giv]
	     (INT h. {s. h <= ask s} LeadsTo {s. h pfixLe giv s})"

  (*spec: preserves part*)
    alloc_preserves :: 'a allocState_d program set
    "alloc_preserves == preserves (funPair rel
				   (funPair ask allocState_d.dummy))"
  
  alloc_spec :: 'a allocState_d program set
    "alloc_spec == alloc_increasing Int alloc_safety Int alloc_progress Int
                   alloc_preserves"

(****
    (** Network specification ***)

      (*spec (9.1)*)
      network_ask :: 'a systemState program set
	"network_ask == INT i : lessThan Nclients.
			    Increasing (ask o sub i o client)
			    guarantees[ask]
			    (ask  Fols (ask o sub i o client))"

      (*spec (9.2)*)
      network_giv :: 'a systemState program set
	"network_giv == INT i : lessThan Nclients.
			    Increasing giv 
			    guarantees[giv o sub i o client]
			    ((giv o sub i o client) Fols giv )"

      (*spec (9.3)*)
      network_rel :: 'a systemState program set
	"network_rel == INT i : lessThan Nclients.
			    Increasing (rel o sub i o client)
			    guarantees[rel]
			    (rel  Fols (rel o sub i o client))"

      (*spec: preserves part*)
	network_preserves :: 'a systemState program set
	"network_preserves == preserves giv  Int
			      (INT i : lessThan Nclients.
			       preserves (funPair rel ask o sub i o client))"

      network_spec :: 'a systemState program set
	"network_spec == network_ask Int network_giv Int
			 network_rel Int network_preserves"


    (** State mappings **)
      sysOfAlloc :: "((nat => merge) * 'a) allocState_d => 'a systemState"
	"sysOfAlloc == %s. let (cl,xtr) = allocState_d.dummy s
			   in (| giv = giv s,
				 ask = ask s,
				 rel = rel s,
				 client   = cl,
				 dummy    = xtr|)"


      sysOfClient :: "(nat => merge) * 'a allocState_d => 'a systemState"
	"sysOfClient == %(cl,al). (| giv = giv al,
				     ask = ask al,
				     rel = rel al,
				     client   = cl,
				     systemState.dummy = allocState_d.dummy al|)"
****)

consts 
    Alloc  :: 'a allocState_d program
    Merge  :: ('a,'b) merge_d program

(*    
    Network :: 'a systemState program
    System  :: 'a systemState program
  *)
  
rules
    Alloc   "Alloc   : alloc_spec"
    Merge  "Merge  : merge_spec"

(**    Network "Network : network_spec"**)



end
