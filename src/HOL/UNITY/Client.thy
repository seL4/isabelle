(*  Title:      HOL/UNITY/Client.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Distributed Resource Management System: the Client
*)

Client = Rename + AllocBase +

types
  tokbag = nat	   (*tokbags could be multisets...or any ordered type?*)

record state =
  giv :: tokbag list   (*input history: tokens granted*)
  ask :: tokbag list   (*output history: tokens requested*)
  rel :: tokbag list   (*output history: tokens released*)
  tok :: tokbag	       (*current token request*)

record 'a state_u =
  state +  
  extra :: 'a          (*new variables*)


(*Array indexing is translated to list indexing as A[n] == A!(n-1). *)

constdefs
  
  (** Release some tokens **)
  
  rel_act :: "('a state_u * 'a state_u) set"
    "rel_act == {(s,s').
		  EX nrel. nrel = size (rel s) &
		           s' = s (| rel := rel s @ [giv s!nrel] |) &
		           nrel < size (giv s) &
		           ask s!nrel <= giv s!nrel}"

  (** Choose a new token requirement **)

  (** Including s'=s suppresses fairness, allowing the non-trivial part
      of the action to be ignored **)

  tok_act :: "('a state_u * 'a state_u) set"
     "tok_act == {(s,s'). s'=s | s' = s (|tok := Suc (tok s mod NbT) |)}"
  
  ask_act :: "('a state_u * 'a state_u) set"
    "ask_act == {(s,s'). s'=s |
		         (s' = s (|ask := ask s @ [tok s]|))}"

  Client :: 'a state_u program
    "Client == mk_program ({s. tok s : atMost NbT &
		               giv s = [] & ask s = [] & rel s = []},
			   {rel_act, tok_act, ask_act})"

  (*Maybe want a special theory section to declare such maps*)
  non_extra :: 'a state_u => state
    "non_extra s == (|giv = giv s, ask = ask s, rel = rel s, tok = tok s|)"

  (*Renaming map to put a Client into the standard form*)
  client_map :: "'a state_u => state*'a"
    "client_map == funPair non_extra extra"

end
