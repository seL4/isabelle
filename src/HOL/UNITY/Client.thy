(*  Title:      HOL/UNITY/Client.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Distributed Resource Management System: the Client
*)

Client = Guar + 

consts
  Max :: nat       (*Maximum number of tokens*)

types
  tokbag = nat	   (*tokbags could be multisets...or any ordered type?*)

record state =
  giv :: tokbag list   (*input history: tokens granted*)
  ask :: tokbag list   (*output history: tokens requested*)
  rel :: tokbag list   (*output history: tokens released*)
  tok :: tokbag	       (*current token request*)


(*Array indexing is translated to list indexing as A[n] == A!(n-1). *)

constdefs
  
  (** Release some tokens **)
  
  rel_act :: "(state*state) set"
    "rel_act == {(s,s').
		  EX nrel. nrel = size (rel s) &
		           s' = s (| rel := rel s @ [giv s!nrel] |) &
		           nrel < size (giv s) &
		           ask s!nrel <= giv s!nrel}"

  (** Choose a new token requirement **)

  (** Including s'=s suppresses fairness, allowing the non-trivial part
      of the action to be ignored **)

  tok_act :: "(state*state) set"
    "tok_act == {(s,s'). s'=s | (EX t: atMost Max. s' = s (|tok := t|))}"

  ask_act :: "(state*state) set"
    "ask_act == {(s,s'). s'=s |
		         (s' = s (|ask := ask s @ [tok s]|) &
		          size (ask s) = size (rel s))}"

  Cli_prg :: state program
    "Cli_prg == mk_program ({s. tok s : atMost Max &
			        giv s = [] &
			        ask s = [] &
			        rel s = []},
			    {rel_act, tok_act, ask_act})"

  giv_meets_ask :: state set
    "giv_meets_ask ==
       {s. size (giv s) <= size (ask s) & 
           (ALL n: lessThan (size (giv s)). ask s!n <= giv s!n)}"

end
