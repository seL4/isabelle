(*  Title:      ZF/UNITY/ClientImpl.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

Distributed Resource Management System:  Client Implementation
*)


ClientImpl = AllocBase + Guar +
consts
  ask :: i (* input history:  tokens requested *)
  giv :: i (* output history: tokens granted *)
  rel :: i (* input history: tokens released *)
  tok :: i (* the number of available tokens *)

translations
  "ask" == "Var(Nil)"
  "giv" == "Var([0])"
  "rel" == "Var([1])"
  "tok" == "Var([2])"

rules
  type_assumes
  "type_of(ask) = list(tokbag) & type_of(giv) = list(tokbag) & 
   type_of(rel) = list(tokbag) & type_of(tok) = nat"
  default_val_assumes
  "default_val(ask) = Nil & default_val(giv)  = Nil & 
   default_val(rel)  = Nil & default_val(tok)  = 0"


(*Array indexing is translated to list indexing as A[n] == nth(n-1,A). *)

constdefs
 (** Release some client_tokens **)
  
  client_rel_act ::i
    "client_rel_act ==
     {<s,t> \\<in> state*state.
      \\<exists>nrel \\<in> nat. nrel = length(s`rel) &
                   t = s(rel:=(s`rel)@[nth(nrel, s`giv)]) &
                   nrel < length(s`giv) &
                   nth(nrel, s`ask) le nth(nrel, s`giv)}"
  
  (** Choose a new token requirement **)
  (** Including t=s suppresses fairness, allowing the non-trivial part
      of the action to be ignored **)

  client_tok_act :: i
 "client_tok_act == {<s,t> \\<in> state*state. t=s |
		     t = s(tok:=succ(s`tok mod NbT))}"

  client_ask_act :: i
  "client_ask_act == {<s,t> \\<in> state*state. t=s | (t=s(ask:=s`ask@[s`tok]))}"
  
  client_prog :: i
  "client_prog ==
   mk_program({s \\<in> state. s`tok le NbT & s`giv = Nil &
	               s`ask = Nil & s`rel = Nil},
                    {client_rel_act, client_tok_act, client_ask_act},
                   \\<Union>G \\<in> preserves(lift(rel)) Int
			 preserves(lift(ask)) Int
	                 preserves(lift(tok)).  Acts(G))"
end