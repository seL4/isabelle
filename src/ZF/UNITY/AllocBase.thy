(*  Title:      ZF/UNITY/AllocBase.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Common declarations for Chandy and Charpentier's Allocator
*)

AllocBase = Follows + MultisetSum + Guar +

consts
  tokbag   :: i  (* tokbags could be multisets...or any ordered type?*)
  NbT      :: i  (* Number of tokens in system *)
  Nclients :: i  (* Number of clients *)
translations
"tokbag" => "nat" 
rules
  NbT_pos  "NbT:nat-{0}"
  Nclients_pos "Nclients:nat-{0}"
  
(*This function merely sums the elements of a list*)
consts tokens     :: i =>i
       item :: i (* Items to be merged/distributed *)
primrec 
  "tokens(Nil) = 0"
  "tokens (Cons(x,xs)) = x #+ tokens(xs)"

consts
  bag_of :: i => i

primrec
  "bag_of(Nil)    = 0"
  "bag_of(Cons(x,xs)) = {#x#} +# bag_of(xs)"

(* definitions needed in Client.thy *)
consts
  all_distinct0:: i=>i
  all_distinct:: i=>o
  
primrec
  "all_distinct0(Nil) = 1"
  "all_distinct0(Cons(a, l)) =
     (if a:set_of_list(l) then 0 else all_distinct0(l))"

defs
all_distinct_def
  "all_distinct(l) == all_distinct0(l)=1"
  
constdefs  
  (* coersion from anyting to state *)
  state_of :: i =>i
  "state_of(s) == if s:state then s else st0"

  (* simplifies the expression of programs  *)

  lift :: "i =>(i=>i)"
  "lift(x) == %s. s`x"

consts (* to show that the set of variables is infinite *)
  nat_list_inj :: i=>i
  nat_var_inj  :: i=>i
  var_inj :: i=>i
defs
  nat_var_inj_def "nat_var_inj(n) == Var(nat_list_inj(n))"
primrec
  "nat_list_inj(0) = Nil"
  "nat_list_inj(succ(n)) = Cons(n, nat_list_inj(n))"

primrec
  "var_inj(Var(l)) = length(l)"

end
