(*  Title: ZF/UNITY/Distributor
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

A multiple-client allocator from a single-client allocator:
Distributor specification
*)
Distributor = AllocBase + Follows +  Guar + GenPrefix +
(** Distributor specification (the number of outputs is Nclients) ***)
 (*spec (14)*)
constdefs  
  distr_follows :: [i, i, i, i =>i] =>i
    "distr_follows(A, In, iIn, Out) ==
     (lift(In) IncreasingWrt prefix(A)/list(A)) Int
     (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) Int
     Always({s:state. ALL elt: set_of_list(s`iIn). elt < Nclients})
         guarantees
         (INT n: Nclients.
          lift(Out(n))
              Fols
          (%s. sublist(s`In, 
                       {k:nat. k<length(s`iIn) & nth(k, s`iIn) = n}))
	  Wrt prefix(A)/list(A))"
  
 distr_allowed_acts :: [i=>i]=>i
  "distr_allowed_acts(Out) ==
   {D:program. AllowedActs(D) =
   cons(id(state), UN G:(INT n:nat. preserves(lift(Out(n)))). Acts(G))}"

  distr_spec :: [i, i, i, i =>i]=>i
  "distr_spec(A, In, iIn, Out) ==
   distr_follows(A, In, iIn, Out) Int distr_allowed_acts(Out)"

locale Distributor =
  fixes In :: i  (*items to distribute*)
        iIn :: i (*destinations of items to distribute*)
        Out :: i=>i  (*distributed items*)
        A :: i   (*the type of items being distributed *)
        D :: i
 assumes
    var_assumes       "In:var & iIn:var & (ALL n. Out(n):var)"
    all_distinct_vars "ALL n. all_distinct([In, iIn, iOut(n)])"
    type_assumes      "type_of(In)=list(A) &  type_of(iIn)=list(nat) &
                       (ALL n. type_of(Out(n))=list(A))"
   default_val_assumes "default_val(In)=Nil &
                        default_val(iIn)=Nil &
                        (ALL n. default_val(Out(n))=Nil)"
   distr_spec  "D:distr_spec(A, In, iIn, Out)"
end
