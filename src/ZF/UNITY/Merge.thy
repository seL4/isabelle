(*  Title: ZF/UNITY/Merge
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

A multiple-client allocator from a single-client allocator:
Merge specification
*)

Merge = AllocBase + Follows +  Guar + GenPrefix +
(** Merge specification (the number of inputs is Nclients) ***)
(** Parameter A represents the type of items to Merge **)
constdefs
  (*spec (10)*)
  merge_increasing :: [i, i, i] =>i
    "merge_increasing(A, Out, iOut) == program guarantees
         (lift(Out) IncreasingWrt  prefix(A)/list(A)) Int
         (lift(iOut) IncreasingWrt prefix(nat)/list(nat))"

  (*spec (11)*)
  merge_eq_Out :: [i, i] =>i
  "merge_eq_Out(Out, iOut) == program guarantees
         Always({s:state. length(s`Out) = length(s`iOut)})"

  (*spec (12)*)
  merge_bounded :: i=>i
  "merge_bounded(iOut) == program guarantees
         Always({s:state. ALL elt:set_of_list(s`iOut). elt<Nclients})"
  
  (*spec (13)*)
  (* Parameter A represents the type of tokens *)
  merge_follows :: [i, i=>i, i, i] =>i
    "merge_follows(A, In, Out, iOut) ==
     (INT n:Nclients. lift(In(n)) IncreasingWrt prefix(A)/list(A))
		   guarantees
     (INT n:Nclients. 
        (%s. sublist(s`Out, {k:nat. k < length(s`iOut) &
                      nth(k, s`iOut) = n})) Fols lift(In(n))
         Wrt prefix(A)/list(A))"

  (*spec: preserves part*)
  merge_preserves :: [i=>i] =>i
    "merge_preserves(In) == INT n:nat. preserves(lift(In(n)))"

(* environmental constraints*)
  merge_allowed_acts :: [i, i] =>i
  "merge_allowed_acts(Out, iOut) ==
         {F:program. AllowedActs(F) =
            cons(id(state), (UN G:preserves(lift(Out)) Int
                                  preserves(lift(iOut)). Acts(G)))}"
  
  merge_spec :: [i, i =>i, i, i]=>i
  "merge_spec(A, In, Out, iOut) ==
   merge_increasing(A, Out, iOut) Int merge_eq_Out(Out, iOut) Int
   merge_bounded(iOut) Int  merge_follows(A, In, Out, iOut)
   Int merge_allowed_acts(Out, iOut) Int merge_preserves(In)"

(** State definitions.  OUTPUT variables are locals **)
locale Merge =
  fixes In :: i=>i (*merge's INPUT histories: streams to merge*)
        Out :: i   (*merge's OUTPUT history: merged items*)
        iOut :: i  (*merge's OUTPUT history: origins of merged items*)
        A  :: i    (*the type of items being merged *)
        M :: i
 assumes
    var_assumes       "(ALL n. In(n):var) & Out:var & iOut:var"
    all_distinct_vars "ALL n. all_distinct([In(n), Out, iOut])"
    type_assumes      "(ALL n. type_of(In(n))=list(A))&
		       type_of(Out)=list(A) &
                       type_of(iOut)=list(nat)"
   default_val_assumes "(ALL n. default_val(In(n))=Nil) &
                        default_val(Out)=Nil &
                        default_val(iOut)=Nil"

   merge_spec  "M:merge_spec(A, In, Out, iOut)"
end

  