(*  Title:      ZF/UNITY/GenPrefix.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Charpentier's Generalized Prefix Relation
   <xs,ys>:gen_prefix(r)
     if ys = xs' @ zs where length(xs) = length(xs')
     and corresponding elements of xs, xs' are pairwise related by r

Based on Lex/Prefix
*)

GenPrefix = ListPlus + 

consts
  gen_prefix :: "[i, i] => i"
  
inductive
  (* Parameter A is the domain of zs's elements *)
  
  domains "gen_prefix(A, r)" <= "list(A)*list(A)"
  
  intrs
    Nil     "<[],[]>:gen_prefix(A, r)"

    prepend "[| <xs,ys>:gen_prefix(A, r);  <x,y>:r; x:A; y:A |]
	      ==> <Cons(x,xs), Cons(y,ys)>: gen_prefix(A, r)"

    append  "[| <xs,ys>:gen_prefix(A, r); zs:list(A) |]
	     ==> <xs, ys@zs>:gen_prefix(A, r)"
    type_intrs "list.intrs@[app_type]"

constdefs
   prefix :: i=>i
  "prefix(A) == gen_prefix(A, id(A))"

   strict_prefix :: i=>i  
  "strict_prefix(A) == prefix(A) - id(list(A))"

  (* Probably to be moved elsewhere *)

   Le :: i
  "Le == {<x,y>:nat*nat. x le y}"
  
   Ge :: i
  "Ge == {<x,y>:nat*nat. y le x}"

syntax
  (* less or equal and greater or equal over prefixes *)
  pfixLe :: [i, i] => o               (infixl "pfixLe" 50)
  pfixGe :: [i, i] => o               (infixl "pfixGe" 50)

translations
   "xs pfixLe ys" == "<xs, ys>:gen_prefix(nat, Le)"
   "xs pfixGe ys" == "<xs, ys>:gen_prefix(nat, Ge)"
  

end
