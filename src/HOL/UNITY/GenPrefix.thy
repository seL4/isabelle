(*  Title:      HOL/UNITY/GenPrefix.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Charpentier's Generalized Prefix Relation
   (xs,ys) : genPrefix(r)
     if ys = xs' @ zs where length xs = length xs'
     and corresponding elements of xs, xs' are pairwise related by r

Also overloads <= and < for lists!

Based on Lex/Prefix
*)

GenPrefix = Main +

consts
  genPrefix :: "('a * 'a)set => ('a list * 'a list)set"

inductive "genPrefix(r)"
  intrs
    Nil     "([],[]) : genPrefix(r)"

    prepend "[| (xs,ys) : genPrefix(r);  (x,y) : r |] ==>
	     (x#xs, y#ys) : genPrefix(r)"

    append  "(xs,ys) : genPrefix(r) ==> (xs, ys@zs) : genPrefix(r)"

instance list :: (type)ord

defs
  prefix_def        "xs <= zs  ==  (xs,zs) : genPrefix Id"

  strict_prefix_def "xs < zs  ==  xs <= zs & xs ~= (zs::'a list)"
  

(*Constants for the <= and >= relations, used below in translations*)
constdefs
  Le :: "(nat*nat) set"
    "Le == {(x,y). x <= y}"

  Ge :: "(nat*nat) set"
    "Ge == {(x,y). y <= x}"

syntax
  pfixLe :: [nat list, nat list] => bool               (infixl "pfixLe" 50)
  pfixGe :: [nat list, nat list] => bool               (infixl "pfixGe" 50)

translations
  "xs pfixLe ys" == "(xs,ys) : genPrefix Le"

  "xs pfixGe ys" == "(xs,ys) : genPrefix Ge"

end
