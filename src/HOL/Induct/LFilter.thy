(*  Title:      HOL/LList.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

The "filter" functional for coinductive lists
  --defined by a combination of induction and coinduction
*)

LFilter = LList +

consts
  findRel	:: "('a => bool) => ('a llist * 'a llist)set"

inductive "findRel p"
  intrs
    found  "p x ==> (LCons x l, LCons x l) : findRel p"
    seek   "[| ~p x;  (l,l') : findRel p |] ==> (LCons x l, l') : findRel p"

constdefs
  find		:: ['a => bool, 'a llist] => 'a llist
    "find p l == @l'. (l,l'): findRel p | (l' = LNil & l ~: Domain(findRel p))"

  lfilter	:: ['a => bool, 'a llist] => 'a llist
    "lfilter p l == llist_corec l (%l. case find p l of
                                            LNil => None
                                          | LCons y z => Some(y,z))"

end
