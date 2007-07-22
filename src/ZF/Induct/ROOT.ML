(*  Title:      ZF/Induct/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Inductive definitions.
*)

use_thys [
(** Datatypes **)
  "Datatypes",       (*sample datatypes*)
  "Binary_Trees",    (*binary trees*)
  "Term",            (*recursion over the list functor*)
  "Ntree",           (*variable-branching trees; function demo*)
  "Tree_Forest",     (*mutual recursion*)
  "Brouwer",         (*Infinite-branching trees*)
  "Mutil",           (*mutilated chess board*)

(*by Sidi Ehmety: Multisets.  A parent is FoldSet, the "fold" function for
finite sets*)
  "Multiset",
  "Rmap",            (*mapping a relation over a list*)
  "PropLog",         (*completeness of propositional logic*)

(*two Coq examples by Christine Paulin-Mohring*)
  "ListN",
  "Acc",

  "Comb",            (*Combinatory Logic example*)
  "Primrec"          (*Primitive recursive functions*)
];
