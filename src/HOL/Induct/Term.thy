(*  Title:      HOL/Induct/Term.thy
    ID:         $Id$
    Author:     Stefan Berghofer,  TU Muenchen
    Copyright   1998  TU Muenchen

Terms over a given alphabet -- function applications
*)

Term = Main +

datatype
  ('a, 'b) term = Var 'a
                | App 'b ((('a, 'b) term) list)


(** substitution function on terms **)

consts
  subst_term :: "['a => ('a, 'b) term, ('a, 'b) term] => ('a, 'b) term"
  subst_term_list ::
    "['a => ('a, 'b) term, ('a, 'b) term list] => ('a, 'b) term list"

primrec
  "subst_term f (Var a) = f a"
  "subst_term f (App b ts) = App b (subst_term_list f ts)"

  "subst_term_list f [] = []"
  "subst_term_list f (t # ts) =
     subst_term f t # subst_term_list f ts"

end
