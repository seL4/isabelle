(*  Title:      HOL/AxClasses/Tutorial/Semigroups.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Semigroups with different 'signatures'.
*)

Semigroups = HOL +

consts
  "<+>"         :: "['a, 'a] => 'a"             (infixl 65)
  "<*>"         :: "['a, 'a] => 'a"             (infixl 70)
  assoc         :: "(['a, 'a] => 'a) => bool"

defs
  assoc_def     "assoc f == ALL x y z. f (f x y) z = f x (f y z)"


(* semigroups with op <+> *)

axclass
  plus_sg < term
  plus_assoc    "assoc (op <+>)"


(* semigroups with op <*> *)

axclass
  times_sg < term
  times_assoc   "assoc (op <*>)"

end
