(*  Title:      OrdDefs.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some overloaded definitions.
*)

OrdDefs = Order + Prod +


(* binary / general products *)

instance
  "*" :: (le, le) le

instance
  fun :: (term, le) le

defs
  le_prod_def   "p [= q == fst p [= fst q & snd p [= snd q"
  le_fun_def    "f [= g == ALL x. f x [= g x"


(* duals *)

subtype
  'a dual = "{x::'a. True}"

instance
  dual :: (le) le

defs
  le_dual_def   "x [= y == Rep_dual y [= Rep_dual x"

end
