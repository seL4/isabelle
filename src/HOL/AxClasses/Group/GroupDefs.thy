(*  Title:      GroupDefs.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

GroupDefs = MonoidGroupInsts + Prod + Fun +


(* bool *)

instance
  bool :: {times, inv, one}

defs
  times_bool_def        "x * y == (x ~= y)"
  inv_bool_def          "inv x == (x::bool)"
  one_bool_def          "1 == False"


(* cartesian products *)

instance
  "*" :: (term, term) {times, inv, one}

defs
  times_prod_def        "p * q == (fst p * fst q, snd p * snd q)"
  inv_prod_def          "inv p == (inv (fst p), inv (snd p))"
  one_prod_def          "1 == (1, 1)"


(* function spaces *)

instance
  fun :: (term, term) {times, inv, one}

defs
  times_fun_def         "f * g == (%x. f x * g x)"
  inv_fun_def           "inv f == (%x. inv (f x))"
  one_fun_def           "1 == (%x. 1)"

end
