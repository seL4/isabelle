(*  Title:      GroupDefs.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

GroupDefs = MonoidGroupInsts + Prod + Fun +


(* bool *)

instance
  bool :: {times, inverse, one}

defs
  times_bool_def        "x * y == (x ~= y)"
  inverse_bool_def      "inverse x == (x::bool)"
  one_bool_def          "1 == False"


(* cartesian products *)

instance
  "*" :: (term, term) {times, inverse, one}

defs
  times_prod_def        "p * q == (fst p * fst q, snd p * snd q)"
  inverse_prod_def      "inverse p == (inverse (fst p), inverse (snd p))"
  one_prod_def          "1 == (1, 1)"


(* function spaces *)

instance
  fun :: (term, term) {times, inverse, one}

defs
  times_fun_def         "f * g == (%x. f x * g x)"
  inverse_fun_def       "inverse f == (%x. inverse (f x))"
  one_fun_def           "1 == (%x. 1)"

end
