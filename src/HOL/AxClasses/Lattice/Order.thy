(*  Title:      Order.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Basic theory of orders (quasi orders, partial orders, linear orders)
and limits (inf, sup, min, max).
*)

Order = HOL + Set +


(** class definitions **)

(* syntax for orders *)

axclass
  le < term

consts
  "[="          :: "['a::le, 'a] => bool"             (infixl 50)


(* quasi orders *)

axclass
  quasi_order < le
  le_refl       "x [= x"
  le_trans      "x [= y & y [= z --> x [= z"


(* partial orders *)

axclass
  order < quasi_order
  le_antisym    "x [= y & y [= x --> x = y"


(* linear orders *)

axclass
  lin_order < order
  le_lin        "x [= y | y [= x"



(** limits **)

(* infima and suprema (on orders) *)

consts
  (*binary*)
  is_inf        :: "['a::order, 'a, 'a] => bool"
  is_sup        :: "['a::order, 'a, 'a] => bool"
  (*general*)
  is_Inf        :: "['a::order set, 'a] => bool"
  is_Sup        :: "['a::order set, 'a] => bool"

defs
  is_inf_def    "is_inf x y inf ==
                   inf [= x & inf [= y &
                   (ALL lb. lb [= x & lb [= y --> lb [= inf)"
  is_sup_def    "is_sup x y sup ==
                   x [= sup & y [= sup &
                   (ALL ub. x [= ub & y [= ub --> sup [= ub)"
  is_Inf_def    "is_Inf A inf ==
                   (ALL x:A. inf [= x) &
                   (ALL lb. (ALL x:A. lb [= x) --> lb [= inf)"
  is_Sup_def    "is_Sup A sup ==
                   (ALL x:A. x [= sup) &
                   (ALL ub. (ALL x:A. x [= ub) --> sup [= ub)"


(* binary minima and maxima (on lin_orders) *)

consts
  minimum      :: "['a::lin_order, 'a] => 'a"
  maximum      :: "['a::lin_order, 'a] => 'a"

defs
  minimum_def  "minimum x y == (if x [= y then x else y)"
  maximum_def  "maximum x y == (if x [= y then y else x)"

end
