(*  Title:      HOL/ex/Points.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen

Basic use of extensible records in HOL, including the famous points
and coloured points.
*)

Points = Main +


(** points **)

record point =
  x :: nat
  y :: nat

(*
  To find out, which theorems are produced by the record declaration,
  type the following commands:

    thms "point.simps";
    thms "point.iffs";
    thms "point.update_defs";

  The set of theorems "point.simps" is added automatically to the
  standard simpset, "point.iffs" is added to the claset and simpset.
*)


(*
  Record declarations define new type abbreviations:

    point = (| x :: nat, y :: nat |)
    'a point_scheme = (| x :: nat, y :: nat, ... :: 'a |)

  Extensions `...' must be in type class `more'!
*)

consts foo1 :: point
consts foo2 :: "(| x :: nat, y :: nat |)"
consts foo3 :: 'a => ('a::more) point_scheme
consts foo4 :: "'a => (| x :: nat, y :: nat, ... :: 'a |)"


(* Introducing concrete records and record schemes *)

defs
  foo1_def "foo1 == (| x = 1, y = 0 |)"
  foo3_def "foo3 ext == (| x = 1, y = 0, ... = ext |)"


(* Record selection and record update *)

constdefs
  getX :: ('a::more) point_scheme => nat
  "getX r == x r"
  setX :: ('a::more) point_scheme => nat => 'a point_scheme
  "setX r n == r (| x := n |)"


(* concrete records are type instances of record schemes *)

constdefs
  foo5 :: nat
  "foo5 == getX (| x = 1, y = 0 |)"


(* manipulating the `...' (more-part) *)

constdefs
  incX :: ('a::more) point_scheme => 'a point_scheme
  "incX r == (| x = Suc (x r), y = y r, ... = point.more r |)"

(*alternative definition*)
constdefs
  incX' :: ('a::more) point_scheme => 'a point_scheme
  "incX' r == r (| x := Suc (x r) |)"



(** coloured points: record extension **)

datatype colour = Red | Green | Blue

record cpoint = point +
  colour :: colour


(*
  The record declaration defines new type constructors:

    cpoint = (| x :: nat, y :: nat, colour :: colour |)
    'a cpoint_scheme = (| x :: nat, y :: nat, colour :: colour, ... :: 'a |)
*)

consts foo6 :: cpoint
consts foo7 :: "(| x :: nat, y :: nat, colour :: colour |)"
consts foo8 :: ('a::more) cpoint_scheme
consts foo9 :: "(| x :: nat, y :: nat, colour :: colour, ... :: 'a |)"


(* functions on point schemes work for cpoints as well *)

constdefs
  foo10 :: nat
  "foo10 == getX (| x = 2, y = 0, colour = Blue |)"


(* non-coercive structural subtyping *)

(*foo11 has type cpoint, not type point*)                       (*Great!*)
constdefs
  foo11 :: cpoint
  "foo11 == setX (| x = 2, y = 0, colour = Blue |) 0"



(** other features **)

(* field names contribute to record identity *)

record point' =
  x' :: nat
  y' :: nat

consts
  foo12 :: nat
(*"foo12 == getX (| x' = 2, y' = 0 |)"*)        (*invalid*)


(* polymorphic records *)

record 'a point'' = point +
  content :: 'a

types cpoint'' = colour point''



(*Have a lot of fun!*)

end
