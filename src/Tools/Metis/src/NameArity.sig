(* ========================================================================= *)
(* NAME/ARITY PAIRS                                                          *)
(* Copyright (c) 2004 Joe Hurd, distributed under the MIT license            *)
(* ========================================================================= *)

signature NameArity =
sig

(* ------------------------------------------------------------------------- *)
(* A type of name/arity pairs.                                               *)
(* ------------------------------------------------------------------------- *)

type nameArity = Name.name * int

val name : nameArity -> Name.name

val arity : nameArity -> int

(* ------------------------------------------------------------------------- *)
(* Testing for different arities.                                            *)
(* ------------------------------------------------------------------------- *)

val nary : int -> nameArity -> bool

val nullary : nameArity -> bool

val unary : nameArity -> bool

val binary : nameArity -> bool

val ternary : nameArity -> bool

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

val compare : nameArity * nameArity -> order

val equal : nameArity -> nameArity -> bool

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp : nameArity Print.pp

end
