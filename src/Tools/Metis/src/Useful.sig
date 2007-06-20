(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* Copyright (c) 2001-2005 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Useful =
sig

(* ------------------------------------------------------------------------- *)
(* Exceptions.                                                               *)
(* ------------------------------------------------------------------------- *)

exception Error of string

exception Bug of string

val partial : exn -> ('a -> 'b option) -> 'a -> 'b

val total : ('a -> 'b) -> 'a -> 'b option

val can : ('a -> 'b) -> 'a -> bool

(* ------------------------------------------------------------------------- *)
(* Tracing.                                                                  *)
(* ------------------------------------------------------------------------- *)

val tracePrint : (string -> unit) ref

val maxTraceLevel : int ref

val traceLevel : int ref  (* in the set {0, ..., maxTraceLevel} *)

val traceAlign : {module : string, alignment : int -> int option} list ref

val tracing : {module : string, level : int} -> bool

val trace : string -> unit

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val I : 'a -> 'a

val K : 'a -> 'b -> 'a

val S : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val W : ('a -> 'a -> 'b) -> 'a -> 'b

val funpow : int -> ('a -> 'a) -> 'a -> 'a

val exp : ('a * 'a -> 'a) -> 'a -> int -> 'a -> 'a

val equal : ''a -> ''a -> bool

val notEqual : ''a -> ''a -> bool

(* ------------------------------------------------------------------------- *)
(* Pairs.                                                                    *)
(* ------------------------------------------------------------------------- *)

val fst : 'a * 'b -> 'a

val snd : 'a * 'b -> 'b

val pair : 'a -> 'b -> 'a * 'b

val swap : 'a * 'b -> 'b * 'a

val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c

val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c

val ## : ('a -> 'c) * ('b -> 'd) -> 'a * 'b -> 'c * 'd

(* ------------------------------------------------------------------------- *)
(* State transformers.                                                       *)
(* ------------------------------------------------------------------------- *)

val unit : 'a -> 's -> 'a * 's

val bind : ('s -> 'a * 's) -> ('a -> 's -> 'b * 's) -> 's -> 'b * 's

val mmap : ('a -> 'b) -> ('s -> 'a * 's) -> 's -> 'b * 's

val mjoin : ('s -> ('s -> 'a * 's) * 's) -> 's -> 'a * 's

val mwhile : ('a -> bool) -> ('a -> 's -> 'a * 's) -> 'a -> 's -> 'a * 's

(* ------------------------------------------------------------------------- *)
(* Lists: note we count elements from 0.                                     *)
(* ------------------------------------------------------------------------- *)

val cons : 'a -> 'a list -> 'a list

val hdTl : 'a list -> 'a * 'a list

val append : 'a list -> 'a list -> 'a list

val singleton : 'a -> 'a list

val first : ('a -> 'b option) -> 'a list -> 'b option

val index : ('a -> bool) -> 'a list -> int option

val maps : ('a -> 's -> 'b * 's) -> 'a list -> 's -> 'b list * 's

val mapsPartial : ('a -> 's -> 'b option * 's) -> 'a list -> 's -> 'b list * 's

val enumerate : 'a list -> (int * 'a) list

val zipwith : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

val zip : 'a list -> 'b list -> ('a * 'b) list

val unzip : ('a * 'b) list -> 'a list * 'b list

val cartwith : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

val cart : 'a list -> 'b list -> ('a * 'b) list

val divide : 'a list -> int -> 'a list * 'a list  (* Subscript *)

val revDivide : 'a list -> int -> 'a list * 'a list  (* Subscript *)

val updateNth : int * 'a -> 'a list -> 'a list  (* Subscript *)

val deleteNth : int -> 'a list -> 'a list  (* Subscript *)

(* ------------------------------------------------------------------------- *)
(* Sets implemented with lists.                                              *)
(* ------------------------------------------------------------------------- *)

val mem : ''a -> ''a list -> bool

val insert : ''a -> ''a list -> ''a list

val delete : ''a -> ''a list -> ''a list

val setify : ''a list -> ''a list  (* removes duplicates *)

val union : ''a list -> ''a list -> ''a list

val intersect : ''a list -> ''a list -> ''a list

val difference : ''a list -> ''a list -> ''a list

val subset : ''a list -> ''a list -> bool

val distinct : ''a list -> bool

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

val mapCompare : ('a -> 'b) -> ('b * 'b -> order) -> 'a * 'a -> order

val revCompare : ('a * 'a -> order) -> 'a * 'a -> order

val prodCompare :
    ('a * 'a -> order) -> ('b * 'b -> order) -> ('a * 'b) * ('a * 'b) -> order

val lexCompare : ('a * 'a -> order) -> 'a list * 'a list -> order

val boolCompare : bool * bool -> order  (* true < false *)

(* ------------------------------------------------------------------------- *)
(* Sorting and searching.                                                    *)
(* ------------------------------------------------------------------------- *)

val minimum : ('a * 'a -> order) -> 'a list -> 'a * 'a list  (* Empty *)

val maximum : ('a * 'a -> order) -> 'a list -> 'a * 'a list  (* Empty *)

val merge : ('a * 'a -> order) -> 'a list -> 'a list -> 'a list

val sort : ('a * 'a -> order) -> 'a list -> 'a list

val sortMap : ('a -> 'b) -> ('b * 'b -> order) -> 'a list -> 'a list

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

val interval : int -> int -> int list

val divides : int -> int -> bool

val gcd : int -> int -> int

val primes : int -> int list

val primesUpTo : int -> int list

(* ------------------------------------------------------------------------- *)
(* Strings.                                                                  *)
(* ------------------------------------------------------------------------- *)

val rot : int -> char -> char

val charToInt : char -> int option

val charFromInt : int -> char option

val nChars : char -> int -> string

val chomp : string -> string

val trim : string -> string

val join : string -> string list -> string

val split : string -> string -> string list

val mkPrefix : string -> string -> string

val destPrefix : string -> string -> string

val isPrefix : string -> string -> bool

(* ------------------------------------------------------------------------- *)
(* Tables.                                                                   *)
(* ------------------------------------------------------------------------- *)

type columnAlignment = {leftAlign : bool, padChar : char}

val alignColumn : columnAlignment -> string list -> string list -> string list

val alignTable : columnAlignment list -> string list list -> string list

(* ------------------------------------------------------------------------- *)
(* Reals.                                                                    *)
(* ------------------------------------------------------------------------- *)

val percentToString : real -> string

val pos : real -> real

val log2 : real -> real  (* Domain *)

(* ------------------------------------------------------------------------- *)
(* Sum datatype.                                                             *)
(* ------------------------------------------------------------------------- *)

datatype ('a,'b) sum = Left of 'a | Right of 'b

val destLeft : ('a,'b) sum -> 'a

val isLeft : ('a,'b) sum -> bool

val destRight : ('a,'b) sum -> 'b

val isRight : ('a,'b) sum -> bool

(* ------------------------------------------------------------------------- *)
(* Useful impure features.                                                   *)
(* ------------------------------------------------------------------------- *)

val newInt : unit -> int

val newInts : int -> int list

val random : int -> int

val uniform : unit -> real

val coinFlip : unit -> bool

val withRef : 'r ref * 'r -> ('a -> 'b) -> 'a -> 'b

(* ------------------------------------------------------------------------- *)
(* The environment.                                                          *)
(* ------------------------------------------------------------------------- *)

val host : unit -> string

val time : unit -> string

val date : unit -> string

val readTextFile : {filename : string} -> string

val writeTextFile : {filename : string, contents : string} -> unit

(* ------------------------------------------------------------------------- *)
(* Profiling and error reporting.                                            *)
(* ------------------------------------------------------------------------- *)

val try : ('a -> 'b) -> 'a -> 'b

val warn : string -> unit

val die : string -> 'exit

val timed : ('a -> 'b) -> 'a -> real * 'b

val timedMany : ('a -> 'b) -> 'a -> real * 'b

val executionTime : unit -> real  (* Wall clock execution time *)

end
