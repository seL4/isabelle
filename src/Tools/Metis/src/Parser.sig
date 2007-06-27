(* ========================================================================= *)
(* PARSING AND PRETTY PRINTING                                               *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Parser =
sig

(* ------------------------------------------------------------------------- *)
(* Pretty printing for built-in types                                        *)
(* ------------------------------------------------------------------------- *)

type ppstream = PP.ppstream

datatype breakStyle = Consistent | Inconsistent

type 'a pp = ppstream -> 'a -> unit

val lineLength : int ref

val beginBlock : ppstream -> breakStyle -> int -> unit

val endBlock : ppstream -> unit

val addString : ppstream -> string -> unit

val addBreak : ppstream -> int * int -> unit

val addNewline : ppstream -> unit

val ppMap : ('a -> 'b) -> 'b pp -> 'a pp

val ppBracket : string -> string -> 'a pp -> 'a pp

val ppSequence : string -> 'a pp -> 'a list pp

val ppBinop : string -> 'a pp -> 'b pp -> ('a * 'b) pp

val ppChar : char pp

val ppString : string pp

val ppUnit : unit pp

val ppBool : bool pp

val ppInt : int pp

val ppReal : real pp

val ppOrder : order pp

val ppList : 'a pp -> 'a list pp

val ppOption : 'a pp -> 'a option pp

val ppPair : 'a pp -> 'b pp -> ('a * 'b) pp

val ppTriple : 'a pp -> 'b pp -> 'c pp -> ('a * 'b * 'c) pp

val toString : 'a pp -> 'a -> string  (* Uses !lineLength *)

val fromString : ('a -> string) -> 'a pp

val ppTrace : 'a pp -> string -> 'a -> unit

(* ------------------------------------------------------------------------- *)
(* Recursive descent parsing combinators                                     *)
(* ------------------------------------------------------------------------- *)

(* Generic parsers

Recommended fixities:
  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||
*)

exception NoParse

val error : 'a -> 'b * 'a

val ++ : ('a -> 'b * 'a) * ('a -> 'c * 'a) -> 'a -> ('b * 'c) * 'a

val >> : ('a -> 'b * 'a) * ('b -> 'c) -> 'a -> 'c * 'a

val >>++ : ('a -> 'b * 'a) * ('b -> 'a -> 'c * 'a) -> 'a -> 'c * 'a

val || : ('a -> 'b * 'a) * ('a -> 'b * 'a) -> 'a -> 'b * 'a

val first : ('a -> 'b * 'a) list -> 'a -> 'b * 'a

val mmany : ('s -> 'a -> 's * 'a) -> 's -> 'a -> 's * 'a

val many : ('a -> 'b * 'a) -> 'a -> 'b list * 'a

val atLeastOne : ('a -> 'b * 'a) -> 'a -> 'b list * 'a

val nothing : 'a -> unit * 'a

val optional : ('a -> 'b * 'a) -> 'a -> 'b option * 'a

(* Stream based parsers *)

type ('a,'b) parser = 'a Stream.stream -> 'b * 'a Stream.stream

val everything : ('a, 'b list) parser -> 'a Stream.stream -> 'b Stream.stream

val maybe : ('a -> 'b option) -> ('a,'b) parser

val finished : ('a,unit) parser

val some : ('a -> bool) -> ('a,'a) parser

val any : ('a,'a) parser

val exact : ''a -> (''a,''a) parser

(* ------------------------------------------------------------------------- *)
(* Infix operators                                                           *)
(* ------------------------------------------------------------------------- *)

type infixities = {token : string, precedence : int, leftAssoc : bool} list

val infixTokens : infixities -> string list

val parseInfixes :
    infixities -> (string * 'a * 'a -> 'a) -> (string,'a) parser ->
    (string,'a) parser

val ppInfixes :
    infixities -> ('a -> (string * 'a * 'a) option) -> ('a * bool) pp ->
    ('a * bool) pp

(* ------------------------------------------------------------------------- *)
(* Quotations                                                                *)
(* ------------------------------------------------------------------------- *)

type 'a quotation = 'a frag list

val parseQuotation : ('a -> string) -> (string -> 'b) -> 'a quotation -> 'b

end
