(* ========================================================================= *)
(* PARSING                                                                   *)
(* Copyright (c) 2001 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

signature Parse =
sig

(* ------------------------------------------------------------------------- *)
(* A "cannot parse" exception.                                               *)
(* ------------------------------------------------------------------------- *)

exception NoParse

(* ------------------------------------------------------------------------- *)
(* Recursive descent parsing combinators.                                    *)
(* ------------------------------------------------------------------------- *)

(*
  Recommended fixities:

  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||
*)

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

(* ------------------------------------------------------------------------- *)
(* Stream-based parsers.                                                     *)
(* ------------------------------------------------------------------------- *)

type ('a,'b) parser = 'a Stream.stream -> 'b * 'a Stream.stream

val maybe : ('a -> 'b option) -> ('a,'b) parser

val finished : ('a,unit) parser

val some : ('a -> bool) -> ('a,'a) parser

val any : ('a,'a) parser

(* ------------------------------------------------------------------------- *)
(* Parsing whole streams.                                                    *)
(* ------------------------------------------------------------------------- *)

val fromStream : ('a,'b) parser -> 'a Stream.stream -> 'b

val fromList : ('a,'b) parser -> 'a list -> 'b

val everything : ('a, 'b list) parser -> 'a Stream.stream -> 'b Stream.stream

(* ------------------------------------------------------------------------- *)
(* Parsing lines of text.                                                    *)
(* ------------------------------------------------------------------------- *)

val initialize :
    {lines : string Stream.stream} ->
    {chars : char list Stream.stream,
     parseErrorLocation : unit -> string}

val exactChar : char -> (char,unit) parser

val exactCharList : char list -> (char,unit) parser

val exactString : string -> (char,unit) parser

val escapeString : {escape : char list} -> (char,string) parser

val manySpace : (char,unit) parser

val atLeastOneSpace : (char,unit) parser

val fromString : (char,'a) parser -> string -> 'a

(* ------------------------------------------------------------------------- *)
(* Infix operators.                                                          *)
(* ------------------------------------------------------------------------- *)

val parseInfixes :
    Print.infixes -> (string * 'a * 'a -> 'a) -> (string,'a) parser ->
    (string,'a) parser

(* ------------------------------------------------------------------------- *)
(* Quotations.                                                               *)
(* ------------------------------------------------------------------------- *)

type 'a quotation = 'a frag list

val parseQuotation : ('a -> string) -> (string -> 'b) -> 'a quotation -> 'b

end
