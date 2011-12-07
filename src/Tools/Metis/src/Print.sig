(* ========================================================================= *)
(* PRETTY-PRINTING                                                           *)
(* Copyright (c) 2008 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

signature Print =
sig

(* ------------------------------------------------------------------------- *)
(* Escaping strings.                                                         *)
(* ------------------------------------------------------------------------- *)

val escapeString : {escape : char list} -> string -> string

(* ------------------------------------------------------------------------- *)
(* A type of pretty-printers.                                                *)
(* ------------------------------------------------------------------------- *)

type ppstream

type 'a pp = 'a -> ppstream

val skip : ppstream

val sequence : ppstream -> ppstream -> ppstream

val duplicate : int -> ppstream -> ppstream

val program : ppstream list -> ppstream

val stream : ppstream Stream.stream -> ppstream

val ppPpstream : ppstream pp

(* ------------------------------------------------------------------------- *)
(* Pretty-printing blocks.                                                   *)
(* ------------------------------------------------------------------------- *)

datatype style = Consistent | Inconsistent

datatype block =
    Block of
      {style : style,
       indent : int}

val styleBlock : block -> style

val indentBlock : block -> int

val block : block -> ppstream -> ppstream

val consistentBlock : int -> ppstream list -> ppstream

val inconsistentBlock : int -> ppstream list -> ppstream

(* ------------------------------------------------------------------------- *)
(* Words are unbreakable strings annotated with their effective size.        *)
(* ------------------------------------------------------------------------- *)

datatype word = Word of {word : string, size : int}

val mkWord : string -> word

val emptyWord : word

val charWord : char -> word

val ppWord : word pp

val space : ppstream

val spaces : int -> ppstream

(* ------------------------------------------------------------------------- *)
(* Possible line breaks.                                                     *)
(* ------------------------------------------------------------------------- *)

datatype break = Break of {size : int, extraIndent : int}

val mkBreak : int -> break

val ppBreak : break pp

val break : ppstream

val breaks : int -> ppstream

(* ------------------------------------------------------------------------- *)
(* Forced line breaks.                                                       *)
(* ------------------------------------------------------------------------- *)

val newline : ppstream

val newlines : int -> ppstream

(* ------------------------------------------------------------------------- *)
(* Pretty-printer combinators.                                               *)
(* ------------------------------------------------------------------------- *)

val ppMap : ('a -> 'b) -> 'b pp -> 'a pp

val ppBracket : string -> string -> 'a pp -> 'a pp

val ppOp : string -> ppstream

val ppOp2 : string -> 'a pp -> 'b pp -> ('a * 'b) pp

val ppOp3 : string -> string -> 'a pp -> 'b pp -> 'c pp -> ('a * 'b * 'c) pp

val ppOpList : string -> 'a pp -> 'a list pp

val ppOpStream : string -> 'a pp -> 'a Stream.stream pp

(* ------------------------------------------------------------------------- *)
(* Pretty-printers for common types.                                         *)
(* ------------------------------------------------------------------------- *)

val ppChar : char pp

val ppString : string pp

val ppEscapeString : {escape : char list} -> string pp

val ppUnit : unit pp

val ppBool : bool pp

val ppInt : int pp

val ppPrettyInt : int pp

val ppReal : real pp

val ppPercent : real pp

val ppOrder : order pp

val ppList : 'a pp -> 'a list pp

val ppStream : 'a pp -> 'a Stream.stream pp

val ppOption : 'a pp -> 'a option pp

val ppPair : 'a pp -> 'b pp -> ('a * 'b) pp

val ppTriple : 'a pp -> 'b pp -> 'c pp -> ('a * 'b * 'c) pp

val ppException : exn pp

(* ------------------------------------------------------------------------- *)
(* Pretty-printing infix operators.                                          *)
(* ------------------------------------------------------------------------- *)

type token = string

datatype assoc =
    LeftAssoc
  | NonAssoc
  | RightAssoc

datatype infixes =
    Infixes of
      {token : token,
       precedence : int,
       assoc : assoc} list

val tokensInfixes : infixes -> StringSet.set

val layerInfixes : infixes -> {tokens : StringSet.set, assoc : assoc} list

val ppInfixes :
    infixes ->
    ('a -> (token * 'a * 'a) option) -> ('a * token) pp ->
    ('a * bool) pp -> ('a * bool) pp

(* ------------------------------------------------------------------------- *)
(* Pretty-printer rendering.                                                 *)
(* ------------------------------------------------------------------------- *)

val render :
    {lineLength : int option} -> ppstream ->
    {indent : int, line : string} Stream.stream

val toStringWithLineLength :
    {lineLength : int option} -> 'a pp -> 'a -> string

val toStreamWithLineLength :
    {lineLength : int option} -> 'a pp -> 'a -> string Stream.stream

val toLine : 'a pp -> 'a -> string

(* ------------------------------------------------------------------------- *)
(* Pretty-printer rendering with a global line length.                       *)
(* ------------------------------------------------------------------------- *)

val lineLength : int ref

val toString : 'a pp -> 'a -> string

val toStream : 'a pp -> 'a -> string Stream.stream

val trace : 'a pp -> string -> 'a -> unit

end
