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
(* A type of strings annotated with their size.                              *)
(* ------------------------------------------------------------------------- *)

type stringSize = string * int

val mkStringSize : string -> stringSize

(* ------------------------------------------------------------------------- *)
(* A type of pretty-printers.                                                *)
(* ------------------------------------------------------------------------- *)

datatype breakStyle = Consistent | Inconsistent

datatype step =
    BeginBlock of breakStyle * int
  | EndBlock
  | AddString of stringSize
  | AddBreak of int
  | AddNewline

type ppstream = step Stream.stream

(* ------------------------------------------------------------------------- *)
(* Pretty-printer primitives.                                                *)
(* ------------------------------------------------------------------------- *)

val beginBlock : breakStyle -> int -> ppstream

val endBlock : ppstream

val addString : stringSize -> ppstream

val addBreak : int -> ppstream

val addNewline : ppstream

val skip : ppstream

val sequence : ppstream -> ppstream -> ppstream

val duplicate : int -> ppstream -> ppstream

val program : ppstream list -> ppstream

val stream : ppstream Stream.stream -> ppstream

val block : breakStyle -> int -> ppstream -> ppstream

val blockProgram : breakStyle -> int -> ppstream list -> ppstream

(* ------------------------------------------------------------------------- *)
(* Executing pretty-printers to generate lines.                              *)
(* ------------------------------------------------------------------------- *)

val execute :
    {lineLength : int} -> ppstream ->
    {indent : int, line : string} Stream.stream

(* ------------------------------------------------------------------------- *)
(* Pretty-printer combinators.                                               *)
(* ------------------------------------------------------------------------- *)

type 'a pp = 'a -> ppstream

val ppMap : ('a -> 'b) -> 'b pp -> 'a pp

val ppString : string pp

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

val ppBreakStyle : breakStyle pp

val ppStep : step pp

val ppPpstream : ppstream pp

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
(* Executing pretty-printers with a global line length.                      *)
(* ------------------------------------------------------------------------- *)

val lineLength : int ref

val toString : 'a pp -> 'a -> string

val toStream : 'a pp -> 'a -> string Stream.stream

val trace : 'a pp -> string -> 'a -> unit

end
