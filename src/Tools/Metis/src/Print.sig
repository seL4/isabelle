(* ========================================================================= *)
(* PRETTY-PRINTING                                                           *)
(* Copyright (c) 2001-2008 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Print =
sig

(* ------------------------------------------------------------------------- *)
(* A type of pretty-printers.                                                *)
(* ------------------------------------------------------------------------- *)

datatype breakStyle = Consistent | Inconsistent

datatype ppStep =
    BeginBlock of breakStyle * int
  | EndBlock
  | AddString of string
  | AddBreak of int
  | AddNewline

type ppstream = ppStep Stream.stream

type 'a pp = 'a -> ppstream

(* ------------------------------------------------------------------------- *)
(* Pretty-printer primitives.                                                *)
(* ------------------------------------------------------------------------- *)

val beginBlock : breakStyle -> int -> ppstream

val endBlock : ppstream

val addString : string -> ppstream

val addBreak : int -> ppstream

val addNewline : ppstream

val skip : ppstream

val sequence : ppstream -> ppstream -> ppstream

val duplicate : int -> ppstream -> ppstream

val program : ppstream list -> ppstream

val stream : ppstream Stream.stream -> ppstream

val block : breakStyle -> int -> ppstream -> ppstream

val blockProgram : breakStyle -> int -> ppstream list -> ppstream

val bracket : string -> string -> ppstream -> ppstream

val field : string -> ppstream -> ppstream

val record : (string * ppstream) list -> ppstream

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

val ppBreakStyle : breakStyle pp

val ppPpStep : ppStep pp

val ppPpstream : ppstream pp

(* ------------------------------------------------------------------------- *)
(* Pretty-printing infix operators.                                          *)
(* ------------------------------------------------------------------------- *)

datatype infixes =
    Infixes of
      {token : string,
       precedence : int,
       leftAssoc : bool} list

val tokensInfixes : infixes -> StringSet.set

val layerInfixes :
    infixes ->
    {tokens : {leftSpaces : int, token : string, rightSpaces : int} list,
     leftAssoc : bool} list

val ppInfixes :
    infixes -> ('a -> (string * 'a * 'a) option) -> ('a * bool) pp ->
    ('a * bool) pp

(* ------------------------------------------------------------------------- *)
(* Executing pretty-printers to generate lines.                              *)
(* ------------------------------------------------------------------------- *)

val execute : {lineLength : int} -> ppstream -> string Stream.stream

(* ------------------------------------------------------------------------- *)
(* Executing pretty-printers with a global line length.                      *)
(* ------------------------------------------------------------------------- *)

val lineLength : int ref

val toString : 'a pp -> 'a -> string

val toStream : 'a pp -> 'a -> string Stream.stream

val trace : 'a pp -> string -> 'a -> unit

end
