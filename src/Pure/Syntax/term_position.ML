(*  Title:      Pure/Syntax/term_position.ML
    Author:     Makarius

Positions within term syntax trees (non-empty list).
*)

signature TERM_POSITION =
sig
  val pretty: Position.T list -> Pretty.T
  val encode: Position.T list -> string
  val decode: string -> Position.T list
  val decode_position: term -> (Position.T list * typ) option
  val decode_position1: term -> Position.T option
  val decode_positionT: typ -> Position.T list
  val decode_positionS: sort -> Position.T list * sort
  val is_position: term -> bool
  val is_positionT: typ -> bool
  val markers: string list
  val strip_positions: term -> term
end;

structure Term_Position: TERM_POSITION =
struct

(* markup *)

val position_dummy = "<position>";
val position_text = XML.Text position_dummy;

fun pretty ps = Pretty.marks_str (map Position.markup ps, position_dummy);

fun encode_pos pos = XML.Elem (Position.markup pos, [position_text]);

fun decode_pos (XML.Elem ((name, props), [arg])) =
      if name = Markup.positionN andalso arg = position_text
      then SOME (Position.of_properties props)
      else NONE
  | decode_pos _ = NONE;

fun encode ps =
  YXML.string_of_body (map encode_pos (if null ps then [Position.none] else ps));

fun decode str =
  let
    val xml = YXML.parse_body str handle Fail msg => error msg;
    val ps = map decode_pos xml;
  in
    if not (null ps) andalso forall is_some ps then map the ps
    else if forall is_none ps then []
    else error ("Bad encoded positions: " ^ quote str)
  end;


(* positions within parse trees *)

fun decode_position (Free (x, _)) =
      (case decode x of
        [] => NONE
      | ps => SOME (ps, TFree (x, dummyS)))
  | decode_position _ = NONE;

fun decode_position1 (Free (x, _)) =
      (case decode x of
        [] => NONE
      | pos :: _ => SOME pos)
  | decode_position1 _ = NONE;

fun decode_positionT (TFree (x, _)) = decode x
  | decode_positionT _ = [];

fun decode_positionS cs =
  let val (ps, sort) = List.partition (not o null o decode) cs
  in (maps decode ps, sort) end;

val is_position = is_some o decode_position;
val is_positionT = not o null o decode_positionT;

val markers = ["_constrain", "_constrainAbs", "_ofsort"];

fun strip_positions ((t as Const (c, _)) $ u $ v) =
      if member (op =) markers c andalso is_position v
      then strip_positions u
      else t $ strip_positions u $ strip_positions v
  | strip_positions (t $ u) = strip_positions t $ strip_positions u
  | strip_positions (Abs (x, T, t)) = Abs (x, T, strip_positions t)
  | strip_positions t = t;

end;
