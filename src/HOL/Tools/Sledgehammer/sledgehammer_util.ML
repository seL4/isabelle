(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature SLEDGEHAMMER_UTIL =
sig
  val plural_s : int -> string
  val serial_commas : string -> string list -> string list
  val timestamp : unit -> string
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time_option : string -> string -> Time.time option
  val nat_subscript : int -> string
  val unyxml : string -> string
  val maybe_quote : string -> string
  val monomorphic_term : Type.tyenv -> term -> term
  val specialize_type : theory -> (string * typ) -> term -> term
end;
 
structure Sledgehammer_Util : SLEDGEHAMMER_UTIL =
struct

fun plural_s n = if n = 1 then "" else "s"

fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss

val timestamp = Date.fmt "%Y-%m-%d %H:%M:%S" o Date.fromTimeLocal o Time.now

fun parse_bool_option option name s =
  (case s of
     "smart" => if option then NONE else raise Option
   | "false" => SOME false
   | "true" => SOME true
   | "" => SOME true
   | _ => raise Option)
  handle Option.Option =>
         let val ss = map quote ((option ? cons "smart") ["true", "false"]) in
           error ("Parameter " ^ quote name ^ " must be assigned " ^
                  space_implode " " (serial_commas "or" ss) ^ ".")
         end

fun parse_time_option _ "none" = NONE
  | parse_time_option name s =
    let
      val msecs =
        case space_explode " " s of
          [s1, "min"] => 60000 * the (Int.fromString s1)
        | [s1, "s"] => 1000 * the (Int.fromString s1)
        | [s1, "ms"] => the (Int.fromString s1)
        | _ => 0
    in
      if msecs <= 0 then
        error ("Parameter " ^ quote name ^ " must be assigned a positive time \
               \value (e.g., \"60 s\", \"200 ms\") or \"none\".")
      else
        SOME (Time.fromMilliseconds msecs)
    end

val subscript = implode o map (prefix "\<^isub>") o explode
fun nat_subscript n =
  n |> string_of_int |> print_mode_active Symbol.xsymbolsN ? subscript

fun plain_string_from_xml_tree t =
  Buffer.empty |> XML.add_content t |> Buffer.content
val unyxml = plain_string_from_xml_tree o YXML.parse

val is_long_identifier = forall Syntax.is_identifier o space_explode "."
fun maybe_quote y =
  let val s = unyxml y in
    y |> ((not (is_long_identifier (perhaps (try (unprefix "'")) s)) andalso
           not (is_long_identifier (perhaps (try (unprefix "?")) s))) orelse
           Keyword.is_keyword s) ? quote
  end

fun monomorphic_term subst t =
  map_types (map_type_tvar (fn v =>
      case Type.lookup subst v of
        SOME typ => typ
      | NONE => raise TERM ("monomorphic_term: uninstanitated schematic type \
                            \variable", [t]))) t

fun specialize_type thy (s, T) t =
  let
    fun subst_for (Const (s', T')) =
      if s = s' then
        SOME (Sign.typ_match thy (T', T) Vartab.empty)
        handle Type.TYPE_MATCH => NONE
      else
        NONE
    | subst_for (t1 $ t2) =
      (case subst_for t1 of SOME x => SOME x | NONE => subst_for t2)
    | subst_for (Abs (_, _, t')) = subst_for t'
    | subst_for _ = NONE
  in
    case subst_for t of
      SOME subst => monomorphic_term subst t
    | NONE => raise Type.TYPE_MATCH
  end


end;
