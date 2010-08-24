(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature SLEDGEHAMMER_UTIL =
sig
  val plural_s : int -> string
  val serial_commas : string -> string list -> string list
  val strip_spaces : string -> string
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time_option : string -> string -> Time.time option
  val scan_integer : string list -> int * string list
  val nat_subscript : int -> string
  val unyxml : string -> string
  val maybe_quote : string -> string
  val monomorphic_term : Type.tyenv -> term -> term
  val eta_expand : typ list -> term -> int -> term
  val transform_elim_term : term -> term
  val specialize_type : theory -> (string * typ) -> term -> term
  val subgoal_count : Proof.state -> int
  val strip_subgoal : thm -> int -> (string * typ) list * term list * term
  val reserved_isar_keyword_table : unit -> unit Symtab.table
end;
 
structure Sledgehammer_Util : SLEDGEHAMMER_UTIL =
struct

fun plural_s n = if n = 1 then "" else "s"

fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss

fun is_ident_char c = Char.isAlphaNum c orelse c = #"_"

fun strip_spaces_in_list [] = ""
  | strip_spaces_in_list [c1] = if Char.isSpace c1 then "" else str c1
  | strip_spaces_in_list [c1, c2] =
    strip_spaces_in_list [c1] ^ strip_spaces_in_list [c2]
  | strip_spaces_in_list (c1 :: c2 :: c3 :: cs) =
    if Char.isSpace c1 then
      strip_spaces_in_list (c2 :: c3 :: cs)
    else if Char.isSpace c2 then
      if Char.isSpace c3 then
        strip_spaces_in_list (c1 :: c3 :: cs)
      else
        str c1 ^ (if forall is_ident_char [c1, c3] then " " else "") ^
        strip_spaces_in_list (c3 :: cs)
    else
      str c1 ^ strip_spaces_in_list (c2 :: c3 :: cs)
val strip_spaces = strip_spaces_in_list o String.explode

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

fun is_head_digit s = Char.isDigit (String.sub (s, 0))
val scan_integer = Scan.many1 is_head_digit >> (the o Int.fromString o implode)

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

fun eta_expand _ t 0 = t
  | eta_expand Ts (Abs (s, T, t')) n =
    Abs (s, T, eta_expand (T :: Ts) t' (n - 1))
  | eta_expand Ts t n =
    fold_rev (fn T => fn t' => Abs ("x" ^ nat_subscript n, T, t'))
             (List.take (binder_types (fastype_of1 (Ts, t)), n))
             (list_comb (incr_boundvars n t, map Bound (n - 1 downto 0)))

(* Converts an elim-rule into an equivalent theorem that does not have the
   predicate variable. Leaves other theorems unchanged. We simply instantiate
   the conclusion variable to False. (Cf. "transform_elim_theorem" in
   "Clausifier".) *)
fun transform_elim_term t =
  case Logic.strip_imp_concl t of
    @{const Trueprop} $ Var (z, @{typ bool}) =>
    subst_Vars [(z, @{const False})] t
  | Var (z, @{typ prop}) => subst_Vars [(z, @{prop False})] t
  | _ => t

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

val subgoal_count = Logic.count_prems o prop_of o #goal o Proof.goal

fun strip_subgoal goal i =
  let
    val (t, frees) = Logic.goal_params (prop_of goal) i
    val hyp_ts = t |> Logic.strip_assums_hyp |> map (curry subst_bounds frees)
    val concl_t = t |> Logic.strip_assums_concl |> curry subst_bounds frees
  in (rev (map dest_Free frees), hyp_ts, concl_t) end

fun reserved_isar_keyword_table () =
  union (op =) (Keyword.dest_keywords ()) (Keyword.dest_commands ())
  |> map (rpair ()) |> Symtab.make

end;
