(*  Title:      HOL/Tools/Nunchaku/nunchaku_util.ML
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

General-purpose functions used by Nunchaku.
*)

signature NUNCHAKU_UTIL =
sig
  val elide_string: int -> string -> string
  val nat_subscript: int -> string
  val timestamp: unit -> string
  val parse_bool_option: bool -> string -> string -> bool option
  val parse_time: string -> string -> Time.time
  val string_of_time: Time.time -> string
  val simplify_spaces: string -> string
  val ascii_of: string -> string
  val unascii_of: string -> string
  val double_lookup: ('a * 'a -> bool) -> ('a option * 'b) list -> 'a -> 'b option
  val triple_lookup: (''a * ''a -> bool) -> (''a option * 'b) list -> ''a -> 'b option
  val plural_s_for_list: 'a list -> string
  val with_overlord_file: string -> string -> (Path.T -> 'a) -> 'a
  val with_tmp_or_overlord_file: bool -> string -> string -> (Path.T -> 'a) -> 'a
  val num_binder_types: typ -> int
  val strip_fun_type: typ -> typ list * typ
  val attach_typeS: term -> term
  val specialize_type: theory -> string * typ -> term -> term
  val typ_match: theory -> typ * typ -> bool
  val term_match: theory -> term * term -> bool
  val const_match: theory -> (string * typ) * (string * typ) -> bool
  val DETERM_TIMEOUT: Time.time -> tactic -> tactic
  val spying: bool -> (unit -> Proof.state * int * string) -> unit
end;

structure Nunchaku_Util : NUNCHAKU_UTIL =
struct

val elide_string = ATP_Util.elide_string;
val nat_subscript = Nitpick_Util.nat_subscript;
val timestamp = ATP_Util.timestamp;

val parse_bool_option = Sledgehammer_Util.parse_bool_option;
val parse_time = Sledgehammer_Util.parse_time;
val string_of_time = ATP_Util.string_of_time;
val simplify_spaces = Sledgehammer_Util.simplify_spaces;
val ascii_of = ATP_Problem_Generate.ascii_of;
val unascii_of = ATP_Problem_Generate.unascii_of;
val double_lookup = Nitpick_Util.double_lookup;
val triple_lookup = Nitpick_Util.triple_lookup;
val plural_s_for_list = Nitpick_Util.plural_s_for_list;

fun with_overlord_file name ext f =
  f (Path.explode ("$ISABELLE_HOME_USER/" ^ name ^ "." ^ ext));

fun with_tmp_or_overlord_file overlord =
  if overlord then with_overlord_file else Isabelle_System.with_tmp_file;

val num_binder_types = BNF_Util.num_binder_types
val strip_fun_type = BNF_Util.strip_fun_type;

(* Clone from "HOL/Tools/inductive_realizer.ML". *)
val attach_typeS =
  map_types (map_atyps
    (fn TFree (s, []) => TFree (s, \<^sort>\<open>type\<close>)
      | TVar (ixn, []) => TVar (ixn, \<^sort>\<open>type\<close>)
      | T => T));

val specialize_type = ATP_Util.specialize_type;

fun typ_match thy TU = can (Sign.typ_match thy TU) Vartab.empty;
fun term_match thy tu = can (Pattern.match thy tu) (Vartab.empty, Vartab.empty);
fun const_match thy = term_match thy o apply2 Const;

val DETERM_TIMEOUT = Nitpick_Util.DETERM_TIMEOUT;

val spying_version = "a"

val hackish_string_of_term = Sledgehammer_Util.hackish_string_of_term;

fun spying spy f =
  if spy then
    let
      val (state, i, message) = f ();
      val ctxt = Proof.context_of state;
      val goal = Logic.get_goal (Thm.prop_of (#goal (Proof.goal state))) i;
      val hash =
        String.substring (SHA1.rep (SHA1.digest (hackish_string_of_term ctxt goal)), 0, 12);
    in
      File.append (Path.explode "$ISABELLE_HOME_USER/spy_nunchaku")
        (spying_version ^ " " ^ timestamp () ^ ": " ^ hash ^ ": " ^ message ^ "\n")
    end
  else
    ();

end;
