(*  Title:      Pure/attribute.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theorem tags and attributes.
*)

signature BASIC_ATTRIBUTE =
sig
  type tag
  type tthm
  type 'a attribute
  val show_tags: bool ref
end;

signature ATTRIBUTE =
sig
  include BASIC_ATTRIBUTE
  val thm_of: tthm -> thm
  val tthm_of: thm -> tthm
  val thms_of: tthm list -> thm list
  val tthms_of: thm list -> tthm list
  val rule: ('a -> thm -> thm) -> 'a attribute
  val none: 'a -> 'a * 'b attribute list
  val no_attrs: 'a * 'b -> ('a * ('b * tag list)) * 'c attribute list
  val no_attrss: 'a * 'b list -> ('a * ('b * tag list) list) * 'c attribute list
  val apply: ('a * tthm) * 'a attribute list -> ('a * tthm)
  val applys: ('a * tthm list) * 'a attribute list -> ('a * tthm list)
  val pretty_tthm: tthm -> Pretty.T
  val pretty_tthms: tthm list -> Pretty.T
  val print_tthm: tthm -> unit
  val print_tthms: tthm list -> unit
  val tag: tag -> 'a attribute
  val untag: tag -> 'a attribute
  val lemma: tag
  val assumption: tag
  val internal: tag
  val tag_lemma: 'a attribute
  val tag_assumption: 'a attribute
  val tag_internal: 'a attribute
end;

structure Attribute: ATTRIBUTE =
struct


(** tags and attributes **)

type tag = string * string list;
type tthm = thm * tag list;
type 'a attribute = 'a * tthm -> 'a * tthm;

fun thm_of (thm, _) = thm;
fun tthm_of thm = (thm, []);

fun thms_of ths = map thm_of ths;
fun tthms_of ths = map tthm_of ths;

fun rule f (x, (thm, _)) = (x, (f x thm, []));

fun none x = (x, []);
fun no_attrs (x, y) = ((x, (y, [])), []);
fun no_attrss (x, ys) = ((x, map (rpair []) ys), []);


(* apply attributes *)

fun apply (x_th, atts) = Library.apply atts x_th;
fun applys (x_ths, atts) = foldl_map (Library.apply atts) x_ths;


(* display tagged theorems *)

val show_tags = ref false;

fun pretty_tag (name, args) = Pretty.strs (name :: args);
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_tthm (thm, tags) =
  if null tags orelse not (! show_tags) then Pretty.quote (Display.pretty_thm thm)
  else Pretty.block [Pretty.quote (Display.pretty_thm thm), Pretty.brk 1, pretty_tags tags];

fun pretty_tthms [th] = pretty_tthm th
  | pretty_tthms ths = Pretty.block (Pretty.fbreaks (map pretty_tthm ths));

val print_tthm = Pretty.writeln o pretty_tthm;
val print_tthms = Pretty.writeln o pretty_tthms;


(* basic attributes *)

fun tag tg (x, (thm, tags)) = (x, (thm, if tg mem tags then tags else tags @ [tg]));
fun untag tg (x, (thm, tags)) = (x, (thm, tags \ tg));

val lemma = ("lemma", []);
val assumption = ("assumption", []);
val internal = ("internal", []);
fun tag_lemma x = tag lemma x;
fun tag_assumption x = tag assumption x;
fun tag_internal x = tag internal x;


end;


structure BasicAttribute: BASIC_ATTRIBUTE = Attribute;
open BasicAttribute;
