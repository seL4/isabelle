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
end;

signature ATTRIBUTE =
sig
  include BASIC_ATTRIBUTE
  val thm_of: tthm -> thm
  val tthm_of: thm -> tthm
  val none: 'a -> 'a * 'b attribute list
  val no_attrs: 'a * 'b -> ('a * ('b * tag list)) * 'c attribute list
  val no_attrss: 'a * 'b list -> ('a * ('b * tag list) list) * 'c attribute list
  val fail: string -> string -> 'a
  val apply: ('a * tthm) * 'a attribute list -> ('a * tthm)
  val applys: ('a * tthm list) * 'a attribute list -> ('a * tthm list)
  val pretty_tthm: tthm -> Pretty.T
  val tag: tag -> 'a attribute
  val untag: tag -> 'a attribute
  val lemma: tag
  val assumption: tag
  val tag_lemma: 'a attribute
  val tag_assumption: 'a attribute
end;

structure Attribute: ATTRIBUTE =
struct


(** tags and attributes **)

type tag = string * string list;
type tthm = thm * tag list;
type 'a attribute = 'a * tthm -> 'a * tthm;

fun thm_of (thm, _) = thm;
fun tthm_of thm = (thm, []);

fun none x = (x, []);
fun no_attrs (x, y) = ((x, (y, [])), []);
fun no_attrss (x, ys) = ((x, map (rpair []) ys), []);


(* apply attributes *)

exception FAIL of string * string;

fun fail name msg = raise FAIL (name, msg);

(* FIXME error (!!?), push up the warning (??) *)
fun warn_failed (name, msg) =
  warning ("Failed invocation of " ^ quote name ^ " attribute: " ^ msg);

fun apply (x_th, []) = x_th
  | apply (x_th, f :: fs) = apply (f x_th handle FAIL info => (warn_failed info; x_th), fs);

fun applys ((x, []), _) = (x, [])
  | applys ((x, th :: ths), atts) =
      let
        val (x', th') = apply ((x, th), atts);
        val (x'', ths') = applys ((x', ths), atts);
      in (x'', th' :: ths') end;


(* display tagged theorems *)

fun pretty_tag (name, []) = Pretty.str name
  | pretty_tag (name, args) = Pretty.block
      [Pretty.str name, Pretty.list "(" ")" (map Pretty.str args)];

val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_tthm (thm, []) = Pretty.quote (Display.pretty_thm thm)
  | pretty_tthm (thm, tags) = Pretty.block
      [Pretty.quote (Display.pretty_thm thm), Pretty.brk 1, pretty_tags tags];


(* basic attributes *)

fun tag tg (x, (thm, tags)) = (x, (thm, tg ins tags));
fun untag tg (x, (thm, tags)) = (x, (thm, tags \ tg));

val lemma = ("lemma", []);
val assumption = ("assumption", []);
fun tag_lemma x = tag lemma x;
fun tag_assumption x = tag assumption x;


end;


structure BasicAttribute: BASIC_ATTRIBUTE = Attribute;
open BasicAttribute;
