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
  val print_attributes: theory -> unit
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
  val setup: (theory -> theory) list
  val global_attr: theory -> (xstring * string list) -> theory attribute
  val local_attr: theory -> (xstring * string list) -> local_theory attribute
  val add_attributes: (bstring * (string list -> theory attribute) *
      (string list -> local_theory attribute) * string) list -> theory -> theory
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



(** theory data **)

(* data kind 'attributes' *)

local
  val attributesK = Object.kind "Pure/attributes";

  exception Attributes of
    {space: NameSpace.T,
     attrs:
       ((((string list -> theory attribute) * (string list -> local_theory attribute))
         * string) * stamp) Symtab.table};


  val empty = Attributes {space = NameSpace.empty, attrs = Symtab.empty};

  fun prep_ext (x as Attributes _) = x;

  fun merge (Attributes {space = space1, attrs = attrs1},
      Attributes {space = space2, attrs = attrs2}) =
    Attributes {
      space = NameSpace.merge (space1, space2),
      attrs = Symtab.merge eq_snd (attrs1, attrs2) handle Symtab.DUPS dups =>
        error ("Attempt to merge different versions of attributes " ^ commas_quote dups)};

  fun pretty_attr (name, ((_, comment), _)) = Pretty.block
    [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];

  fun print _ (Attributes {space, attrs}) =
   (Pretty.writeln (Display.pretty_name_space ("attribute name space", space));
    Pretty.writeln (Pretty.big_list "attributes:" (map pretty_attr (Symtab.dest attrs))));
in
  val init_attributes = Theory.init_data attributesK (empty, prep_ext, merge, print);
  val print_attributes = Theory.print_data attributesK;
  val get_attributes = Theory.get_data attributesK (fn Attributes x => x);
  val put_attributes = Theory.put_data attributesK Attributes;
end;


(* get global / local attributes *)

fun gen_attr which thy =
  let
    val {space, attrs} = get_attributes thy;
    val intern = NameSpace.intern space;

    fun attr (raw_name, args) x_th =
      (case Symtab.lookup (attrs, intern raw_name) of
        None => raise FAIL (intern raw_name, "unknown attribute")
      | Some ((p, _), _) => which p args x_th);
  in attr end;

val global_attr = gen_attr fst;
val local_attr = gen_attr snd;


(* add_attributes *)

fun add_attributes raw_attrs thy =
  let
    val full = Sign.full_name (Theory.sign_of thy);
    val new_attrs =
      map (fn (name, f, g, comment) => (full name, (((f, g), comment), stamp ()))) raw_attrs;

    val {space, attrs} = get_attributes thy;
    val space' = NameSpace.extend (space, map fst new_attrs);
    val attrs' = Symtab.extend (attrs, new_attrs) handle Symtab.DUPS dups =>
      error ("Duplicate declaration of attributes(s) " ^ commas_quote dups);
  in
    thy |> put_attributes {space = space', attrs = attrs'}
  end;


(* setup *)	(* FIXME add_attributes: lemma etc. *)

val setup =
 [init_attributes];


end;


structure BasicAttribute: BASIC_ATTRIBUTE = Attribute;
open BasicAttribute;
