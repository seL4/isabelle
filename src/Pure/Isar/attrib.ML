(*  Title:      Pure/Isar/attrib.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Symbolic theorem attributes.
*)

signature BASIC_ATTRIB =
sig
  val print_attributes: theory -> unit
end;

signature ATTRIB =
sig
  include BASIC_ATTRIB
  val global_attribute: theory -> Args.src -> theory attribute
  val local_attribute: theory -> Args.src -> Proof.context attribute
  val add_attributes: (bstring * ((Args.src -> theory attribute) *
      (Args.src -> Proof.context attribute)) * string) list -> theory -> theory
  val syntax: (Args.T list -> 'a * Args.T list) -> ('a -> 'b) -> Args.src -> 'b
  val no_args: 'a attribute -> Args.src -> 'a attribute
  val thm_args: ('a -> string list -> tthm list)
    -> (tthm list -> 'a attribute) -> Args.src -> 'a attribute
  val global_thm_args: (tthm list -> theory attribute) -> Args.src -> theory attribute
  val local_thm_args: (tthm list -> Proof.context attribute)
    -> Args.src -> Proof.context attribute
  val setup: (theory -> theory) list
end;

structure Attrib: ATTRIB =
struct


(** attributes theory data **)

(* data kind 'Isar/attributes' *)

structure AttributesDataArgs =
struct
  val name = "Isar/attributes";
  type T =
    {space: NameSpace.T,
     attrs:
       ((((Args.src -> theory attribute) * (Args.src -> Proof.context attribute))
         * string) * stamp) Symtab.table};

  val empty = {space = NameSpace.empty, attrs = Symtab.empty};
  val prep_ext = I;

  fun merge ({space = space1, attrs = attrs1}, {space = space2, attrs = attrs2}) =
    {space = NameSpace.merge (space1, space2),
      attrs = Symtab.merge eq_snd (attrs1, attrs2) handle Symtab.DUPS dups =>
        error ("Attempt to merge different versions of attributes " ^ commas_quote dups)};

  fun print _ ({space, attrs}) =
    let
      fun prt_attr (name, ((_, comment), _)) = Pretty.block
        [Pretty.str (NameSpace.cond_extern space name ^ ":"), Pretty.brk 2, Pretty.str comment];
    in
      Pretty.writeln (Display.pretty_name_space ("attribute name space", space));
      Pretty.writeln (Pretty.big_list "attributes:" (map prt_attr (Symtab.dest attrs)))
    end;
end;

structure AttributesData = TheoryDataFun(AttributesDataArgs);
val print_attributes = AttributesData.print;


(* get global / local attributes *)

fun gen_attribute which thy =
  let
    val {space, attrs} = AttributesData.get thy;

    fun attr ((raw_name, args), pos) =
      let val name = NameSpace.intern space raw_name in
        (case Symtab.lookup (attrs, name) of
          None => error ("Unknown attribute: " ^ quote name ^ Position.str_of pos)
        | Some ((p, _), _) => which p ((name, args), pos))
      end;
  in attr end;

val global_attribute = gen_attribute fst;
val local_attribute = gen_attribute snd;


(* add_attributes *)

fun add_attributes raw_attrs thy =
  let
    val full = Sign.full_name (Theory.sign_of thy);
    val new_attrs =
      map (fn (name, (f, g), comment) => (full name, (((f, g), comment), stamp ()))) raw_attrs;

    val {space, attrs} = AttributesData.get thy;
    val space' = NameSpace.extend (space, map fst new_attrs);
    val attrs' = Symtab.extend (attrs, new_attrs) handle Symtab.DUPS dups =>
      error ("Duplicate declaration of attributes(s) " ^ commas_quote dups);
  in thy |> AttributesData.put {space = space', attrs = attrs'} end;


(* attribute syntax *)

val attributeN = "attribute";
fun syntax scan = Args.syntax attributeN scan;

fun no_args x = syntax (Scan.succeed x) I;

fun thm_args get f = syntax (Scan.repeat Args.name)
  (fn names => fn (x, ths) => f (get x names) (x, ths));

fun global_thm_args f = thm_args PureThy.get_tthmss f;
fun local_thm_args f = thm_args ProofContext.get_tthmss f;



(** Pure attributes **)

(* tags *)

fun gen_tag x = syntax (Args.name -- Scan.repeat Args.name) Attribute.tag x;
fun gen_untag x = syntax (Args.name -- Scan.repeat Args.name) Attribute.untag x;
fun gen_lemma x = no_args Attribute.tag_lemma x;
fun gen_assumption x = no_args Attribute.tag_assumption x;


(* resolution *)

fun gen_RS get = syntax Args.name
  (fn name => fn (x, (thm, tags)) => (x, (thm RS (Attribute.thm_of (get x name)), tags)));

fun RS_global x = gen_RS PureThy.get_tthm x;
fun RS_local x = gen_RS ProofContext.get_tthm x;


(* pure_attributes *)

val pure_attributes =
 [("tag", (gen_tag, gen_tag), "tag theorem"),
  ("untag", (gen_untag, gen_untag), "untag theorem"),
  ("lemma", (gen_lemma, gen_lemma), "tag as lemma"),
  ("assumption", (gen_assumption, gen_assumption), "tag as assumption"),
  ("RS", (RS_global, RS_local), "resolve with rule")];



(** theory setup **)

val setup = [AttributesData.init, add_attributes pure_attributes];


end;


structure BasicAttrib: BASIC_ATTRIB = Attrib;
open BasicAttrib;
