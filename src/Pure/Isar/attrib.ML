(*  Title:      Pure/Isar/attrib.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Symbolic theorem attributes.
*)

signature BASIC_ATTRIB =
sig
  val print_attributes: theory -> unit
  val Attribute: bstring -> (Args.src -> theory attribute) * (Args.src -> Proof.context attribute)
    -> string -> unit
end;

signature ATTRIB =
sig
  include BASIC_ATTRIB
  val global_attribute: theory -> Args.src -> theory attribute
  val local_attribute: theory -> Args.src -> Proof.context attribute
  val add_attributes: (bstring * ((Args.src -> theory attribute) *
      (Args.src -> Proof.context attribute)) * string) list -> theory -> theory
  val global_thm: theory * Args.T list -> tthm * (theory * Args.T list)
  val global_thms: theory * Args.T list -> tthm list * (theory * Args.T list)
  val global_thmss: theory * Args.T list -> tthm list * (theory * Args.T list)
  val local_thm: Proof.context * Args.T list -> tthm * (Proof.context * Args.T list)
  val local_thms: Proof.context * Args.T list -> tthm list * (Proof.context * Args.T list)
  val local_thmss: Proof.context * Args.T list -> tthm list * (Proof.context * Args.T list)
  val syntax: ('a * Args.T list -> 'a attribute * ('a * Args.T list)) -> Args.src -> 'a attribute
  val no_args: 'a attribute -> Args.src -> 'a attribute
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

    fun attr src =
      let
        val ((raw_name, _), pos) = Args.dest_src src;
        val name = NameSpace.intern space raw_name;
      in
        (case Symtab.lookup (attrs, name) of
          None => error ("Unknown attribute: " ^ quote name ^ Position.str_of pos)
        | Some ((p, _), _) => which p src)
      end;
  in attr end;

val global_attribute = gen_attribute fst;
val local_attribute = gen_attribute snd;
val local_attribute' = local_attribute o ProofContext.theory_of;


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

(*implicit version*)
fun Attribute name att cmt = Context.>> (add_attributes [(name, att, cmt)]);



(** attribute parsers **)

(* tags *)

fun tag x = Scan.lift (Args.name -- Scan.repeat Args.name) x;


(* theorems *)

fun gen_thm get attrib app =
  Scan.depend (fn st => Args.name -- Args.opt_attribs >>
    (fn (name, srcs) => app ((st, get st name), map (attrib st) srcs)));

val global_thm = gen_thm PureThy.get_tthm global_attribute Attribute.apply;
val global_thms = gen_thm PureThy.get_tthms global_attribute Attribute.applys;
val global_thmss = Scan.repeat global_thms >> flat;

val local_thm = gen_thm ProofContext.get_tthm local_attribute' Attribute.apply;
val local_thms = gen_thm ProofContext.get_tthms local_attribute' Attribute.applys;
val local_thmss = Scan.repeat local_thms >> flat;



(** attribute syntax **)

fun syntax scan src (st, th) =
  let val (st', f) = Args.syntax "attribute" scan st src
  in f (st', th) end;

fun no_args x = syntax (Scan.succeed x);



(** Pure attributes **)

(* tags *)

fun gen_tag x = syntax (tag >> Attribute.tag) x;
fun gen_untag x = syntax (tag >> Attribute.untag) x;
fun gen_lemma x = no_args Attribute.tag_lemma x;
fun gen_assumption x = no_args Attribute.tag_assumption x;


(* transfer *)

fun gen_transfer theory_of = no_args (Attribute.rule (fn st => Thm.transfer (theory_of st)));

val global_transfer = gen_transfer I;
val local_transfer = gen_transfer ProofContext.theory_of;


(* RS *)

fun resolve (i, B) (x, A) =
  (x, Attribute.tthm_of (Attribute.thm_of A RSN (i, Attribute.thm_of B)));

fun gen_RS thm = syntax (Scan.lift (Scan.optional Args.nat 1) -- thm >> resolve);
val global_RS = gen_RS global_thm;
val local_RS = gen_RS local_thm;


(* APP *)

fun apply Bs (x, A) =
  (x, Attribute.tthm_of (Attribute.thms_of Bs MRS Attribute.thm_of A));

val global_APP = syntax (global_thmss >> apply);
val local_APP = syntax (local_thmss >> apply);


(* instantiations *)

(* FIXME assumes non var hyps *)  (* FIXME move (see also drule.ML) *)
val add_vars = foldl_aterms (fn (vs, Var v) => v ins vs | (vs, _) => vs);
fun vars_of thm = (add_vars ([], #prop (Thm.rep_thm thm)));

fun read_instantiate context_of raw_insts x thm =
  let
    val ctxt = context_of x;
    val sign = ProofContext.sign_of ctxt;

    val vars = vars_of thm;
    fun get_typ xi =
      (case assoc (vars, xi) of
        Some T => T
      | None => error ("No such variable in theorem: " ^ Syntax.string_of_vname xi));

    val (xs, ss) = Library.split_list raw_insts;
    val Ts = map get_typ xs;

    (* FIXME really declare_thm (!!!!??????) *)
    val (ts, envT) = ProofContext.read_termTs (ctxt |> ProofContext.declare_thm thm) (ss ~~ Ts);

    val cenvT = map (apsnd (Thm.ctyp_of sign)) envT;
    val cenv = map2 (fn (xi, t) => pairself (Thm.cterm_of sign) (Var (xi, fastype_of t), t)) (xs, ts);
  in Thm.instantiate (cenvT, cenv) thm end;


val insts = Scan.lift (Args.enum1 "and" (Args.var --| Args.$$$ "=" -- Args.name));
fun gen_where context_of = syntax (insts >> (Attribute.rule o read_instantiate context_of));

val global_where = gen_where ProofContext.init;
val local_where = gen_where I;


(* misc rules *)

fun standard x = no_args (Attribute.rule (K Drule.standard)) x;
fun elimify x = no_args (Attribute.rule (K Tactic.make_elim)) x;



(** theory setup **)

(* pure_attributes *)

val pure_attributes =
 [("tag", (gen_tag, gen_tag), "tag theorem"),
  ("untag", (gen_untag, gen_untag), "untag theorem"),
  ("lemma", (gen_lemma, gen_lemma), "tag as lemma"),
  ("assumption", (gen_assumption, gen_assumption), "tag as assumption"),
  ("RS", (global_RS, local_RS), "resolve with rule"),
  ("APP", (global_APP, local_APP), "resolve rule with"),
  ("where", (global_where, local_where), "instantiate theorem (named vars)"),
  ("standard", (standard, standard), "put theorem into standard form"),
  ("elimify", (elimify, elimify), "turn destruct rule into elimination rule"),
  ("transfer", (global_transfer, local_transfer), "transfer theorem to this theory")];


(* setup *)

val setup = [AttributesData.init, add_attributes pure_attributes];


end;


structure BasicAttrib: BASIC_ATTRIB = Attrib;
open BasicAttrib;
