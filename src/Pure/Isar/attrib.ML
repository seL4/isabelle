(*  Title:      Pure/Isar/attrib.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

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
  exception ATTRIB_FAIL of (string * Position.T) * exn
  val global_attribute: theory -> Args.src -> theory attribute
  val local_attribute: theory -> Args.src -> Proof.context attribute
  val local_attribute': Proof.context -> Args.src -> Proof.context attribute
  val undef_global_attribute: theory attribute
  val undef_local_attribute: Proof.context attribute
  val add_attributes: (bstring * ((Args.src -> theory attribute) *
      (Args.src -> Proof.context attribute)) * string) list -> theory -> theory
  val global_thm: theory * Args.T list -> thm * (theory * Args.T list)
  val global_thms: theory * Args.T list -> thm list * (theory * Args.T list)
  val global_thmss: theory * Args.T list -> thm list * (theory * Args.T list)
  val local_thm: Proof.context * Args.T list -> thm * (Proof.context * Args.T list)
  val local_thms: Proof.context * Args.T list -> thm list * (Proof.context * Args.T list)
  val local_thmss: Proof.context * Args.T list -> thm list * (Proof.context * Args.T list)
  val syntax: ('a * Args.T list -> 'a attribute * ('a * Args.T list)) -> Args.src -> 'a attribute
  val no_args: 'a attribute -> Args.src -> 'a attribute
  val add_del_args: 'a attribute -> 'a attribute -> Args.src -> 'a attribute
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
  val copy = I;
  val prep_ext = I;

  fun merge ({space = space1, attrs = attrs1}, {space = space2, attrs = attrs2}) =
    {space = NameSpace.merge (space1, space2),
      attrs = Symtab.merge eq_snd (attrs1, attrs2) handle Symtab.DUPS dups =>
        error ("Attempt to merge different versions of attributes " ^ commas_quote dups)};

  fun print _ {space, attrs} =
    let
      fun prt_attr (name, ((_, comment), _)) = Pretty.block
        [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    in
      [Pretty.big_list "attributes:" (map prt_attr (NameSpace.cond_extern_table space attrs))]
      |> Pretty.chunks |> Pretty.writeln
    end;
end;

structure AttributesData = TheoryDataFun(AttributesDataArgs);
val print_attributes = AttributesData.print;


(* get global / local attributes *)

exception ATTRIB_FAIL of (string * Position.T) * exn;

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
        | Some ((p, _), _) => transform_failure (curry ATTRIB_FAIL (name, pos)) (which p src))
      end;
  in attr end;

val global_attribute = gen_attribute fst;
val local_attribute = gen_attribute snd;
val local_attribute' = local_attribute o ProofContext.theory_of;

val undef_global_attribute: theory attribute =
  fn _ => error "attribute undefined in theory context";

val undef_local_attribute: Proof.context attribute =
  fn _ => error "attribute undefined in proof context";


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

val global_thm = gen_thm PureThy.get_thm global_attribute Thm.apply_attributes;
val global_thms = gen_thm PureThy.get_thms global_attribute Thm.applys_attributes;
val global_thmss = Scan.repeat global_thms >> flat;

val local_thm = gen_thm ProofContext.get_thm local_attribute' Thm.apply_attributes;
val local_thms = gen_thm ProofContext.get_thms local_attribute' Thm.applys_attributes;
val local_thmss = Scan.repeat local_thms >> flat;



(** attribute syntax **)

fun syntax scan src (st, th) =
  let val (st', f) = Args.syntax "attribute" scan src st
  in f (st', th) end;

fun no_args x = syntax (Scan.succeed x);

fun add_del_args add del x =
  syntax (Scan.lift (Args.$$$ "add" >> K add || Args.$$$ "del" >> K del || Scan.succeed add)) x;



(** Pure attributes **)

(* tags *)

fun gen_tagged x = syntax (tag >> Drule.tag) x;
fun gen_untagged x = syntax (Scan.lift Args.name >> Drule.untag) x;


(* COMP *)

fun comp (i, B) (x, A) = (x, Drule.compose_single (A, i, B));

fun gen_COMP thm = syntax (Scan.lift (Scan.optional Args.nat 1) -- thm >> comp);
val COMP_global = gen_COMP global_thm;
val COMP_local = gen_COMP local_thm;


(* RS *)

fun resolve (i, B) (x, A) = (x, A RSN (i, B));

fun gen_RS thm = syntax (Scan.lift (Scan.optional Args.nat 1) -- thm >> resolve);
val RS_global = gen_RS global_thm;
val RS_local = gen_RS local_thm;


(* OF *)

fun apply Bs (x, A) = (x, Bs MRS A);

val OF_global = syntax (global_thmss >> apply);
val OF_local = syntax (local_thmss >> apply);


(* where: named instantiations *)

fun read_instantiate context_of insts x thm =
  let
    val ctxt = context_of x;
    val sign = ProofContext.sign_of ctxt;

    val vars = Drule.vars_of thm;
    fun get_typ xi =
      (case assoc (vars, xi) of
        Some T => T
      | None => error ("No such variable in theorem: " ^ Syntax.string_of_vname xi));

    val (xs, ss) = Library.split_list insts;
    val Ts = map get_typ xs;

    val (ts, envT) = ProofContext.read_termTs ctxt (ss ~~ Ts);
    val cenvT = map (apsnd (Thm.ctyp_of sign)) envT;
    val cenv =
      map (fn (xi, t) => pairself (Thm.cterm_of sign) (Var (xi, fastype_of t), t))
        (gen_distinct (fn ((x1, t1), (x2, t2)) => x1 = x2 andalso t1 aconv t2) (xs ~~ ts));
  in Drule.instantiate (cenvT, cenv) thm end;

fun insts x = Args.and_list (Scan.lift (Args.var --| Args.$$$ "=" -- Args.name)) x;

fun gen_where context_of = syntax (insts >> (Drule.rule_attribute o read_instantiate context_of));

val where_global = gen_where ProofContext.init;
val where_local = gen_where I;


(* of: positional instantiations *)

fun read_instantiate' context_of (args, concl_args) x thm =
  let
    fun zip_vars _ [] = []
      | zip_vars (_ :: xs) (None :: opt_ts) = zip_vars xs opt_ts
      | zip_vars ((x, _) :: xs) (Some t :: opt_ts) = (x, t) :: zip_vars xs opt_ts
      | zip_vars [] _ = error "More instantiations than variables in theorem";
    val insts =
      zip_vars (Drule.vars_of_terms [#prop (Thm.rep_thm thm)]) args @
      zip_vars (Drule.vars_of_terms [Thm.concl_of thm]) concl_args;
  in read_instantiate context_of insts x thm end;

val concl = Args.$$$ "concl" -- Args.$$$ ":";
val inst_arg = Scan.unless concl Args.name_dummy;
val inst_args = Scan.repeat inst_arg;
fun insts' x = Scan.lift (inst_args -- Scan.optional (concl |-- Args.!!! inst_args) []) x;

fun gen_of context_of = syntax (insts' >> (Drule.rule_attribute o read_instantiate' context_of));

val of_global = gen_of ProofContext.init;
val of_local = gen_of I;


(* unfold / fold definitions *)

fun gen_rewrite rew defs (x, thm) = (x, rew defs thm);

val unfolded_global = syntax (global_thmss >> gen_rewrite Tactic.rewrite_rule);
val unfolded_local = syntax (local_thmss >> gen_rewrite Tactic.rewrite_rule);
val folded_global = syntax (global_thmss >> gen_rewrite Tactic.fold_rule);
val folded_local = syntax (local_thmss >> gen_rewrite Tactic.fold_rule);


(* rule cases *)

fun case_names x = syntax (Scan.lift (Scan.repeat1 Args.name) >> RuleCases.case_names) x;
fun params x = syntax (Args.and_list1 (Scan.lift (Scan.repeat Args.name)) >> RuleCases.params) x;


(* misc rules *)

fun standard x = no_args (Drule.rule_attribute (K Drule.standard)) x;
fun elimified x = no_args (Drule.rule_attribute (K Tactic.make_elim)) x;
fun no_vars x = no_args (Drule.rule_attribute (K (#1 o Drule.freeze_thaw))) x;

fun exported_global x = no_args (Drule.rule_attribute (Proof.export_thm o ProofContext.init)) x;
fun exported_local x = no_args (Drule.rule_attribute Proof.export_thm) x;



(** theory setup **)

(* pure_attributes *)

val pure_attributes =
 [("tagged", (gen_tagged, gen_tagged), "tagged theorem"),
  ("untagged", (gen_untagged, gen_untagged), "untagged theorem"),
  ("COMP", (COMP_global, COMP_local), "direct composition with rules (no lifting)"),
  ("THEN", (RS_global, RS_local), "resolution with rule"),
  ("OF", (OF_global, OF_local), "rule applied to facts"),
  ("where", (where_global, where_local), "named instantiation of theorem"),
  ("of", (of_global, of_local), "rule applied to terms"),
  ("unfolded", (unfolded_global, unfolded_local), "unfolded definitions"),
  ("folded", (folded_global, folded_local), "folded definitions"),
  ("standard", (standard, standard), "result put into standard form"),
  ("elimified", (elimified, elimified), "destruct rule turned into elimination rule"),
  ("no_vars", (no_vars, no_vars), "frozen schematic vars"),
  ("case_names", (case_names, case_names), "named rule cases"),
  ("params", (params, params), "named rule parameters"),
  ("exported", (exported_global, exported_local), "theorem exported from context")];


(* setup *)

val setup = [AttributesData.init, add_attributes pure_attributes];

end;

structure BasicAttrib: BASIC_ATTRIB = Attrib;
open BasicAttrib;
