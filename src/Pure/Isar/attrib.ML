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

fun add_del_args add del x = syntax
  (Scan.lift (Args.add >> K add || Args.del >> K del || Scan.succeed add)) x;



(** Pure attributes **)

(* tags *)

fun gen_tagged x = syntax (tag >> Drule.tag) x;
fun gen_untagged x = syntax (Scan.lift Args.name >> Drule.untag) x;


(* COMP *)

fun comp (i, B) (x, A) = (x, Drule.compose_single (A, i, B));

fun gen_COMP thm = syntax (Scan.lift (Scan.optional (Args.bracks Args.nat) 1) -- thm >> comp);
val COMP_global = gen_COMP global_thm;
val COMP_local = gen_COMP local_thm;


(* RS *)

fun resolve (i, B) (x, A) = (x, A RSN (i, B));

fun gen_RS thm = syntax (Scan.lift (Scan.optional (Args.bracks Args.nat) 1) -- thm >> resolve);
val RS_global = gen_RS global_thm;
val RS_local = gen_RS local_thm;


(* OF *)

fun apply Bs (x, A) = (x, Bs MRS A);

val OF_global = syntax (global_thmss >> apply);
val OF_local = syntax (local_thmss >> apply);


(* where *)

(*named instantiations; permits instantiation of type and term variables*)

fun read_instantiate _ [] _ thm = thm
  | read_instantiate context_of insts x thm =
      let
        val ctxt = context_of x;
        val sign = ProofContext.sign_of ctxt;

        (* Separate type and term insts,
           type insts must occur strictly before term insts *)
        fun has_type_var ((x, _), _) = (case Symbol.explode x of
             "'"::cs => true | cs => false);
        val (Tinst, tinsts) = take_prefix has_type_var insts;
        val _ = if exists has_type_var tinsts
              then error
                "Type instantiations must occur before term instantiations."
              else ();

        val Tinsts = filter has_type_var insts;
        val tinsts = filter_out has_type_var insts;

        (* Type instantiations first *)
        (* Process type insts: Tinsts_env *)
        fun absent xi = error
              ("No such type variable in theorem: " ^
               Syntax.string_of_vname xi);
        val (rtypes, rsorts) = types_sorts thm;
        fun readT (xi, s) =
            let val S = case rsorts xi of Some S => S | None => absent xi;
                val T = ProofContext.read_typ ctxt s;
            in if Sign.typ_instance sign (T, TVar (xi, S)) then (xi, T)
               else error
                 ("Instantiation of " ^ Syntax.string_of_vname xi ^ " fails")
            end;
        val Tinsts_env = map readT Tinsts;
        val cenvT = map (apsnd (Thm.ctyp_of sign)) (Tinsts_env);
        val thm' = Thm.instantiate (cenvT, []) thm;
           (* Instantiate, but don't normalise: *)
           (* this happens after term insts anyway. *)

        (* Term instantiations *)
        val vars = Drule.vars_of thm';
        fun get_typ xi =
          (case assoc (vars, xi) of
            Some T => T
          | None => error ("No such variable in theorem: " ^ Syntax.string_of_vname xi));

        val (xs, ss) = Library.split_list tinsts;
        val Ts = map get_typ xs;

        val used = add_term_tvarnames (prop_of thm',[])
        (* Names of TVars occuring in thm'.  read_def_termTs ensures
           that new TVars introduced when reading the instantiation string
           are distinct from those occuring in the theorem. *)

        val (ts, envT) =
          ProofContext.read_termTs ctxt (K false) (K None) (K None) used (ss ~~ Ts);

        val cenvT = map (apsnd (Thm.ctyp_of sign)) envT;
        val cenv =
          map (fn (xi, t) => pairself (Thm.cterm_of sign) (Var (xi, fastype_of t), t))
            (gen_distinct (fn ((x1, t1), (x2, t2)) => x1 = x2 andalso t1 aconv t2) (xs ~~ ts));
      in
        thm'
        |> Drule.instantiate (cenvT, cenv)
        |> RuleCases.save thm
      end;

fun insts x = Args.and_list (Scan.lift (Args.var --| Args.$$$ "=" -- Args.name)) x;

fun gen_where context_of = syntax (insts >> (Drule.rule_attribute o read_instantiate context_of));

val where_global = gen_where ProofContext.init;
val where_local = gen_where I;


(* of: positional instantiations *)
(*        permits instantiation of term variables only *)

fun read_instantiate' _ ([], []) _ thm = thm
  | read_instantiate' context_of (args, concl_args) x thm =
      let
        fun zip_vars _ [] = []
          | zip_vars (_ :: xs) (None :: opt_ts) = zip_vars xs opt_ts
          | zip_vars ((x, _) :: xs) (Some t :: opt_ts) = (x, t) :: zip_vars xs opt_ts
          | zip_vars [] _ = error "More instantiations than variables in theorem";
        val insts =
          zip_vars (Drule.vars_of_terms [Thm.prop_of thm]) args @
          zip_vars (Drule.vars_of_terms [Thm.concl_of thm]) concl_args;
      in
        thm
        |> read_instantiate context_of insts x
        |> RuleCases.save thm
      end;

val concl = Args.$$$ "concl" -- Args.colon;
val inst_arg = Scan.unless concl Args.name_dummy;
val inst_args = Scan.repeat inst_arg;
fun insts' x = (inst_args -- Scan.optional (concl |-- Args.!!! inst_args) []) x;

fun gen_of context_of =
  syntax (Scan.lift insts' >> (Drule.rule_attribute o read_instantiate' context_of));

val of_global = gen_of ProofContext.init;
val of_local = gen_of I;


(* rename_abs *)

fun rename_abs src = syntax
  (Scan.lift (Scan.repeat Args.name_dummy >> (apsnd o Drule.rename_bvars'))) src;


(* unfold / fold definitions *)

fun gen_rewrite rew defs (x, thm) = (x, rew defs thm);

val unfolded_global = syntax (global_thmss >> gen_rewrite Tactic.rewrite_rule);
val unfolded_local = syntax (local_thmss >> gen_rewrite Tactic.rewrite_rule);
val folded_global = syntax (global_thmss >> gen_rewrite Tactic.fold_rule);
val folded_local = syntax (local_thmss >> gen_rewrite Tactic.fold_rule);


(* rule cases *)

fun consumes x = syntax (Scan.lift (Scan.optional Args.nat 1) >> RuleCases.consumes) x;
fun case_names x = syntax (Scan.lift (Scan.repeat1 Args.name) >> RuleCases.case_names) x;
fun params x = syntax (Args.and_list1 (Scan.lift (Scan.repeat Args.name)) >> RuleCases.params) x;


(* rule_format *)

fun rule_format_att x = syntax
  (Scan.lift (Args.parens (Args.$$$ "no_asm")
  >> K ObjectLogic.rule_format_no_asm || Scan.succeed ObjectLogic.rule_format)) x;


(* misc rules *)

fun standard x = no_args (Drule.rule_attribute (K Drule.standard)) x;
fun elim_format x = no_args (Drule.rule_attribute (K Tactic.make_elim)) x;
fun no_vars x = no_args (Drule.rule_attribute (K (#1 o Drule.freeze_thaw))) x;


(* rule declarations *)

local

fun add_args a b c x = syntax
  (Scan.lift ((Args.bang >> K a || Args.query >> K c || Scan.succeed b) -- (Scan.option Args.nat))
    >> (fn (f, n) => f n)) x;

fun del_args att = syntax (Scan.lift Args.del >> K att);

open ContextRules;

in

val rule_atts =
 [("intro",
   (add_args intro_bang_global intro_global intro_query_global,
    add_args intro_bang_local intro_local intro_query_local),
    "declaration of introduction rule"),
  ("elim",
   (add_args elim_bang_global elim_global elim_query_global,
    add_args elim_bang_local elim_local elim_query_local),
    "declaration of elimination rule"),
  ("dest",
   (add_args dest_bang_global dest_global dest_query_global,
    add_args dest_bang_local dest_local dest_query_local),
    "declaration of destruction rule"),
  ("rule", (del_args rule_del_global, del_args rule_del_local),
    "remove declaration of intro/elim/dest rule")];

end;



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
  ("rename_abs", (rename_abs, rename_abs), "rename bound variables in abstractions"),
  ("unfolded", (unfolded_global, unfolded_local), "unfolded definitions"),
  ("folded", (folded_global, folded_local), "folded definitions"),
  ("standard", (standard, standard), "result put into standard form"),
  ("elim_format", (elim_format, elim_format), "destruct rule turned into elimination rule format"),
  ("no_vars", (no_vars, no_vars), "frozen schematic vars"),
  ("consumes", (consumes, consumes), "number of consumed facts"),
  ("case_names", (case_names, case_names), "named rule cases"),
  ("params", (params, params), "named rule parameters"),
  ("atomize", (no_args ObjectLogic.declare_atomize, no_args undef_local_attribute),
    "declaration of atomize rule"),
  ("rulify", (no_args ObjectLogic.declare_rulify, no_args undef_local_attribute),
    "declaration of rulify rule"),
  ("rule_format", (rule_format_att, rule_format_att), "result put into standard rule format")] @
  rule_atts;


(* setup *)

val setup = [AttributesData.init, add_attributes pure_attributes];

end;

structure BasicAttrib: BASIC_ATTRIB = Attrib;
open BasicAttrib;
