(*  Title:      Pure/theory.ML
    Author:     Lawrence C Paulson and Markus Wenzel

Logical theory content: axioms, definitions, and begin/end wrappers.
*)

signature THEORY =
sig
  val eq_thy: theory * theory -> bool
  val subthy: theory * theory -> bool
  val assert_super: theory -> theory -> theory
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val nodes_of: theory -> theory list
  val check_thy: theory -> theory_ref
  val deref: theory_ref -> theory
  val merge: theory * theory -> theory
  val merge_refs: theory_ref * theory_ref -> theory_ref
  val merge_list: theory list -> theory
  val checkpoint: theory -> theory
  val copy: theory -> theory
  val requires: theory -> string -> string -> unit
  val axiom_space: theory -> Name_Space.T
  val axiom_table: theory -> term Symtab.table
  val axioms_of: theory -> (string * term) list
  val all_axioms_of: theory -> (string * term) list
  val defs_of: theory -> Defs.T
  val at_begin: (theory -> theory option) -> theory -> theory
  val at_end: (theory -> theory option) -> theory -> theory
  val begin_theory: string -> theory list -> theory
  val end_theory: theory -> theory
  val add_axiom: Proof.context -> binding * term -> theory -> theory
  val add_deps: Proof.context -> string -> string * typ -> (string * typ) list -> theory -> theory
  val add_deps_global: string -> string * typ -> (string * typ) list -> theory -> theory
  val add_def: Proof.context -> bool -> bool -> binding * term -> theory -> theory
  val specify_const: (binding * typ) * mixfix -> theory -> term * theory
  val check_overloading: Proof.context -> bool -> string * typ -> unit
end

structure Theory: THEORY =
struct


(** theory context operations **)

val eq_thy = Context.eq_thy;
val subthy = Context.subthy;

fun assert_super thy1 thy2 =
  if subthy (thy1, thy2) then thy2
  else raise THEORY ("Not a super theory", [thy1, thy2]);

val parents_of = Context.parents_of;
val ancestors_of = Context.ancestors_of;
fun nodes_of thy = thy :: ancestors_of thy;

val check_thy = Context.check_thy;
val deref = Context.deref;

val merge = Context.merge;
val merge_refs = Context.merge_refs;

fun merge_list [] = raise THEORY ("Empty merge of theories", [])
  | merge_list (thy :: thys) = Library.foldl merge (thy, thys);

val checkpoint = Context.checkpoint_thy;
val copy = Context.copy_thy;

fun requires thy name what =
  if exists (fn thy' => Context.theory_name thy' = name) (nodes_of thy) then ()
  else error ("Require theory " ^ quote name ^ " as an ancestor for " ^ what);



(** datatype thy **)

type wrapper = (theory -> theory option) * stamp;

fun apply_wrappers (wrappers: wrapper list) =
  perhaps (perhaps_loop (perhaps_apply (map fst wrappers)));

datatype thy = Thy of
 {axioms: term Name_Space.table,
  defs: Defs.T,
  wrappers: wrapper list * wrapper list};

fun make_thy (axioms, defs, wrappers) = Thy {axioms = axioms, defs = defs, wrappers = wrappers};

structure Thy = Theory_Data_PP
(
  type T = thy;
  val empty_axioms = Name_Space.empty_table "axiom" : term Name_Space.table;
  val empty = make_thy (empty_axioms, Defs.empty, ([], []));

  fun extend (Thy {axioms = _, defs, wrappers}) = make_thy (empty_axioms, defs, wrappers);

  fun merge pp (thy1, thy2) =
    let
      val ctxt = Syntax.init_pretty pp;
      val Thy {axioms = _, defs = defs1, wrappers = (bgs1, ens1)} = thy1;
      val Thy {axioms = _, defs = defs2, wrappers = (bgs2, ens2)} = thy2;

      val axioms' = empty_axioms;
      val defs' = Defs.merge ctxt (defs1, defs2);
      val bgs' = Library.merge (eq_snd op =) (bgs1, bgs2);
      val ens' = Library.merge (eq_snd op =) (ens1, ens2);
    in make_thy (axioms', defs', (bgs', ens')) end;
);

fun rep_theory thy = Thy.get thy |> (fn Thy args => args);

fun map_thy f = Thy.map (fn (Thy {axioms, defs, wrappers}) =>
  make_thy (f (axioms, defs, wrappers)));


fun map_axioms f = map_thy (fn (axioms, defs, wrappers) => (f axioms, defs, wrappers));
fun map_defs f = map_thy (fn (axioms, defs, wrappers) => (axioms, f defs, wrappers));
fun map_wrappers f = map_thy (fn (axioms, defs, wrappers) => (axioms, defs, f wrappers));


(* basic operations *)

val axiom_space = #1 o #axioms o rep_theory;
val axiom_table = #2 o #axioms o rep_theory;

val axioms_of = Symtab.dest o #2 o #axioms o rep_theory;
fun all_axioms_of thy = maps axioms_of (nodes_of thy);

val defs_of = #defs o rep_theory;


(* begin/end theory *)

val begin_wrappers = rev o #1 o #wrappers o rep_theory;
val end_wrappers = rev o #2 o #wrappers o rep_theory;

fun at_begin f = map_wrappers (apfst (cons (f, stamp ())));
fun at_end f = map_wrappers (apsnd (cons (f, stamp ())));

fun begin_theory name imports =
  let
    val thy = Context.begin_thy Context.pretty_global name imports;
    val wrappers = begin_wrappers thy;
  in
    thy
    |> Sign.local_path
    |> Sign.map_naming (Name_Space.set_theory_name name)
    |> apply_wrappers wrappers
    |> tap (Syntax.force_syntax o Sign.syn_of)
  end;

fun end_theory thy =
  thy |> apply_wrappers (end_wrappers thy) |> Context.finish_thy;



(** primitive specifications **)

(* raw axioms *)

fun cert_axm ctxt (b, raw_tm) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val t = Sign.cert_prop thy raw_tm
      handle TYPE (msg, _, _) => error msg
        | TERM (msg, _) => error msg;
    val _ = Term.no_dummy_patterns t handle TERM (msg, _) => error msg;

    val bad_sorts =
      rev ((fold_types o fold_atyps_sorts) (fn (_, []) => I | (T, _) => insert (op =) T) t []);
    val _ = null bad_sorts orelse
      error ("Illegal sort constraints in primitive specification: " ^
        commas (map (Syntax.string_of_typ (Config.put show_sorts true ctxt)) bad_sorts));
  in (b, Sign.no_vars ctxt t) end
  handle ERROR msg => cat_error msg ("The error(s) above occurred in axiom " ^ Binding.print b);

fun add_axiom ctxt raw_axm thy = thy |> map_axioms (fn axioms =>
  let
    val axm = apsnd Logic.varify_global (cert_axm ctxt raw_axm);
    val (_, axioms') = Name_Space.define ctxt true (Sign.naming_of thy) axm axioms;
  in axioms' end);


(* dependencies *)

fun dependencies ctxt unchecked def description lhs rhs =
  let
    val thy = Proof_Context.theory_of ctxt;
    val consts = Sign.consts_of thy;
    fun prep const =
      let val Const (c, T) = Sign.no_vars ctxt (Const const)
      in (c, Consts.typargs consts (c, Logic.varifyT_global T)) end;

    val lhs_vars = Term.add_tfreesT (#2 lhs) [];
    val rhs_extras = fold (#2 #> Term.fold_atyps (fn TFree v =>
      if member (op =) lhs_vars v then I else insert (op =) v | _ => I)) rhs [];
    val _ =
      if null rhs_extras then ()
      else error ("Specification depends on extra type variables: " ^
        commas_quote (map (Syntax.string_of_typ ctxt o TFree) rhs_extras) ^
        "\nThe error(s) above occurred in " ^ quote description);
  in Defs.define ctxt unchecked def description (prep lhs) (map prep rhs) end;

fun add_deps ctxt a raw_lhs raw_rhs thy =
  let
    val lhs :: rhs = map (dest_Const o Sign.cert_term thy o Const) (raw_lhs :: raw_rhs);
    val description = if a = "" then #1 lhs ^ " axiom" else a;
  in thy |> map_defs (dependencies ctxt false NONE description lhs rhs) end;

fun add_deps_global a x y thy = add_deps (Syntax.init_pretty_global thy) a x y thy;

fun specify_const decl thy =
  let val (t as Const const, thy') = Sign.declare_const_global decl thy;
  in (t, add_deps_global "" const [] thy') end;


(* overloading *)

fun check_overloading ctxt overloaded (c, T) =
  let
    val thy = Proof_Context.theory_of ctxt;

    val declT = Sign.the_const_constraint thy c
      handle TYPE (msg, _, _) => error msg;
    val T' = Logic.varifyT_global T;

    fun message sorts txt =
      [Pretty.block [Pretty.str "Specification of constant ",
        Pretty.str c, Pretty.str " ::", Pretty.brk 1,
        Pretty.quote (Syntax.pretty_typ (Config.put show_sorts sorts ctxt) T)],
        Pretty.str txt] |> Pretty.chunks |> Pretty.string_of;
  in
    if Sign.typ_instance thy (declT, T') then ()
    else if Type.raw_instance (declT, T') then
      error (message true "imposes additional sort constraints on the constant declaration")
    else if overloaded then ()
    else warning (message false "is strictly less general than the declared type")
  end;


(* definitional axioms *)

local

fun check_def ctxt thy unchecked overloaded (b, tm) defs =
  let
    val name = Sign.full_name thy b;
    val ((lhs, rhs), _) = Primitive_Defs.dest_def ctxt Term.is_Const (K false) (K false) tm
      handle TERM (msg, _) => error msg;
    val lhs_const = Term.dest_Const (Term.head_of lhs);
    val rhs_consts = fold_aterms (fn Const const => insert (op =) const | _ => I) rhs [];
    val _ = check_overloading ctxt overloaded lhs_const;
  in defs |> dependencies ctxt unchecked (SOME name) name lhs_const rhs_consts end
  handle ERROR msg => cat_error msg (Pretty.string_of (Pretty.block
   [Pretty.str ("The error(s) above occurred in definition " ^ Binding.print b ^ ":"),
    Pretty.fbrk, Pretty.quote (Syntax.pretty_term ctxt tm)]));

in

fun add_def ctxt unchecked overloaded raw_axm thy =
  let val axm = cert_axm ctxt raw_axm in
    thy
    |> map_defs (check_def ctxt thy unchecked overloaded axm)
    |> add_axiom ctxt axm
  end;

end;

end;
