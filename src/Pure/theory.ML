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
  val check_thy: theory -> theory_ref
  val deref: theory_ref -> theory
  val merge: theory * theory -> theory
  val merge_refs: theory_ref * theory_ref -> theory_ref
  val merge_list: theory list -> theory
  val checkpoint: theory -> theory
  val copy: theory -> theory
  val requires: theory -> string -> string -> unit
  val axiom_space: theory -> NameSpace.T
  val axiom_table: theory -> term Symtab.table
  val axioms_of: theory -> (string * term) list
  val all_axioms_of: theory -> (string * term) list
  val defs_of: theory -> Defs.T
  val at_begin: (theory -> theory option) -> theory -> theory
  val at_end: (theory -> theory option) -> theory -> theory
  val begin_theory: string -> theory list -> theory
  val end_theory: theory -> theory
  val add_axioms_i: (binding * term) list -> theory -> theory
  val add_axioms: (bstring * string) list -> theory -> theory
  val add_deps: string -> string * typ -> (string * typ) list -> theory -> theory
  val add_defs_i: bool -> bool -> (binding * term) list -> theory -> theory
  val add_defs: bool -> bool -> (bstring * string) list -> theory -> theory
  val add_finals_i: bool -> term list -> theory -> theory
  val add_finals: bool -> string list -> theory -> theory
  val specify_const: Properties.T -> (binding * typ) * mixfix -> theory -> term * theory
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

val check_thy = Context.check_thy;
val deref = Context.deref;

val merge = Context.merge;
val merge_refs = Context.merge_refs;

fun merge_list [] = raise THEORY ("Empty merge of theories", [])
  | merge_list (thy :: thys) = Library.foldl merge (thy, thys);

val checkpoint = Context.checkpoint_thy;
val copy = Context.copy_thy;

fun requires thy name what =
  if exists (fn thy' => Context.theory_name thy' = name) (thy :: ancestors_of thy) then ()
  else error ("Require theory " ^ quote name ^ " as an ancestor for " ^ what);



(** datatype thy **)

type wrapper = (theory -> theory option) * stamp;

fun apply_wrappers (wrappers: wrapper list) =
  perhaps (perhaps_loop (perhaps_apply (map fst wrappers)));

datatype thy = Thy of
 {axioms: term NameSpace.table,
  defs: Defs.T,
  wrappers: wrapper list * wrapper list};

fun make_thy (axioms, defs, wrappers) = Thy {axioms = axioms, defs = defs, wrappers = wrappers};

fun err_dup_axm dup = error ("Duplicate axiom: " ^ quote dup);

structure ThyData = TheoryDataFun
(
  type T = thy;
  val empty = make_thy (NameSpace.empty_table, Defs.empty, ([], []));
  val copy = I;

  fun extend (Thy {axioms, defs, wrappers}) = make_thy (NameSpace.empty_table, defs, wrappers);

  fun merge pp (thy1, thy2) =
    let
      val Thy {axioms = _, defs = defs1, wrappers = (bgs1, ens1)} = thy1;
      val Thy {axioms = _, defs = defs2, wrappers = (bgs2, ens2)} = thy2;

      val axioms' = NameSpace.empty_table;
      val defs' = Defs.merge pp (defs1, defs2);
      val bgs' = Library.merge (eq_snd op =) (bgs1, bgs2);
      val ens' = Library.merge (eq_snd op =) (ens1, ens2);
    in make_thy (axioms', defs', (bgs', ens')) end;
);

fun rep_theory thy = ThyData.get thy |> (fn Thy args => args);

fun map_thy f = ThyData.map (fn (Thy {axioms, defs, wrappers}) =>
  make_thy (f (axioms, defs, wrappers)));


fun map_axioms f = map_thy (fn (axioms, defs, wrappers) => (f axioms, defs, wrappers));
fun map_defs f = map_thy (fn (axioms, defs, wrappers) => (axioms, f defs, wrappers));
fun map_wrappers f = map_thy (fn (axioms, defs, wrappers) => (axioms, defs, f wrappers));


(* basic operations *)

val axiom_space = #1 o #axioms o rep_theory;
val axiom_table = #2 o #axioms o rep_theory;

val axioms_of = Symtab.dest o #2 o #axioms o rep_theory;
fun all_axioms_of thy = maps axioms_of (thy :: ancestors_of thy);

val defs_of = #defs o rep_theory;


(* begin/end theory *)

val begin_wrappers = rev o #1 o #wrappers o rep_theory;
val end_wrappers = rev o #2 o #wrappers o rep_theory;

fun at_begin f = map_wrappers (apfst (cons (f, stamp ())));
fun at_end f = map_wrappers (apsnd (cons (f, stamp ())));

fun begin_theory name imports =
  let
    val thy = Context.begin_thy Syntax.pp_global name imports;
    val wrappers = begin_wrappers thy;
  in thy |> Sign.local_path |> apply_wrappers wrappers end;

fun end_theory thy =
  thy |> apply_wrappers (end_wrappers thy) |> Context.finish_thy;



(** add axioms **)

(* prepare axioms *)

fun err_in_axm msg name =
  cat_error msg ("The error(s) above occurred in axiom " ^ quote name);

fun cert_axm thy (b, raw_tm) =
  let
    val (t, T, _) = Sign.certify_prop thy raw_tm
      handle TYPE (msg, _, _) => error msg
        | TERM (msg, _) => error msg;
  in
    Term.no_dummy_patterns t handle TERM (msg, _) => error msg;
    (b, Sign.no_vars (Syntax.pp_global thy) t)
  end;

fun read_axm thy (bname, str) =
  cert_axm thy (Binding.name bname, Syntax.read_prop_global thy str)
    handle ERROR msg => err_in_axm msg bname;


(* add_axioms(_i) *)

local

fun gen_add_axioms prep_axm raw_axms thy = thy |> map_axioms (fn axioms =>
  let
    val axms = map (apsnd Logic.varify o prep_axm thy) raw_axms;
    val axioms' = fold (snd oo NameSpace.bind (Sign.naming_of thy)) axms axioms
      handle Symtab.DUP dup => err_dup_axm dup;
  in axioms' end);

in

val add_axioms_i = gen_add_axioms cert_axm;
val add_axioms = gen_add_axioms read_axm;

end;



(** add constant definitions **)

(* dependencies *)

fun dependencies thy unchecked is_def name lhs rhs =
  let
    val pp = Syntax.pp_global thy;
    val consts = Sign.consts_of thy;
    fun prep const =
      let val Const (c, T) = Sign.no_vars pp (Const const)
      in (c, Consts.typargs consts (c, Logic.varifyT T)) end;

    val lhs_vars = Term.add_tfreesT (#2 lhs) [];
    val rhs_extras = fold (#2 #> Term.fold_atyps (fn TFree v =>
      if member (op =) lhs_vars v then I else insert (op =) v | _ => I)) rhs [];
    val _ =
      if null rhs_extras then ()
      else error ("Specification depends on extra type variables: " ^
        commas_quote (map (Pretty.string_of_typ pp o TFree) rhs_extras) ^
        "\nThe error(s) above occurred in " ^ quote name);
  in Defs.define pp unchecked is_def name (prep lhs) (map prep rhs) end;

fun add_deps a raw_lhs raw_rhs thy =
  let
    val lhs :: rhs = map (dest_Const o Sign.cert_term thy o Const) (raw_lhs :: raw_rhs);
    val name = if a = "" then (#1 lhs ^ " axiom") else a;
  in thy |> map_defs (dependencies thy false false name lhs rhs) end;

fun specify_const tags decl thy =
  let val (t as Const const, thy') = Sign.declare_const tags decl thy
  in (t, add_deps "" const [] thy') end;


(* check_overloading *)

fun check_overloading thy overloaded (c, T) =
  let
    val declT = Sign.the_const_constraint thy c
      handle TYPE (msg, _, _) => error msg;
    val T' = Logic.varifyT T;

    fun message txt =
      [Pretty.block [Pretty.str "Specification of constant ",
        Pretty.str c, Pretty.str " ::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ_global thy T)],
        Pretty.str txt] |> Pretty.chunks |> Pretty.string_of;
  in
    if Sign.typ_instance thy (declT, T') then ()
    else if Type.raw_instance (declT, T') then
      error (Library.setmp show_sorts true
        message "imposes additional sort constraints on the constant declaration")
    else if overloaded then ()
    else warning (message "is strictly less general than the declared type");
    (c, T)
  end;


(* check_def *)

fun check_def thy unchecked overloaded (b, tm) defs =
  let
    val ctxt = ProofContext.init thy;
    val name = Sign.full_name thy b;
    val (lhs_const, rhs) = Sign.cert_def ctxt tm;
    val rhs_consts = fold_aterms (fn Const const => insert (op =) const | _ => I) rhs [];
    val _ = check_overloading thy overloaded lhs_const;
  in defs |> dependencies thy unchecked true name lhs_const rhs_consts end
  handle ERROR msg => cat_error msg (Pretty.string_of (Pretty.block
   [Pretty.str ("The error(s) above occurred in definition " ^ quote (Binding.str_of b) ^ ":"),
    Pretty.fbrk, Pretty.quote (Syntax.pretty_term_global thy tm)]));


(* add_defs(_i) *)

local

fun gen_add_defs prep_axm unchecked overloaded raw_axms thy =
  let val axms = map (prep_axm thy) raw_axms in
    thy
    |> map_defs (fold (check_def thy unchecked overloaded) axms)
    |> add_axioms_i axms
  end;

in

val add_defs_i = gen_add_defs cert_axm;
val add_defs = gen_add_defs read_axm;

end;


(* add_finals(_i) *)

local

fun gen_add_finals prep_term overloaded args thy =
  let
    fun const_of (Const const) = const
      | const_of (Free _) = error "Attempt to finalize variable (or undeclared constant)"
      | const_of _ = error "Attempt to finalize non-constant term";
    fun specify (c, T) = dependencies thy false false (c ^ " axiom") (c, T) [];
    val finalize = specify o check_overloading thy overloaded o const_of o
      Sign.cert_term thy o prep_term thy;
  in thy |> map_defs (fold finalize args) end;

in

val add_finals_i = gen_add_finals (K I);
val add_finals = gen_add_finals Syntax.read_term_global;

end;

end;
