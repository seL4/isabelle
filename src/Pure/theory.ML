(*  Title:      Pure/theory.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

Logical theory content: axioms, definitions, oracles.
*)

signature BASIC_THEORY =
sig
  type theory
  type theory_ref
  val sign_of: theory -> theory    (*obsolete*)
  val rep_theory: theory ->
   {axioms: term NameSpace.table,
    defs: Defs.T,
    oracles: ((theory * Object.T -> term) * stamp) NameSpace.table}
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val eq_thy: theory * theory -> bool
  val subthy: theory * theory -> bool
  val cert_axm: theory -> string * term -> string * term
  val read_def_axm: theory * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> string * string -> string * term
  val read_axm: theory -> string * string -> string * term
  val inferT_axm: theory -> string * term -> string * term
end

signature THEORY =
sig
  include BASIC_THEORY
  include SIGN_THEORY
  val begin_theory: string -> theory list -> theory
  val end_theory: theory -> theory
  val checkpoint: theory -> theory
  val copy: theory -> theory
  val init_data: theory -> theory
  val axiom_space: theory -> NameSpace.T
  val oracle_space: theory -> NameSpace.T
  val axioms_of: theory -> (string * term) list
  val all_axioms_of: theory -> (string * term) list
  val defs_of : theory -> Defs.T
  val definitions_of: theory -> string ->
    {module: string, name: string, lhs: typ, rhs: (string * typ) list} list
  val self_ref: theory -> theory_ref
  val deref: theory_ref -> theory
  val merge: theory * theory -> theory                     (*exception TERM*)
  val merge_refs: theory_ref * theory_ref -> theory_ref    (*exception TERM*)
  val requires: theory -> string -> string -> unit
  val assert_super: theory -> theory -> theory
  val add_axioms: (bstring * string) list -> theory -> theory
  val add_axioms_i: (bstring * term) list -> theory -> theory
  val add_defs: bool -> (bstring * string) list -> theory -> theory
  val add_defs_i: bool -> (bstring * term) list -> theory -> theory
  val add_finals: bool -> string list -> theory -> theory
  val add_finals_i: bool -> term list -> theory -> theory
  val add_oracle: bstring * (theory * Object.T -> term) -> theory -> theory
end

structure Theory: THEORY =
struct

(** type theory **)

(* context operations *)

type theory = Context.theory;
type theory_ref = Context.theory_ref;

val eq_thy = Context.eq_thy;
val subthy = Context.subthy;

val parents_of = Context.parents_of;
val ancestors_of = Context.ancestors_of;

val self_ref = Context.self_ref;
val deref = Context.deref;
val merge = Context.merge;
val merge_refs = Context.merge_refs;

val begin_theory = Sign.local_path oo Context.begin_thy Sign.pp;
val end_theory = Context.finish_thy;
val checkpoint = Context.checkpoint_thy;
val copy = Context.copy_thy;


(* signature operations *)

val sign_of = I;

structure SignTheory: SIGN_THEORY = Sign;
open SignTheory;



(** datatype thy **)

datatype thy = Thy of
 {axioms: term NameSpace.table,
  defs: Defs.T,
  oracles: ((theory * Object.T -> term) * stamp) NameSpace.table};

fun make_thy (axioms, defs, oracles) =
  Thy {axioms = axioms, defs = defs, oracles = oracles};

fun err_dup_axms dups = error ("Duplicate axiom(s): " ^ commas_quote dups);
fun err_dup_oras dups = error ("Duplicate oracle(s): " ^ commas_quote dups);

structure ThyData = TheoryDataFun
(struct
  val name = "Pure/theory";
  type T = thy;
  val empty = make_thy (NameSpace.empty_table, Defs.empty, NameSpace.empty_table);
  val copy = I;

  fun extend (Thy {axioms, defs, oracles}) = make_thy (NameSpace.empty_table, defs, oracles);

  fun merge pp (thy1, thy2) =
    let
      val Thy {axioms = _, defs = defs1, oracles = oracles1} = thy1;
      val Thy {axioms = _, defs = defs2, oracles = oracles2} = thy2;

      val axioms = NameSpace.empty_table;
      val defs = Defs.merge (defs1, defs2);
      val oracles = NameSpace.merge_tables (eq_snd (op =)) (oracles1, oracles2)
        handle Symtab.DUPS dups => err_dup_oras dups;
    in make_thy (axioms, defs, oracles) end;

  fun print _ _ = ();
end);

val init_data = ThyData.init;

fun rep_theory thy = ThyData.get thy |> (fn Thy args => args);

fun map_thy f = ThyData.map (fn (Thy {axioms, defs, oracles}) =>
  make_thy (f (axioms, defs, oracles)));

fun map_axioms f = map_thy (fn (axioms, defs, oracles) => (f axioms, defs, oracles));
fun map_defs f = map_thy (fn (axioms, defs, oracles) => (axioms, f defs, oracles));
fun map_oracles f = map_thy (fn (axioms, defs, oracles) => (axioms, defs, f oracles));


(* basic operations *)

val axiom_space = #1 o #axioms o rep_theory;
val oracle_space = #1 o #oracles o rep_theory;

val axioms_of = Symtab.dest o #2 o #axioms o rep_theory;
fun all_axioms_of thy = maps axioms_of (thy :: ancestors_of thy);

val defs_of = #defs o rep_theory;

fun definitions_of thy c =
  Defs.specifications_of (defs_of thy) c
  |> map_filter (fn (_, {is_def, module, name, lhs, rhs}) =>
    if is_def then SOME {module = module, name = name, lhs = lhs, rhs = rhs} else NONE);


fun requires thy name what =
  if Context.exists_name name thy then ()
  else error ("Require theory " ^ quote name ^ " as an ancestor for " ^ what);

fun assert_super thy1 thy2 =
  if subthy (thy1, thy2) then thy2
  else raise THEORY ("Not a super theory", [thy1, thy2]);



(** add axioms **)

(* prepare axioms *)

fun err_in_axm msg name =
  cat_error msg ("The error(s) above occurred in axiom " ^ quote name);

fun cert_axm thy (name, raw_tm) =
  let
    val (t, T, _) = Sign.certify_prop thy raw_tm
      handle TYPE (msg, _, _) => error msg
        | TERM (msg, _) => error msg;
  in
    Term.no_dummy_patterns t handle TERM (msg, _) => error msg;
    (name, Sign.no_vars (Sign.pp thy) t)
  end;

fun read_def_axm (thy, types, sorts) used (name, str) =
  let
    val ts = Syntax.read (Context.Theory thy) (Sign.is_logtype thy) (Sign.syn_of thy) propT str;
    val (t, _) =
      Sign.infer_types (Sign.pp thy) thy (Sign.consts_of thy) types sorts used true (ts, propT);
  in cert_axm thy (name, t) end
  handle ERROR msg => err_in_axm msg name;

fun read_axm thy name_str = read_def_axm (thy, K NONE, K NONE) [] name_str;

fun inferT_axm thy (name, pre_tm) =
  let
    val pp = Sign.pp thy;
    val (t, _) =
      Sign.infer_types pp thy (Sign.consts_of thy) (K NONE) (K NONE) [] true ([pre_tm], propT);
  in (name, Sign.no_vars pp t) end
  handle ERROR msg => err_in_axm msg name;


(* add_axioms(_i) *)

local

fun gen_add_axioms prep_axm raw_axms thy = thy |> map_axioms (fn axioms =>
  let
    val axms = map (apsnd (Compress.term thy o Logic.varify) o prep_axm thy) raw_axms;
    val axioms' = NameSpace.extend_table (Sign.naming_of thy) (axioms, axms)
      handle Symtab.DUPS dups => err_dup_axms dups;
  in axioms' end);

in

val add_axioms = gen_add_axioms read_axm;
val add_axioms_i = gen_add_axioms cert_axm;

end;



(** add constant definitions **)

fun prep_const thy (c, T) = (c, Compress.typ thy (Type.varifyT T));


(* check_overloading *)

fun check_overloading thy overloaded (c, T) =
  let
    val declT =
      (case Sign.const_constraint thy c of
        NONE => error ("Undeclared constant " ^ quote c)
      | SOME declT => declT);
    val T' = Type.varifyT T;

    fun message txt =
      [Pretty.block [Pretty.str "Specification of constant ",
        Pretty.str c, Pretty.str " ::", Pretty.brk 1, Pretty.quote (Sign.pretty_typ thy T)],
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

fun check_def thy overloaded (bname, tm) defs =
  let
    val pp = Sign.pp thy;
    fun prt_const (c, T) =
     [Pretty.str c, Pretty.str " ::", Pretty.brk 1,
      Pretty.quote (Pretty.typ pp (Type.freeze_type T))];

    val name = Sign.full_name thy bname;
    val (lhs_const, rhs) = Sign.cert_def pp tm;
    val rhs_consts = fold_aterms (fn Const const => insert (op =) const | _ => I) rhs [];
    val _ = check_overloading thy overloaded lhs_const;
  in
    defs |> Defs.define (Sign.const_typargs thy) true (Context.theory_name thy)
      name (prep_const thy lhs_const) (map (prep_const thy) rhs_consts)
  end
  handle ERROR msg => cat_error msg (Pretty.string_of (Pretty.block
   [Pretty.str ("The error(s) above occurred in definition " ^ quote bname ^ ":"),
    Pretty.fbrk, Pretty.quote (Pretty.term (Sign.pp thy) tm)]));


(* add_defs(_i) *)

local

fun gen_add_defs prep_axm overloaded raw_axms thy =
  let val axms = map (prep_axm thy) raw_axms in
    thy
    |> map_defs (fold (check_def thy overloaded) axms)
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
    fun specify (c, T) = Defs.define (Sign.const_typargs thy) false (Context.theory_name thy)
      (c ^ " axiom") (prep_const thy (c, T)) [];
    val finalize = specify o check_overloading thy overloaded o
      const_of o Sign.no_vars (Sign.pp thy) o prep_term thy;
  in thy |> map_defs (fold finalize args) end;

in

val add_finals = gen_add_finals Sign.read_term;
val add_finals_i = gen_add_finals Sign.cert_term;

end;



(** add oracle **)

fun add_oracle (bname, oracle) thy = thy |> map_oracles (fn oracles =>
  NameSpace.extend_table (Sign.naming_of thy) (oracles, [(bname, (oracle, stamp ()))])
    handle Symtab.DUPS dups => err_dup_oras dups);

end;

structure BasicTheory: BASIC_THEORY = Theory;
open BasicTheory;
