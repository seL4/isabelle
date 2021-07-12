(*  Title:      Pure/Isar/code.ML
    Author:     Florian Haftmann, TU Muenchen

Abstract executable ingredients of theory.  Management of data
dependent on executable ingredients as synchronized cache; purged
on any change of underlying executable ingredients.
*)

signature CODE =
sig
  (*constants*)
  val check_const: theory -> term -> string
  val read_const: theory -> string -> string
  val string_of_const: theory -> string -> string
  val args_number: theory -> string -> int

  (*constructor sets*)
  val constrset_of_consts: theory -> (string * typ) list
    -> string * ((string * sort) list * (string * ((string * sort) list * typ list)) list)

  (*code equations and certificates*)
  val assert_eqn: theory -> thm * bool -> thm * bool
  val assert_abs_eqn: theory -> string option -> thm -> thm * (string * string)
  type cert
  val constrain_cert: theory -> sort list -> cert -> cert
  val conclude_cert: cert -> cert
  val typargs_deps_of_cert: theory -> cert -> (string * sort) list * (string * typ list) list
  val equations_of_cert: theory -> cert -> ((string * sort) list * typ)
    * (((term * string option) list * (term * string option)) * (thm option * bool)) list option
  val pretty_cert: theory -> cert -> Pretty.T list

  (*executable code*)
  type constructors
  type abs_type
  val type_interpretation: (string -> theory -> theory) -> theory -> theory
  val datatype_interpretation: (string * constructors -> theory -> theory) -> theory -> theory
  val abstype_interpretation: (string * abs_type -> theory -> theory) -> theory -> theory
  val declare_datatype_global: (string * typ) list -> theory -> theory
  val declare_datatype_cmd: string list -> theory -> theory
  val declare_abstype: thm -> local_theory -> local_theory
  val declare_abstype_global: thm -> theory -> theory
  val declare_default_eqns: (thm * bool) list -> local_theory -> local_theory
  val declare_default_eqns_global: (thm * bool) list -> theory -> theory
  val declare_eqns: (thm * bool) list -> local_theory -> local_theory
  val declare_eqns_global: (thm * bool) list -> theory -> theory
  val add_eqn_global: thm * bool -> theory -> theory
  val del_eqn_global: thm -> theory -> theory
  val declare_abstract_eqn: thm -> local_theory -> local_theory
  val declare_abstract_eqn_global: thm -> theory -> theory
  val declare_aborting_global: string -> theory -> theory
  val declare_unimplemented_global: string -> theory -> theory
  val declare_case_global: thm -> theory -> theory
  val declare_undefined_global: string -> theory -> theory
  val get_type: theory -> string -> constructors * bool
  val get_type_of_constr_or_abstr: theory -> string -> (string * bool) option
  val is_constr: theory -> string -> bool
  val is_abstr: theory -> string -> bool
  val get_cert: Proof.context -> ((thm * bool) list -> (thm * bool) list option) list
    -> string -> cert
  type case_schema
  val get_case_schema: theory -> string -> case_schema option
  val get_case_cong: theory -> string -> thm option
  val is_undefined: theory -> string -> bool
  val print_codesetup: theory -> unit
end;

signature CODE_DATA_ARGS =
sig
  type T
  val empty: T
end;

signature CODE_DATA =
sig
  type T
  val change: theory option -> (T -> T) -> T
  val change_yield: theory option -> (T -> 'a * T) -> 'a * T
end;

signature PRIVATE_CODE =
sig
  include CODE
  val declare_data: Any.T -> serial
  val change_yield_data: serial * ('a -> Any.T) * (Any.T -> 'a)
    -> theory -> ('a -> 'b * 'a) -> 'b * 'a
end;

structure Code : PRIVATE_CODE =
struct

(** auxiliary **)

(* printing *)

fun string_of_typ thy =
  Syntax.string_of_typ (Config.put show_sorts true (Syntax.init_pretty_global thy));

fun string_of_const thy c =
  let val ctxt = Proof_Context.init_global thy in
    case Axclass.inst_of_param thy c of
      SOME (c, tyco) =>
        Proof_Context.extern_const ctxt c ^ " " ^ enclose "[" "]"
          (Proof_Context.extern_type ctxt tyco)
    | NONE => Proof_Context.extern_const ctxt c
  end;


(* constants *)

fun const_typ thy = Type.strip_sorts o Sign.the_const_type thy;

fun args_number thy = length o binder_types o const_typ thy;

fun devarify ty =
  let
    val tys = fold_atyps (fn TVar vi_sort => AList.update (op =) vi_sort) ty [];
    val vs = Name.invent Name.context Name.aT (length tys);
    val mapping = map2 (fn v => fn (vi, sort) => (vi, TFree (v, sort))) vs tys;
  in Term.typ_subst_TVars mapping ty end;

fun typscheme thy (c, ty) =
  (map dest_TFree (Sign.const_typargs thy (c, ty)), Type.strip_sorts ty);

fun typscheme_equiv (ty1, ty2) =
  Type.raw_instance (devarify ty1, ty2) andalso Type.raw_instance (devarify ty2, ty1);

fun check_bare_const thy t = case try dest_Const t
 of SOME c_ty => c_ty
  | NONE => error ("Not a constant: " ^ Syntax.string_of_term_global thy t);

fun check_unoverload thy (c, ty) =
  let
    val c' = Axclass.unoverload_const thy (c, ty);
    val ty_decl = const_typ thy c';
  in
    if typscheme_equiv (ty_decl, Logic.varifyT_global ty)
    then c'
    else
      error ("Type\n" ^ string_of_typ thy ty ^
        "\nof constant " ^ quote c ^
        "\nis too specific compared to declared type\n" ^
        string_of_typ thy ty_decl)
  end;

fun check_const thy = check_unoverload thy o check_bare_const thy;

fun read_bare_const thy = check_bare_const thy o Syntax.read_term_global thy;

fun read_const thy = check_unoverload thy o read_bare_const thy;


(** executable specifications **)

(* types *)

datatype type_spec = Constructors of {
      constructors: (string * ((string * sort) list * typ list)) list,
      case_combinators: string list}
  | Abstractor of {
      abs_rep: thm,
      abstractor: string * ((string * sort) list * typ),
      projection: string,
      more_abstract_functions: string list};

fun concrete_constructors_of (Constructors {constructors, ...}) =
      constructors
  | concrete_constructors_of _ =
      [];

fun constructors_of (Constructors {constructors, ...}) =
      (constructors, false)
  | constructors_of (Abstractor {abstractor = (co, (vs, ty)), ...}) =
      ([(co, (vs, [ty]))], true);

fun case_combinators_of (Constructors {case_combinators, ...}) =
      case_combinators
  | case_combinators_of (Abstractor _) =
      [];

fun add_case_combinator c (vs, Constructors {constructors, case_combinators}) =
  (vs, Constructors {constructors = constructors,
    case_combinators = insert (op =) c case_combinators});

fun projection_of (Constructors _) =
      NONE
  | projection_of (Abstractor {projection, ...}) =
      SOME projection;

fun abstract_functions_of (Constructors _) =
      []
  | abstract_functions_of (Abstractor {more_abstract_functions, projection, ...}) =
      projection :: more_abstract_functions;

fun add_abstract_function c (vs, Abstractor {abs_rep, abstractor, projection, more_abstract_functions}) =
  (vs, Abstractor {abs_rep = abs_rep, abstractor = abstractor, projection = projection,
    more_abstract_functions = insert (op =) c more_abstract_functions});

fun join_same_types' (Constructors {constructors, case_combinators = case_combinators1},
    Constructors {case_combinators = case_combinators2, ...}) =
      Constructors {constructors = constructors,
        case_combinators = merge (op =) (case_combinators1, case_combinators2)}
  | join_same_types' (Abstractor {abs_rep, abstractor, projection, more_abstract_functions = more_abstract_functions1},
      Abstractor {more_abstract_functions = more_abstract_functions2, ...}) =
      Abstractor {abs_rep = abs_rep, abstractor = abstractor, projection = projection,
        more_abstract_functions = merge (op =) (more_abstract_functions1, more_abstract_functions2)};

fun join_same_types ((vs, spec1), (_, spec2)) = (vs, join_same_types' (spec1, spec2));


(* functions *)

datatype fun_spec =
    Eqns of bool * (thm * bool) list
  | Proj of term * (string * string)
  | Abstr of thm * (string * string);

val unimplemented = Eqns (true, []);

fun is_unimplemented (Eqns (true, [])) = true
  | is_unimplemented _ = false;

fun is_default (Eqns (true, _)) = true
  | is_default _ = false;

val aborting = Eqns (false, []);

fun associated_abstype (Proj (_, tyco_abs)) = SOME tyco_abs
  | associated_abstype (Abstr (_, tyco_abs)) = SOME tyco_abs
  | associated_abstype _ = NONE;


(* cases *)

type case_schema = int * (int * string option list);

datatype case_spec =
    No_Case
  | Case of {schema: case_schema, tycos: string list, cong: thm}
  | Undefined;

fun associated_datatypes (Case {tycos, schema = (_, (_, raw_cos)), ...}) = (tycos, map_filter I raw_cos)
  | associated_datatypes _ = ([], []);


(** background theory data store **)

(* historized declaration data *)

structure History =
struct

type 'a T = {
  entry: 'a,
  suppressed: bool,     (*incompatible entries are merely suppressed after theory merge but sustain*)
  history: serial list  (*explicit trace of declaration history supports non-monotonic declarations*)
} Symtab.table;

fun some_entry (SOME {suppressed = false, entry, ...}) = SOME entry
  | some_entry _ = NONE;

fun lookup table =
  Symtab.lookup table #> some_entry;

fun register key entry table =
  if is_some (Symtab.lookup table key)
  then Symtab.map_entry key
    (fn {history, ...} => {entry = entry, suppressed = false, history = serial () :: history}) table
  else Symtab.update (key, {entry = entry, suppressed = false, history = [serial ()]}) table;

fun modify_entry key f = Symtab.map_entry key
  (fn {entry, suppressed, history} => {entry = f entry, suppressed = suppressed, history = history});

fun all table = Symtab.dest table
  |> map_filter (fn (key, {entry, suppressed = false, ...}) => SOME (key, entry) | _ => NONE);

local

fun merge_history join_same
    ({entry = entry1, history = history1, ...}, {entry = entry2, history = history2, ...}) =
  let
    val history = merge (op =) (history1, history2);
    val entry = if hd history1 = hd history2 then join_same (entry1, entry2)
      else if hd history = hd history1 then entry1 else entry2;
  in {entry = entry, suppressed = false, history = history} end;

in

fun join join_same tables = Symtab.join (K (merge_history join_same)) tables;

fun suppress key = Symtab.map_entry key
  (fn {entry, history, ...} => {entry = entry, suppressed = true, history = history});

fun suppress_except f = Symtab.map (fn key => fn {entry, suppressed, history} =>
  {entry = entry, suppressed = suppressed orelse (not o f) (key, entry), history = history});

end;

end;

datatype specs = Specs of {
  types: ((string * sort) list * type_spec) History.T,
  pending_eqns: (thm * bool) list Symtab.table,
  functions: fun_spec History.T,
  cases: case_spec History.T
};

fun types_of (Specs {types, ...}) = types;
fun pending_eqns_of (Specs {pending_eqns, ...}) = pending_eqns;
fun functions_of (Specs {functions, ...}) = functions;
fun cases_of (Specs {cases, ...}) = cases;

fun make_specs (types, ((pending_eqns, functions), cases)) =
  Specs {types = types, pending_eqns = pending_eqns,
    functions = functions, cases = cases};

val empty_specs =
  make_specs (Symtab.empty, ((Symtab.empty, Symtab.empty), Symtab.empty));

fun map_specs f (Specs {types = types, pending_eqns = pending_eqns,
    functions = functions, cases = cases}) =
  make_specs (f (types, ((pending_eqns, functions), cases)));

fun merge_specs (Specs {types = types1, pending_eqns = _,
    functions = functions1, cases = cases1},
  Specs {types = types2, pending_eqns = _,
    functions = functions2, cases = cases2}) =
  let
    val types = History.join join_same_types (types1, types2);
    val all_types = map (snd o snd) (History.all types);
    fun check_abstype (c, fun_spec) = case associated_abstype fun_spec of
        NONE => true
      | SOME (tyco, abs) => (case History.lookup types tyco of
          NONE => false
        | SOME (_, Constructors _) => false
        | SOME (_, Abstractor {abstractor = (abs', _), projection, more_abstract_functions, ...}) =>
            abs = abs' andalso (c = projection orelse member (op =) more_abstract_functions c));
    fun check_datatypes (_, case_spec) =
      let
        val (tycos, required_constructors) = associated_datatypes case_spec;
        val allowed_constructors =
          tycos
          |> maps (these o Option.map (concrete_constructors_of o snd) o History.lookup types)
          |> map fst;
      in subset (op =) (required_constructors, allowed_constructors) end;
    val all_constructors =
      maps (fst o constructors_of) all_types;
    val functions = History.join fst (functions1, functions2)
      |> fold (History.suppress o fst) all_constructors
      |> History.suppress_except check_abstype;
    val cases = History.join fst (cases1, cases2)
      |> History.suppress_except check_datatypes;
  in make_specs (types, ((Symtab.empty, functions), cases)) end;

val map_types = map_specs o apfst;
val map_pending_eqns = map_specs o apsnd o apfst o apfst;
val map_functions = map_specs o apsnd o apfst o apsnd;
val map_cases = map_specs o apsnd o apsnd;


(* data slots dependent on executable code *)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = Table(type key = int val ord = int_ord);

local

type kind = {empty: Any.T};

val kinds = Synchronized.var "Code_Data" (Datatab.empty: kind Datatab.table);

fun invoke f k =
  (case Datatab.lookup (Synchronized.value kinds) k of
    SOME kind => f kind
  | NONE => raise Fail "Invalid code data identifier");

in

fun declare_data empty =
  let
    val k = serial ();
    val kind = {empty = empty};
    val _ = Synchronized.change kinds (Datatab.update (k, kind));
  in k end;

fun invoke_init k = invoke (fn kind => #empty kind) k;

end; (*local*)


(* global theory store *)

local

type data = Any.T Datatab.table;

fun make_dataref thy =
  (Context.theory_long_name thy,
    Synchronized.var "code data" (NONE : (data * Context.theory_id) option));

structure Code_Data = Theory_Data
(
  type T = specs * (string * (data * Context.theory_id) option Synchronized.var);
  val empty = (empty_specs, make_dataref (Context.the_global_context ()));
  val extend = I;
  fun merge ((specs1, dataref), (specs2, _)) =
    (merge_specs (specs1, specs2), dataref);
);

fun init_dataref thy =
  if #1 (#2 (Code_Data.get thy)) = Context.theory_long_name thy then NONE
  else SOME ((Code_Data.map o apsnd) (fn _ => make_dataref thy) thy)

in

val _ = Theory.setup (Theory.at_begin init_dataref);


(* access to executable specifications *)

val specs_of : theory -> specs = fst o Code_Data.get;

fun modify_specs f thy =
  Code_Data.map (fn (specs, _) => (f specs, make_dataref thy)) thy;


(* access to data dependent on executable specifications *)

fun change_yield_data (kind, mk, dest) theory f =
  let
    val dataref = #2 (#2 (Code_Data.get theory));
    val (datatab, thy_id) = case Synchronized.value dataref
     of SOME (datatab, thy_id) =>
        if Context.eq_thy_id (Context.theory_id theory, thy_id)
          then (datatab, thy_id)
          else (Datatab.empty, Context.theory_id theory)
      | NONE => (Datatab.empty, Context.theory_id theory)
    val data = case Datatab.lookup datatab kind
     of SOME data => data
      | NONE => invoke_init kind;
    val result as (_, data') = f (dest data);
    val _ = Synchronized.change dataref
      ((K o SOME) (Datatab.update (kind, mk data') datatab, thy_id));
  in result end;

end; (*local*)


(* pending function equations *)

(* Ideally, *all* equations implementing a functions would be treated as
   *one* atomic declaration;  unfortunately, we cannot implement this:
   the too-well-established declaration interface are Isar attributes
   which operate on *one* single theorem.  Hence we treat such Isar
   declarations as "pending" and historize them as proper declarations
   at the end of each theory. *)

fun modify_pending_eqns c f specs =
  let
    val existing_eqns = case History.lookup (functions_of specs) c of
        SOME (Eqns (false, eqns)) => eqns
      | _ => [];
  in
    specs
    |> map_pending_eqns (Symtab.map_default (c, existing_eqns) f)
  end;

fun register_fun_spec c spec =
  map_pending_eqns (Symtab.delete_safe c)
  #> map_functions (History.register c spec);

fun lookup_fun_spec specs c =
  case Symtab.lookup (pending_eqns_of specs) c of
    SOME eqns => Eqns (false, eqns)
  | NONE => (case History.lookup (functions_of specs) c of
      SOME spec => spec
    | NONE => unimplemented);

fun lookup_proper_fun_spec specs c =
  let
    val spec = lookup_fun_spec specs c
  in
    if is_unimplemented spec then NONE else SOME spec
  end;

fun all_fun_specs specs =
  map_filter (fn c => Option.map (pair c) (lookup_proper_fun_spec specs c))
    (union (op =)
      ((Symtab.keys o pending_eqns_of) specs)
      ((Symtab.keys o functions_of) specs));

fun historize_pending_fun_specs thy =
  let
    val pending_eqns = (pending_eqns_of o specs_of) thy;
  in if Symtab.is_empty pending_eqns
    then
      NONE
    else
      thy
      |> modify_specs (map_functions
          (Symtab.fold (fn (c, eqs) => History.register c (Eqns (false, eqs))) pending_eqns)
          #> map_pending_eqns (K Symtab.empty))
      |> SOME
  end;

val _ = Theory.setup (Theory.at_end historize_pending_fun_specs);


(** foundation **)

(* types *)

fun no_constr thy s (c, ty) = error ("Not a datatype constructor:\n" ^ string_of_const thy c
  ^ " :: " ^ string_of_typ thy ty ^ "\n" ^ enclose "(" ")" s);

fun analyze_constructor thy (c, ty) =
  let
    val _ = Thm.global_cterm_of thy (Const (c, ty));
    val ty_decl = devarify (const_typ thy c);
    fun last_typ c_ty ty =
      let
        val tfrees = Term.add_tfreesT ty [];
        val (tyco, vs) = (apsnd o map) dest_TFree (dest_Type (body_type ty))
          handle TYPE _ => no_constr thy "bad type" c_ty
        val _ = if tyco = "fun" then no_constr thy "bad type" c_ty else ();
        val _ =
          if has_duplicates (eq_fst (op =)) vs
          then no_constr thy "duplicate type variables in datatype" c_ty else ();
        val _ =
          if length tfrees <> length vs
          then no_constr thy "type variables missing in datatype" c_ty else ();
      in (tyco, vs) end;
    val (tyco, _) = last_typ (c, ty) ty_decl;
    val (_, vs) = last_typ (c, ty) ty;
  in ((tyco, map snd vs), (c, (map fst vs, ty))) end;

fun constrset_of_consts thy consts =
  let
    val _ = map (fn (c, _) => if (is_some o Axclass.class_of_param thy) c
      then error ("Is a class parameter: " ^ string_of_const thy c) else ()) consts;
    val raw_constructors = map (analyze_constructor thy) consts;
    val tyco = case distinct (op =) (map (fst o fst) raw_constructors)
     of [tyco] => tyco
      | [] => error "Empty constructor set"
      | tycos => error ("Different type constructors in constructor set: " ^ commas_quote tycos)
    val vs = Name.invent Name.context Name.aT (Sign.arity_number thy tyco);
    fun inst vs' (c, (vs, ty)) =
      let
        val the_v = the o AList.lookup (op =) (vs ~~ vs');
        val ty' = map_type_tfree (fn (v, _) => TFree (the_v v, [])) ty;
        val (vs'', ty'') = typscheme thy (c, ty');
      in (c, (vs'', binder_types ty'')) end;
    val constructors = map (inst vs o snd) raw_constructors;
  in (tyco, (map (rpair []) vs, constructors)) end;

fun lookup_vs_type_spec thy = History.lookup ((types_of o specs_of) thy);

type constructors =
  (string * sort) list * (string * ((string * sort) list * typ list)) list;

fun get_type thy tyco = case lookup_vs_type_spec thy tyco
 of SOME (vs, type_spec) => apfst (pair vs) (constructors_of type_spec)
  | NONE => Sign.arity_number thy tyco
      |> Name.invent Name.context Name.aT
      |> map (rpair [])
      |> rpair []
      |> rpair false;

type abs_type =
  (string * sort) list * {abs_rep: thm, abstractor: string * ((string * sort) list * typ), projection: string};

fun get_abstype_spec thy tyco = case lookup_vs_type_spec thy tyco of
    SOME (vs, Abstractor {abs_rep, abstractor, projection, ...}) =>
      (vs, {abs_rep = abs_rep, abstractor = abstractor, projection = projection})
  | _ => error ("Not an abstract type: " ^ tyco);

fun get_type_of_constr_or_abstr thy c =
  case (body_type o const_typ thy) c
   of Type (tyco, _) => let val ((_, cos), abstract) = get_type thy tyco
        in if member (op =) (map fst cos) c then SOME (tyco, abstract) else NONE end
    | _ => NONE;

fun is_constr thy c = case get_type_of_constr_or_abstr thy c
 of SOME (_, false) => true
   | _ => false;

fun is_abstr thy c = case get_type_of_constr_or_abstr thy c
 of SOME (_, true) => true
   | _ => false;


(* bare code equations *)

(* convention for variables:
    ?x ?'a   for free-floating theorems (e.g. in the data store)
    ?x  'a   for certificates
     x  'a   for final representation of equations
*)

exception BAD_THM of string;

fun bad_thm msg = raise BAD_THM msg;

datatype strictness = Silent | Liberal | Strict

fun handle_strictness thm_of f strictness thy x = SOME (f x)
  handle BAD_THM msg => case strictness of
    Silent => NONE
  | Liberal => (warning (msg ^ ", in theorem:\n" ^ Thm.string_of_thm_global thy (thm_of x)); NONE)
  | Strict => error (msg ^ ", in theorem:\n" ^ Thm.string_of_thm_global thy (thm_of x));

fun is_linear thm =
  let
    val (_, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm
  in
    not (has_duplicates (op =) ((fold o fold_aterms)
      (fn Var (v, _) => cons v | _ => I) args []))
  end;

fun check_decl_ty thy (c, ty) =
  let
    val ty_decl = const_typ thy c;
  in if typscheme_equiv (ty_decl, ty) then ()
    else bad_thm ("Type\n" ^ string_of_typ thy ty
      ^ "\nof constant " ^ quote c
      ^ "\nis too specific compared to declared type\n"
      ^ string_of_typ thy ty_decl)
  end;

fun check_eqn thy {allow_nonlinear, allow_consts, allow_pats} thm (lhs, rhs) =
  let
    fun vars_of t = fold_aterms (fn Var (v, _) => insert (op =) v
      | Free _ => bad_thm "Illegal free variable"
      | _ => I) t [];
    fun tvars_of t = fold_term_types (fn _ =>
      fold_atyps (fn TVar (v, _) => insert (op =) v
        | TFree _ => bad_thm "Illegal free type variable")) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of rhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad_thm "Free variables on right hand side of equation";
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad_thm "Free type variables on right hand side of equation";
    val (head, args) = strip_comb lhs;
    val (c, ty) = case head
     of Const (c_ty as (_, ty)) => (Axclass.unoverload_const thy c_ty, ty)
      | _ => bad_thm "Equation not headed by constant";
    fun check _ (Abs _) = bad_thm "Abstraction on left hand side of equation"
      | check 0 (Var _) = ()
      | check _ (Var _) = bad_thm "Variable with application on left hand side of equation"
      | check n (t1 $ t2) = (check (n+1) t1; check 0 t2)
      | check n (Const (c_ty as (c, ty))) =
          if allow_pats then let
            val c' = Axclass.unoverload_const thy c_ty
          in if n = (length o binder_types) ty
            then if allow_consts orelse is_constr thy c'
              then ()
              else bad_thm (quote c ^ " is not a constructor, on left hand side of equation")
            else bad_thm ("Partially applied constant " ^ quote c ^ " on left hand side of equation")
          end else bad_thm ("Pattern not allowed here, but constant " ^ quote c ^ " encountered on left hand side of equation")
    val _ = map (check 0) args;
    val _ = if allow_nonlinear orelse is_linear thm then ()
      else bad_thm "Duplicate variables on left hand side of equation";
    val _ = if (is_none o Axclass.class_of_param thy) c then ()
      else bad_thm "Overloaded constant as head in equation";
    val _ = if not (is_constr thy c) then ()
      else bad_thm "Constructor as head in equation";
    val _ = if not (is_abstr thy c) then ()
      else bad_thm "Abstractor as head in equation";
    val _ = check_decl_ty thy (c, ty);
    val _ = case strip_type ty of
        (Type (tyco, _) :: _, _) => (case lookup_vs_type_spec thy tyco of
          SOME (_, type_spec) => (case projection_of type_spec of
            SOME proj =>
              if c = proj
              then bad_thm "Projection as head in equation"
              else ()
          | _ => ())
        | _ => ())
      | _ => ();
  in () end;

local

fun raw_assert_eqn thy check_patterns (thm, proper) =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm
      handle TERM _ => bad_thm "Not an equation"
           | THM _ => bad_thm "Not a proper equation";
    val _ = check_eqn thy {allow_nonlinear = not proper,
      allow_consts = not (proper andalso check_patterns), allow_pats = true} thm (lhs, rhs);
  in (thm, proper) end;

fun raw_assert_abs_eqn thy some_tyco thm =
  let
    val (full_lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm
      handle TERM _ => bad_thm "Not an equation"
           | THM _ => bad_thm "Not a proper equation";
    val (proj_t, lhs) = dest_comb full_lhs
      handle TERM _ => bad_thm "Not an abstract equation";
    val (proj, ty) = dest_Const proj_t
      handle TERM _ => bad_thm "Not an abstract equation";
    val (tyco, Ts) = (dest_Type o domain_type) ty
      handle TERM _ => bad_thm "Not an abstract equation"
           | TYPE _ => bad_thm "Not an abstract equation";
    val _ = case some_tyco of SOME tyco' => if tyco = tyco' then ()
          else bad_thm ("Abstract type mismatch:" ^ quote tyco ^ " vs. " ^ quote tyco')
      | NONE => ();
    val (vs, proj', (abs', _)) = case lookup_vs_type_spec thy tyco
     of SOME (vs, Abstractor spec) => (vs, #projection spec, #abstractor spec)
      | _ => bad_thm ("Not an abstract type: " ^ tyco);
    val _ = if proj = proj' then ()
      else bad_thm ("Projection mismatch: " ^ quote proj ^ " vs. " ^ quote proj');
    val _ = check_eqn thy {allow_nonlinear = false,
      allow_consts = false, allow_pats = false} thm (lhs, rhs);
    val _ = if ListPair.all (fn (T, (_, sort)) => Sign.of_sort thy (T, sort)) (Ts, vs) then ()
      else error ("Type arguments do not satisfy sort constraints of abstype certificate.");
  in (thm, (tyco, abs')) end;

in

fun generic_assert_eqn strictness thy check_patterns eqn =
  handle_strictness fst (raw_assert_eqn thy check_patterns) strictness thy eqn;

fun generic_assert_abs_eqn strictness thy check_patterns thm =
  handle_strictness I (raw_assert_abs_eqn thy check_patterns) strictness thy thm;

end;

fun assert_eqn thy = the o generic_assert_eqn Strict thy true;

fun assert_abs_eqn thy some_tyco = the o generic_assert_abs_eqn Strict thy some_tyco;

val head_eqn = dest_Const o fst o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;

fun const_typ_eqn thy thm =
  let
    val (c, ty) = head_eqn thm;
    val c' = Axclass.unoverload_const thy (c, ty);
      (*permissive wrt. to overloaded constants!*)
  in (c', ty) end;

fun const_eqn thy = fst o const_typ_eqn thy;

fun const_abs_eqn thy = Axclass.unoverload_const thy o dest_Const o fst o strip_comb o snd
  o dest_comb o fst o Logic.dest_equals o Thm.plain_prop_of;

fun mk_proj tyco vs ty abs rep =
  let
    val ty_abs = Type (tyco, map TFree vs);
    val xarg = Var (("x", 0), ty);
  in Logic.mk_equals (Const (rep, ty_abs --> ty) $ (Const (abs, ty --> ty_abs) $ xarg), xarg) end;


(* technical transformations of code equations *)

fun meta_rewrite thy = Local_Defs.meta_rewrite_rule (Proof_Context.init_global thy);

fun expand_eta thy k thm =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm;
    val (_, args) = strip_comb lhs;
    val l = if k = ~1
      then (length o fst o strip_abs) rhs
      else Int.max (0, k - length args);
    val (raw_vars, _) = Term.strip_abs_eta l rhs;
    val vars = burrow_fst (Name.variant_list (map (fst o fst) (Term.add_vars lhs [])))
      raw_vars;
    fun expand (v, ty) thm = Drule.fun_cong_rule thm
      (Thm.global_cterm_of thy (Var ((v, 0), ty)));
  in
    thm
    |> fold expand vars
    |> Conv.fconv_rule Drule.beta_eta_conversion
  end;

fun same_arity thy thms =
  let
    val num_args_of = length o snd o strip_comb o fst o Logic.dest_equals;
    val k = fold (Integer.max o num_args_of o Thm.prop_of) thms 0;
  in map (expand_eta thy k) thms end;

fun mk_desymbolization pre post mk vs =
  let
    val names = map (pre o fst o fst) vs
      |> map (Name.desymbolize (SOME false))
      |> Name.variant_list []
      |> map post;
  in map_filter (fn (((v, i), x), v') =>
    if v = v' andalso i = 0 then NONE
    else SOME (((v, i), x), mk ((v', 0), x))) (vs ~~ names)
  end;

fun desymbolize_tvars thy thms =
  let
    val tvs = fold (Term.add_tvars o Thm.prop_of) thms [];
    val instT =
      mk_desymbolization (unprefix "'") (prefix "'") (Thm.global_ctyp_of thy o TVar) tvs;
  in map (Thm.instantiate (instT, [])) thms end;

fun desymbolize_vars thy thm =
  let
    val vs = Term.add_vars (Thm.prop_of thm) [];
    val inst = mk_desymbolization I I (Thm.global_cterm_of thy o Var) vs;
  in Thm.instantiate ([], inst) thm end;

fun canonize_thms thy = desymbolize_tvars thy #> same_arity thy #> map (desymbolize_vars thy);


(* preparation and classification of code equations *)

fun prep_eqn strictness thy =
  apfst (meta_rewrite thy)
  #> generic_assert_eqn strictness thy false
  #> Option.map (fn eqn => (const_eqn thy (fst eqn), eqn));

fun prep_eqns strictness thy =
  map_filter (prep_eqn strictness thy)
  #> AList.group (op =);

fun prep_abs_eqn strictness thy =
  meta_rewrite thy
  #> generic_assert_abs_eqn strictness thy NONE
  #> Option.map (fn abs_eqn => (const_abs_eqn thy (fst abs_eqn), abs_eqn));

fun prep_maybe_abs_eqn thy raw_thm =
  let
    val thm = meta_rewrite thy raw_thm;
    val some_abs_thm = generic_assert_abs_eqn Silent thy NONE thm;
  in case some_abs_thm of
      SOME (thm, tyco) => SOME (const_abs_eqn thy thm, ((thm, true), SOME tyco))
    | NONE => generic_assert_eqn Liberal thy false (thm, false)
        |> Option.map (fn (thm, _) => (const_eqn thy thm, ((thm, is_linear thm), NONE)))
  end;


(* abstype certificates *)

local

fun raw_abstype_cert thy proto_thm =
  let
    val thm = (Axclass.unoverload (Proof_Context.init_global thy) o meta_rewrite thy) proto_thm;
    val (lhs, rhs) = Logic.dest_equals (Thm.plain_prop_of thm)
      handle TERM _ => bad_thm "Not an equation"
           | THM _ => bad_thm "Not a proper equation";
    val ((abs, raw_ty), ((rep, rep_ty), param)) = (apsnd (apfst dest_Const o dest_comb)
        o apfst dest_Const o dest_comb) lhs
      handle TERM _ => bad_thm "Not an abstype certificate";
    val _ = apply2 (fn c => if (is_some o Axclass.class_of_param thy) c
      then error ("Is a class parameter: " ^ string_of_const thy c) else ()) (abs, rep);
    val _ = check_decl_ty thy (abs, raw_ty);
    val _ = check_decl_ty thy (rep, rep_ty);
    val _ = if length (binder_types raw_ty) = 1
      then ()
      else bad_thm "Bad type for abstract constructor";
    val _ = (fst o dest_Var) param
      handle TERM _ => bad_thm "Not an abstype certificate";
    val _ = if param = rhs then () else bad_thm "Not an abstype certificate";
    val ((tyco, sorts), (abs, (vs, ty'))) =
      analyze_constructor thy (abs, devarify raw_ty);
    val ty = domain_type ty';
    val (vs', _) = typscheme thy (abs, ty');
  in (tyco, (vs ~~ sorts, ((abs, (vs', ty)), (rep, thm)))) end;

in

fun check_abstype_cert strictness thy proto_thm =
  handle_strictness I (raw_abstype_cert thy) strictness thy proto_thm;

end;


(* code equation certificates *)

fun build_head thy (c, ty) =
  Thm.global_cterm_of thy (Logic.mk_equals (Free ("HEAD", ty), Const (c, ty)));

fun get_head thy cert_thm =
  let
    val [head] = Thm.chyps_of cert_thm;
    val (_, Const (c, ty)) = (Logic.dest_equals o Thm.term_of) head;
  in (typscheme thy (c, ty), head) end;

fun typscheme_projection thy =
  typscheme thy o dest_Const o fst o dest_comb o fst o Logic.dest_equals;

fun typscheme_abs thy =
  typscheme thy o dest_Const o fst o strip_comb o snd o dest_comb o fst o Logic.dest_equals o Thm.prop_of;

fun constrain_thm thy vs sorts thm =
  let
    val mapping = map2 (fn (v, sort) => fn sort' =>
      (v, Sorts.inter_sort (Sign.classes_of thy) (sort, sort'))) vs sorts;
    val inst = map2 (fn (v, sort) => fn (_, sort') =>
      (((v, 0), sort), Thm.global_ctyp_of thy (TFree (v, sort')))) vs mapping;
    val subst = (Term.map_types o map_type_tfree)
      (fn (v, _) => TFree (v, the (AList.lookup (op =) mapping v)));
  in
    thm
    |> Thm.varifyT_global
    |> Thm.instantiate (inst, [])
    |> pair subst
  end;

fun concretify_abs thy tyco abs_thm =
  let
    val (_, {abstractor = (c_abs, _), abs_rep, ...}) = get_abstype_spec thy tyco;
    val lhs = (fst o Logic.dest_equals o Thm.prop_of) abs_thm
    val ty = fastype_of lhs;
    val ty_abs = (fastype_of o snd o dest_comb) lhs;
    val abs = Thm.global_cterm_of thy (Const (c_abs, ty --> ty_abs));
    val raw_concrete_thm = Drule.transitive_thm OF [Thm.symmetric abs_rep, Thm.combination (Thm.reflexive abs) abs_thm];
  in (c_abs, (Thm.varifyT_global o zero_var_indexes) raw_concrete_thm) end;

fun add_rhss_of_eqn thy t =
  let
    val (args, rhs) = (apfst (snd o strip_comb) o Logic.dest_equals) t;
    fun add_const (Const (c, ty)) = insert (op =) (c, Sign.const_typargs thy (c, ty))
      | add_const _ = I
    val add_consts = fold_aterms add_const
  in add_consts rhs o fold add_consts args end;

val dest_eqn = apfst (snd o strip_comb) o Logic.dest_equals o Logic.unvarify_global;

abstype cert = Nothing of thm
  | Equations of thm * bool list
  | Projection of term * string
  | Abstract of thm * string
with

fun dummy_thm ctxt c =
  let
    val thy = Proof_Context.theory_of ctxt;
    val raw_ty = devarify (const_typ thy c);
    val (vs, _) = typscheme thy (c, raw_ty);
    val sortargs = case Axclass.class_of_param thy c
     of SOME class => [[class]]
      | NONE => (case get_type_of_constr_or_abstr thy c
         of SOME (tyco, _) => (map snd o fst o the)
              (AList.lookup (op =) ((snd o fst o get_type thy) tyco) c)
          | NONE => replicate (length vs) []);
    val the_sort = the o AList.lookup (op =) (map fst vs ~~ sortargs);
    val ty = map_type_tfree (fn (v, _) => TFree (v, the_sort v)) raw_ty
    val chead = build_head thy (c, ty);
  in Thm.weaken chead Drule.dummy_thm end;

fun nothing_cert ctxt c = Nothing (dummy_thm ctxt c);

fun cert_of_eqns ctxt c [] = Equations (dummy_thm ctxt c, [])
  | cert_of_eqns ctxt c raw_eqns =
      let
        val thy = Proof_Context.theory_of ctxt;
        val eqns = burrow_fst (canonize_thms thy) raw_eqns;
        val _ = map (assert_eqn thy) eqns;
        val (thms, propers) = split_list eqns;
        val _ = map (fn thm => if c = const_eqn thy thm then ()
          else error ("Wrong head of code equation,\nexpected constant "
            ^ string_of_const thy c ^ "\n" ^ Thm.string_of_thm_global thy thm)) thms;
        fun tvars_of T = rev (Term.add_tvarsT T []);
        val vss = map (tvars_of o snd o head_eqn) thms;
        fun inter_sorts vs =
          fold (curry (Sorts.inter_sort (Sign.classes_of thy)) o snd) vs [];
        val sorts = map_transpose inter_sorts vss;
        val vts = Name.invent_names Name.context Name.aT sorts;
        val thms' =
          map2 (fn vs => Thm.instantiate (vs ~~ map (Thm.ctyp_of ctxt o TFree) vts, [])) vss thms;
        val head_thm = Thm.symmetric (Thm.assume (build_head thy (head_eqn (hd thms'))));
        fun head_conv ct = if can Thm.dest_comb ct
          then Conv.fun_conv head_conv ct
          else Conv.rewr_conv head_thm ct;
        val rewrite_head = Conv.fconv_rule (Conv.arg1_conv head_conv);
        val cert_thm = Conjunction.intr_balanced (map rewrite_head thms');
      in Equations (cert_thm, propers) end;

fun cert_of_proj ctxt proj tyco =
  let
    val thy = Proof_Context.theory_of ctxt
    val (vs, {abstractor = (abs, (_, ty)), projection = proj', ...}) = get_abstype_spec thy tyco;
    val _ = if proj = proj' then () else
      error ("Wrong head of projection,\nexpected constant " ^ string_of_const thy proj);
  in Projection (mk_proj tyco vs ty abs proj, tyco) end;

fun cert_of_abs ctxt tyco c raw_abs_thm =
  let
    val thy = Proof_Context.theory_of ctxt;
    val abs_thm = singleton (canonize_thms thy) raw_abs_thm;
    val _ = assert_abs_eqn thy (SOME tyco) abs_thm;
    val _ = if c = const_abs_eqn thy abs_thm then ()
      else error ("Wrong head of abstract code equation,\nexpected constant "
        ^ string_of_const thy c ^ "\n" ^ Thm.string_of_thm_global thy abs_thm);
  in Abstract (Thm.legacy_freezeT abs_thm, tyco) end;

fun constrain_cert_thm thy sorts cert_thm =
  let
    val ((vs, _), head) = get_head thy cert_thm;
    val (subst, cert_thm') = cert_thm
      |> Thm.implies_intr head
      |> constrain_thm thy vs sorts;
    val head' = Thm.term_of head
      |> subst
      |> Thm.global_cterm_of thy;
    val cert_thm'' = cert_thm'
      |> Thm.elim_implies (Thm.assume head');
  in cert_thm'' end;

fun constrain_cert thy sorts (Nothing cert_thm) =
      Nothing (constrain_cert_thm thy sorts cert_thm)
  | constrain_cert thy sorts (Equations (cert_thm, propers)) =
      Equations (constrain_cert_thm thy sorts cert_thm, propers)
  | constrain_cert _ _ (cert as Projection _) =
      cert
  | constrain_cert thy sorts (Abstract (abs_thm, tyco)) =
      Abstract (snd (constrain_thm thy (fst (typscheme_abs thy abs_thm)) sorts abs_thm), tyco);

fun conclude_cert (Nothing cert_thm) =
      Nothing (Thm.close_derivation \<^here> cert_thm)
  | conclude_cert (Equations (cert_thm, propers)) =
      Equations (Thm.close_derivation \<^here> cert_thm, propers)
  | conclude_cert (cert as Projection _) =
      cert
  | conclude_cert (Abstract (abs_thm, tyco)) =
      Abstract (Thm.close_derivation \<^here> abs_thm, tyco);

fun typscheme_of_cert thy (Nothing cert_thm) =
      fst (get_head thy cert_thm)
  | typscheme_of_cert thy (Equations (cert_thm, _)) =
      fst (get_head thy cert_thm)
  | typscheme_of_cert thy (Projection (proj, _)) =
      typscheme_projection thy proj
  | typscheme_of_cert thy (Abstract (abs_thm, _)) =
      typscheme_abs thy abs_thm;

fun typargs_deps_of_cert thy (Nothing cert_thm) =
      let
        val vs = (fst o fst) (get_head thy cert_thm);
      in (vs, []) end
  | typargs_deps_of_cert thy (Equations (cert_thm, propers)) =
      let
        val vs = (fst o fst) (get_head thy cert_thm);
        val equations = if null propers then [] else
          Thm.prop_of cert_thm
          |> Logic.dest_conjunction_balanced (length propers);
      in (vs, fold (add_rhss_of_eqn thy) equations []) end
  | typargs_deps_of_cert thy (Projection (t, _)) =
      (fst (typscheme_projection thy t), add_rhss_of_eqn thy t [])
  | typargs_deps_of_cert thy (Abstract (abs_thm, tyco)) =
      let
        val vs = fst (typscheme_abs thy abs_thm);
        val (_, concrete_thm) = concretify_abs thy tyco abs_thm;
      in (vs, add_rhss_of_eqn thy (Logic.unvarify_types_global (Thm.prop_of concrete_thm)) []) end;

fun equations_of_cert thy (cert as Nothing _) =
      (typscheme_of_cert thy cert, NONE)
  | equations_of_cert thy (cert as Equations (cert_thm, propers)) =
      let
        val tyscm = typscheme_of_cert thy cert;
        val thms = if null propers then [] else
          cert_thm
          |> Local_Defs.expand [snd (get_head thy cert_thm)]
          |> Thm.varifyT_global
          |> Conjunction.elim_balanced (length propers);
        fun abstractions (args, rhs) = (map (rpair NONE) args, (rhs, NONE));
      in (tyscm, SOME (map (abstractions o dest_eqn o Thm.prop_of) thms ~~ (map SOME thms ~~ propers))) end
  | equations_of_cert thy (Projection (t, tyco)) =
      let
        val (_, {abstractor = (abs, _), ...}) = get_abstype_spec thy tyco;
        val tyscm = typscheme_projection thy t;
        val t' = Logic.varify_types_global t;
        fun abstractions (args, rhs) = (map (rpair (SOME abs)) args, (rhs, NONE));
      in (tyscm, SOME [((abstractions o dest_eqn) t', (NONE, true))]) end
  | equations_of_cert thy (Abstract (abs_thm, tyco)) =
      let
        val tyscm = typscheme_abs thy abs_thm;
        val (abs, concrete_thm) = concretify_abs thy tyco abs_thm;
        fun abstractions (args, rhs) = (map (rpair NONE) args, (rhs, (SOME abs)));
      in
        (tyscm, SOME [((abstractions o dest_eqn o Thm.prop_of) concrete_thm,
          (SOME (Thm.varifyT_global abs_thm), true))])
      end;

fun pretty_cert _ (Nothing _) =
      []
  | pretty_cert thy (cert as Equations _) =
      (map_filter
        (Option.map (Thm.pretty_thm_global thy o
            Axclass.overload (Proof_Context.init_global thy)) o fst o snd)
         o these o snd o equations_of_cert thy) cert
  | pretty_cert thy (Projection (t, _)) =
      [Syntax.pretty_term_global thy (Logic.varify_types_global t)]
  | pretty_cert thy (Abstract (abs_thm, _)) =
      [(Thm.pretty_thm_global thy o
         Axclass.overload (Proof_Context.init_global thy) o Thm.varifyT_global) abs_thm];

end;


(* code certificate access with preprocessing *)

fun eqn_conv conv ct =
  let
    fun lhs_conv ct = if can Thm.dest_comb ct
      then Conv.combination_conv lhs_conv conv ct
      else Conv.all_conv ct;
  in Conv.combination_conv (Conv.arg_conv lhs_conv) conv ct end;

fun rewrite_eqn conv ctxt =
  singleton (Variable.trade (K (map (Conv.fconv_rule (conv (Simplifier.rewrite ctxt))))) ctxt)

fun preprocess conv ctxt =
  Thm.transfer' ctxt
  #> rewrite_eqn conv ctxt
  #> Axclass.unoverload ctxt;

fun cert_of_eqns_preprocess ctxt functrans c =
  let
    fun trace_eqns s eqns = (Pretty.writeln o Pretty.chunks)
      (Pretty.str s :: map (Thm.pretty_thm ctxt o fst) eqns);
    val tracing = if Config.get ctxt simp_trace then trace_eqns else (K o K) ();
  in
    tap (tracing "before function transformation")
    #> (perhaps o perhaps_loop o perhaps_apply) functrans
    #> tap (tracing "after function transformation")
    #> (map o apfst) (preprocess eqn_conv ctxt)
    #> cert_of_eqns ctxt c
  end;

fun get_cert ctxt functrans c =
  case lookup_proper_fun_spec (specs_of (Proof_Context.theory_of ctxt)) c of
    NONE => nothing_cert ctxt c
  | SOME (Eqns (_, eqns)) => eqns
      |> cert_of_eqns_preprocess ctxt functrans c
  | SOME (Proj (_, (tyco, _))) => cert_of_proj ctxt c tyco
  | SOME (Abstr (abs_thm, (tyco, _))) => abs_thm
     |> preprocess Conv.arg_conv ctxt
     |> cert_of_abs ctxt tyco c;


(* case certificates *)

local

fun raw_case_cert thm =
  let
    val ((head, raw_case_expr), cases) = (apfst Logic.dest_equals
      o apsnd Logic.dest_conjunctions o Logic.dest_implies o Thm.plain_prop_of) thm;
    val _ = case head of Free _ => ()
      | Var _ => ()
      | _ => raise TERM ("case_cert", []);
    val ([(case_var, _)], case_expr) = Term.strip_abs_eta 1 raw_case_expr;
    val (Const (case_const, _), raw_params) = strip_comb case_expr;
    val n = find_index (fn Free (v, _) => v = case_var | _ => false) raw_params;
    val _ = if n = ~1 then raise TERM ("case_cert", []) else ();
    val params = map (fst o dest_Var) (nth_drop n raw_params);
    fun dest_case t =
      let
        val (head' $ t_co, rhs) = Logic.dest_equals t;
        val _ = if head' = head then () else raise TERM ("case_cert", []);
        val (Const (co, _), args) = strip_comb t_co;
        val (Var (param, _), args') = strip_comb rhs;
        val _ = if args' = args then () else raise TERM ("case_cert", []);
      in (param, co) end;
    fun analyze_cases cases =
      let
        val co_list = fold (AList.update (op =) o dest_case) cases [];
      in map (AList.lookup (op =) co_list) params end;
    fun analyze_let t =
      let
        val (head' $ arg, Var (param', _) $ arg') = Logic.dest_equals t;
        val _ = if head' = head then () else raise TERM ("case_cert", []);
        val _ = if arg' = arg then () else raise TERM ("case_cert", []);
        val _ = if [param'] = params then () else raise TERM ("case_cert", []);
      in [] end;
    fun analyze (cases as [let_case]) =
          (analyze_cases cases handle Bind => analyze_let let_case)
      | analyze cases = analyze_cases cases;
  in (case_const, (n, analyze cases)) end;

in

fun case_cert thm = raw_case_cert thm
  handle Bind => error "bad case certificate"
       | TERM _ => error "bad case certificate";

end;

fun lookup_case_spec thy = History.lookup ((cases_of o specs_of) thy);

fun get_case_schema thy c = case lookup_case_spec thy c of
    SOME (Case {schema, ...}) => SOME schema
  | _ => NONE;

fun get_case_cong thy c = case lookup_case_spec thy c of
    SOME (Case {cong, ...}) => SOME cong
  | _ => NONE;

fun is_undefined thy c = case lookup_case_spec thy c of
    SOME Undefined => true
  | _ => false;


(* diagnostic *)

fun print_codesetup thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val specs = specs_of thy;
    fun pretty_equations const thms =
      (Pretty.block o Pretty.fbreaks)
        (Pretty.str (string_of_const thy const) :: map (Thm.pretty_thm_item ctxt) thms);
    fun pretty_function (const, Eqns (_, eqns)) =
          pretty_equations const (map fst eqns)
      | pretty_function (const, Proj (proj, _)) = Pretty.block
          [Pretty.str (string_of_const thy const), Pretty.fbrk, Syntax.pretty_term ctxt proj]
      | pretty_function (const, Abstr (thm, _)) = pretty_equations const [thm];
    fun pretty_typ (tyco, vs) = Pretty.str
      (string_of_typ thy (Type (tyco, map TFree vs)));
    fun pretty_type_spec (typ, (cos, abstract)) = if null cos
      then pretty_typ typ
      else (Pretty.block o Pretty.breaks) (
        pretty_typ typ
        :: Pretty.str "="
        :: (if abstract then [Pretty.str "(abstract)"] else [])
        @ separate (Pretty.str "|") (map (fn (c, (_, [])) => Pretty.str (string_of_const thy c)
             | (c, (_, tys)) =>
                 (Pretty.block o Pretty.breaks)
                    (Pretty.str (string_of_const thy c)
                      :: Pretty.str "of"
                      :: map (Pretty.quote o Syntax.pretty_typ_global thy) tys)) cos)
      );
    fun pretty_case_param NONE = "<ignored>"
      | pretty_case_param (SOME c) = string_of_const thy c
    fun pretty_case (const, Case {schema = (_, (_, [])), ...}) =
          Pretty.str (string_of_const thy const)
      | pretty_case (const, Case {schema = (_, (_, cos)), ...}) =
          (Pretty.block o Pretty.breaks) [
            Pretty.str (string_of_const thy const), Pretty.str "with",
            (Pretty.block o Pretty.commas o map (Pretty.str o pretty_case_param)) cos]
      | pretty_case (const, Undefined) =
          (Pretty.block o Pretty.breaks) [
            Pretty.str (string_of_const thy const), Pretty.str "<undefined>"];
    val functions = all_fun_specs specs
      |> sort (string_ord o apply2 fst);
    val types = History.all (types_of specs)
      |> map (fn (tyco, (vs, spec)) =>
          ((tyco, vs), constructors_of spec))
      |> sort (string_ord o apply2 (fst o fst));
    val cases = History.all (cases_of specs)
      |> filter (fn (_, No_Case) => false | _ => true)
      |> sort (string_ord o apply2 fst);
  in
    Pretty.writeln_chunks [
      Pretty.block (
        Pretty.str "types:" :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_type_spec) types
      ),
      Pretty.block (
        Pretty.str "functions:" :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_function) functions
      ),
      Pretty.block (
        Pretty.str "cases:" :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_case) cases
      )
    ]
  end;


(** declaration of executable ingredients **)

(* plugins for dependent applications *)

structure Codetype_Plugin = Plugin(type T = string);

val codetype_plugin = Plugin_Name.declare_setup \<^binding>\<open>codetype\<close>;

fun type_interpretation f =
  Codetype_Plugin.interpretation codetype_plugin
    (fn tyco => Local_Theory.background_theory
      (fn thy =>
        thy
        |> Sign.root_path
        |> Sign.add_path (Long_Name.qualifier tyco)
        |> f tyco
        |> Sign.restore_naming thy));

fun datatype_interpretation f =
  type_interpretation (fn tyco => fn thy =>
    case get_type thy tyco of
      (spec, false) => f (tyco, spec) thy
    | (_, true) => thy
  );

fun abstype_interpretation f =
  type_interpretation (fn tyco => fn thy =>
    case try (get_abstype_spec thy) tyco of
      SOME spec => f (tyco, spec) thy
    | NONE => thy
  );

fun register_tyco_for_plugin tyco =
  Named_Target.theory_map (Codetype_Plugin.data_default tyco);


(* abstract code declarations *)

local

fun generic_code_declaration strictness lift_phi f x =
  Local_Theory.declaration
    {syntax = false, pervasive = false}
    (fn phi => Context.mapping (f strictness (lift_phi phi x)) I);

in

fun silent_code_declaration lift_phi = generic_code_declaration Silent lift_phi;
fun code_declaration lift_phi = generic_code_declaration Liberal lift_phi;

end;


(* types *)

fun invalidate_constructors_of (_, type_spec) =
  fold (fn (c, _) => History.register c unimplemented) (fst (constructors_of type_spec));

fun invalidate_abstract_functions_of (_, type_spec) =
  fold (fn c => History.register c unimplemented) (abstract_functions_of type_spec);

fun invalidate_case_combinators_of (_, type_spec) =
  fold (fn c => History.register c No_Case) (case_combinators_of type_spec);

fun register_type (tyco, vs_typ_spec) specs =
  let
    val olds = the_list (History.lookup (types_of specs) tyco);
  in
    specs
    |> map_functions (fold invalidate_abstract_functions_of olds
        #> invalidate_constructors_of vs_typ_spec)
    |> map_cases (fold invalidate_case_combinators_of olds)
    |> map_types (History.register tyco vs_typ_spec)
  end;

fun declare_datatype_global proto_constrs thy =
  let
    fun unoverload_const_typ (c, ty) =
      (Axclass.unoverload_const thy (c, ty), ty);
    val constrs = map unoverload_const_typ proto_constrs;
    val (tyco, (vs, cos)) = constrset_of_consts thy constrs;
  in
    thy
    |> modify_specs (register_type
        (tyco, (vs, Constructors {constructors = cos, case_combinators = []})))
    |> register_tyco_for_plugin tyco
  end;

fun declare_datatype_cmd raw_constrs thy =
  declare_datatype_global (map (read_bare_const thy) raw_constrs) thy;

fun generic_declare_abstype strictness proto_thm thy =
  case check_abstype_cert strictness thy proto_thm of
    SOME (tyco, (vs, (abstractor as (abs, (_, ty)), (proj, abs_rep)))) =>
      thy
      |> modify_specs (register_type
            (tyco, (vs, Abstractor {abstractor = abstractor, projection = proj, abs_rep = abs_rep, more_abstract_functions = []}))
          #> register_fun_spec proj
            (Proj (Logic.varify_types_global (mk_proj tyco vs ty abs proj), (tyco, abs))))
      |> register_tyco_for_plugin tyco
  | NONE => thy;

val declare_abstype_global = generic_declare_abstype Strict;

val declare_abstype =
  code_declaration Morphism.thm generic_declare_abstype;


(* functions *)

(*
  strictness wrt. shape of theorem propositions:
    * default equations: silent
    * using declarations and attributes: warnings (after morphism application!)
    * using global declarations (... -> thy -> thy): strict
    * internal processing after storage: strict
*)

local

fun subsumptive_add thy verbose (thm, proper) eqns =
  let
    val args_of = drop_prefix is_Var o rev o snd o strip_comb
      o Term.map_types Type.strip_sorts o fst o Logic.dest_equals o Thm.plain_prop_of
      o Thm.transfer thy;
    val args = args_of thm;
    val incr_idx = Logic.incr_indexes ([], [], Thm.maxidx_of thm + 1);
    fun matches_args args' =
      let
        val k = length args' - length args
      in if k >= 0
        then Pattern.matchess thy (args, (map incr_idx o drop k) args')
        else false
      end;
    fun drop (thm', proper') = if (proper orelse not proper')
      andalso matches_args (args_of thm') then
        (if verbose then warning ("Code generator: dropping subsumed code equation\n" ^
            Thm.string_of_thm_global thy thm') else (); true)
      else false;
  in (thm |> Thm.close_derivation \<^here> |> Thm.trim_context, proper) :: filter_out drop eqns end;

fun add_eqn_for (c, eqn) thy =
  thy |> modify_specs (modify_pending_eqns c (subsumptive_add thy true eqn));

fun add_eqns_for default (c, proto_eqns) thy =
  thy |> modify_specs (fn specs =>
    if is_default (lookup_fun_spec specs c) orelse not default
    then
      let
        val eqns = []
          |> fold_rev (subsumptive_add thy (not default)) proto_eqns;
      in specs |> register_fun_spec c (Eqns (default, eqns)) end
    else specs);

fun add_abstract_for (c, (thm, tyco_abs as (tyco, _))) =
  modify_specs (register_fun_spec c (Abstr (Thm.close_derivation \<^here> thm, tyco_abs))
    #> map_types (History.modify_entry tyco (add_abstract_function c)))

in

fun generic_declare_eqns default strictness raw_eqns thy =
  fold (add_eqns_for default) (prep_eqns strictness thy raw_eqns) thy;

fun generic_add_eqn strictness raw_eqn thy =
  fold add_eqn_for (the_list (prep_eqn strictness thy raw_eqn)) thy;

fun generic_declare_abstract_eqn strictness raw_abs_eqn thy =
  fold add_abstract_for (the_list (prep_abs_eqn strictness thy raw_abs_eqn)) thy;

fun add_maybe_abs_eqn_liberal thm thy =
  case prep_maybe_abs_eqn thy thm
   of SOME (c, (eqn, NONE)) => add_eqn_for (c, eqn) thy
    | SOME (c, ((thm, _), SOME tyco)) => add_abstract_for (c, (thm, tyco)) thy
    | NONE => thy;

end;

val declare_default_eqns_global = generic_declare_eqns true Silent;

val declare_default_eqns =
  silent_code_declaration (map o apfst o Morphism.thm) (generic_declare_eqns true);

val declare_eqns_global = generic_declare_eqns false Strict;

val declare_eqns =
  code_declaration (map o apfst o Morphism.thm) (generic_declare_eqns false);

val add_eqn_global = generic_add_eqn Strict;

fun del_eqn_global thm thy =
  case prep_eqn Liberal thy (thm, false) of
    SOME (c, (thm, _)) =>
      modify_specs (modify_pending_eqns c (filter_out (fn (thm', _) => Thm.eq_thm_prop (thm, thm')))) thy
  | NONE => thy;

val declare_abstract_eqn_global = generic_declare_abstract_eqn Strict;

val declare_abstract_eqn =
  code_declaration Morphism.thm generic_declare_abstract_eqn;

fun declare_aborting_global c =
  modify_specs (register_fun_spec c aborting);

fun declare_unimplemented_global c =
  modify_specs (register_fun_spec c unimplemented);


(* cases *)

fun case_cong thy case_const (num_args, (pos, _)) =
  let
    val ([x, y], ctxt) = fold_map Name.variant ["A", "A'"] Name.context;
    val (zs, _) = fold_map Name.variant (replicate (num_args - 1) "") ctxt;
    val (ws, vs) = chop pos zs;
    val T = devarify (const_typ thy case_const);
    val Ts = binder_types T;
    val T_cong = nth Ts pos;
    fun mk_prem z = Free (z, T_cong);
    fun mk_concl z = list_comb (Const (case_const, T), map2 (curry Free) (ws @ z :: vs) Ts);
    val (prem, concl) = apply2 Logic.mk_equals (apply2 mk_prem (x, y), apply2 mk_concl (x, y));
  in
    Goal.prove_sorry_global thy (x :: y :: zs) [prem] concl
      (fn {context = ctxt', prems} =>
        Simplifier.rewrite_goals_tac ctxt' prems
        THEN ALLGOALS (Proof_Context.fact_tac ctxt' [Drule.reflexive_thm]))
  end;

fun declare_case_global thm thy =
  let
    val (case_const, (k, cos)) = case_cert thm;
    fun get_type_of_constr c = case get_type_of_constr_or_abstr thy c of
        SOME (c, false) => SOME c
      | _ => NONE;
    val cos_with_tycos =
      (map_filter o Option.map) (fn c => (c, get_type_of_constr c)) cos;
    val _ = case map_filter (fn (c, NONE) => SOME c | _ => NONE) cos_with_tycos of
        [] => ()
      | cs => error ("Non-constructor(s) in case certificate: " ^ commas_quote cs);
    val tycos = distinct (op =) (map_filter snd cos_with_tycos);
    val schema = (1 + Int.max (1, length cos), (k, cos));
    val cong = case_cong thy case_const schema;
  in
    thy
    |> modify_specs (map_cases (History.register case_const
         (Case {schema = schema, tycos = tycos, cong = cong}))
      #> map_types (fold (fn tyco => History.modify_entry tyco
        (add_case_combinator case_const)) tycos))
  end;

fun declare_undefined_global c =
  (modify_specs o map_cases) (History.register c Undefined);


(* attributes *)

fun code_attribute f = Thm.declaration_attribute
  (fn thm => Context.mapping (f thm) I);

fun code_thm_attribute g f =
  Scan.lift (g |-- Scan.succeed (code_attribute f));

fun code_const_attribute g f =
  Scan.lift (g -- Args.colon) |-- Scan.repeat1 Args.term
    >> (fn ts => code_attribute (K (fold (fn t => fn thy => f ((check_const thy o Logic.unvarify_types_global) t) thy) ts)));

val _ = Theory.setup
  (let
    val code_attribute_parser =
      code_thm_attribute (Args.$$$ "equation")
        (fn thm => generic_add_eqn Liberal (thm, true))
      || code_thm_attribute (Args.$$$ "nbe")
          (fn thm => generic_add_eqn Liberal (thm, false))
      || code_thm_attribute (Args.$$$ "abstract")
          (generic_declare_abstract_eqn Liberal)
      || code_thm_attribute (Args.$$$ "abstype")
          (generic_declare_abstype Liberal)
      || code_thm_attribute Args.del
          del_eqn_global
      || code_const_attribute (Args.$$$ "abort")
          declare_aborting_global
      || code_const_attribute (Args.$$$ "drop")
          declare_unimplemented_global
      || Scan.succeed (code_attribute
          add_maybe_abs_eqn_liberal);
  in
    Attrib.setup \<^binding>\<open>code\<close> code_attribute_parser
        "declare theorems for code generation"
  end);

end; (*struct*)


(* type-safe interfaces for data dependent on executable code *)

functor Code_Data(Data: CODE_DATA_ARGS): CODE_DATA =
struct

type T = Data.T;
exception Data of T;
fun dest (Data x) = x

val kind = Code.declare_data (Data Data.empty);

val data_op = (kind, Data, dest);

fun change_yield (SOME thy) f = Code.change_yield_data data_op thy f
  | change_yield NONE f = f Data.empty

fun change some_thy f = snd (change_yield some_thy (pair () o f));

end;

structure Code : CODE = struct open Code; end;
