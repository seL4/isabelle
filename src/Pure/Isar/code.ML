(*  Title:      Pure/Isar/code.ML
    Author:     Florian Haftmann, TU Muenchen

Abstract executable code of theory.  Management of data dependent on
executable code.  Cache assumes non-concurrent processing of a single theory.
*)

signature CODE =
sig
  (*constants*)
  val check_const: theory -> term -> string
  val read_bare_const: theory -> string -> string * typ
  val read_const: theory -> string -> string
  val string_of_const: theory -> string -> string
  val args_number: theory -> string -> int

  (*constructor sets*)
  val constrset_of_consts: theory -> (string * typ) list
    -> string * ((string * sort) list * (string * typ list) list)

  (*code equations*)
  val mk_eqn: theory -> thm * bool -> thm * bool
  val mk_eqn_warning: theory -> thm -> (thm * bool) option
  val mk_eqn_liberal: theory -> thm -> (thm * bool) option
  val assert_eqn: theory -> thm * bool -> thm * bool
  val assert_eqns_const: theory -> string
    -> (thm * bool) list -> (thm * bool) list
  val const_typ_eqn: theory -> thm -> string * typ
  val typscheme_eqn: theory -> thm -> (string * sort) list * typ
  val typscheme_eqns: theory -> string -> thm list -> (string * sort) list * typ
  val standard_typscheme: theory -> thm list -> thm list

  (*executable code*)
  val add_datatype: (string * typ) list -> theory -> theory
  val add_datatype_cmd: string list -> theory -> theory
  val type_interpretation:
    (string * ((string * sort) list * (string * typ list) list)
      -> theory -> theory) -> theory -> theory
  val add_eqn: thm -> theory -> theory
  val add_nbe_eqn: thm -> theory -> theory
  val add_default_eqn: thm -> theory -> theory
  val add_default_eqn_attribute: attribute
  val add_default_eqn_attrib: Attrib.src
  val del_eqn: thm -> theory -> theory
  val del_eqns: string -> theory -> theory
  val add_case: thm -> theory -> theory
  val add_undefined: string -> theory -> theory
  val get_datatype: theory -> string -> ((string * sort) list * (string * typ list) list)
  val get_datatype_of_constr: theory -> string -> string option
  val these_eqns: theory -> string -> (thm * bool) list
  val all_eqns: theory -> (thm * bool) list
  val get_case_scheme: theory -> string -> (int * (int * string list)) option
  val undefineds: theory -> string list
  val print_codesetup: theory -> unit

  (*infrastructure*)
  val set_code_target_attr: (string -> thm -> theory -> theory) -> theory -> theory
  val purge_data: theory -> theory
end;

signature CODE_DATA_ARGS =
sig
  type T
  val empty: T
  val purge: theory -> string list -> T -> T
end;

signature CODE_DATA =
sig
  type T
  val get: theory -> T
  val change: theory -> (T -> T) -> T
  val change_yield: theory -> (T -> 'a * T) -> 'a * T
end;

signature PRIVATE_CODE =
sig
  include CODE
  val declare_data: Object.T -> (theory -> string list -> Object.T -> Object.T)
    -> serial
  val get_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> 'a
  val change_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> ('a -> 'a) -> 'a
  val change_yield_data: serial * ('a -> Object.T) * (Object.T -> 'a)
    -> theory -> ('a -> 'b * 'a) -> 'b * 'a
end;

structure Code : PRIVATE_CODE =
struct

(** auxiliary **)

(* printing *)

fun string_of_typ thy = setmp_CRITICAL show_sorts true (Syntax.string_of_typ_global thy);

fun string_of_const thy c = case AxClass.inst_of_param thy c
 of SOME (c, tyco) => Sign.extern_const thy c ^ " " ^ enclose "[" "]" (Sign.extern_type thy tyco)
  | NONE => Sign.extern_const thy c;


(* constants *)

fun check_bare_const thy t = case try dest_Const t
 of SOME c_ty => c_ty
  | NONE => error ("Not a constant: " ^ Syntax.string_of_term_global thy t);

fun check_const thy = AxClass.unoverload_const thy o check_bare_const thy;

fun read_bare_const thy = check_bare_const thy o Syntax.read_term_global thy;

fun read_const thy = AxClass.unoverload_const thy o read_bare_const thy;



(** data store **)

(* code equations *)

type eqns = bool * (thm * bool) list;
  (*default flag, theorems with proper flag *)

fun add_drop_redundant thy (thm, proper) thms =
  let
    val args_of = snd o strip_comb o map_types Type.strip_sorts
      o fst o Logic.dest_equals o Thm.plain_prop_of;
    val args = args_of thm;
    val incr_idx = Logic.incr_indexes ([], Thm.maxidx_of thm + 1);
    fun matches_args args' = length args <= length args' andalso
      Pattern.matchess thy (args, (map incr_idx o curry Library.take (length args)) args');
    fun drop (thm', proper') = if (proper orelse not proper')
      andalso matches_args (args_of thm') then 
        (warning ("Code generator: dropping redundant code equation\n" ^
            Display.string_of_thm_global thy thm'); true)
      else false;
  in (thm, proper) :: filter_out drop thms end;

fun add_thm thy _ thm (false, thms) = (false, add_drop_redundant thy thm thms)
  | add_thm thy true thm (true, thms) = (true, thms @ [thm])
  | add_thm thy false thm (true, thms) = (false, [thm]);

fun del_thm thm = apsnd (remove (eq_fst Thm.eq_thm_prop) (thm, true));


(* executable code data *)

datatype spec = Spec of {
  history_concluded: bool,
  eqns: ((bool * eqns) * (serial * eqns) list) Symtab.table
    (*with explicit history*),
  dtyps: ((serial * ((string * sort) list * (string * typ list) list)) list) Symtab.table
    (*with explicit history*),
  cases: (int * (int * string list)) Symtab.table * unit Symtab.table
};

fun make_spec (history_concluded, (eqns, (dtyps, cases))) =
  Spec { history_concluded = history_concluded, eqns = eqns, dtyps = dtyps, cases = cases };
fun map_spec f (Spec { history_concluded = history_concluded, eqns = eqns,
  dtyps = dtyps, cases = cases }) =
  make_spec (f (history_concluded, (eqns, (dtyps, cases))));
fun merge_spec (Spec { history_concluded = _, eqns = eqns1,
    dtyps = dtyps1, cases = (cases1, undefs1) },
  Spec { history_concluded = _, eqns = eqns2,
    dtyps = dtyps2, cases = (cases2, undefs2) }) =
  let
    fun merge_eqns ((_, history1), (_, history2)) =
      let
        val raw_history = AList.merge (op = : serial * serial -> bool)
          (K true) (history1, history2)
        val filtered_history = filter_out (fst o snd) raw_history
        val history = if null filtered_history
          then raw_history else filtered_history;
      in ((false, (snd o hd) history), history) end;
    val eqns = Symtab.join (K merge_eqns) (eqns1, eqns2);
    val dtyps = Symtab.join (K (AList.merge (op =) (K true))) (dtyps1, dtyps2);
    val cases = (Symtab.merge (K true) (cases1, cases2),
      Symtab.merge (K true) (undefs1, undefs2));
  in make_spec (false, (eqns, (dtyps, cases))) end;

fun history_concluded (Spec { history_concluded, ... }) = history_concluded;
fun the_eqns (Spec { eqns, ... }) = eqns;
fun the_dtyps (Spec { dtyps, ... }) = dtyps;
fun the_cases (Spec { cases, ... }) = cases;
val map_history_concluded = map_spec o apfst;
val map_eqns = map_spec o apsnd o apfst;
val map_dtyps = map_spec o apsnd o apsnd o apfst;
val map_cases = map_spec o apsnd o apsnd o apsnd;


(* data slots dependent on executable code *)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = Table(type key = int val ord = int_ord);

local

type kind = {
  empty: Object.T,
  purge: theory -> string list -> Object.T -> Object.T
};

val kinds = Unsynchronized.ref (Datatab.empty: kind Datatab.table);
val kind_keys = Unsynchronized.ref ([]: serial list);

fun invoke f k = case Datatab.lookup (! kinds) k
 of SOME kind => f kind
  | NONE => sys_error "Invalid code data identifier";

in

fun declare_data empty purge =
  let
    val k = serial ();
    val kind = {empty = empty, purge = purge};
    val _ = Unsynchronized.change kinds (Datatab.update (k, kind));
    val _ = Unsynchronized.change kind_keys (cons k);
  in k end;

fun invoke_init k = invoke (fn kind => #empty kind) k;

fun invoke_purge_all thy cs =
  fold (fn k => Datatab.map_entry k
    (invoke (fn kind => #purge kind thy cs) k)) (! kind_keys);

end; (*local*)


(* theory store *)

local

type data = Object.T Datatab.table;
val empty_data = Datatab.empty : data;

structure Code_Data = TheoryDataFun
(
  type T = spec * data Unsynchronized.ref;
  val empty = (make_spec (false,
    (Symtab.empty, (Symtab.empty, (Symtab.empty, Symtab.empty)))), Unsynchronized.ref empty_data);
  fun copy (spec, data) = (spec, Unsynchronized.ref (! data));
  val extend = copy;
  fun merge pp ((spec1, data1), (spec2, data2)) =
    (merge_spec (spec1, spec2), Unsynchronized.ref empty_data);
);

fun thy_data f thy = f ((snd o Code_Data.get) thy);

fun get_ensure_init kind data_ref =
  case Datatab.lookup (! data_ref) kind
   of SOME x => x
    | NONE => let val y = invoke_init kind
        in (Unsynchronized.change data_ref (Datatab.update (kind, y)); y) end;

in

(* access to executable code *)

val the_exec = fst o Code_Data.get;

fun complete_class_params thy cs =
  fold (fn c => case AxClass.inst_of_param thy c
   of NONE => insert (op =) c
    | SOME (c', _) => insert (op =) c' #> insert (op =) c) cs [];

fun map_exec_purge touched f thy =
  Code_Data.map (fn (exec, data) => (f exec, Unsynchronized.ref (case touched
   of SOME cs => invoke_purge_all thy (complete_class_params thy cs) (! data)
    | NONE => empty_data))) thy;

val purge_data = (Code_Data.map o apsnd) (K (Unsynchronized.ref empty_data));

fun change_eqns delete c f = (map_exec_purge (SOME [c]) o map_eqns
  o (if delete then Symtab.map_entry c else Symtab.map_default (c, ((false, (true, [])), [])))
    o apfst) (fn (_, eqns) => (true, f eqns));

fun del_eqns c = change_eqns true c (K (false, []));


(* tackling equation history *)

fun get_eqns thy c =
  Symtab.lookup ((the_eqns o the_exec) thy) c
  |> Option.map (snd o snd o fst)
  |> these;

fun continue_history thy = if (history_concluded o the_exec) thy
  then thy
    |> (Code_Data.map o apfst o map_history_concluded) (K false)
    |> SOME
  else NONE;

fun conclude_history thy = if (history_concluded o the_exec) thy
  then NONE
  else thy
    |> (Code_Data.map o apfst)
        ((map_eqns o Symtab.map) (fn ((changed, current), history) =>
          ((false, current),
            if changed then (serial (), current) :: history else history))
        #> map_history_concluded (K true))
    |> SOME;

val _ = Context.>> (Context.map_theory (Code_Data.init
  #> Theory.at_begin continue_history
  #> Theory.at_end conclude_history));


(* access to data dependent on abstract executable code *)

fun get_data (kind, _, dest) = thy_data (get_ensure_init kind #> dest);

fun change_data (kind, mk, dest) =
  let
    fun chnge data_ref f =
      let
        val data = get_ensure_init kind data_ref;
        val data' = f (dest data);
      in (Unsynchronized.change data_ref (Datatab.update (kind, mk data')); data') end;
  in thy_data chnge end;

fun change_yield_data (kind, mk, dest) =
  let
    fun chnge data_ref f =
      let
        val data = get_ensure_init kind data_ref;
        val (x, data') = f (dest data);
      in (x, (Unsynchronized.change data_ref (Datatab.update (kind, mk data')); data')) end;
  in thy_data chnge end;

end; (*local*)


(** foundation **)

(* constants *)

fun args_number thy = length o fst o strip_type o Sign.the_const_type thy;


(* datatypes *)

fun constrset_of_consts thy cs =
  let
    val _ = map (fn (c, _) => if (is_some o AxClass.class_of_param thy) c
      then error ("Is a class parameter: " ^ string_of_const thy c) else ()) cs;
    fun no_constr (c, ty) = error ("Not a datatype constructor: " ^ string_of_const thy c
      ^ " :: " ^ string_of_typ thy ty);
    fun last_typ c_ty ty =
      let
        val frees = OldTerm.typ_tfrees ty;
        val (tyco, vs) = ((apsnd o map) (dest_TFree) o dest_Type o snd o strip_type) ty
          handle TYPE _ => no_constr c_ty
        val _ = if has_duplicates (eq_fst (op =)) vs then no_constr c_ty else ();
        val _ = if length frees <> length vs then no_constr c_ty else ();
      in (tyco, vs) end;
    fun ty_sorts (c, ty) =
      let
        val ty_decl = (Logic.unvarifyT o Sign.the_const_type thy) c;
        val (tyco, _) = last_typ (c, ty) ty_decl;
        val (_, vs) = last_typ (c, ty) ty;
      in ((tyco, map snd vs), (c, (map fst vs, ty))) end;
    fun add ((tyco', sorts'), c) ((tyco, sorts), cs) =
      let
        val _ = if (tyco' : string) <> tyco
          then error "Different type constructors in constructor set"
          else ();
        val sorts'' = map2 (curry (Sorts.inter_sort (Sign.classes_of thy))) sorts' sorts
      in ((tyco, sorts), c :: cs) end;
    fun inst vs' (c, (vs, ty)) =
      let
        val the_v = the o AList.lookup (op =) (vs ~~ vs');
        val ty' = map_atyps (fn TFree (v, _) => TFree (the_v v)) ty;
      in (c, (fst o strip_type) ty') end;
    val c' :: cs' = map ty_sorts cs;
    val ((tyco, sorts), cs'') = fold add cs' (apsnd single c');
    val vs = Name.names Name.context Name.aT sorts;
    val cs''' = map (inst vs) cs'';
  in (tyco, (vs, rev cs''')) end;

fun get_datatype thy tyco =
  case these (Symtab.lookup ((the_dtyps o the_exec) thy) tyco)
   of (_, spec) :: _ => spec
    | [] => Sign.arity_number thy tyco
        |> Name.invents Name.context Name.aT
        |> map (rpair [])
        |> rpair [];

fun get_datatype_of_constr thy c =
  case (snd o strip_type o Sign.the_const_type thy) c
   of Type (tyco, _) => if member (op =) ((map fst o snd o get_datatype thy) tyco) c
       then SOME tyco else NONE
    | _ => NONE;

fun is_constr thy = is_some o get_datatype_of_constr thy;


(* code equations *)

exception BAD_THM of string;
fun bad_thm msg = raise BAD_THM msg;
fun error_thm f thm = f thm handle BAD_THM msg => error msg;
fun warning_thm f thm = SOME (f thm) handle BAD_THM msg => (warning msg; NONE)
fun try_thm f thm = SOME (f thm) handle BAD_THM _ => NONE;

fun is_linear thm =
  let val (_, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm
  in not (has_duplicates (op =) ((fold o fold_aterms)
    (fn Var (v, _) => cons v | _ => I) args [])) end;

fun gen_assert_eqn thy is_constr_pat (thm, proper) =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm
      handle TERM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm_global thy thm)
           | THM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm_global thy thm);
    fun vars_of t = fold_aterms (fn Var (v, _) => insert (op =) v
      | Free _ => bad_thm ("Illegal free variable in equation\n"
          ^ Display.string_of_thm_global thy thm)
      | _ => I) t [];
    fun tvars_of t = fold_term_types (fn _ =>
      fold_atyps (fn TVar (v, _) => insert (op =) v
        | TFree _ => bad_thm 
      ("Illegal free type variable in equation\n" ^ Display.string_of_thm_global thy thm))) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of rhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad_thm ("Free variables on right hand side of equation\n"
        ^ Display.string_of_thm_global thy thm);
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad_thm ("Free type variables on right hand side of equation\n"
        ^ Display.string_of_thm_global thy thm)
    val (head, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm;
    val (c, ty) = case head
     of Const (c_ty as (_, ty)) => (AxClass.unoverload_const thy c_ty, ty)
      | _ => bad_thm ("Equation not headed by constant\n" ^ Display.string_of_thm_global thy thm);
    fun check _ (Abs _) = bad_thm
          ("Abstraction on left hand side of equation\n"
            ^ Display.string_of_thm_global thy thm)
      | check 0 (Var _) = ()
      | check _ (Var _) = bad_thm
          ("Variable with application on left hand side of equation\n"
            ^ Display.string_of_thm_global thy thm)
      | check n (t1 $ t2) = (check (n+1) t1; check 0 t2)
      | check n (Const (c_ty as (c, ty))) = if n = (length o fst o strip_type) ty
          then if not proper orelse is_constr_pat (AxClass.unoverload_const thy c_ty)
            then ()
            else bad_thm (quote c ^ " is not a constructor, on left hand side of equation\n"
              ^ Display.string_of_thm_global thy thm)
          else bad_thm
            ("Partially applied constant " ^ quote c ^ " on left hand side of equation\n"
               ^ Display.string_of_thm_global thy thm);
    val _ = map (check 0) args;
    val _ = if not proper orelse is_linear thm then ()
      else bad_thm ("Duplicate variables on left hand side of equation\n"
        ^ Display.string_of_thm_global thy thm);
    val _ = if (is_none o AxClass.class_of_param thy) c
      then ()
      else bad_thm ("Polymorphic constant as head in equation\n"
        ^ Display.string_of_thm_global thy thm)
    val _ = if not (is_constr thy c)
      then ()
      else bad_thm ("Constructor as head in equation\n"
        ^ Display.string_of_thm_global thy thm)
    val ty_decl = Sign.the_const_type thy c;
    val _ = if Sign.typ_equiv thy (Type.strip_sorts ty_decl, Type.strip_sorts ty)
      then () else bad_thm ("Type\n" ^ string_of_typ thy ty
           ^ "\nof equation\n"
           ^ Display.string_of_thm_global thy thm
           ^ "\nis incompatible with declared function type\n"
           ^ string_of_typ thy ty_decl)
  in (thm, proper) end;

fun assert_eqn thy = error_thm (gen_assert_eqn thy (is_constr thy));

fun meta_rewrite thy = LocalDefs.meta_rewrite_rule (ProofContext.init thy);

fun mk_eqn thy = error_thm (gen_assert_eqn thy (K true)) o
  apfst (meta_rewrite thy);

fun mk_eqn_warning thy = Option.map (fn (thm, _) => (thm, is_linear thm))
  o warning_thm (gen_assert_eqn thy (K true)) o rpair false o meta_rewrite thy;

fun mk_eqn_liberal thy = Option.map (fn (thm, _) => (thm, is_linear thm))
  o try_thm (gen_assert_eqn thy (K true)) o rpair false o meta_rewrite thy;

(*those following are permissive wrt. to overloaded constants!*)

val head_eqn = dest_Const o fst o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;
fun const_typ_eqn thy thm =
  let
    val (c, ty) = head_eqn thm;
    val c' = AxClass.unoverload_const thy (c, ty);
  in (c', ty) end;
fun const_eqn thy = fst o const_typ_eqn thy;

fun typscheme thy (c, ty) =
  (map dest_TFree (Sign.const_typargs thy (c, ty)), Type.strip_sorts ty);
fun typscheme_eqn thy = typscheme thy o apsnd Logic.unvarifyT o const_typ_eqn thy;
fun typscheme_eqns thy c [] = 
      let
        val raw_ty = Sign.the_const_type thy c;
        val tvars = Term.add_tvar_namesT raw_ty [];
        val tvars' = case AxClass.class_of_param thy c
         of SOME class => [TFree (Name.aT, [class])]
          | NONE => Name.invent_list [] Name.aT (length tvars)
              |> map (fn v => TFree (v, []));
        val ty = typ_subst_TVars (tvars ~~ tvars') raw_ty;
      in typscheme thy (c, ty) end
  | typscheme_eqns thy c (thms as thm :: _) = typscheme_eqn thy thm;

fun assert_eqns_const thy c eqns =
  let
    fun cert (eqn as (thm, _)) = if c = const_eqn thy thm
      then eqn else error ("Wrong head of code equation,\nexpected constant "
        ^ string_of_const thy c ^ "\n" ^ Display.string_of_thm_global thy thm)
  in map (cert o assert_eqn thy) eqns end;

fun standard_typscheme thy thms =
  let
    fun tvars_of T = rev (Term.add_tvarsT T []);
    val vss = map (tvars_of o snd o head_eqn) thms;
    fun inter_sorts vs =
      fold (curry (Sorts.inter_sort (Sign.classes_of thy)) o snd) vs [];
    val sorts = map_transpose inter_sorts vss;
    val vts = Name.names Name.context Name.aT sorts
      |> map (fn (v, sort) => TVar ((v, 0), sort));
  in map2 (fn vs => Thm.certify_instantiate (vs ~~ vts, [])) vss thms end;

fun these_eqns thy c =
  get_eqns thy c
  |> (map o apfst) (Thm.transfer thy)
  |> burrow_fst (standard_typscheme thy);

fun all_eqns thy =
  Symtab.dest ((the_eqns o the_exec) thy)
  |> maps (snd o snd o fst o snd);


(* cases *)

fun case_certificate thm =
  let
    val ((head, raw_case_expr), cases) = (apfst Logic.dest_equals
      o apsnd Logic.dest_conjunctions o Logic.dest_implies o Thm.plain_prop_of) thm;
    val _ = case head of Free _ => true
      | Var _ => true
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
      in map (the o AList.lookup (op =) co_list) params end;
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

fun case_cert thm = case_certificate thm
  handle Bind => error "bad case certificate"
       | TERM _ => error "bad case certificate";

fun get_case_scheme thy = Symtab.lookup ((fst o the_cases o the_exec) thy);

val undefineds = Symtab.keys o snd o the_cases o the_exec;


(* diagnostic *)

fun print_codesetup thy =
  let
    val ctxt = ProofContext.init thy;
    val exec = the_exec thy;
    fun pretty_eqns (s, (_, eqns)) =
      (Pretty.block o Pretty.fbreaks) (
        Pretty.str s :: map (Display.pretty_thm ctxt o fst) eqns
      );
    fun pretty_dtyp (s, []) =
          Pretty.str s
      | pretty_dtyp (s, cos) =
          (Pretty.block o Pretty.breaks) (
            Pretty.str s
            :: Pretty.str "="
            :: separate (Pretty.str "|") (map (fn (c, []) => Pretty.str (string_of_const thy c)
                 | (c, tys) =>
                     (Pretty.block o Pretty.breaks)
                        (Pretty.str (string_of_const thy c)
                          :: Pretty.str "of"
                          :: map (Pretty.quote o Syntax.pretty_typ_global thy) tys)) cos)
          );
    val eqns = the_eqns exec
      |> Symtab.dest
      |> (map o apfst) (string_of_const thy)
      |> (map o apsnd) (snd o fst)
      |> sort (string_ord o pairself fst);
    val dtyps = the_dtyps exec
      |> Symtab.dest
      |> map (fn (dtco, (_, (vs, cos)) :: _) =>
          (string_of_typ thy (Type (dtco, map TFree vs)), cos))
      |> sort (string_ord o pairself fst)
  in
    (Pretty.writeln o Pretty.chunks) [
      Pretty.block (
        Pretty.str "code equations:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_eqns) eqns
      ),
      Pretty.block (
        Pretty.str "datatypes:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_dtyp) dtyps
      )
    ]
  end;


(** declaring executable ingredients **)

(* datatypes *)

structure Type_Interpretation =
  Interpretation(type T = string * serial val eq = eq_snd (op =) : T * T -> bool);

fun add_datatype raw_cs thy =
  let
    val cs = map (fn c_ty as (_, ty) => (AxClass.unoverload_const thy c_ty, ty)) raw_cs;
    val (tyco, vs_cos) = constrset_of_consts thy cs;
    val old_cs = (map fst o snd o get_datatype thy) tyco;
    fun drop_outdated_cases cases = fold Symtab.delete_safe
      (Symtab.fold (fn (c, (_, (_, cos))) =>
        if exists (member (op =) old_cs) cos
          then insert (op =) c else I) cases []) cases;
  in
    thy
    |> fold (del_eqns o fst) cs
    |> map_exec_purge NONE
        ((map_dtyps o Symtab.map_default (tyco, [])) (cons (serial (), vs_cos))
        #> (map_cases o apfst) drop_outdated_cases)
    |> Type_Interpretation.data (tyco, serial ())
  end;

fun type_interpretation f =  Type_Interpretation.interpretation
  (fn (tyco, _) => fn thy => f (tyco, get_datatype thy tyco) thy);

fun add_datatype_cmd raw_cs thy =
  let
    val cs = map (read_bare_const thy) raw_cs;
  in add_datatype cs thy end;


(* code equations *)

fun gen_add_eqn default (thm, proper) thy =
  let
    val thm' = Thm.close_derivation thm;
    val c = const_eqn thy thm';
  in change_eqns false c (add_thm thy default (thm', proper)) thy end;

fun add_eqn thm thy =
  gen_add_eqn false (mk_eqn thy (thm, true)) thy;

fun add_warning_eqn thm thy =
  case mk_eqn_warning thy thm
   of SOME eqn => gen_add_eqn false eqn thy
    | NONE => thy;

fun add_default_eqn thm thy =
  case mk_eqn_liberal thy thm
   of SOME eqn => gen_add_eqn true eqn thy
    | NONE => thy;

fun add_nbe_eqn thm thy =
  gen_add_eqn false (mk_eqn thy (thm, false)) thy;

val add_default_eqn_attribute = Thm.declaration_attribute
  (fn thm => Context.mapping (add_default_eqn thm) I);
val add_default_eqn_attrib = Attrib.internal (K add_default_eqn_attribute);

fun del_eqn thm thy = case mk_eqn_liberal thy thm
 of SOME (thm, _) => change_eqns true (const_eqn thy thm) (del_thm thm) thy
  | NONE => thy;

(* c.f. src/HOL/Tools/recfun_codegen.ML *)

structure Code_Target_Attr = Theory_Data
(
  type T = (string -> thm -> theory -> theory) option;
  val empty = NONE;
  val extend = I;
  fun merge (f1, f2) = if is_some f1 then f1 else f2;
);

fun set_code_target_attr f = Code_Target_Attr.map (K (SOME f));

fun code_target_attr prefix thm thy =
  let
    val attr = the_default ((K o K) I) (Code_Target_Attr.get thy);
  in thy |> add_warning_eqn thm |> attr prefix thm end;

(* setup *)

val _ = Context.>> (Context.map_theory
  (let
    fun mk_attribute f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);
    val code_attribute_parser =
      Args.del |-- Scan.succeed (mk_attribute del_eqn)
      || Args.$$$ "nbe" |-- Scan.succeed (mk_attribute add_nbe_eqn)
      || (Args.$$$ "target" |-- Args.colon |-- Args.name >>
           (mk_attribute o code_target_attr))
      || Scan.succeed (mk_attribute add_warning_eqn);
  in
    Type_Interpretation.init
    #> Attrib.setup (Binding.name "code") (Scan.lift code_attribute_parser)
        "declare theorems for code generation"
  end));


(* cases *)

fun add_case thm thy =
  let
    val (c, (k, case_pats)) = case_cert thm;
    val _ = case filter_out (is_constr thy) case_pats
     of [] => ()
      | cs => error ("Non-constructor(s) in case certificate: " ^ commas (map quote cs));
    val entry = (1 + Int.max (1, length case_pats), (k, case_pats))
  in (map_exec_purge (SOME [c]) o map_cases o apfst) (Symtab.update (c, entry)) thy end;

fun add_undefined c thy =
  (map_exec_purge (SOME [c]) o map_cases o apsnd) (Symtab.update (c, ())) thy;

end; (*struct*)


(** type-safe interfaces for data dependent on executable code **)

functor Code_Data_Fun(Data: CODE_DATA_ARGS): CODE_DATA =
struct

type T = Data.T;
exception Data of T;
fun dest (Data x) = x

val kind = Code.declare_data (Data Data.empty)
  (fn thy => fn cs => fn Data x => Data (Data.purge thy cs x));

val data_op = (kind, Data, dest);

val get = Code.get_data data_op;
val change = Code.change_data data_op;
fun change_yield thy = Code.change_yield_data data_op thy;

end;

(** datastructure to log definitions for preprocessing of the predicate compiler **)
(* obviously a clone of Named_Thms *)

signature PREDICATE_COMPILE_PREPROC_CONST_DEFS =
sig
  val get: Proof.context -> thm list
  val add_thm: thm -> Context.generic -> Context.generic
  val del_thm: thm -> Context.generic -> Context.generic
  
  val add_attribute : attribute
  val del_attribute : attribute
  
  val add_attrib : Attrib.src
  
  val setup: theory -> theory
end;

structure Predicate_Compile_Preproc_Const_Defs : PREDICATE_COMPILE_PREPROC_CONST_DEFS =
struct

structure Data = Generic_Data
(
  type T = thm list;
  val empty = [];
  val extend = I;
  val merge = Thm.merge_thms;
);

val get = Data.get o Context.Proof;

val add_thm = Data.map o Thm.add_thm;
val del_thm = Data.map o Thm.del_thm;

val add_attribute = Thm.declaration_attribute add_thm;
val del_attribute = Thm.declaration_attribute del_thm;

val add_attrib = Attrib.internal (K add_attribute)

val setup =
  Attrib.setup (Binding.name "pred_compile_preproc") (Attrib.add_del add_attribute del_attribute)
    ("declaration of definition for preprocessing of the predicate compiler") #>
  PureThy.add_thms_dynamic (Binding.name "pred_compile_preproc", Data.get);

end;

structure Code : CODE = struct open Code; end;
