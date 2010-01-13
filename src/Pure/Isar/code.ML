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
  val read_bare_const: theory -> string -> string * typ
  val read_const: theory -> string -> string
  val string_of_const: theory -> string -> string
  val cert_signature: theory -> typ -> typ
  val read_signature: theory -> string -> typ
  val const_typ: theory -> string -> typ
  val subst_signatures: theory -> term -> term
  val args_number: theory -> string -> int

  (*constructor sets*)
  val constrset_of_consts: theory -> (string * typ) list
    -> string * ((string * sort) list * (string * typ list) list)

  (*code equations and certificates*)
  val mk_eqn: theory -> thm * bool -> thm * bool
  val mk_eqn_warning: theory -> thm -> (thm * bool) option
  val mk_eqn_liberal: theory -> thm -> (thm * bool) option
  val assert_eqn: theory -> thm * bool -> thm * bool
  val const_typ_eqn: theory -> thm -> string * typ
  val expand_eta: theory -> int -> thm -> thm
  type cert
  val empty_cert: theory -> string -> cert
  val cert_of_eqns: theory -> string -> (thm * bool) list -> cert
  val constrain_cert: theory -> sort list -> cert -> cert
  val typscheme_cert: theory -> cert -> (string * sort) list * typ
  val equations_cert: theory -> cert -> ((string * sort) list * typ) * (term list * term) list
  val equations_thms_cert: theory -> cert -> ((string * sort) list * typ) * ((term list * term) * (thm * bool)) list
  val pretty_cert: theory -> cert -> Pretty.T list

  (*executable code*)
  val add_type: string -> theory -> theory
  val add_type_cmd: string -> theory -> theory
  val add_signature: string * typ -> theory -> theory
  val add_signature_cmd: string * string -> theory -> theory
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
  val get_cert: theory -> ((thm * bool) list -> (thm * bool) list) -> string -> cert
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
end;

signature CODE_DATA =
sig
  type T
  val change: theory -> (T -> T) -> T
  val change_yield: theory -> (T -> 'a * T) -> 'a * T
end;

signature PRIVATE_CODE =
sig
  include CODE
  val declare_data: Object.T -> serial
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

fun typ_equiv tys = Type.raw_instance tys andalso Type.raw_instance (swap tys);

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
      Pattern.matchess thy (args, (map incr_idx o take (length args)) args');
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
  signatures: int Symtab.table * typ Symtab.table,
  eqns: ((bool * eqns) * (serial * eqns) list) Symtab.table
    (*with explicit history*),
  dtyps: ((serial * ((string * sort) list * (string * typ list) list)) list) Symtab.table
    (*with explicit history*),
  cases: (int * (int * string list)) Symtab.table * unit Symtab.table
};

fun make_spec (history_concluded, ((signatures, eqns), (dtyps, cases))) =
  Spec { history_concluded = history_concluded,
    signatures = signatures, eqns = eqns, dtyps = dtyps, cases = cases };
fun map_spec f (Spec { history_concluded = history_concluded, signatures = signatures,
  eqns = eqns, dtyps = dtyps, cases = cases }) =
  make_spec (f (history_concluded, ((signatures, eqns), (dtyps, cases))));
fun merge_spec (Spec { history_concluded = _, signatures = (tycos1, sigs1), eqns = eqns1,
    dtyps = dtyps1, cases = (cases1, undefs1) },
  Spec { history_concluded = _, signatures = (tycos2, sigs2), eqns = eqns2,
    dtyps = dtyps2, cases = (cases2, undefs2) }) =
  let
    val signatures = (Symtab.merge (op =) (tycos1, tycos2),
      Symtab.merge typ_equiv (sigs1, sigs2));
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
  in make_spec (false, ((signatures, eqns), (dtyps, cases))) end;

fun history_concluded (Spec { history_concluded, ... }) = history_concluded;
fun the_signatures (Spec { signatures, ... }) = signatures;
fun the_eqns (Spec { eqns, ... }) = eqns;
fun the_dtyps (Spec { dtyps, ... }) = dtyps;
fun the_cases (Spec { cases, ... }) = cases;
val map_history_concluded = map_spec o apfst;
val map_signatures = map_spec o apsnd o apfst o apfst;
val map_eqns = map_spec o apsnd o apfst o apsnd;
val map_dtyps = map_spec o apsnd o apsnd o apfst;
val map_cases = map_spec o apsnd o apsnd o apsnd;


(* data slots dependent on executable code *)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = Table(type key = int val ord = int_ord);

local

type kind = { empty: Object.T };

val kinds = Unsynchronized.ref (Datatab.empty: kind Datatab.table);

fun invoke f k = case Datatab.lookup (! kinds) k
 of SOME kind => f kind
  | NONE => sys_error "Invalid code data identifier";

in

fun declare_data empty =
  let
    val k = serial ();
    val kind = { empty = empty };
    val _ = CRITICAL (fn () => Unsynchronized.change kinds (Datatab.update (k, kind)));
  in k end;

fun invoke_init k = invoke (fn kind => #empty kind) k;

end; (*local*)


(* theory store *)

local

type data = Object.T Datatab.table;
fun empty_dataref () = Synchronized.var "code data" (NONE : (data * theory_ref) option);

structure Code_Data = Theory_Data
(
  type T = spec * (data * theory_ref) option Synchronized.var;
  val empty = (make_spec (false, (((Symtab.empty, Symtab.empty), Symtab.empty),
    (Symtab.empty, (Symtab.empty, Symtab.empty)))), empty_dataref ());
  val extend = I
  fun merge ((spec1, _), (spec2, _)) =
    (merge_spec (spec1, spec2), empty_dataref ());
);

in

(* access to executable code *)

val the_exec = fst o Code_Data.get;

fun map_exec_purge f = Code_Data.map (fn (exec, _) => (f exec, empty_dataref ()));

val purge_data = (Code_Data.map o apsnd) (fn _ => empty_dataref ());

fun change_eqns delete c f = (map_exec_purge o map_eqns
  o (if delete then Symtab.map_entry c else Symtab.map_default (c, ((false, (true, [])), [])))
    o apfst) (fn (_, eqns) => (true, f eqns));


(* tackling equation history *)

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

val _ = Context.>> (Context.map_theory (Theory.at_begin continue_history #> Theory.at_end conclude_history));


(* access to data dependent on abstract executable code *)

fun change_yield_data (kind, mk, dest) theory f =
  let
    val dataref = (snd o Code_Data.get) theory;
    val (datatab, thy_ref) = case Synchronized.value dataref
     of SOME (datatab, thy_ref) => if Theory.eq_thy (theory, Theory.deref thy_ref)
          then (datatab, thy_ref)
          else (Datatab.empty, Theory.check_thy theory)
      | NONE => (Datatab.empty, Theory.check_thy theory)
    val data = case Datatab.lookup datatab kind
     of SOME data => data
      | NONE => invoke_init kind;
    val result as (x, data') = f (dest data);
    val _ = Synchronized.change dataref
      ((K o SOME) (Datatab.update (kind, mk data') datatab, thy_ref));
  in result end;

fun change_data ops theory f = change_yield_data ops theory (f #> pair ()) |> snd;

end; (*local*)


(** foundation **)

(* constants *)

fun arity_number thy tyco = case Symtab.lookup ((fst o the_signatures o the_exec) thy) tyco
 of SOME n => n
  | NONE => Sign.arity_number thy tyco;

fun build_tsig thy =
  let
    val (tycos, _) = (the_signatures o the_exec) thy;
    val decls = (#types o Type.rep_tsig o Sign.tsig_of) thy
      |> snd 
      |> Symtab.fold (fn (tyco, n) =>
          Symtab.update (tyco, Type.LogicalType n)) tycos;
  in
    Type.empty_tsig
    |> Symtab.fold (fn (tyco, Type.LogicalType n) => Type.add_type Name_Space.default_naming
        (Binding.qualified_name tyco, n) | _ => I) decls
  end;

fun cert_signature thy = Logic.varifyT o Type.cert_typ (build_tsig thy) o Type.no_tvars;

fun read_signature thy = cert_signature thy o Type.strip_sorts
  o Syntax.parse_typ (ProofContext.init thy);

fun expand_signature thy = Type.cert_typ_mode Type.mode_syntax (Sign.tsig_of thy);

fun lookup_typ thy = Symtab.lookup ((snd o the_signatures o the_exec) thy);

fun const_typ thy c = case lookup_typ thy c
 of SOME ty => ty
  | NONE => (Type.strip_sorts o Sign.the_const_type thy) c;

fun subst_signature thy c ty =
  let
    fun mk_subst (Type (tyco, tys1)) (ty2 as Type (tyco2, tys2)) =
          fold2 mk_subst tys1 tys2
      | mk_subst ty (TVar (v, sort)) = Vartab.update (v, ([], ty))
  in case lookup_typ thy c
   of SOME ty' => Envir.subst_type (mk_subst ty (expand_signature thy ty') Vartab.empty) ty'
    | NONE => ty
  end;

fun subst_signatures thy = map_aterms (fn Const (c, ty) => Const (c, subst_signature thy c ty) | t => t);

fun args_number thy = length o fst o strip_type o const_typ thy;


(* datatypes *)

fun constrset_of_consts thy cs =
  let
    val _ = map (fn (c, _) => if (is_some o AxClass.class_of_param thy) c
      then error ("Is a class parameter: " ^ string_of_const thy c) else ()) cs;
    fun no_constr s (c, ty) = error ("Not a datatype constructor:\n" ^ string_of_const thy c
      ^ " :: " ^ string_of_typ thy ty ^ "\n" ^ enclose "(" ")" s);
    fun last_typ c_ty ty =
      let
        val tfrees = Term.add_tfreesT ty [];
        val (tyco, vs) = ((apsnd o map) (dest_TFree) o dest_Type o snd o strip_type) ty
          handle TYPE _ => no_constr "bad type" c_ty
        val _ = if has_duplicates (eq_fst (op =)) vs
          then no_constr "duplicate type variables in datatype" c_ty else ();
        val _ = if length tfrees <> length vs
          then no_constr "type variables missing in datatype" c_ty else ();
      in (tyco, vs) end;
    fun ty_sorts (c, raw_ty) =
      let
        val ty = subst_signature thy c raw_ty;
        val ty_decl = (Logic.unvarifyT o const_typ thy) c;
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
    | [] => arity_number thy tyco
        |> Name.invents Name.context Name.aT
        |> map (rpair [])
        |> rpair [];

fun get_datatype_of_constr thy c =
  case (snd o strip_type o const_typ thy) c
   of Type (tyco, _) => if member (op =) ((map fst o snd o get_datatype thy) tyco) c
       then SOME tyco else NONE
    | _ => NONE;

fun is_constr thy = is_some o get_datatype_of_constr thy;


(* bare code equations *)

exception BAD_THM of string;
fun bad_thm msg = raise BAD_THM msg;
fun error_thm f thm = f thm handle BAD_THM msg => error msg;
fun warning_thm f thm = SOME (f thm) handle BAD_THM msg => (warning msg; NONE)
fun try_thm f thm = SOME (f thm) handle BAD_THM _ => NONE;

fun is_linear thm =
  let val (_, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm
  in not (has_duplicates (op =) ((fold o fold_aterms)
    (fn Var (v, _) => cons v | _ => I) args [])) end;

fun gen_assert_eqn thy check_patterns (thm, proper) =
  let
    fun bad s = bad_thm (s ^ ":\n" ^ Display.string_of_thm_global thy thm);
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm
      handle TERM _ => bad "Not an equation"
           | THM _ => bad "Not an equation";
    fun vars_of t = fold_aterms (fn Var (v, _) => insert (op =) v
      | Free _ => bad "Illegal free variable in equation"
      | _ => I) t [];
    fun tvars_of t = fold_term_types (fn _ =>
      fold_atyps (fn TVar (v, _) => insert (op =) v
        | TFree _ => bad "Illegal free type variable in equation")) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of rhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad "Free variables on right hand side of equation";
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad "Free type variables on right hand side of equation";
    val (head, args) = strip_comb lhs;
    val (c, ty) = case head
     of Const (c_ty as (_, ty)) => (AxClass.unoverload_const thy c_ty, ty)
      | _ => bad "Equation not headed by constant";
    fun check _ (Abs _) = bad "Abstraction on left hand side of equation"
      | check 0 (Var _) = ()
      | check _ (Var _) = bad "Variable with application on left hand side of equation"
      | check n (t1 $ t2) = (check (n+1) t1; check 0 t2)
      | check n (Const (c_ty as (c, ty))) =
          let
            val c' = AxClass.unoverload_const thy c_ty
          in if n = (length o fst o strip_type o subst_signature thy c') ty
            then if not proper orelse not check_patterns orelse is_constr thy c'
              then ()
              else bad (quote c ^ " is not a constructor, on left hand side of equation")
            else bad ("Partially applied constant " ^ quote c ^ " on left hand side of equation")
          end;
    val _ = map (check 0) args;
    val _ = if not proper orelse is_linear thm then ()
      else bad "Duplicate variables on left hand side of equation";
    val _ = if (is_none o AxClass.class_of_param thy) c then ()
      else bad "Overloaded constant as head in equation";
    val _ = if not (is_constr thy c) then ()
      else bad "Constructor as head in equation";
    val ty_decl = Sign.the_const_type thy c;
    val _ = if Sign.typ_equiv thy (Type.strip_sorts ty_decl, Type.strip_sorts ty)
      then () else bad_thm ("Type\n" ^ string_of_typ thy ty
        ^ "\nof equation\n"
        ^ Display.string_of_thm_global thy thm
        ^ "\nis incompatible with declared function type\n"
        ^ string_of_typ thy ty_decl)
  in (thm, proper) end;

fun assert_eqn thy = error_thm (gen_assert_eqn thy true);

fun meta_rewrite thy = LocalDefs.meta_rewrite_rule (ProofContext.init thy);

fun mk_eqn thy = error_thm (gen_assert_eqn thy false) o
  apfst (meta_rewrite thy);

fun mk_eqn_warning thy = Option.map (fn (thm, _) => (thm, is_linear thm))
  o warning_thm (gen_assert_eqn thy false) o rpair false o meta_rewrite thy;

fun mk_eqn_liberal thy = Option.map (fn (thm, _) => (thm, is_linear thm))
  o try_thm (gen_assert_eqn thy false) o rpair false o meta_rewrite thy;

val head_eqn = dest_Const o fst o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;

fun const_typ_eqn thy thm =
  let
    val (c, ty) = head_eqn thm;
    val c' = AxClass.unoverload_const thy (c, ty);
      (*permissive wrt. to overloaded constants!*)
  in (c', ty) end;

fun const_eqn thy = fst o const_typ_eqn thy;

fun logical_typscheme thy (c, ty) =
  (map dest_TFree (Sign.const_typargs thy (c, ty)), Type.strip_sorts ty);

fun typscheme thy (c, ty) = logical_typscheme thy (c, subst_signature thy c ty);


(* technical transformations of code equations *)

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
      (Thm.cterm_of thy (Var ((v, 0), ty)));
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
      |> map (Name.desymbolize false)
      |> Name.variant_list []
      |> map post;
  in map_filter (fn (((v, i), x), v') =>
    if v = v' andalso i = 0 then NONE
    else SOME (((v, i), x), mk ((v', 0), x))) (vs ~~ names)
  end;

fun desymbolize_tvars thy thms =
  let
    val tvs = fold (Term.add_tvars o Thm.prop_of) thms [];
    val tvar_subst = mk_desymbolization (unprefix "'") (prefix "'") TVar tvs;
  in map (Thm.certify_instantiate (tvar_subst, [])) thms end;

fun desymbolize_vars thy thm =
  let
    val vs = Term.add_vars (Thm.prop_of thm) [];
    val var_subst = mk_desymbolization I I Var vs;
  in Thm.certify_instantiate ([], var_subst) thm end;

fun canonize_thms thy = desymbolize_tvars thy #> same_arity thy #> map (desymbolize_vars thy);


(* code equation certificates *)

fun build_head thy (c, ty) =
  Thm.cterm_of thy (Logic.mk_equals (Free ("HEAD", ty), Const (c, ty)));

fun get_head thy cert_thm =
  let
    val [head] = (#hyps o Thm.crep_thm) cert_thm;
    val (_, Const (c, ty)) = (Logic.dest_equals o Thm.term_of) head;
  in (typscheme thy (c, ty), head) end;

abstype cert = Cert of thm * bool list with

fun empty_cert thy c = 
  let
    val raw_ty = const_typ thy c;
    val tvars = Term.add_tvar_namesT raw_ty [];
    val tvars' = case AxClass.class_of_param thy c
     of SOME class => [TFree (Name.aT, [class])]
      | NONE => Name.invent_list [] Name.aT (length tvars)
          |> map (fn v => TFree (v, []));
    val ty = typ_subst_TVars (tvars ~~ tvars') raw_ty;
    val chead = build_head thy (c, ty);
  in Cert (Thm.weaken chead Drule.dummy_thm, []) end;

fun cert_of_eqns thy c [] = empty_cert thy c
  | cert_of_eqns thy c raw_eqns = 
      let
        val eqns = burrow_fst (canonize_thms thy) raw_eqns;
        val _ = map (assert_eqn thy) eqns;
        val (thms, propers) = split_list eqns;
        val _ = map (fn thm => if c = const_eqn thy thm then ()
          else error ("Wrong head of code equation,\nexpected constant "
            ^ string_of_const thy c ^ "\n" ^ Display.string_of_thm_global thy thm)) thms;
        fun tvars_of T = rev (Term.add_tvarsT T []);
        val vss = map (tvars_of o snd o head_eqn) thms;
        fun inter_sorts vs =
          fold (curry (Sorts.inter_sort (Sign.classes_of thy)) o snd) vs [];
        val sorts = map_transpose inter_sorts vss;
        val vts = Name.names Name.context Name.aT sorts;
        val thms as thm :: _ =
          map2 (fn vs => Thm.certify_instantiate (vs ~~ map TFree vts, [])) vss thms;
        val head_thm = Thm.symmetric (Thm.assume (build_head thy (head_eqn (hd thms))));
        fun head_conv ct = if can Thm.dest_comb ct
          then Conv.fun_conv head_conv ct
          else Conv.rewr_conv head_thm ct;
        val rewrite_head = Conv.fconv_rule (Conv.arg1_conv head_conv);
        val cert_thm = Conjunction.intr_balanced (map rewrite_head thms);
      in Cert (cert_thm, propers) end;

fun constrain_cert thy sorts (Cert (cert_thm, propers)) =
  let
    val ((vs, _), head) = get_head thy cert_thm;
    val subst = map2 (fn (v, sort) => fn sort' =>
      (v, Sorts.inter_sort (Sign.classes_of thy) (sort, sort'))) vs sorts;
    val head' = Thm.term_of head
      |> (map_types o map_atyps)
          (fn TFree (v, _) => TFree (v, the (AList.lookup (op =) subst v)))
      |> Thm.cterm_of thy;
    val inst = map2 (fn (v, sort) => fn (_, sort') =>
      (((v, 0), sort), TFree (v, sort'))) vs subst;
    val cert_thm' = cert_thm
      |> Thm.implies_intr head
      |> Thm.varifyT
      |> Thm.certify_instantiate (inst, [])
      |> Thm.elim_implies (Thm.assume head');
  in (Cert (cert_thm', propers)) end;

fun typscheme_cert thy (Cert (cert_thm, _)) =
  fst (get_head thy cert_thm);

fun equations_cert thy (cert as Cert (cert_thm, propers)) =
  let
    val tyscm = typscheme_cert thy cert;
    val equations = if null propers then [] else
      Thm.prop_of cert_thm
      |> Logic.dest_conjunction_balanced (length propers)
      |> map Logic.dest_equals
      |> (map o apfst) (snd o strip_comb)
  in (tyscm, equations) end;

fun equations_thms_cert thy (cert as Cert (cert_thm, propers)) =
  let
    val (tyscm, equations) = equations_cert thy cert;
    val thms = if null propers then [] else
      cert_thm
      |> LocalDefs.expand [snd (get_head thy cert_thm)]
      |> Thm.varifyT
      |> Conjunction.elim_balanced (length propers)
  in (tyscm, equations ~~ (thms ~~ propers)) end;

fun pretty_cert thy = map (Display.pretty_thm_global thy o AxClass.overload thy o fst o snd)
  o snd o equations_thms_cert thy;

end;


(* code equation access *)

fun get_cert thy f c =
  Symtab.lookup ((the_eqns o the_exec) thy) c
  |> Option.map (snd o snd o fst)
  |> these
  |> (map o apfst) (Thm.transfer thy)
  |> f
  |> (map o apfst) (AxClass.unoverload thy)
  |> cert_of_eqns thy c;


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

(* constant signatures *)

fun add_type tyco thy =
  case Symtab.lookup ((snd o #types o Type.rep_tsig o Sign.tsig_of) thy) tyco
   of SOME (Type.Abbreviation (vs, _, _)) =>
          (map_exec_purge o map_signatures o apfst)
            (Symtab.update (tyco, length vs)) thy
    | _ => error ("No such type abbreviation: " ^ quote tyco);

fun add_type_cmd s thy = add_type (Sign.intern_type thy s) thy;

fun gen_add_signature prep_const prep_signature (raw_c, raw_ty) thy =
  let
    val c = prep_const thy raw_c;
    val ty = prep_signature thy raw_ty;
    val ty' = expand_signature thy ty;
    val ty'' = Sign.the_const_type thy c;
    val _ = if typ_equiv (ty', ty'') then () else
      error ("Illegal constant signature: " ^ Syntax.string_of_typ_global thy ty);
  in
    thy
    |> (map_exec_purge o map_signatures o apsnd) (Symtab.update (c, ty))
  end;

val add_signature = gen_add_signature (K I) cert_signature;
val add_signature_cmd = gen_add_signature read_const read_signature;


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

fun del_eqns c = change_eqns true c (K (false, []));


(* cases *)

fun add_case thm thy =
  let
    val (c, (k, case_pats)) = case_cert thm;
    val _ = case filter_out (is_constr thy) case_pats
     of [] => ()
      | cs => error ("Non-constructor(s) in case certificate: " ^ commas (map quote cs));
    val entry = (1 + Int.max (1, length case_pats), (k, case_pats))
  in (map_exec_purge o map_cases o apfst) (Symtab.update (c, entry)) thy end;

fun add_undefined c thy =
  (map_exec_purge o map_cases o apsnd) (Symtab.update (c, ())) thy;


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
    |> map_exec_purge
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

end; (*struct*)


(** type-safe interfaces for data dependent on executable code **)

functor Code_Data(Data: CODE_DATA_ARGS): CODE_DATA =
struct

type T = Data.T;
exception Data of T;
fun dest (Data x) = x

val kind = Code.declare_data (Data Data.empty);

val data_op = (kind, Data, dest);

val change = Code.change_data data_op;
fun change_yield thy = Code.change_yield_data data_op thy;

end;

structure Code : CODE = struct open Code; end;
