(*  Title:      Pure/Isar/code.ML
    Author:     Florian Haftmann, TU Muenchen

Abstract executable content of theory.  Management of data dependent on
executable content.  Cache assumes non-concurrent processing of a single theory.
*)

signature CODE =
sig
  (*constructor sets*)
  val constrset_of_consts: theory -> (string * typ) list
    -> string * ((string * sort) list * (string * typ list) list)

  (*typ instantiations*)
  val typscheme: theory -> string * typ -> (string * sort) list * typ
  val inst_thm: theory -> sort Vartab.table -> thm -> thm

  (*constants*)
  val string_of_typ: theory -> typ -> string
  val string_of_const: theory -> string -> string
  val no_args: theory -> string -> int
  val check_const: theory -> term -> string
  val read_bare_const: theory -> string -> string * typ
  val read_const: theory -> string -> string

  (*constant aliasses*)
  val add_const_alias: thm -> theory -> theory
  val triv_classes: theory -> class list
  val resubst_alias: theory -> string -> string

  (*code equations*)
  val mk_eqn: theory -> (string -> bool) -> thm * bool -> thm * bool
  val mk_eqn_liberal: theory -> (string -> bool) -> thm -> (thm * bool) option
  val assert_eqn: theory -> thm * bool -> thm * bool
  val assert_eqns_const: theory -> string
    -> (thm * bool) list -> (thm * bool) list
  val const_typ_eqn: thm -> string * typ
  val const_eqn: theory -> thm -> string
  val typscheme_eqn: theory -> thm -> (string * sort) list * typ
  val expand_eta: theory -> int -> thm -> thm
  val rewrite_eqn: simpset -> thm -> thm
  val rewrite_head: thm list -> thm -> thm
  val norm_args: theory -> thm list -> thm list 
  val norm_varnames: theory -> thm list -> thm list

  (*case certificates*)
  val case_cert: thm -> string * (int * string list)

  (*infrastructure*)
  val add_attribute: string * attribute parser -> theory -> theory
  val purge_data: theory -> theory

  (*executable content*)
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
  val add_eqnl: string * (thm * bool) list lazy -> theory -> theory
  val add_case: thm -> theory -> theory
  val add_undefined: string -> theory -> theory

  (*data retrieval*)
  val get_datatype: theory -> string -> ((string * sort) list * (string * typ list) list)
  val get_datatype_of_constr: theory -> string -> string option
  val default_typscheme: theory -> string -> (string * sort) list * typ
  val these_eqns: theory -> string -> (thm * bool) list
  val get_case_scheme: theory -> string -> (int * (int * string list)) option
  val is_undefined: theory -> string -> bool
  val print_codesetup: theory -> unit
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

(* auxiliary *)

fun string_of_typ thy = setmp show_sorts true (Syntax.string_of_typ_global thy);
fun string_of_const thy c = case AxClass.inst_of_param thy c
 of SOME (c, tyco) => Sign.extern_const thy c ^ " " ^ enclose "[" "]" (Sign.extern_type thy tyco)
  | NONE => Sign.extern_const thy c;

fun no_args thy = length o fst o strip_type o Sign.the_const_type thy;


(* utilities *)

fun typscheme thy (c, ty) =
  let
    val ty' = Logic.unvarifyT ty;
    fun dest (TFree (v, sort)) = (v, sort)
      | dest ty = error ("Illegal type parameter in type scheme: " ^ Syntax.string_of_typ_global thy ty);
    val vs = map dest (Sign.const_typargs thy (c, ty'));
  in (vs, Type.strip_sorts ty') end;

fun inst_thm thy tvars' thm =
  let
    val tvars = (Term.add_tvars o Thm.prop_of) thm [];
    val inter_sort = Sorts.inter_sort (Sign.classes_of thy);
    fun mk_inst (tvar as (v, sort)) = case Vartab.lookup tvars' v
     of SOME sort' => SOME (pairself (Thm.ctyp_of thy o TVar)
          (tvar, (v, inter_sort (sort, sort'))))
      | NONE => NONE;
    val insts = map_filter mk_inst tvars;
  in Thm.instantiate (insts, []) thm end;

fun expand_eta thy k thm =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm;
    val (head, args) = strip_comb lhs;
    val l = if k = ~1
      then (length o fst o strip_abs) rhs
      else Int.max (0, k - length args);
    val used = Name.make_context (map (fst o fst) (Term.add_vars lhs []));
    fun get_name _ 0 = pair []
      | get_name (Abs (v, ty, t)) k =
          Name.variants [v]
          ##>> get_name t (k - 1)
          #>> (fn ([v'], vs') => (v', ty) :: vs')
      | get_name t k = 
          let
            val (tys, _) = (strip_type o fastype_of) t
          in case tys
           of [] => raise TERM ("expand_eta", [t])
            | ty :: _ =>
                Name.variants [""]
                #-> (fn [v] => get_name (t $ Var ((v, 0), ty)) (k - 1)
                #>> (fn vs' => (v, ty) :: vs'))
          end;
    val (vs, _) = get_name rhs l used;
    fun expand (v, ty) thm = Drule.fun_cong_rule thm
      (Thm.cterm_of thy (Var ((v, 0), ty)));
  in
    thm
    |> fold expand vs
    |> Conv.fconv_rule Drule.beta_eta_conversion
  end;

fun eqn_conv conv =
  let
    fun lhs_conv ct = if can Thm.dest_comb ct
      then (Conv.combination_conv lhs_conv conv) ct
      else Conv.all_conv ct;
  in Conv.combination_conv (Conv.arg_conv lhs_conv) conv end;

fun head_conv conv =
  let
    fun lhs_conv ct = if can Thm.dest_comb ct
      then (Conv.fun_conv lhs_conv) ct
      else conv ct;
  in Conv.fun_conv (Conv.arg_conv lhs_conv) end;

val rewrite_eqn = Conv.fconv_rule o eqn_conv o Simplifier.rewrite;
val rewrite_head = Conv.fconv_rule o head_conv o MetaSimplifier.rewrite false;

fun norm_args thy thms =
  let
    val num_args_of = length o snd o strip_comb o fst o Logic.dest_equals;
    val k = fold (curry Int.max o num_args_of o Thm.prop_of) thms 0;
  in
    thms
    |> map (expand_eta thy k)
    |> map (Conv.fconv_rule Drule.beta_eta_conversion)
  end;

fun canonical_tvars thy thm =
  let
    val ctyp = Thm.ctyp_of thy;
    val purify_tvar = unprefix "'" #> Name.desymbolize false #> prefix "'";
    fun tvars_subst_for thm = (fold_types o fold_atyps)
      (fn TVar (v_i as (v, _), sort) => let
            val v' = purify_tvar v
          in if v = v' then I
          else insert (op =) (v_i, (v', sort)) end
        | _ => I) (prop_of thm) [];
    fun mk_inst (v_i, (v', sort)) (maxidx, acc) =
      let
        val ty = TVar (v_i, sort)
      in
        (maxidx + 1, (ctyp ty, ctyp (TVar ((v', maxidx), sort))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (tvars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate (inst, []) thm end;

fun canonical_vars thy thm =
  let
    val cterm = Thm.cterm_of thy;
    val purify_var = Name.desymbolize false;
    fun vars_subst_for thm = fold_aterms
      (fn Var (v_i as (v, _), ty) => let
            val v' = purify_var v
          in if v = v' then I
          else insert (op =) (v_i, (v', ty)) end
        | _ => I) (prop_of thm) [];
    fun mk_inst (v_i as (v, i), (v', ty)) (maxidx, acc) =
      let
        val t = Var (v_i, ty)
      in
        (maxidx + 1, (cterm t, cterm (Var ((v', maxidx), ty))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (vars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate ([], inst) thm end;

fun canonical_absvars thm =
  let
    val t = Thm.plain_prop_of thm;
    val purify_var = Name.desymbolize false;
    val t' = Term.map_abs_vars purify_var t;
  in Thm.rename_boundvars t t' thm end;

fun norm_varnames thy thms =
  let
    fun burrow_thms f [] = []
      | burrow_thms f thms =
          thms
          |> Conjunction.intr_balanced
          |> f
          |> Conjunction.elim_balanced (length thms)
  in
    thms
    |> map (canonical_vars thy)
    |> map canonical_absvars
    |> map Drule.zero_var_indexes
    |> burrow_thms (canonical_tvars thy)
    |> Drule.zero_var_indexes_list
  end;


(* const aliasses *)

structure ConstAlias = TheoryDataFun
(
  type T = ((string * string) * thm) list * class list;
  val empty = ([], []);
  val copy = I;
  val extend = I;
  fun merge _ ((alias1, classes1), (alias2, classes2)) : T =
    (Library.merge (eq_snd Thm.eq_thm_prop) (alias1, alias2),
      Library.merge (op =) (classes1, classes2));
);

fun add_const_alias thm thy =
  let
    val lhs_rhs = case try Logic.dest_equals (Thm.prop_of thm)
     of SOME lhs_rhs => lhs_rhs
      | _ => error ("Not an equation: " ^ Display.string_of_thm thm);
    val c_c' = case try (pairself (AxClass.unoverload_const thy o dest_Const)) lhs_rhs
     of SOME c_c' => c_c'
      | _ => error ("Not an equation with two constants: " ^ Display.string_of_thm thm);
    val some_class = the_list (AxClass.class_of_param thy (snd c_c'));
  in thy |>
    ConstAlias.map (fn (alias, classes) =>
      ((c_c', thm) :: alias, fold (insert (op =)) some_class classes))
  end;

fun resubst_alias thy =
  let
    val alias = fst (ConstAlias.get thy);
    val subst_inst_param = Option.map fst o AxClass.inst_of_param thy;
    fun subst_alias c =
      get_first (fn ((c', c''), _) => if c = c'' then SOME c' else NONE) alias;
  in
    perhaps subst_inst_param
    #> perhaps subst_alias
  end;

val triv_classes = snd o ConstAlias.get;


(* reading constants as terms *)

fun check_bare_const thy t = case try dest_Const t
 of SOME c_ty => c_ty
  | NONE => error ("Not a constant: " ^ Syntax.string_of_term_global thy t);

fun check_const thy = AxClass.unoverload_const thy o check_bare_const thy;

fun read_bare_const thy = check_bare_const thy o Syntax.read_term_global thy;

fun read_const thy = AxClass.unoverload_const thy o read_bare_const thy;


(* constructor sets *)

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
        val _ = if tyco' <> tyco
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


(* code equations *)

exception BAD_THM of string;
fun bad_thm msg = raise BAD_THM msg;
fun error_thm f thm = f thm handle BAD_THM msg => error msg;
fun try_thm f thm = SOME (f thm) handle BAD_THM _ => NONE;

fun is_linear thm =
  let val (_, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm
  in not (has_duplicates (op =) ((fold o fold_aterms)
    (fn Var (v, _) => cons v | _ => I) args [])) end;

fun gen_assert_eqn thy is_constr_head is_constr_pat (thm, proper) =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm
      handle TERM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm thm)
           | THM _ => bad_thm ("Not an equation: " ^ Display.string_of_thm thm);
    fun vars_of t = fold_aterms (fn Var (v, _) => insert (op =) v
      | Free _ => bad_thm ("Illegal free variable in equation\n"
          ^ Display.string_of_thm thm)
      | _ => I) t [];
    fun tvars_of t = fold_term_types (fn _ =>
      fold_atyps (fn TVar (v, _) => insert (op =) v
        | TFree _ => bad_thm 
      ("Illegal free type variable in equation\n" ^ Display.string_of_thm thm))) t [];
    val lhs_vs = vars_of lhs;
    val rhs_vs = vars_of rhs;
    val lhs_tvs = tvars_of lhs;
    val rhs_tvs = tvars_of rhs;
    val _ = if null (subtract (op =) lhs_vs rhs_vs)
      then ()
      else bad_thm ("Free variables on right hand side of equation\n"
        ^ Display.string_of_thm thm);
    val _ = if null (subtract (op =) lhs_tvs rhs_tvs)
      then ()
      else bad_thm ("Free type variables on right hand side of equation\n"
        ^ Display.string_of_thm thm)    val (head, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm;
    val (c, ty) = case head
     of Const (c_ty as (_, ty)) => (AxClass.unoverload_const thy c_ty, ty)
      | _ => bad_thm ("Equation not headed by constant\n" ^ Display.string_of_thm thm);
    fun check _ (Abs _) = bad_thm
          ("Abstraction on left hand side of equation\n"
            ^ Display.string_of_thm thm)
      | check 0 (Var _) = ()
      | check _ (Var _) = bad_thm
          ("Variable with application on left hand side of equation\n"
            ^ Display.string_of_thm thm)
      | check n (t1 $ t2) = (check (n+1) t1; check 0 t2)
      | check n (Const (c_ty as (c, ty))) = if n = (length o fst o strip_type) ty
          then if not proper orelse is_constr_pat (AxClass.unoverload_const thy c_ty)
            then ()
            else bad_thm (quote c ^ " is not a constructor, on left hand side of equation\n"
              ^ Display.string_of_thm thm)
          else bad_thm
            ("Partially applied constant " ^ quote c ^ " on left hand side of equation\n"
               ^ Display.string_of_thm thm);
    val _ = map (check 0) args;
    val _ = if not proper orelse is_linear thm then ()
      else bad_thm ("Duplicate variables on left hand side of equation\n"
        ^ Display.string_of_thm thm);
    val _ = if (is_none o AxClass.class_of_param thy) c
      then ()
      else bad_thm ("Polymorphic constant as head in equation\n"
        ^ Display.string_of_thm thm)
    val _ = if not (is_constr_head c)
      then ()
      else bad_thm ("Constructor as head in equation\n"
        ^ Display.string_of_thm thm)
    val ty_decl = Sign.the_const_type thy c;
    val _ = if Sign.typ_equiv thy (Type.strip_sorts ty_decl, Type.strip_sorts ty)
      then () else bad_thm ("Type\n" ^ string_of_typ thy ty
           ^ "\nof equation\n"
           ^ Display.string_of_thm thm
           ^ "\nis incompatible with declared function type\n"
           ^ string_of_typ thy ty_decl)
  in (thm, proper) end;

fun assert_eqn thy is_constr = error_thm (gen_assert_eqn thy is_constr is_constr);

val const_typ_eqn = dest_Const o fst o strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of;


(*those following are permissive wrt. to overloaded constants!*)

fun mk_eqn thy is_constr_head = error_thm (gen_assert_eqn thy is_constr_head (K true)) o
  apfst (LocalDefs.meta_rewrite_rule (ProofContext.init thy));

fun mk_eqn_liberal thy is_constr_head = Option.map (fn (thm, _) => (thm, is_linear thm))
  o try_thm (gen_assert_eqn thy is_constr_head (K true))
  o rpair false o LocalDefs.meta_rewrite_rule (ProofContext.init thy);

fun const_typ_eqn_unoverload thy thm =
  let
    val (c, ty) = const_typ_eqn thm;
    val c' = AxClass.unoverload_const thy (c, ty);
  in (c', ty) end;

fun typscheme_eqn thy = typscheme thy o const_typ_eqn_unoverload thy;
fun const_eqn thy = fst o const_typ_eqn_unoverload thy;


(* case cerificates *)

fun case_certificate thm =
  let
    val ((head, raw_case_expr), cases) = (apfst Logic.dest_equals
      o apsnd Logic.dest_conjunctions o Logic.dest_implies o Thm.prop_of) thm;
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


(** code attributes **)

structure CodeAttr = TheoryDataFun (
  type T = (string * attribute parser) list;
  val empty = [];
  val copy = I;
  val extend = I;
  fun merge _ = AList.merge (op = : string * string -> bool) (K true);
);

fun add_attribute (attr as (name, _)) =
  let
    fun add_parser ("", parser) attrs = attrs |> rev |> AList.update (op =) ("", parser) |> rev
      | add_parser (name, parser) attrs = (name, Args.$$$ name |-- parser) :: attrs;
  in CodeAttr.map (fn attrs => if not (name = "") andalso AList.defined (op =) attrs name
    then error ("Code attribute " ^ name ^ " already declared") else add_parser attr attrs)
  end;

val _ = Context.>> (Context.map_theory
  (Attrib.setup (Binding.name "code")
    (Scan.peek (fn context =>
      List.foldr op || Scan.fail (map snd (CodeAttr.get (Context.theory_of context)))))
    "declare theorems for code generation"));



(** logical and syntactical specification of executable code **)

(* code equations *)

type eqns = bool * (thm * bool) list lazy;
  (*default flag, theorems with proper flag (perhaps lazy)*)

fun pretty_lthms ctxt r = case Lazy.peek r
 of SOME thms => map (ProofContext.pretty_thm ctxt o fst) (Exn.release thms)
  | NONE => [Pretty.str "[...]"];

fun certificate thy f r =
  case Lazy.peek r
   of SOME thms => (Lazy.value o f thy) (Exn.release thms)
    | NONE => let
        val thy_ref = Theory.check_thy thy;
      in Lazy.lazy (fn () => (f (Theory.deref thy_ref) o Lazy.force) r) end;

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
        (warning ("Code generator: dropping redundant code equation\n" ^ Display.string_of_thm thm'); true)
      else false;
  in (thm, proper) :: filter_out drop thms end;

fun add_thm thy _ thm (false, thms) = (false, Lazy.map_force (add_drop_redundant thy thm) thms)
  | add_thm thy true thm (true, thms) = (true, Lazy.map_force (fn thms => thms @ [thm]) thms)
  | add_thm thy false thm (true, thms) = (false, Lazy.value [thm]);

fun add_lthms lthms _ = (false, lthms);

fun del_thm thm = (apsnd o Lazy.map_force) (remove (eq_fst Thm.eq_thm_prop) (thm, true));


(* specification data *)

datatype spec = Spec of {
  concluded_history: bool,
  eqns: ((bool * eqns) * (serial * eqns) list) Symtab.table
    (*with explicit history*),
  dtyps: ((serial * ((string * sort) list * (string * typ list) list)) list) Symtab.table
    (*with explicit history*),
  cases: (int * (int * string list)) Symtab.table * unit Symtab.table
};

fun make_spec ((concluded_history, eqns), (dtyps, cases)) =
  Spec { concluded_history = concluded_history, eqns = eqns, dtyps = dtyps, cases = cases };
fun map_spec f (Spec { concluded_history = concluded_history, eqns = eqns,
  dtyps = dtyps, cases = cases }) =
  make_spec (f ((concluded_history, eqns), (dtyps, cases)));
fun merge_spec (Spec { concluded_history = _, eqns = eqns1, dtyps = dtyps1, cases = (cases1, undefs1) },
  Spec { concluded_history = _, eqns = eqns2, dtyps = dtyps2, cases = (cases2, undefs2) }) =
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
  in make_spec ((false, eqns), (dtyps, cases)) end;


(* code setup data *)

fun the_spec (Spec x) = x;
fun the_eqns (Spec { eqns, ... }) = eqns;
fun the_dtyps (Spec { dtyps, ... }) = dtyps;
fun the_cases (Spec { cases, ... }) = cases;
fun history_concluded (Spec { concluded_history, ... }) = concluded_history;
val map_concluded_history = map_spec o apfst o apfst;
val map_eqns = map_spec o apfst o apsnd;
val map_dtyps = map_spec o apsnd o apfst;
val map_cases = map_spec o apsnd o apsnd;


(* data slots dependent on executable content *)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = TableFun(type key = int val ord = int_ord);

local

type kind = {
  empty: Object.T,
  purge: theory -> string list -> Object.T -> Object.T
};

val kinds = ref (Datatab.empty: kind Datatab.table);
val kind_keys = ref ([]: serial list);

fun invoke f k = case Datatab.lookup (! kinds) k
 of SOME kind => f kind
  | NONE => sys_error "Invalid code data identifier";

in

fun declare_data empty purge =
  let
    val k = serial ();
    val kind = {empty = empty, purge = purge};
    val _ = change kinds (Datatab.update (k, kind));
    val _ = change kind_keys (cons k);
  in k end;

fun invoke_init k = invoke (fn kind => #empty kind) k;

fun invoke_purge_all thy cs =
  fold (fn k => Datatab.map_entry k
    (invoke (fn kind => #purge kind thy cs) k)) (! kind_keys);

end; (*local*)


(** theory store **)

local

type data = Object.T Datatab.table;
val empty_data = Datatab.empty : data;

structure Code_Data = TheoryDataFun
(
  type T = spec * data ref;
  val empty = (make_spec ((false, Symtab.empty),
    (Symtab.empty, (Symtab.empty, Symtab.empty))), ref empty_data);
  fun copy (spec, data) = (spec, ref (! data));
  val extend = copy;
  fun merge pp ((spec1, data1), (spec2, data2)) =
    (merge_spec (spec1, spec2), ref empty_data);
);

fun thy_data f thy = f ((snd o Code_Data.get) thy);

fun get_ensure_init kind data_ref =
  case Datatab.lookup (! data_ref) kind
   of SOME x => x
    | NONE => let val y = invoke_init kind
        in (change data_ref (Datatab.update (kind, y)); y) end;

in

(* access to executable content *)

val the_exec = fst o Code_Data.get;

fun complete_class_params thy cs =
  fold (fn c => case AxClass.inst_of_param thy c
   of NONE => insert (op =) c
    | SOME (c', _) => insert (op =) c' #> insert (op =) c) cs [];

fun map_exec_purge touched f thy =
  Code_Data.map (fn (exec, data) => (f exec, ref (case touched
   of SOME cs => invoke_purge_all thy (complete_class_params thy cs) (! data)
    | NONE => empty_data))) thy;

val purge_data = (Code_Data.map o apsnd) (K (ref empty_data));


(* tackling equation history *)

fun get_eqns thy c =
  Symtab.lookup ((the_eqns o the_exec) thy) c
  |> Option.map (Lazy.force o snd o snd o fst)
  |> these;

fun continue_history thy = if (history_concluded o the_exec) thy
  then thy
    |> (Code_Data.map o apfst o map_concluded_history) (K false)
    |> SOME
  else NONE;

fun conclude_history thy = if (history_concluded o the_exec) thy
  then NONE
  else thy
    |> (Code_Data.map o apfst)
        ((map_eqns o Symtab.map) (fn ((changed, current), history) =>
          ((false, current),
            if changed then (serial (), current) :: history else history))
        #> map_concluded_history (K true))
    |> SOME;

val _ = Context.>> (Context.map_theory (Code_Data.init
  #> Theory.at_begin continue_history
  #> Theory.at_end conclude_history));


(* access to data dependent on abstract executable content *)

fun get_data (kind, _, dest) = thy_data (get_ensure_init kind #> dest);

fun change_data (kind, mk, dest) =
  let
    fun chnge data_ref f =
      let
        val data = get_ensure_init kind data_ref;
        val data' = f (dest data);
      in (change data_ref (Datatab.update (kind, mk data')); data') end;
  in thy_data chnge end;

fun change_yield_data (kind, mk, dest) =
  let
    fun chnge data_ref f =
      let
        val data = get_ensure_init kind data_ref;
        val (x, data') = f (dest data);
      in (x, (change data_ref (Datatab.update (kind, mk data')); data')) end;
  in thy_data chnge end;

end; (*local*)

fun print_codesetup thy =
  let
    val ctxt = ProofContext.init thy;
    val exec = the_exec thy;
    fun pretty_eqn (s, (_, lthms)) =
      (Pretty.block o Pretty.fbreaks) (
        Pretty.str s :: pretty_lthms ctxt lthms
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
          (Syntax.string_of_typ_global thy (Type (dtco, map TFree vs)), cos))
      |> sort (string_ord o pairself fst)
  in
    (Pretty.writeln o Pretty.chunks) [
      Pretty.block (
        Pretty.str "code equations:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_eqn) eqns
      ),
      Pretty.block (
        Pretty.str "datatypes:"
        :: Pretty.fbrk
        :: (Pretty.fbreaks o map pretty_dtyp) dtyps
      )
    ]
  end;


(** theorem transformation and certification **)

fun common_typ_eqns thy [] = []
  | common_typ_eqns thy [thm] = [thm]
  | common_typ_eqns thy (thms as thm :: _) = (*FIXME is too general*)
      let
        fun incr_thm thm max =
          let
            val thm' = incr_indexes max thm;
            val max' = Thm.maxidx_of thm' + 1;
          in (thm', max') end;
        val (thms', maxidx) = fold_map incr_thm thms 0;
        val ty1 :: tys = map (snd o const_typ_eqn) thms';
        fun unify ty env = Sign.typ_unify thy (ty1, ty) env
          handle Type.TUNIFY =>
            error ("Type unificaton failed, while unifying code equations\n"
            ^ (cat_lines o map Display.string_of_thm) thms
            ^ "\nwith types\n"
            ^ (cat_lines o map (string_of_typ thy)) (ty1 :: tys));
        val (env, _) = fold unify tys (Vartab.empty, maxidx)
        val instT = Vartab.fold (fn (x_i, (sort, ty)) =>
          cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [];
      in map (Thm.instantiate (instT, [])) thms' end;


(** interfaces and attributes **)

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

val assert_eqn = fn thy => assert_eqn thy (is_constr thy);

fun assert_eqns_const thy c eqns =
  let
    fun cert (eqn as (thm, _)) = if c = const_eqn thy thm
      then eqn else error ("Wrong head of code equation,\nexpected constant "
        ^ string_of_const thy c ^ "\n" ^ Display.string_of_thm thm)
  in map (cert o assert_eqn thy) eqns end;

fun change_eqns delete c f = (map_exec_purge (SOME [c]) o map_eqns
  o (if delete then Symtab.map_entry c else Symtab.map_default (c, ((false, (true, Lazy.value [])), [])))
    o apfst) (fn (_, eqns) => (true, f eqns));

fun gen_add_eqn default (eqn as (thm, _)) thy =
  let val c = const_eqn thy thm
  in change_eqns false c (add_thm thy default eqn) thy end;

fun add_eqn thm thy =
  gen_add_eqn false (mk_eqn thy (is_constr thy) (thm, true)) thy;

fun add_default_eqn thm thy =
  case mk_eqn_liberal thy (is_constr thy) thm
   of SOME eqn => gen_add_eqn true eqn thy
    | NONE => thy;

fun add_nbe_eqn thm thy =
  gen_add_eqn false (mk_eqn thy (is_constr thy) (thm, false)) thy;

fun add_eqnl (c, lthms) thy =
  let
    val lthms' = certificate thy (fn thy => assert_eqns_const thy c) lthms;
  in change_eqns false c (add_lthms lthms') thy end;

val add_default_eqn_attribute = Thm.declaration_attribute
  (fn thm => Context.mapping (add_default_eqn thm) I);
val add_default_eqn_attrib = Attrib.internal (K add_default_eqn_attribute);

fun del_eqn thm thy = case mk_eqn_liberal thy (is_constr thy) thm
 of SOME (thm, _) => change_eqns true (const_eqn thy thm) (del_thm thm) thy
  | NONE => thy;

fun del_eqns c = change_eqns true c (K (false, Lazy.value []));

fun get_case_scheme thy = Symtab.lookup ((fst o the_cases o the_exec) thy);

val is_undefined = Symtab.defined o snd o the_cases o the_exec;

structure TypeInterpretation = InterpretationFun(type T = string * serial val eq = eq_snd (op =) : T * T -> bool);

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
    |> TypeInterpretation.data (tyco, serial ())
  end;

fun type_interpretation f =  TypeInterpretation.interpretation
  (fn (tyco, _) => fn thy => f (tyco, get_datatype thy tyco) thy);

fun add_datatype_cmd raw_cs thy =
  let
    val cs = map (read_bare_const thy) raw_cs;
  in add_datatype cs thy end;

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

val _ = Context.>> (Context.map_theory
  (let
    fun mk_attribute f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);
    fun add_simple_attribute (name, f) =
      add_attribute (name, Scan.succeed (mk_attribute f));
    fun add_del_attribute (name, (add, del)) =
      add_attribute (name, Args.del |-- Scan.succeed (mk_attribute del)
        || Scan.succeed (mk_attribute add))
  in
    TypeInterpretation.init
    #> add_del_attribute ("", (add_eqn, del_eqn))
    #> add_simple_attribute ("nbe", add_nbe_eqn)
  end));

fun these_eqns thy c =
  get_eqns thy c
  |> (map o apfst) (Thm.transfer thy)
  |> burrow_fst (common_typ_eqns thy);

fun default_typscheme thy c =
  let
    fun the_const_typscheme c = (curry (typscheme thy) c o snd o dest_Const
      o TermSubst.zero_var_indexes o curry Const "" o Sign.the_const_type thy) c;
    fun strip_sorts (vs, ty) = (map (fn (v, _) => (v, [])) vs, ty);
  in case AxClass.class_of_param thy c
   of SOME class => ([(Name.aT, [class])], snd (the_const_typscheme c))
    | NONE => if is_constr thy c
        then strip_sorts (the_const_typscheme c)
        else case get_eqns thy c
         of (thm, _) :: _ => (typscheme_eqn thy o Drule.zero_var_indexes) thm
          | [] => strip_sorts (the_const_typscheme c) end;

end; (*struct*)


(** type-safe interfaces for data depedent on executable content **)

functor CodeDataFun(Data: CODE_DATA_ARGS): CODE_DATA =
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

structure Code : CODE = struct open Code; end;
