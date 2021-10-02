(*  Title:      Tools/Code/code_thingol.ML
    Author:     Florian Haftmann, TU Muenchen

Intermediate language ("Thin-gol") representing executable code.
Representation and translation.
*)

infix 8 `%%;
infix 4 `$;
infix 4 `$$;
infixr 3 `->;
infixr 3 `|=>;
infixr 3 `|==>;

signature BASIC_CODE_THINGOL =
sig
  type vname = string;
  datatype dict =
      Dict of (class * class) list * plain_dict
  and plain_dict = 
      Dict_Const of (string * class) * dict list list
    | Dict_Var of { var: vname, index: int, length: int, class: class, unique: bool };
  datatype itype =
      `%% of string * itype list
    | ITyVar of vname;
  type const = { sym: Code_Symbol.T, typargs: itype list, dicts: dict list list,
    dom: itype list, annotation: itype option };
  datatype iterm =
      IConst of const
    | IVar of vname option
    | `$ of iterm * iterm
    | `|=> of (vname option * itype) * iterm
    | ICase of { term: iterm, typ: itype, clauses: (iterm * iterm) list, primitive: iterm };
  val `-> : itype * itype -> itype;
  val `$$ : iterm * iterm list -> iterm;
  val `|==> : (vname option * itype) list * iterm -> iterm;
  type typscheme = (vname * sort) list * itype;
end;

signature CODE_THINGOL =
sig
  include BASIC_CODE_THINGOL
  val unfoldl: ('a -> ('a * 'b) option) -> 'a -> 'a * 'b list
  val unfoldr: ('a -> ('b * 'a) option) -> 'a -> 'b list * 'a
  val unfold_fun: itype -> itype list * itype
  val unfold_fun_n: int -> itype -> itype list * itype
  val unfold_app: iterm -> iterm * iterm list
  val unfold_abs: iterm -> (vname option * itype) list * iterm
  val split_let: iterm -> (((iterm * itype) * iterm) * iterm) option
  val split_let_no_pat: iterm -> (((string option * itype) * iterm) * iterm) option
  val unfold_let: iterm -> ((iterm * itype) * iterm) list * iterm
  val unfold_let_no_pat: iterm -> ((string option * itype) * iterm) list * iterm
  val split_pat_abs: iterm -> ((iterm * itype) * iterm) option
  val unfold_pat_abs: iterm -> (iterm * itype) list * iterm
  val unfold_const_app: iterm -> (const * iterm list) option
  val is_IVar: iterm -> bool
  val is_IAbs: iterm -> bool
  val eta_expand: int -> const * iterm list -> iterm
  val contains_dict_var: iterm -> bool
  val unambiguous_dictss: dict list list -> bool
  val add_constsyms: iterm -> Code_Symbol.T list -> Code_Symbol.T list
  val add_tyconames: iterm -> string list -> string list
  val fold_varnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a

  datatype stmt =
      NoStmt
    | Fun of (typscheme * ((iterm list * iterm) * (thm option * bool)) list) * thm option
    | Datatype of vname list *
        ((string * vname list (*type argument wrt. canonical order*)) * itype list) list
    | Datatypecons of string
    | Class of vname * ((class * class) list * (string * itype) list)
    | Classrel of class * class
    | Classparam of class
    | Classinst of { class: string, tyco: string, vs: (vname * sort) list,
        superinsts: (class * dict list list) list,
        inst_params: ((string * (const * int)) * (thm * bool)) list,
        superinst_params: ((string * (const * int)) * (thm * bool)) list };
  type program = stmt Code_Symbol.Graph.T
  val unimplemented: program -> string list
  val implemented_deps: program -> string list
  val map_terms_bottom_up: (iterm -> iterm) -> iterm -> iterm
  val map_terms_stmt: (iterm -> iterm) -> stmt -> stmt
  val is_constr: program -> Code_Symbol.T -> bool
  val is_case: stmt -> bool
  val group_stmts: Proof.context -> program
    -> ((Code_Symbol.T * stmt) list * (Code_Symbol.T * stmt) list
      * ((Code_Symbol.T * stmt) list * (Code_Symbol.T * stmt) list)) list

  val read_const_exprs: Proof.context -> string list -> string list
  val consts_program: Proof.context -> string list -> program
  val dynamic_conv: Proof.context -> (program
    -> typscheme * iterm -> Code_Symbol.T list -> conv)
    -> conv
  val dynamic_value: Proof.context -> ((term -> term) -> 'a -> 'a) -> (program
    -> term -> typscheme * iterm -> Code_Symbol.T list -> 'a)
    -> term -> 'a
  val static_conv_thingol: { ctxt: Proof.context, consts: string list }
    -> ({ program: program, deps: string list }
      -> Proof.context -> typscheme * iterm -> Code_Symbol.T list -> conv)
    -> Proof.context -> conv
  val static_conv_isa: { ctxt: Proof.context, consts: string list }
    -> (program -> Proof.context -> term -> conv)
    -> Proof.context -> conv
  val static_value: { ctxt: Proof.context, lift_postproc: ((term -> term) -> 'a -> 'a), consts: string list }
    -> ({ program: program, deps: string list }
      -> Proof.context -> term -> typscheme * iterm -> Code_Symbol.T list -> 'a)
    -> Proof.context -> term -> 'a
end;

structure Code_Thingol : CODE_THINGOL =
struct

open Basic_Code_Symbol;

(** auxiliary **)

fun unfoldl dest x =
  case dest x
   of NONE => (x, [])
    | SOME (x1, x2) =>
        let val (x', xs') = unfoldl dest x1 in (x', xs' @ [x2]) end;

fun unfoldr dest x =
  case dest x
   of NONE => ([], x)
    | SOME (x1, x2) =>
        let val (xs', x') = unfoldr dest x2 in (x1 :: xs', x') end;


(** language core - types, terms **)

type vname = string;

datatype dict =
    Dict of (class * class) list * plain_dict
and plain_dict = 
    Dict_Const of (string * class) * dict list list
  | Dict_Var of { var: vname, index: int, length: int, class: class, unique: bool };

datatype itype =
    `%% of string * itype list
  | ITyVar of vname;

fun ty1 `-> ty2 = "fun" `%% [ty1, ty2];

val unfold_fun = unfoldr
  (fn "fun" `%% [ty1, ty2] => SOME (ty1, ty2)
    | _ => NONE);

fun unfold_fun_n n ty =
  let
    val (tys1, ty1) = unfold_fun ty;
    val (tys3, tys2) = chop n tys1;
    val ty3 = Library.foldr (op `->) (tys2, ty1);
  in (tys3, ty3) end;

type const = { sym: Code_Symbol.T, typargs: itype list, dicts: dict list list,
  dom: itype list, annotation: itype option };

datatype iterm =
    IConst of const
  | IVar of vname option
  | `$ of iterm * iterm
  | `|=> of (vname option * itype) * iterm
  | ICase of { term: iterm, typ: itype, clauses: (iterm * iterm) list, primitive: iterm };
    (*see also signature*)

fun is_IVar (IVar _) = true
  | is_IVar _ = false;

fun is_IAbs (_ `|=> _) = true
  | is_IAbs _ = false;

val op `$$ = Library.foldl (op `$);
val op `|==> = Library.foldr (op `|=>);

val unfold_app = unfoldl
  (fn op `$ t => SOME t
    | _ => NONE);

val unfold_abs = unfoldr
  (fn op `|=> t => SOME t
    | _ => NONE);

val split_let = 
  (fn ICase { term = t, typ = ty, clauses = [(p, body)], ... } => SOME (((p, ty), t), body)
    | _ => NONE);

val split_let_no_pat = 
  (fn ICase { term = t, typ = ty, clauses = [(IVar v, body)], ... } => SOME (((v, ty), t), body)
    | _ => NONE);

val unfold_let = unfoldr split_let;

val unfold_let_no_pat = unfoldr split_let_no_pat;

fun unfold_const_app t =
 case unfold_app t
  of (IConst c, ts) => SOME (c, ts)
   | _ => NONE;

fun fold_constexprs f =
  let
    fun fold' (IConst c) = f c
      | fold' (IVar _) = I
      | fold' (t1 `$ t2) = fold' t1 #> fold' t2
      | fold' (_ `|=> t) = fold' t
      | fold' (ICase { term = t, clauses = clauses, ... }) = fold' t
          #> fold (fn (p, body) => fold' p #> fold' body) clauses
  in fold' end;

val add_constsyms = fold_constexprs (fn { sym, ... } => insert (op =) sym);

fun add_tycos (tyco `%% tys) = insert (op =) tyco #> fold add_tycos tys
  | add_tycos (ITyVar _) = I;

val add_tyconames = fold_constexprs (fn { typargs = tys, ... } => fold add_tycos tys);

fun fold_varnames f =
  let
    fun fold_aux add_vars f =
      let
        fun fold_term _ (IConst _) = I
          | fold_term vs (IVar (SOME v)) = if member (op =) vs v then I else f v
          | fold_term _ (IVar NONE) = I
          | fold_term vs (t1 `$ t2) = fold_term vs t1 #> fold_term vs t2
          | fold_term vs ((SOME v, _) `|=> t) = fold_term (insert (op =) v vs) t
          | fold_term vs ((NONE, _) `|=> t) = fold_term vs t
          | fold_term vs (ICase { term = t, clauses = clauses, ... }) =
              fold_term vs t #> fold (fold_clause vs) clauses
        and fold_clause vs (p, t) = fold_term (add_vars p vs) t;
      in fold_term [] end
    fun add_vars t = fold_aux add_vars (insert (op =)) t;
  in fold_aux add_vars f end;

fun exists_var t v = fold_varnames (fn w => fn b => v = w orelse b) t false;

fun split_pat_abs ((NONE, ty) `|=> t) = SOME ((IVar NONE, ty), t)
  | split_pat_abs ((SOME v, ty) `|=> t) = SOME (case t
     of ICase { term = IVar (SOME w), clauses = [(p, body)], ... } =>
          if v = w andalso (exists_var p v orelse not (exists_var body v))
          then ((p, ty), body)
          else ((IVar (SOME v), ty), t)
      | _ => ((IVar (SOME v), ty), t))
  | split_pat_abs _ = NONE;

val unfold_pat_abs = unfoldr split_pat_abs;

fun unfold_abs_eta [] t = ([], t)
  | unfold_abs_eta (_ :: tys) (v_ty `|=> t) =
      let
        val (vs_tys, t') = unfold_abs_eta tys t;
      in (v_ty :: vs_tys, t') end
  | unfold_abs_eta tys t =
      let
        val ctxt = fold_varnames Name.declare t Name.context;
        val vs_tys = (map o apfst) SOME (Name.invent_names ctxt "a" tys);
      in (vs_tys, t `$$ map (IVar o fst) vs_tys) end;

fun eta_expand k (const as { dom = tys, ... }, ts) =
  let
    val j = length ts;
    val l = k - j;
    val _ = if l > length tys
      then error "Impossible eta-expansion" else ();
    val vars = (fold o fold_varnames) Name.declare ts Name.context;
    val vs_tys = (map o apfst) SOME
      (Name.invent_names vars "a" ((take l o drop j) tys));
  in vs_tys `|==> IConst const `$$ ts @ map (IVar o fst) vs_tys end;

fun exists_dict_var f (Dict (_, d)) = exists_plain_dict_var_pred f d
and exists_plain_dict_var_pred f (Dict_Const (_, dss)) = exists_dictss_var f dss
  | exists_plain_dict_var_pred f (Dict_Var x) = f x
and exists_dictss_var f dss = (exists o exists) (exists_dict_var f) dss;

fun contains_dict_var (IConst { dicts = dss, ... }) = exists_dictss_var (K true) dss
  | contains_dict_var (IVar _) = false
  | contains_dict_var (t1 `$ t2) = contains_dict_var t1 orelse contains_dict_var t2
  | contains_dict_var (_ `|=> t) = contains_dict_var t
  | contains_dict_var (ICase { primitive = t, ... }) = contains_dict_var t;

val unambiguous_dictss = not o exists_dictss_var (fn { unique, ... } => not unique);


(** statements, abstract programs **)

type typscheme = (vname * sort) list * itype;
datatype stmt =
    NoStmt
  | Fun of (typscheme * ((iterm list * iterm) * (thm option * bool)) list) * thm option
  | Datatype of vname list * ((string * vname list) * itype list) list
  | Datatypecons of string
  | Class of vname * ((class * class) list * (string * itype) list)
  | Classrel of class * class
  | Classparam of class
  | Classinst of { class: string, tyco: string, vs: (vname * sort) list,
      superinsts: (class * dict list list) list,
      inst_params: ((string * (const * int)) * (thm * bool)) list,
      superinst_params: ((string * (const * int)) * (thm * bool)) list };

type program = stmt Code_Symbol.Graph.T;

fun unimplemented program =
  Code_Symbol.Graph.fold (fn (Constant c, (NoStmt, _)) => cons c | _ => I) program [];

fun implemented_deps program =
  Code_Symbol.Graph.keys program
  |> subtract (op =) (Code_Symbol.Graph.all_preds program (map Constant (unimplemented program)))
  |> map_filter (fn Constant c => SOME c | _ => NONE);

fun map_terms_bottom_up f (t as IConst _) = f t
  | map_terms_bottom_up f (t as IVar _) = f t
  | map_terms_bottom_up f (t1 `$ t2) = f
      (map_terms_bottom_up f t1 `$ map_terms_bottom_up f t2)
  | map_terms_bottom_up f ((v, ty) `|=> t) = f
      ((v, ty) `|=> map_terms_bottom_up f t)
  | map_terms_bottom_up f (ICase { term = t, typ = ty, clauses = clauses, primitive = t0 }) = f
      (ICase { term = map_terms_bottom_up f t, typ = ty,
        clauses = (map o apply2) (map_terms_bottom_up f) clauses,
        primitive = map_terms_bottom_up f t0 });

fun map_classparam_instances_as_term f =
  (map o apfst o apsnd o apfst) (fn const => case f (IConst const) of IConst const' => const')

fun map_terms_stmt f NoStmt = NoStmt
  | map_terms_stmt f (Fun ((tysm, eqs), case_cong)) = Fun ((tysm, (map o apfst)
      (fn (ts, t) => (map f ts, f t)) eqs), case_cong)
  | map_terms_stmt f (stmt as Datatype _) = stmt
  | map_terms_stmt f (stmt as Datatypecons _) = stmt
  | map_terms_stmt f (stmt as Class _) = stmt
  | map_terms_stmt f (stmt as Classrel _) = stmt
  | map_terms_stmt f (stmt as Classparam _) = stmt
  | map_terms_stmt f (Classinst { class, tyco, vs, superinsts,
      inst_params, superinst_params }) =
        Classinst { class = class, tyco = tyco, vs = vs, superinsts = superinsts,
          inst_params = map_classparam_instances_as_term f inst_params,
          superinst_params = map_classparam_instances_as_term f superinst_params };

fun is_constr program sym = case Code_Symbol.Graph.get_node program sym
 of Datatypecons _ => true
  | _ => false;

fun is_case (Fun (_, SOME _)) = true
  | is_case _ = false;

fun linear_stmts program =
  rev (Code_Symbol.Graph.strong_conn program)
  |> map (AList.make (Code_Symbol.Graph.get_node program));

fun group_stmts ctxt program =
  let
    fun is_fun (_, Fun _) = true | is_fun _ = false;
    fun is_datatypecons (_, Datatypecons _) = true | is_datatypecons _ = false;
    fun is_datatype (_, Datatype _) = true | is_datatype _ = false;
    fun is_class (_, Class _) = true | is_class _ = false;
    fun is_classrel (_, Classrel _) = true | is_classrel _ = false;
    fun is_classparam (_, Classparam _) = true | is_classparam _ = false;
    fun is_classinst (_, Classinst _) = true | is_classinst _ = false;
    fun group stmts =
      if forall (is_datatypecons orf is_datatype) stmts
      then (filter is_datatype stmts, [], ([], []))
      else if forall (is_class orf is_classrel orf is_classparam) stmts
      then ([], filter is_class stmts, ([], []))
      else if forall (is_fun orf is_classinst) stmts
      then ([], [], List.partition is_fun stmts)
      else error ("Illegal mutual dependencies: " ^ (commas
        o map (Code_Symbol.quote ctxt o fst)) stmts);
  in
    linear_stmts program
    |> map group
  end;


(** translation kernel **)

(* generic mechanisms *)

fun ensure_stmt symbolize generate x (deps, program) =
  let
    val sym = symbolize x;
    val add_dep = case deps of [] => I
      | dep :: _ => Code_Symbol.Graph.add_edge (dep, sym);
  in
    if can (Code_Symbol.Graph.get_node program) sym
    then
      program
      |> add_dep
      |> pair deps
      |> pair x
    else
      program
      |> Code_Symbol.Graph.default_node (sym, NoStmt)
      |> add_dep
      |> curry generate (sym :: deps)
      ||> snd
      |-> (fn stmt => (Code_Symbol.Graph.map_node sym) (K stmt))
      |> pair deps
      |> pair x
  end;

exception PERMISSIVE of unit;

fun translation_error ctxt permissive some_thm deps msg sub_msg =
  if permissive
  then raise PERMISSIVE ()
  else
    let
      val thm_msg =
        Option.map (fn thm => "in code equation " ^ Thm.string_of_thm ctxt thm) some_thm;
      val dep_msg = if null (tl deps) then NONE
        else SOME ("with dependency "
          ^ space_implode " -> " (map (Code_Symbol.quote ctxt) (rev deps)));
      val thm_dep_msg = case (thm_msg, dep_msg)
       of (SOME thm_msg, SOME dep_msg) => "\n(" ^ thm_msg ^ ",\n" ^ dep_msg ^ ")"
        | (SOME thm_msg, NONE) => "\n(" ^ thm_msg ^ ")"
        | (NONE, SOME dep_msg) => "\n(" ^ dep_msg ^ ")"
        | (NONE, NONE) => ""
    in error (msg ^ thm_dep_msg ^ ":\n" ^ sub_msg) end;

fun maybe_permissive f prgrm =
  f prgrm |>> SOME handle PERMISSIVE () => (NONE, prgrm);

fun not_wellsorted ctxt permissive some_thm deps ty sort e =
  let
    val err_class = Sorts.class_error (Context.Proof ctxt) e;
    val err_typ =
      "Type " ^ Syntax.string_of_typ ctxt ty ^ " not of sort " ^
        Syntax.string_of_sort ctxt sort;
  in
    translation_error ctxt permissive some_thm deps
      "Wellsortedness error" (err_typ ^ "\n" ^ err_class)
  end;


(* inference of type annotations for disambiguation with type classes *)

fun mk_tagged_type (true, T) = Type ("", [T])
  | mk_tagged_type (false, T) = T;

fun dest_tagged_type (Type ("", [T])) = (true, T)
  | dest_tagged_type T = (false, T);

val untag_term = map_types (snd o dest_tagged_type);

fun tag_term (proj_sort, _) eqngr =
  let
    val has_sort_constraints = exists (not o null) o map proj_sort o Code_Preproc.sortargs eqngr;
    fun tag (Const (_, T')) (Const (c, T)) =
        Const (c,
          mk_tagged_type (not (null (Term.add_tvarsT T' [])) andalso has_sort_constraints c, T))
      | tag (t1 $ u1) (t $ u) = tag t1 t $ tag u1 u
      | tag (Abs (_, _, t1)) (Abs (x, T, t)) = Abs (x, T, tag t1 t)
      | tag (Free _) (t as Free _) = t
      | tag (Var _) (t as Var _) = t
      | tag (Bound _) (t as Bound _) = t;
  in tag end

fun annotate ctxt algbr eqngr (c, ty) args rhs =
  let
    val erase = map_types (fn _ => Type_Infer.anyT []);
    val reinfer = singleton (Type_Infer_Context.infer_types ctxt);
    val lhs = list_comb (Const (c, ty), map (map_types Type.strip_sorts o fst) args);
    val reinferred_rhs = snd (Logic.dest_equals (reinfer (Logic.mk_equals (lhs, erase rhs))));
  in tag_term algbr eqngr reinferred_rhs rhs end

fun annotate_eqns ctxt algbr eqngr (c, ty) eqns =
  let
    val ctxt' = ctxt |> Proof_Context.theory_of |> Proof_Context.init_global
      |> Config.put Type_Infer_Context.const_sorts false;
      (*avoid spurious fixed variables: there is no eigen context for equations*)
  in
    map (apfst (fn (args, (rhs, some_abs)) => (args,
      (annotate ctxt' algbr eqngr (c, ty) args rhs, some_abs)))) eqns
  end;

(* abstract dictionary construction *)

datatype typarg_witness =
    Weakening of (class * class) list * plain_typarg_witness
and plain_typarg_witness =
    Global of (string * class) * typarg_witness list list
  | Local of { var: string, index: int, sort: sort, unique: bool };

fun brand_unique unique (w as Global _) = w
  | brand_unique unique (Local { var, index, sort, unique = _ }) =
      Local { var = var, index = index, sort = sort, unique = unique };

fun construct_dictionaries ctxt (proj_sort, algebra) permissive some_thm (ty, sort) (deps, program) =
  let
    fun class_relation unique (Weakening (classrels, x), sub_class) super_class =
      Weakening ((sub_class, super_class) :: classrels, brand_unique unique x);
    fun type_constructor (tyco, _) dss class =
      Weakening ([], Global ((tyco, class), (map o map) fst dss));
    fun type_variable (TFree (v, sort)) =
      let
        val sort' = proj_sort sort;
      in map_index (fn (n, class) => (Weakening ([], Local
        { var = v, index = n, sort = sort', unique = true }), class)) sort'
      end;
    val typarg_witnesses = Sorts.of_sort_derivation algebra
      {class_relation = fn _ => fn unique =>
         Sorts.classrel_derivation algebra (class_relation unique),
       type_constructor = type_constructor,
       type_variable = type_variable} (ty, proj_sort sort)
      handle Sorts.CLASS_ERROR e => not_wellsorted ctxt permissive some_thm deps ty sort e;
  in (typarg_witnesses, (deps, program)) end;


(* translation *)

fun ensure_tyco ctxt algbr eqngr permissive tyco =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ((vs, cos), _) = Code.get_type thy tyco;
    val stmt_datatype =
      fold_map (translate_tyvar_sort ctxt algbr eqngr permissive) vs
      #>> map fst
      ##>> fold_map (fn (c, (vs, tys)) =>
        ensure_const ctxt algbr eqngr permissive c
        ##>> pair (map (unprefix "'" o fst) vs)
        ##>> fold_map (translate_typ ctxt algbr eqngr permissive) tys) cos
      #>> Datatype;
  in ensure_stmt Type_Constructor stmt_datatype tyco end
and ensure_const ctxt algbr eqngr permissive c =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun stmt_datatypecons tyco =
      ensure_tyco ctxt algbr eqngr permissive tyco
      #>> Datatypecons;
    fun stmt_classparam class =
      ensure_class ctxt algbr eqngr permissive class
      #>> Classparam;
    fun stmt_fun cert = case Code.equations_of_cert thy cert
     of (_, NONE) => pair NoStmt
      | ((vs, ty), SOME eqns) =>
          let
            val eqns' = annotate_eqns ctxt algbr eqngr (c, ty) eqns
            val some_case_cong = Code.get_case_cong thy c;
          in
            fold_map (translate_tyvar_sort ctxt algbr eqngr permissive) vs
            ##>> translate_typ ctxt algbr eqngr permissive ty
            ##>> translate_eqns ctxt algbr eqngr permissive eqns'
            #>>
             (fn (_, NONE) => NoStmt
               | (tyscm, SOME eqns) => Fun ((tyscm, eqns), some_case_cong))
          end;
    val stmt_const = case Code.get_type_of_constr_or_abstr thy c
     of SOME (tyco, _) => stmt_datatypecons tyco
      | NONE => (case Axclass.class_of_param thy c
         of SOME class => stmt_classparam class
          | NONE => stmt_fun (Code_Preproc.cert eqngr c))
  in ensure_stmt Constant stmt_const c end
and ensure_class ctxt (algbr as (_, algebra)) eqngr permissive class =
  let
    val thy = Proof_Context.theory_of ctxt;
    val super_classes = (Sorts.minimize_sort algebra o Sorts.super_classes algebra) class;
    val cs = #params (Axclass.get_info thy class);
    val stmt_class =
      fold_map (fn super_class =>
        ensure_classrel ctxt algbr eqngr permissive (class, super_class)) super_classes
      ##>> fold_map (fn (c, ty) => ensure_const ctxt algbr eqngr permissive c
        ##>> translate_typ ctxt algbr eqngr permissive ty) cs
      #>> (fn info => Class (unprefix "'" Name.aT, info))
  in ensure_stmt Type_Class stmt_class class end
and ensure_classrel ctxt algbr eqngr permissive (sub_class, super_class) =
  let
    val stmt_classrel =
      ensure_class ctxt algbr eqngr permissive sub_class
      ##>> ensure_class ctxt algbr eqngr permissive super_class
      #>> Classrel;
  in ensure_stmt Class_Relation stmt_classrel (sub_class, super_class) end
and ensure_inst ctxt (algbr as (_, algebra)) eqngr permissive (tyco, class) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val super_classes = (Sorts.minimize_sort algebra o Sorts.super_classes algebra) class;
    val these_class_params = these o try (#params o Axclass.get_info thy);
    val class_params = these_class_params class;
    val superclass_params = maps these_class_params
      ((Sorts.complete_sort algebra o Sorts.super_classes algebra) class);
    val vs = Name.invent_names Name.context "'a" (Sorts.mg_domain algebra tyco [class]);
    val sorts' = Sorts.mg_domain (Sign.classes_of thy) tyco [class];
    val vs' = map2 (fn (v, sort1) => fn sort2 => (v,
      Sorts.inter_sort (Sign.classes_of thy) (sort1, sort2))) vs sorts';
    val arity_typ = Type (tyco, map TFree vs);
    val arity_typ' = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort)) vs');
    fun translate_super_instance super_class =
      ensure_class ctxt algbr eqngr permissive super_class
      ##>> translate_dicts ctxt algbr eqngr permissive NONE (arity_typ, [super_class])
      #>> (fn (super_class, [Dict ([], Dict_Const (_, dss))]) => (super_class, dss));
    fun translate_classparam_instance (c, ty) =
      let
        val raw_const = Const (c, map_type_tfree (K arity_typ') ty);
        val dom_length = length (fst (strip_type ty))
        val thm = Axclass.unoverload_conv ctxt (Thm.cterm_of ctxt raw_const);
        val const = (apsnd Logic.unvarifyT_global o dest_Const o snd
          o Logic.dest_equals o Thm.prop_of) thm;
      in
        ensure_const ctxt algbr eqngr permissive c
        ##>> translate_const ctxt algbr eqngr permissive (SOME thm) (const, NONE)
        #>> (fn (c, IConst const') => ((c, (const', dom_length)), (thm, true)))
      end;
    val stmt_inst =
      ensure_class ctxt algbr eqngr permissive class
      ##>> ensure_tyco ctxt algbr eqngr permissive tyco
      ##>> fold_map (translate_tyvar_sort ctxt algbr eqngr permissive) vs
      ##>> fold_map translate_super_instance super_classes
      ##>> fold_map translate_classparam_instance class_params
      ##>> fold_map translate_classparam_instance superclass_params
      #>> (fn (((((class, tyco), vs), superinsts), inst_params), superinst_params) =>
          Classinst { class = class, tyco = tyco, vs = vs,
            superinsts = superinsts, inst_params = inst_params, superinst_params = superinst_params });
  in ensure_stmt Class_Instance stmt_inst (tyco, class) end
and translate_typ ctxt algbr eqngr permissive (TFree (v, _)) =
      pair (ITyVar (unprefix "'" v))
  | translate_typ ctxt algbr eqngr permissive (Type (tyco, tys)) =
      ensure_tyco ctxt algbr eqngr permissive tyco
      ##>> fold_map (translate_typ ctxt algbr eqngr permissive) tys
      #>> (fn (tyco, tys) => tyco `%% tys)
and translate_term ctxt algbr eqngr permissive some_thm (Const (c, ty), some_abs) =
      translate_app ctxt algbr eqngr permissive some_thm (((c, ty), []), some_abs)
  | translate_term ctxt algbr eqngr permissive some_thm (Free (v, _), some_abs) =
      pair (IVar (SOME v))
  | translate_term ctxt algbr eqngr permissive some_thm (Abs (v, ty, t), some_abs) =
      let
        val (v', t') = Syntax_Trans.variant_abs (Name.desymbolize (SOME false) v, ty, t);
        val v'' = if member (op =) (Term.add_free_names t' []) v'
          then SOME v' else NONE
      in
        translate_typ ctxt algbr eqngr permissive ty
        ##>> translate_term ctxt algbr eqngr permissive some_thm (t', some_abs)
        #>> (fn (ty, t) => (v'', ty) `|=> t)
      end
  | translate_term ctxt algbr eqngr permissive some_thm (t as _ $ _, some_abs) =
      case strip_comb t
       of (Const (c, ty), ts) =>
            translate_app ctxt algbr eqngr permissive some_thm (((c, ty), ts), some_abs)
        | (t', ts) =>
            translate_term ctxt algbr eqngr permissive some_thm (t', some_abs)
            ##>> fold_map (translate_term ctxt algbr eqngr permissive some_thm o rpair NONE) ts
            #>> (fn (t, ts) => t `$$ ts)
and translate_eqn ctxt algbr eqngr permissive ((args, (rhs, some_abs)), (some_thm, proper)) =
  fold_map (translate_term ctxt algbr eqngr permissive some_thm) args
  ##>> translate_term ctxt algbr eqngr permissive some_thm (rhs, some_abs)
  #>> rpair (some_thm, proper)
and translate_eqns ctxt algbr eqngr permissive eqns =
  maybe_permissive (fold_map (translate_eqn ctxt algbr eqngr permissive) eqns)
and translate_const ctxt algbr eqngr permissive some_thm ((c, ty), some_abs) (deps, program) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val _ = if (case some_abs of NONE => true | SOME abs => not (c = abs))
        andalso Code.is_abstr thy c
        then translation_error ctxt permissive some_thm deps
          "Abstraction violation" ("constant " ^ Code.string_of_const thy c)
      else ()
  in translate_const_proper ctxt algbr eqngr permissive some_thm (c, ty) (deps, program) end
and translate_const_proper ctxt algbr eqngr permissive some_thm (c, ty) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (annotate, ty') = dest_tagged_type ty;
    val typargs = Sign.const_typargs thy (c, ty');
    val sorts = Code_Preproc.sortargs eqngr c;
    val (dom, range) = Term.strip_type ty';
  in
    ensure_const ctxt algbr eqngr permissive c
    ##>> fold_map (translate_typ ctxt algbr eqngr permissive) typargs
    ##>> fold_map (translate_dicts ctxt algbr eqngr permissive some_thm) (typargs ~~ sorts)
    ##>> fold_map (translate_typ ctxt algbr eqngr permissive) (ty' :: dom)
    #>> (fn (((c, typargs), dss), annotation :: dom) =>
      IConst { sym = Constant c, typargs = typargs, dicts = dss,
        dom = dom, annotation =
          if annotate then SOME annotation else NONE })
  end
and translate_app_const ctxt algbr eqngr permissive some_thm ((c_ty, ts), some_abs) =
  translate_const ctxt algbr eqngr permissive some_thm (c_ty, some_abs)
  ##>> fold_map (translate_term ctxt algbr eqngr permissive some_thm o rpair NONE) ts
  #>> (fn (t, ts) => t `$$ ts)
and translate_case ctxt algbr eqngr permissive some_thm (num_args, (t_pos, case_pats)) (c_ty, ts) =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun arg_types num_args ty = fst (chop num_args (binder_types ty));
    val tys = arg_types num_args (snd c_ty);
    val ty = nth tys t_pos;
    fun mk_constr NONE t = NONE
      | mk_constr (SOME c) t =
          let
            val n = Code.args_number thy c;
          in SOME ((c, arg_types n (fastype_of (untag_term t)) ---> ty), n) end;
    val constrs =
      if null case_pats then []
      else map_filter I (map2 mk_constr case_pats (nth_drop t_pos ts));
    fun disjunctive_varnames ts =
      let
        val vs = (fold o fold_varnames) (insert (op =)) ts [];
      in fn pat => null (inter (op =) vs (fold_varnames (insert (op =)) pat [])) end;
    fun purge_unused_vars_in t =
      let
        val vs = fold_varnames (insert (op =)) t [];
      in
        map_terms_bottom_up (fn IVar (SOME v) =>
          IVar (if member (op =) vs v then SOME v else NONE) | t => t)
      end;
    fun collapse_clause vs_map ts body =
      case body
       of IConst { sym = Constant c, ... } => if Code.is_undefined thy c
            then []
            else [(ts, body)]
        | ICase { term = IVar (SOME v), clauses = clauses, ... } =>
            if forall (fn (pat', body') => exists_var pat' v
              orelse not (exists_var body' v)) clauses
              andalso forall (disjunctive_varnames ts o fst) clauses
            then case AList.lookup (op =) vs_map v
             of SOME i => maps (fn (pat', body') =>
                  collapse_clause (AList.delete (op =) v vs_map)
                    (nth_map i (K pat') ts |> map (purge_unused_vars_in body')) body') clauses
              | NONE => [(ts, body)]
            else [(ts, body)]
        | _ => [(ts, body)];
    fun mk_clause mk tys t =
      let
        val (vs, body) = unfold_abs_eta tys t;
        val vs_map = fold_index (fn (i, (SOME v, _)) => cons (v, i) | _ => I) vs [];
        val ts = map (IVar o fst) vs;
      in map mk (collapse_clause vs_map ts body) end;
    fun casify constrs ty t_app ts =
      let
        val t = nth ts t_pos;
        val ts_clause = nth_drop t_pos ts;
        val clauses = if null case_pats
          then mk_clause (fn ([t], body) => (t, body)) [ty] (the_single ts_clause)
          else maps (fn ((constr as IConst { dom = tys, ... }, n), t) =>
            mk_clause (fn (ts, body) => (constr `$$ ts, body)) (take n tys) t)
              (constrs ~~ (map_filter (fn (NONE, _) => NONE | (SOME _, t) => SOME t)
                (case_pats ~~ ts_clause)));
      in ICase { term = t, typ = ty, clauses = clauses, primitive = t_app `$$ ts } end;
  in
    translate_const ctxt algbr eqngr permissive some_thm (c_ty, NONE)
    ##>> fold_map (fn (constr, n) => translate_const ctxt algbr eqngr permissive some_thm (constr, NONE)
      #>> rpair n) constrs
    ##>> translate_typ ctxt algbr eqngr permissive ty
    ##>> fold_map (translate_term ctxt algbr eqngr permissive some_thm o rpair NONE) ts
    #>> (fn (((t, constrs), ty), ts) =>
      casify constrs ty t ts)
  end
and translate_app_case ctxt algbr eqngr permissive some_thm (case_schema as (num_args, _)) ((c, ty), ts) =
  if length ts < num_args then
    let
      val k = length ts;
      val tys = (take (num_args - k) o drop k o fst o strip_type) ty;
      val names = Name.build_context (ts |> (fold o fold_aterms) Term.declare_term_frees);
      val vs = Name.invent_names names "a" tys;
    in
      fold_map (translate_typ ctxt algbr eqngr permissive) tys
      ##>> translate_case ctxt algbr eqngr permissive some_thm case_schema ((c, ty), ts @ map Free vs)
      #>> (fn (tys, t) => map2 (fn (v, _) => pair (SOME v)) vs tys `|==> t)
    end
  else if length ts > num_args then
    translate_case ctxt algbr eqngr permissive some_thm case_schema ((c, ty), take num_args ts)
    ##>> fold_map (translate_term ctxt algbr eqngr permissive some_thm o rpair NONE) (drop num_args ts)
    #>> (fn (t, ts) => t `$$ ts)
  else
    translate_case ctxt algbr eqngr permissive some_thm case_schema ((c, ty), ts)
and translate_app ctxt algbr eqngr permissive some_thm (c_ty_ts as ((c, _), _), some_abs) =
  case Code.get_case_schema (Proof_Context.theory_of ctxt) c
   of SOME case_schema => translate_app_case ctxt algbr eqngr permissive some_thm case_schema c_ty_ts
    | NONE => translate_app_const ctxt algbr eqngr permissive some_thm (c_ty_ts, some_abs)
and translate_tyvar_sort ctxt (algbr as (proj_sort, _)) eqngr permissive (v, sort) =
  fold_map (ensure_class ctxt algbr eqngr permissive) (proj_sort sort)
  #>> (fn sort => (unprefix "'" v, sort))
and translate_dicts ctxt algbr eqngr permissive some_thm (ty, sort) =
  let
    fun mk_dict (Weakening (classrels, d)) =
          fold_map (ensure_classrel ctxt algbr eqngr permissive) classrels
          ##>> mk_plain_dict d
          #>> Dict 
    and mk_plain_dict (Global (inst, dss)) =
          ensure_inst ctxt algbr eqngr permissive inst
          ##>> (fold_map o fold_map) mk_dict dss
          #>> Dict_Const
      | mk_plain_dict (Local { var, index, sort, unique }) =
          ensure_class ctxt algbr eqngr permissive (nth sort index)
          #>> (fn class => Dict_Var { var = unprefix "'" var, index = index,
            length = length sort, class = class, unique = unique })
  in
    construct_dictionaries ctxt algbr permissive some_thm (ty, sort)
    #-> (fn typarg_witnesses => fold_map mk_dict typarg_witnesses)
  end;


(* store *)

structure Program = Code_Data
(
  type T = program;
  val empty = Code_Symbol.Graph.empty;
);

fun invoke_generation ignore_cache ctxt generate thing =
  Program.change_yield
    (if ignore_cache then NONE else SOME (Proof_Context.theory_of ctxt))
    (fn program => ([], program)
      |> generate thing
      |-> (fn thing => fn (_, program) => (thing, program)));


(* program generation *)

fun check_abstract_constructors thy consts =
  case filter (Code.is_abstr thy) consts of
    [] => ()
  | abstrs => error ("Cannot export abstract constructor(s): "
      ^ commas (map (Code.string_of_const thy) abstrs));

fun invoke_generation_for_consts ctxt { ignore_cache, permissive } { algebra, eqngr } consts =
  let
    val thy = Proof_Context.theory_of ctxt;
    val _ = if permissive then ()
      else check_abstract_constructors thy consts;
  in
    Code_Preproc.timed "translating program" #ctxt
    (fn { ctxt, algebra, eqngr, consts } => invoke_generation ignore_cache ctxt
      (fold_map (ensure_const ctxt algebra eqngr permissive)) consts)
      { ctxt = ctxt, algebra = algebra, eqngr = eqngr, consts = consts }
  end;

fun invoke_generation_for_consts' ctxt ignore_cache_and_permissive consts =
  invoke_generation_for_consts ctxt
    { ignore_cache = ignore_cache_and_permissive, permissive = ignore_cache_and_permissive }
    (Code_Preproc.obtain ignore_cache_and_permissive
      { ctxt = ctxt, consts = consts, terms = []}) consts
  |> snd;

fun invoke_generation_for_consts'' ctxt algebra_eqngr =
  invoke_generation_for_consts ctxt
    { ignore_cache = true, permissive = false }
    algebra_eqngr
  #> (fn (deps, program) => { deps = deps, program = program });

fun consts_program_permissive ctxt =
  invoke_generation_for_consts' ctxt true;

fun consts_program ctxt consts =
  let
    fun project program = Code_Symbol.Graph.restrict
      (member (op =) (Code_Symbol.Graph.all_succs program
        (map Constant consts))) program;
  in
    invoke_generation_for_consts' ctxt false consts
    |> project
  end;


(* value evaluation *)

fun ensure_value ctxt algbr eqngr t =
  let
    val ty = fastype_of t;
    val vs = fold_term_types (K (fold_atyps (insert (eq_fst op =)
      o dest_TFree))) t [];
    val t' = annotate ctxt algbr eqngr (\<^const_name>\<open>Pure.dummy_pattern\<close>, ty) [] t;
    val dummy_constant = Constant \<^const_name>\<open>Pure.dummy_pattern\<close>;
    val stmt_value =
      fold_map (translate_tyvar_sort ctxt algbr eqngr false) vs
      ##>> translate_typ ctxt algbr eqngr false ty
      ##>> translate_term ctxt algbr eqngr false NONE (t', NONE)
      #>> (fn ((vs, ty), t) => Fun
        (((vs, ty), [(([], t), (NONE, true))]), NONE));
    fun term_value (_, program1) =
      let
        val Fun ((vs_ty, [(([], t), _)]), _) =
          Code_Symbol.Graph.get_node program1 dummy_constant;
        val deps' = Code_Symbol.Graph.immediate_succs program1 dummy_constant;
        val program2 = Code_Symbol.Graph.del_node dummy_constant program1;
        val deps_all = Code_Symbol.Graph.all_succs program2 deps';
        val program3 = Code_Symbol.Graph.restrict (member (op =) deps_all) program2;
       in ((program3, ((vs_ty, t), deps')), (deps', program2)) end;
  in
    ensure_stmt Constant stmt_value \<^const_name>\<open>Pure.dummy_pattern\<close>
    #> snd
    #> term_value
  end;

fun dynamic_evaluation comp ctxt algebra eqngr t =
  let
    val ((program, (vs_ty_t', deps)), _) =
      Code_Preproc.timed "translating term" #ctxt
      (fn { ctxt, algebra, eqngr, t } =>
        invoke_generation false ctxt (ensure_value ctxt algebra eqngr) t)
        { ctxt = ctxt, algebra = algebra, eqngr = eqngr, t = t };
  in comp program t vs_ty_t' deps end;

fun dynamic_conv ctxt conv =
  Code_Preproc.dynamic_conv ctxt
    (dynamic_evaluation (fn program => fn _ => conv program) ctxt);

fun dynamic_value ctxt postproc comp =
  Code_Preproc.dynamic_value ctxt postproc
    (dynamic_evaluation comp ctxt);

fun static_evaluation ctxt consts algebra_eqngr static_eval =
  static_eval (invoke_generation_for_consts'' ctxt algebra_eqngr consts);

fun static_evaluation_thingol ctxt consts (algebra_eqngr as { algebra, eqngr }) static_eval =
  let
    fun evaluation program dynamic_eval ctxt t =
      let
        val ((_, ((vs_ty', t'), deps)), _) =
          Code_Preproc.timed "translating term" #ctxt
          (fn { ctxt, t } =>
            ensure_value ctxt algebra eqngr t ([], program))
            { ctxt = ctxt, t = t };
      in dynamic_eval ctxt t (vs_ty', t') deps end;
  in
    static_evaluation ctxt consts algebra_eqngr (fn program_deps =>
      evaluation (#program program_deps) (static_eval program_deps))
  end;

fun static_evaluation_isa ctxt consts algebra_eqngr static_eval =
  static_evaluation ctxt consts algebra_eqngr (fn program_deps =>
    (static_eval (#program program_deps)));

fun static_conv_thingol (ctxt_consts as { ctxt, consts }) conv =
  Code_Preproc.static_conv ctxt_consts (fn algebra_eqngr =>
    static_evaluation_thingol ctxt consts algebra_eqngr
      (fn program_deps =>
        let
          val static_conv = conv program_deps;
        in 
          fn ctxt => fn _ => fn vs_ty => fn deps => static_conv ctxt vs_ty deps
        end));

fun static_conv_isa (ctxt_consts as { ctxt, consts }) conv =
  Code_Preproc.static_conv ctxt_consts (fn algebra_eqngr =>
    static_evaluation_isa ctxt consts algebra_eqngr conv);

fun static_value (ctxt_postproc_consts as { ctxt, consts, ... }) comp =
  Code_Preproc.static_value ctxt_postproc_consts (fn algebra_eqngr =>
    static_evaluation_thingol ctxt consts algebra_eqngr comp);


(** constant expressions **)

fun read_const_exprs_internal ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun this_theory name =
      if Context.theory_name thy = name then thy
      else Context.get_theory {long = false} thy name;

    fun consts_of thy' =
      fold (fn (c, (_, NONE)) => cons c | _ => I)
        (#constants (Consts.dest (Sign.consts_of thy'))) []
      |> filter_out (Code.is_abstr thy);
    fun belongs_here thy' c = forall
      (fn thy'' => not (Sign.declared_const thy'' c)) (Theory.parents_of thy');
    fun consts_of_select thy' = filter (belongs_here thy') (consts_of thy');
    fun read_const_expr str =
      (case Syntax.parse_input ctxt (K NONE) (K Markup.empty) (SOME o Symbol_Pos.implode o #1) str of
        SOME "_" => ([], consts_of thy)
      | SOME s =>
          (case try (unsuffix "._") s of
            SOME name => ([], consts_of_select (this_theory name))
          | NONE => ([Code.read_const thy str], []))
      | NONE => ([Code.read_const thy str], []));
  in apply2 flat o split_list o map read_const_expr end;

fun read_const_exprs_all ctxt = op @ o read_const_exprs_internal ctxt;

fun read_const_exprs ctxt const_exprs =
  let
    val (consts, consts_permissive) =
      read_const_exprs_internal ctxt const_exprs;
    val consts' = 
      consts_program_permissive ctxt consts_permissive
      |> implemented_deps
      |> filter_out (Code.is_abstr (Proof_Context.theory_of ctxt));
  in union (op =) consts' consts end;


(** diagnostic commands **)

fun code_depgr ctxt consts =
  let
    val { eqngr, ... } = Code_Preproc.obtain true
      { ctxt = ctxt, consts = consts, terms = [] };
    val all_consts = Graph.all_succs eqngr consts;
  in Graph.restrict (member (op =) all_consts) eqngr end;

fun code_thms ctxt = Pretty.writeln o Code_Preproc.pretty ctxt o code_depgr ctxt;

fun coalesce_strong_conn gr =
  let
    val xss = Graph.strong_conn gr;
    val xss_ys = map (fn xs => (xs, commas xs)) xss;
    val y_for = the o AList.lookup (op =) (maps (fn (xs, y) => map (fn x => (x, y)) xs) xss_ys);
    fun coalesced_succs_for xs = maps (Graph.immediate_succs gr) xs
      |> subtract (op =) xs
      |> map y_for
      |> distinct (op =);
    val succs = map (fn (xs, _) => (xs, coalesced_succs_for xs)) xss_ys;
  in
    map (fn (xs, y) => ((y, xs), (maps (Graph.get_node gr) xs, (the o AList.lookup (op =) succs) xs))) xss_ys
  end;

fun code_deps ctxt consts =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun mk_entry ((name, consts), (ps, deps)) =
      let
        val label = commas (map (Code.string_of_const thy) consts);
      in ((name, Graph_Display.content_node label (Pretty.str label :: ps)), deps) end;
  in
    code_depgr ctxt consts
    |> Graph.map (K (Code.pretty_cert thy o snd))
    |> coalesce_strong_conn
    |> map mk_entry
    |> Graph_Display.display_graph
  end;

local

fun code_thms_cmd ctxt = code_thms ctxt o read_const_exprs_all ctxt;
fun code_deps_cmd ctxt = code_deps ctxt o read_const_exprs_all ctxt;

in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_thms\<close>
    "print system of code equations for code"
    (Scan.repeat1 Parse.term >> (fn cs =>
      Toplevel.keep (fn st => code_thms_cmd (Toplevel.context_of st) cs)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_deps\<close>
    "visualize dependencies of code equations for code"
    (Scan.repeat1 Parse.term >> (fn cs =>
      Toplevel.keep (fn st => code_deps_cmd (Toplevel.context_of st) cs)));

end;

end; (*struct*)


structure Basic_Code_Thingol: BASIC_CODE_THINGOL = Code_Thingol;
