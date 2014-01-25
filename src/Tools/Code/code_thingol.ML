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
    | Dict_Var of vname * (int * int);
  datatype itype =
      `%% of string * itype list
    | ITyVar of vname;
  type const = { sym: Code_Symbol.symbol, typargs: itype list, dicts: dict list list,
    dom: itype list, range: itype, annotate: bool };
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
  val unfold_let: iterm -> ((iterm * itype) * iterm) list * iterm
  val split_pat_abs: iterm -> ((iterm * itype) * iterm) option
  val unfold_pat_abs: iterm -> (iterm * itype) list * iterm
  val unfold_const_app: iterm -> (const * iterm list) option
  val is_IVar: iterm -> bool
  val is_IAbs: iterm -> bool
  val eta_expand: int -> const * iterm list -> iterm
  val contains_dict_var: iterm -> bool
  val add_constsyms: iterm -> Code_Symbol.symbol list -> Code_Symbol.symbol list
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
  val is_constr: program -> Code_Symbol.symbol -> bool
  val is_case: stmt -> bool
  val group_stmts: theory -> program
    -> ((Code_Symbol.symbol * stmt) list * (Code_Symbol.symbol * stmt) list
      * ((Code_Symbol.symbol * stmt) list * (Code_Symbol.symbol * stmt) list)) list

  val read_const_exprs: theory -> string list -> string list * string list
  val consts_program: theory -> bool -> string list -> program
  val dynamic_conv: theory -> (program
    -> ((string * sort) list * typscheme) * iterm -> Code_Symbol.symbol list -> conv)
    -> conv
  val dynamic_value: theory -> ((term -> term) -> 'a -> 'a) -> (program
    -> ((string * sort) list * typscheme) * iterm -> Code_Symbol.symbol list -> 'a)
    -> term -> 'a
  val static_conv: theory -> string list -> (program -> string list
    -> ((string * sort) list * typscheme) * iterm -> Code_Symbol.symbol list -> conv)
    -> conv
  val static_conv_simple: theory -> string list
    -> (program -> (string * sort) list -> term -> conv) -> conv
  val static_value: theory -> ((term -> term) -> 'a -> 'a) -> string list ->
    (program -> string list
      -> ((string * sort) list * typscheme) * iterm -> Code_Symbol.symbol list -> 'a)
    -> term -> 'a
end;

structure Code_Thingol: CODE_THINGOL =
struct

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
  | Dict_Var of vname * (int * int);

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

type const = { sym: Code_Symbol.symbol, typargs: itype list, dicts: dict list list,
  dom: itype list, range: itype, annotate: bool };

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

val unfold_let = unfoldr split_let;

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
    fun fold_aux add f =
      let
        fun fold_term _ (IConst _) = I
          | fold_term vs (IVar (SOME v)) = if member (op =) vs v then I else f v
          | fold_term _ (IVar NONE) = I
          | fold_term vs (t1 `$ t2) = fold_term vs t1 #> fold_term vs t2
          | fold_term vs ((SOME v, _) `|=> t) = fold_term (insert (op =) v vs) t
          | fold_term vs ((NONE, _) `|=> t) = fold_term vs t
          | fold_term vs (ICase { term = t, clauses = clauses, ... }) = fold_term vs t #> fold (fold_case vs) clauses
        and fold_case vs (p, t) = fold_term (add p vs) t;
      in fold_term [] end;
    fun add t = fold_aux add (insert (op =)) t;
  in fold_aux add f end;

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

fun contains_dict_var t =
  let
    fun cont_dict (Dict (_, d)) = cont_plain_dict d
    and cont_plain_dict (Dict_Const (_, dss)) = (exists o exists) cont_dict dss
      | cont_plain_dict (Dict_Var _) = true;
    fun cont_term (IConst { dicts = dss, ... }) = (exists o exists) cont_dict dss
      | cont_term (IVar _) = false
      | cont_term (t1 `$ t2) = cont_term t1 orelse cont_term t2
      | cont_term (_ `|=> t) = cont_term t
      | cont_term (ICase { primitive = t, ... }) = cont_term t;
  in cont_term t end;


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
  Code_Symbol.Graph.fold (fn (Code_Symbol.Constant c, (NoStmt, _)) => cons c | _ => I) program [];

fun implemented_deps program =
  Code_Symbol.Graph.keys program
  |> subtract (op =) (Code_Symbol.Graph.all_preds program (map Code_Symbol.Constant (unimplemented program)))
  |> map_filter (fn Code_Symbol.Constant c => SOME c | _ => NONE);

fun map_terms_bottom_up f (t as IConst _) = f t
  | map_terms_bottom_up f (t as IVar _) = f t
  | map_terms_bottom_up f (t1 `$ t2) = f
      (map_terms_bottom_up f t1 `$ map_terms_bottom_up f t2)
  | map_terms_bottom_up f ((v, ty) `|=> t) = f
      ((v, ty) `|=> map_terms_bottom_up f t)
  | map_terms_bottom_up f (ICase { term = t, typ = ty, clauses = clauses, primitive = t0 }) = f
      (ICase { term = map_terms_bottom_up f t, typ = ty,
        clauses = (map o pairself) (map_terms_bottom_up f) clauses,
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

fun group_stmts thy program =
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
        o map (Code_Symbol.quote (Proof_Context.init_global thy)
        o fst)) stmts);
  in
    linear_stmts program
    |> map group
  end;


(** translation kernel **)

(* generic mechanisms *)

fun ensure_stmt symbolize generate x (dep, program) =
  let
    val sym = symbolize x;
    val add_dep = case dep of NONE => I
      | SOME dep => Code_Symbol.Graph.add_edge (dep, sym);
  in
    if can (Code_Symbol.Graph.get_node program) sym
    then
      program
      |> add_dep
      |> pair dep
      |> pair x
    else
      program
      |> Code_Symbol.Graph.default_node (sym, NoStmt)
      |> add_dep
      |> curry generate (SOME sym)
      ||> snd
      |-> (fn stmt => (Code_Symbol.Graph.map_node sym) (K stmt))
      |> pair dep
      |> pair x
  end;

exception PERMISSIVE of unit;

fun translation_error thy permissive some_thm msg sub_msg =
  if permissive
  then raise PERMISSIVE ()
  else
    let
      val err_thm =
        (case some_thm of
          SOME thm => "\n(in code equation " ^ Display.string_of_thm_global thy thm ^ ")"
        | NONE => "");
    in error (msg ^ err_thm ^ ":\n" ^ sub_msg) end;

fun maybe_permissive f prgrm =
  f prgrm |>> SOME handle PERMISSIVE () => (NONE, prgrm);

fun not_wellsorted thy permissive some_thm ty sort e =
  let
    val err_class = Sorts.class_error (Context.pretty_global thy) e;
    val err_typ =
      "Type " ^ Syntax.string_of_typ_global thy ty ^ " not of sort " ^
        Syntax.string_of_sort_global thy sort;
  in
    translation_error thy permissive some_thm "Wellsortedness error"
      (err_typ ^ "\n" ^ err_class)
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
  in
    tag
  end

fun annotate thy algbr eqngr (c, ty) args rhs =
  let
    val ctxt = Proof_Context.init_global thy |> Config.put Type_Infer_Context.const_sorts false
    val erase = map_types (fn _ => Type_Infer.anyT [])
    val reinfer = singleton (Type_Infer_Context.infer_types ctxt)
    val lhs = list_comb (Const (c, ty), map (map_types Type.strip_sorts o fst) args)
    val reinferred_rhs = snd (Logic.dest_equals (reinfer (Logic.mk_equals (lhs, erase rhs))))
  in
    tag_term algbr eqngr reinferred_rhs rhs
  end

fun annotate_eqns thy algbr eqngr (c, ty) eqns = 
  map (apfst (fn (args, (rhs, some_abs)) => (args,
    (annotate thy algbr eqngr (c, ty) args rhs, some_abs)))) eqns


(* translation *)

fun ensure_tyco thy algbr eqngr permissive tyco =
  let
    val ((vs, cos), _) = Code.get_type thy tyco;
    val stmt_datatype =
      fold_map (translate_tyvar_sort thy algbr eqngr permissive) vs
      #>> map fst
      ##>> fold_map (fn (c, (vs, tys)) =>
        ensure_const thy algbr eqngr permissive c
        ##>> pair (map (unprefix "'" o fst) vs)
        ##>> fold_map (translate_typ thy algbr eqngr permissive) tys) cos
      #>> Datatype;
  in ensure_stmt Code_Symbol.Type_Constructor stmt_datatype tyco end
and ensure_const thy algbr eqngr permissive c =
  let
    fun stmt_datatypecons tyco =
      ensure_tyco thy algbr eqngr permissive tyco
      #>> Datatypecons;
    fun stmt_classparam class =
      ensure_class thy algbr eqngr permissive class
      #>> Classparam;
    fun stmt_fun cert = case Code.equations_of_cert thy cert
     of (_, NONE) => pair NoStmt
      | ((vs, ty), SOME eqns) =>
          let
            val eqns' = annotate_eqns thy algbr eqngr (c, ty) eqns
            val some_case_cong = Code.get_case_cong thy c;
          in
            fold_map (translate_tyvar_sort thy algbr eqngr permissive) vs
            ##>> translate_typ thy algbr eqngr permissive ty
            ##>> translate_eqns thy algbr eqngr permissive eqns'
            #>>
             (fn (_, NONE) => NoStmt
               | (tyscm, SOME eqns) => Fun ((tyscm, eqns), some_case_cong))
          end;
    val stmt_const = case Code.get_type_of_constr_or_abstr thy c
     of SOME (tyco, _) => stmt_datatypecons tyco
      | NONE => (case Axclass.class_of_param thy c
         of SOME class => stmt_classparam class
          | NONE => stmt_fun (Code_Preproc.cert eqngr c))
  in ensure_stmt Code_Symbol.Constant stmt_const c end
and ensure_class thy (algbr as (_, algebra)) eqngr permissive class =
  let
    val super_classes = (Sorts.minimize_sort algebra o Sorts.super_classes algebra) class;
    val cs = #params (Axclass.get_info thy class);
    val stmt_class =
      fold_map (fn super_class =>
        ensure_classrel thy algbr eqngr permissive (class, super_class)) super_classes
      ##>> fold_map (fn (c, ty) => ensure_const thy algbr eqngr permissive c
        ##>> translate_typ thy algbr eqngr permissive ty) cs
      #>> (fn info => Class (unprefix "'" Name.aT, info))
  in ensure_stmt Code_Symbol.Type_Class stmt_class class end
and ensure_classrel thy algbr eqngr permissive (sub_class, super_class) =
  let
    val stmt_classrel =
      ensure_class thy algbr eqngr permissive sub_class
      ##>> ensure_class thy algbr eqngr permissive super_class
      #>> Classrel;
  in ensure_stmt Code_Symbol.Class_Relation stmt_classrel (sub_class, super_class) end
and ensure_inst thy (algbr as (_, algebra)) eqngr permissive (tyco, class) =
  let
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
      ensure_class thy algbr eqngr permissive super_class
      ##>> translate_dicts thy algbr eqngr permissive NONE (arity_typ, [super_class])
      #>> (fn (super_class, [Dict ([], Dict_Const (_, dss))]) => (super_class, dss));
    fun translate_classparam_instance (c, ty) =
      let
        val raw_const = Const (c, map_type_tfree (K arity_typ') ty);
        val dom_length = length (fst (strip_type ty))
        val thm = Axclass.unoverload_conv thy (Thm.cterm_of thy raw_const);
        val const = (apsnd Logic.unvarifyT_global o dest_Const o snd
          o Logic.dest_equals o Thm.prop_of) thm;
      in
        ensure_const thy algbr eqngr permissive c
        ##>> translate_const thy algbr eqngr permissive (SOME thm) (const, NONE)
        #>> (fn (c, IConst const') => ((c, (const', dom_length)), (thm, true)))
      end;
    val stmt_inst =
      ensure_class thy algbr eqngr permissive class
      ##>> ensure_tyco thy algbr eqngr permissive tyco
      ##>> fold_map (translate_tyvar_sort thy algbr eqngr permissive) vs
      ##>> fold_map translate_super_instance super_classes
      ##>> fold_map translate_classparam_instance class_params
      ##>> fold_map translate_classparam_instance superclass_params
      #>> (fn (((((class, tyco), vs), superinsts), inst_params), superinst_params) =>
          Classinst { class = class, tyco = tyco, vs = vs,
            superinsts = superinsts, inst_params = inst_params, superinst_params = superinst_params });
  in ensure_stmt Code_Symbol.Class_Instance stmt_inst (tyco, class) end
and translate_typ thy algbr eqngr permissive (TFree (v, _)) =
      pair (ITyVar (unprefix "'" v))
  | translate_typ thy algbr eqngr permissive (Type (tyco, tys)) =
      ensure_tyco thy algbr eqngr permissive tyco
      ##>> fold_map (translate_typ thy algbr eqngr permissive) tys
      #>> (fn (tyco, tys) => tyco `%% tys)
and translate_term thy algbr eqngr permissive some_thm (Const (c, ty), some_abs) =
      translate_app thy algbr eqngr permissive some_thm (((c, ty), []), some_abs)
  | translate_term thy algbr eqngr permissive some_thm (Free (v, _), some_abs) =
      pair (IVar (SOME v))
  | translate_term thy algbr eqngr permissive some_thm (Abs (v, ty, t), some_abs) =
      let
        val (v', t') = Syntax_Trans.variant_abs (Name.desymbolize false v, ty, t);
        val v'' = if member (op =) (Term.add_free_names t' []) v'
          then SOME v' else NONE
      in
        translate_typ thy algbr eqngr permissive ty
        ##>> translate_term thy algbr eqngr permissive some_thm (t', some_abs)
        #>> (fn (ty, t) => (v'', ty) `|=> t)
      end
  | translate_term thy algbr eqngr permissive some_thm (t as _ $ _, some_abs) =
      case strip_comb t
       of (Const (c, ty), ts) =>
            translate_app thy algbr eqngr permissive some_thm (((c, ty), ts), some_abs)
        | (t', ts) =>
            translate_term thy algbr eqngr permissive some_thm (t', some_abs)
            ##>> fold_map (translate_term thy algbr eqngr permissive some_thm o rpair NONE) ts
            #>> (fn (t, ts) => t `$$ ts)
and translate_eqn thy algbr eqngr permissive ((args, (rhs, some_abs)), (some_thm, proper)) =
  fold_map (translate_term thy algbr eqngr permissive some_thm) args
  ##>> translate_term thy algbr eqngr permissive some_thm (rhs, some_abs)
  #>> rpair (some_thm, proper)
and translate_eqns thy algbr eqngr permissive eqns =
  maybe_permissive (fold_map (translate_eqn thy algbr eqngr permissive) eqns)
and translate_const thy algbr eqngr permissive some_thm ((c, ty), some_abs) =
  let
    val _ = if (case some_abs of NONE => true | SOME abs => not (c = abs))
        andalso Code.is_abstr thy c
        then translation_error thy permissive some_thm
          "Abstraction violation" ("constant " ^ Code.string_of_const thy c)
      else ()
    val (annotate, ty') = dest_tagged_type ty;
    val typargs = Sign.const_typargs thy (c, ty');
    val sorts = Code_Preproc.sortargs eqngr c;
    val (dom, range) = Term.strip_type ty';
  in
    ensure_const thy algbr eqngr permissive c
    ##>> fold_map (translate_typ thy algbr eqngr permissive) typargs
    ##>> fold_map (translate_dicts thy algbr eqngr permissive some_thm) (typargs ~~ sorts)
    ##>> fold_map (translate_typ thy algbr eqngr permissive) (range :: dom)
    #>> (fn (((c, typargs), dss), range :: dom) =>
      IConst { sym = Code_Symbol.Constant c, typargs = typargs, dicts = dss,
        dom = dom, range = range, annotate = annotate })
  end
and translate_app_const thy algbr eqngr permissive some_thm ((c_ty, ts), some_abs) =
  translate_const thy algbr eqngr permissive some_thm (c_ty, some_abs)
  ##>> fold_map (translate_term thy algbr eqngr permissive some_thm o rpair NONE) ts
  #>> (fn (t, ts) => t `$$ ts)
and translate_case thy algbr eqngr permissive some_thm (num_args, (t_pos, case_pats)) (c_ty, ts) =
  let
    val undefineds = Code.undefineds thy;
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
    fun casify constrs ty t_app ts =
      let
        fun collapse_clause vs_map ts body =
          case body
           of IConst { sym = Code_Symbol.Constant c, ... } => if member (op =) undefineds c
                then []
                else [(ts, body)]
            | ICase { term = IVar (SOME v), clauses = clauses, ... } =>
                if forall (fn (pat', body') => exists_var pat' v
                  orelse not (exists_var body' v)) clauses
                then case AList.lookup (op =) vs_map v
                 of SOME i => maps (fn (pat', body') =>
                      collapse_clause (AList.delete (op =) v vs_map)
                        (nth_map i (K pat') ts) body') clauses
                  | NONE => [(ts, body)]
                else [(ts, body)]
            | _ => [(ts, body)];
        fun mk_clause mk tys t =
          let
            val (vs, body) = unfold_abs_eta tys t;
            val vs_map = fold_index (fn (i, (SOME v, _)) => cons (v, i) | _ => I) vs [];
            val ts = map (IVar o fst) vs;
          in map mk (collapse_clause vs_map ts body) end;
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
    translate_const thy algbr eqngr permissive some_thm (c_ty, NONE)
    ##>> fold_map (fn (constr, n) => translate_const thy algbr eqngr permissive some_thm (constr, NONE)
      #>> rpair n) constrs
    ##>> translate_typ thy algbr eqngr permissive ty
    ##>> fold_map (translate_term thy algbr eqngr permissive some_thm o rpair NONE) ts
    #>> (fn (((t, constrs), ty), ts) =>
      casify constrs ty t ts)
  end
and translate_app_case thy algbr eqngr permissive some_thm (case_scheme as (num_args, _)) ((c, ty), ts) =
  if length ts < num_args then
    let
      val k = length ts;
      val tys = (take (num_args - k) o drop k o fst o strip_type) ty;
      val ctxt = (fold o fold_aterms) Term.declare_term_frees ts Name.context;
      val vs = Name.invent_names ctxt "a" tys;
    in
      fold_map (translate_typ thy algbr eqngr permissive) tys
      ##>> translate_case thy algbr eqngr permissive some_thm case_scheme ((c, ty), ts @ map Free vs)
      #>> (fn (tys, t) => map2 (fn (v, _) => pair (SOME v)) vs tys `|==> t)
    end
  else if length ts > num_args then
    translate_case thy algbr eqngr permissive some_thm case_scheme ((c, ty), take num_args ts)
    ##>> fold_map (translate_term thy algbr eqngr permissive some_thm o rpair NONE) (drop num_args ts)
    #>> (fn (t, ts) => t `$$ ts)
  else
    translate_case thy algbr eqngr permissive some_thm case_scheme ((c, ty), ts)
and translate_app thy algbr eqngr permissive some_thm (c_ty_ts as ((c, _), _), some_abs) =
  case Code.get_case_scheme thy c
   of SOME case_scheme => translate_app_case thy algbr eqngr permissive some_thm case_scheme c_ty_ts
    | NONE => translate_app_const thy algbr eqngr permissive some_thm (c_ty_ts, some_abs)
and translate_tyvar_sort thy (algbr as (proj_sort, _)) eqngr permissive (v, sort) =
  fold_map (ensure_class thy algbr eqngr permissive) (proj_sort sort)
  #>> (fn sort => (unprefix "'" v, sort))
and translate_dicts thy (algbr as (proj_sort, algebra)) eqngr permissive some_thm (ty, sort) =
  let
    datatype typarg_witness =
        Weakening of (class * class) list * plain_typarg_witness
    and plain_typarg_witness =
        Global of (string * class) * typarg_witness list list
      | Local of string * (int * sort);
    fun class_relation ((Weakening (classrels, x)), sub_class) super_class =
      Weakening ((sub_class, super_class) :: classrels, x);
    fun type_constructor (tyco, _) dss class =
      Weakening ([], Global ((tyco, class), (map o map) fst dss));
    fun type_variable (TFree (v, sort)) =
      let
        val sort' = proj_sort sort;
      in map_index (fn (n, class) => (Weakening ([], Local (v, (n, sort'))), class)) sort' end;
    val typarg_witnesses = Sorts.of_sort_derivation algebra
      {class_relation = K (Sorts.classrel_derivation algebra class_relation),
       type_constructor = type_constructor,
       type_variable = type_variable} (ty, proj_sort sort)
      handle Sorts.CLASS_ERROR e => not_wellsorted thy permissive some_thm ty sort e;
    fun mk_dict (Weakening (classrels, x)) =
          fold_map (ensure_classrel thy algbr eqngr permissive) classrels
          ##>> mk_plain_dict x
          #>> Dict 
    and mk_plain_dict (Global (inst, dss)) =
          ensure_inst thy algbr eqngr permissive inst
          ##>> (fold_map o fold_map) mk_dict dss
          #>> (fn (inst, dss) => Dict_Const (inst, dss))
      | mk_plain_dict (Local (v, (n, sort))) =
          pair (Dict_Var (unprefix "'" v, (n, length sort)))
  in fold_map mk_dict typarg_witnesses end;


(* store *)

structure Program = Code_Data
(
  type T = program;
  val empty = Code_Symbol.Graph.empty;
);

fun invoke_generation ignore_cache thy (algebra, eqngr) generate thing =
  Program.change_yield (if ignore_cache then NONE else SOME thy)
    (fn program => (NONE, program)
      |> generate thy algebra eqngr thing
      |-> (fn thing => fn (_, program) => (thing, program)));


(* program generation *)

fun consts_program thy permissive consts =
  let
    fun project program =
      if permissive then program
      else Code_Symbol.Graph.restrict
        (member (op =) (Code_Symbol.Graph.all_succs program
          (map Code_Symbol.Constant consts))) program;
    fun generate_consts thy algebra eqngr =
      fold_map (ensure_const thy algebra eqngr permissive);
  in
    invoke_generation permissive thy (Code_Preproc.obtain false thy consts [])
      generate_consts consts
    |> snd
    |> project
  end;


(* value evaluation *)

fun ensure_value thy algbr eqngr t =
  let
    val ty = fastype_of t;
    val vs = fold_term_types (K (fold_atyps (insert (eq_fst op =)
      o dest_TFree))) t [];
    val t' = annotate thy algbr eqngr (@{const_name dummy_pattern}, ty) [] t;
    val dummy_constant = Code_Symbol.Constant @{const_name dummy_pattern};
    val stmt_value =
      fold_map (translate_tyvar_sort thy algbr eqngr false) vs
      ##>> translate_typ thy algbr eqngr false ty
      ##>> translate_term thy algbr eqngr false NONE (t', NONE)
      #>> (fn ((vs, ty), t) => Fun
        (((vs, ty), [(([], t), (NONE, true))]), NONE));
    fun term_value (dep, program1) =
      let
        val Fun ((vs_ty, [(([], t), _)]), _) =
          Code_Symbol.Graph.get_node program1 dummy_constant;
        val deps = Code_Symbol.Graph.immediate_succs program1 dummy_constant;
        val program2 = Code_Symbol.Graph.del_node dummy_constant program1;
        val deps_all = Code_Symbol.Graph.all_succs program2 deps;
        val program3 = Code_Symbol.Graph.restrict (member (op =) deps_all) program2;
      in ((program3, ((vs_ty, t), deps)), (dep, program2)) end;
  in
    ensure_stmt Code_Symbol.Constant stmt_value @{const_name dummy_pattern}
    #> snd
    #> term_value
  end;

fun original_sorts vs =
  map (fn (v, _) => (v, (the o AList.lookup (op =) vs o prefix "'") v));

fun dynamic_evaluator thy evaluator algebra eqngr vs t =
  let
    val ((program, (((vs', ty'), t'), deps)), _) =
      invoke_generation false thy (algebra, eqngr) ensure_value t;
  in evaluator program ((original_sorts vs vs', (vs', ty')), t') deps end;

fun dynamic_conv thy evaluator =
  Code_Preproc.dynamic_conv thy (dynamic_evaluator thy evaluator);

fun dynamic_value thy postproc evaluator =
  Code_Preproc.dynamic_value thy postproc (dynamic_evaluator thy evaluator);

fun lift_evaluation thy evaluation' algebra eqngr program vs t =
  let
    val ((_, (((vs', ty'), t'), deps)), _) =
      ensure_value thy algebra eqngr t (NONE, program);
  in evaluation' ((original_sorts vs vs', (vs', ty')), t') deps end;

fun lift_evaluator thy evaluator' consts algebra eqngr =
  let
    fun generate_consts thy algebra eqngr =
      fold_map (ensure_const thy algebra eqngr false);
    val (consts', program) =
      invoke_generation true thy (algebra, eqngr) generate_consts consts;
    val evaluation' = evaluator' program consts';
  in lift_evaluation thy evaluation' algebra eqngr program end;

fun lift_evaluator_simple thy evaluator' consts algebra eqngr =
  let
    fun generate_consts thy algebra eqngr =
      fold_map (ensure_const thy algebra eqngr false);
    val (_, program) =
      invoke_generation true thy (algebra, eqngr) generate_consts consts;
  in evaluator' program end;

fun static_conv thy consts conv =
  Code_Preproc.static_conv thy consts (lift_evaluator thy conv consts);

fun static_conv_simple thy consts conv =
  Code_Preproc.static_conv thy consts (lift_evaluator_simple thy conv consts);

fun static_value thy postproc consts evaluator =
  Code_Preproc.static_value thy postproc consts (lift_evaluator thy evaluator consts);


(** diagnostic commands **)

fun read_const_exprs thy =
  let
    fun consts_of thy' = Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
      ((snd o #constants o Consts.dest o Sign.consts_of) thy') [];
    fun belongs_here thy' c = forall
      (fn thy'' => not (Sign.declared_const thy'' c)) (Theory.parents_of thy');
    fun consts_of_select thy' = filter (belongs_here thy') (consts_of thy');

    val ctxt = Proof_Context.init_global thy;
    fun read_const_expr str =
      (case Syntax.parse_token ctxt (K NONE) Markup.empty (SOME o Symbol_Pos.implode o #1) str of
        SOME "_" => ([], consts_of thy)
      | SOME s =>
          if String.isSuffix "._" s
          then ([], consts_of_select (Context.this_theory thy (unsuffix "._" s)))
          else ([Code.read_const thy str], [])
      | NONE => ([Code.read_const thy str], []));
  in pairself flat o split_list o map read_const_expr end;

fun code_depgr thy consts =
  let
    val (_, eqngr) = Code_Preproc.obtain true thy consts [];
    val all_consts = Graph.all_succs eqngr consts;
  in Graph.restrict (member (op =) all_consts) eqngr end;

fun code_thms thy = Pretty.writeln o Code_Preproc.pretty thy o code_depgr thy;

fun code_deps thy consts =
  let
    val eqngr = code_depgr thy consts;
    val constss = Graph.strong_conn eqngr;
    val mapping = Symtab.empty |> fold (fn consts => fold (fn const =>
      Symtab.update (const, consts)) consts) constss;
    fun succs consts = consts
      |> maps (Graph.immediate_succs eqngr)
      |> subtract (op =) consts
      |> map (the o Symtab.lookup mapping)
      |> distinct (op =);
    val conn = [] |> fold (fn consts => cons (consts, succs consts)) constss;
    fun namify consts = map (Code.string_of_const thy) consts
      |> commas;
    val prgr = map (fn (consts, constss) =>
      { name = namify consts, ID = namify consts, dir = "", unfold = true,
        path = "", parents = map namify constss, content = [] }) conn;
  in Graph_Display.display_graph prgr end;

local

fun code_thms_cmd thy = code_thms thy o op @ o read_const_exprs thy;
fun code_deps_cmd thy = code_deps thy o op @ o read_const_exprs thy;

in

val _ =
  Outer_Syntax.improper_command @{command_spec "code_thms"}
    "print system of code equations for code"
    (Scan.repeat1 Parse.term >> (fn cs =>
      Toplevel.unknown_theory o
      Toplevel.keep (fn state => code_thms_cmd (Toplevel.theory_of state) cs)));

val _ =
  Outer_Syntax.improper_command @{command_spec "code_deps"}
    "visualize dependencies of code equations for code"
    (Scan.repeat1 Parse.term >> (fn cs =>
      Toplevel.unknown_theory o
      Toplevel.keep (fn state => code_deps_cmd (Toplevel.theory_of state) cs)));

end;

end; (*struct*)


structure Basic_Code_Thingol: BASIC_CODE_THINGOL = Code_Thingol;
