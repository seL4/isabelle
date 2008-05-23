(*  Title:      Tools/code/code_thingol.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Intermediate language ("Thin-gol") representing executable code.
Representation and translation.
*)

infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 3 `|->;
infixr 3 `|-->;

signature BASIC_CODE_THINGOL =
sig
  type vname = string;
  datatype dict =
      DictConst of string * dict list list
    | DictVar of string list * (vname * (int * int));
  datatype itype =
      `%% of string * itype list
    | ITyVar of vname;
  type const = string * (dict list list * itype list (*types of arguments*))
  datatype iterm =
      IConst of const
    | IVar of vname
    | `$ of iterm * iterm
    | `|-> of (vname * itype) * iterm
    | ICase of ((iterm * itype) * (iterm * iterm) list) * iterm;
        (*((term, type), [(selector pattern, body term )]), primitive term)*)
  val `-> : itype * itype -> itype;
  val `--> : itype list * itype -> itype;
  val `$$ : iterm * iterm list -> iterm;
  val `|--> : (vname * itype) list * iterm -> iterm;
  type typscheme = (vname * sort) list * itype;
end;

signature CODE_THINGOL =
sig
  include BASIC_CODE_THINGOL;
  val unfoldl: ('a -> ('a * 'b) option) -> 'a -> 'a * 'b list;
  val unfoldr: ('a -> ('b * 'a) option) -> 'a -> 'b list * 'a;
  val unfold_fun: itype -> itype list * itype;
  val unfold_app: iterm -> iterm * iterm list;
  val split_abs: iterm -> (((vname * iterm option) * itype) * iterm) option;
  val unfold_abs: iterm -> ((vname * iterm option) * itype) list * iterm;
  val split_let: iterm -> (((iterm * itype) * iterm) * iterm) option;
  val unfold_let: iterm -> ((iterm * itype) * iterm) list * iterm;
  val unfold_const_app: iterm ->
    ((string * (dict list list * itype list)) * iterm list) option;
  val collapse_let: ((vname * itype) * iterm) * iterm
    -> (iterm * itype) * (iterm * iterm) list;
  val eta_expand: (string * (dict list list * itype list)) * iterm list -> int -> iterm;
  val contains_dictvar: iterm -> bool;
  val locally_monomorphic: iterm -> bool;
  val fold_constnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;
  val fold_varnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;
  val fold_unbound_varnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;

  datatype stmt =
      Bot
    | Fun of typscheme * ((iterm list * iterm) * thm) list
    | Datatype of (vname * sort) list * (string * itype list) list
    | Datatypecons of string
    | Class of vname * ((class * string) list * (string * itype) list)
    | Classrel of class * class
    | Classparam of class
    | Classinst of (class * (string * (vname * sort) list))
          * ((class * (string * (string * dict list list))) list
        * ((string * const) * thm) list);
  type code = stmt Graph.T;
  val empty_code: code;
  val merge_code: code * code -> code;
  val project_code: bool (*delete empty funs*)
    -> string list (*hidden*) -> string list option (*selected*)
    -> code -> code;
  val empty_funs: code -> string list;
  val is_cons: code -> string -> bool;
  val contr_classparam_typs: code -> string -> itype option list;

  type transact;
  val ensure_const: theory -> (sort -> sort) * Sorts.algebra -> CodeFuncgr.T
    -> string -> transact -> string * transact;
  val ensure_value: theory -> (sort -> sort) * Sorts.algebra -> CodeFuncgr.T
    -> term -> transact -> (code * ((typscheme * iterm) * string list)) * transact;
  val transact: theory -> CodeFuncgr.T
    -> (theory -> (sort -> sort) * Sorts.algebra -> CodeFuncgr.T
      -> transact -> 'a * transact) -> code -> 'a * code;
  val add_value_stmt: iterm * itype -> code -> code;
end;

structure CodeThingol: CODE_THINGOL =
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
        let val (xs', x') = unfoldr dest x2 in (x1::xs', x') end;


(** language core - types, pattern, expressions **)

(* language representation *)

type vname = string;

datatype dict =
    DictConst of string * dict list list
  | DictVar of string list * (vname * (int * int));

datatype itype =
    `%% of string * itype list
  | ITyVar of vname;

type const = string * (dict list list * itype list (*types of arguments*))

datatype iterm =
    IConst of const
  | IVar of vname
  | `$ of iterm * iterm
  | `|-> of (vname * itype) * iterm
  | ICase of ((iterm * itype) * (iterm * iterm) list) * iterm;
    (*see also signature*)

(*
  variable naming conventions

  bare names:
    variable names          v
    class names             class
    type constructor names  tyco
    datatype names          dtco
    const names (general)   c (const)
    constructor names       co
    class parameter names   classparam
    arbitrary name          s

    v, c, co, classparam also annotated with types etc.

  constructs:
    sort                    sort
    type parameters         vs
    type                    ty
    type schemes            tysm
    term                    t
    (term as pattern)       p
    instance (class, tyco)  inst
 *)

fun ty1 `-> ty2 = "fun" `%% [ty1, ty2];
val op `--> = Library.foldr (op `->);
val op `$$ = Library.foldl (op `$);
val op `|--> = Library.foldr (op `|->);

val unfold_fun = unfoldr
  (fn "fun" `%% [ty1, ty2] => SOME (ty1, ty2)
    | _ => NONE);

val unfold_app = unfoldl
  (fn op `$ t => SOME t
    | _ => NONE);

val split_abs =
  (fn (v, ty) `|-> (t as ICase (((IVar w, _), [(p, t')]), _)) =>
        if v = w then SOME (((v, SOME p), ty), t') else SOME (((v, NONE), ty), t)
    | (v, ty) `|-> t => SOME (((v, NONE), ty), t)
    | _ => NONE);

val unfold_abs = unfoldr split_abs;

val split_let = 
  (fn ICase (((td, ty), [(p, t)]), _) => SOME (((p, ty), td), t)
    | _ => NONE);

val unfold_let = unfoldr split_let;

fun unfold_const_app t =
 case unfold_app t
  of (IConst c, ts) => SOME (c, ts)
   | _ => NONE;

fun fold_aiterms f (t as IConst _) = f t
  | fold_aiterms f (t as IVar _) = f t
  | fold_aiterms f (t1 `$ t2) = fold_aiterms f t1 #> fold_aiterms f t2
  | fold_aiterms f (t as _ `|-> t') = f t #> fold_aiterms f t'
  | fold_aiterms f (ICase (_, t)) = fold_aiterms f t;

fun fold_constnames f =
  let
    fun add (IConst (c, _)) = f c
      | add _ = I;
  in fold_aiterms add end;

fun fold_varnames f =
  let
    fun add (IVar v) = f v
      | add ((v, _) `|-> _) = f v
      | add _ = I;
  in fold_aiterms add end;

fun fold_unbound_varnames f =
  let
    fun add _ (IConst _) = I
      | add vs (IVar v) = if not (member (op =) vs v) then f v else I
      | add vs (t1 `$ t2) = add vs t1 #> add vs t2
      | add vs ((v, _) `|-> t) = add (insert (op =) v vs) t
      | add vs (ICase (_, t)) = add vs t;
  in add [] end;

fun collapse_let (((v, ty), se), be as ICase (((IVar w, _), ds), _)) =
      let
        fun exists_v t = fold_unbound_varnames (fn w => fn b =>
          b orelse v = w) t false;
      in if v = w andalso forall (fn (t1, t2) =>
        exists_v t1 orelse not (exists_v t2)) ds
        then ((se, ty), ds)
        else ((se, ty), [(IVar v, be)])
      end
  | collapse_let (((v, ty), se), be) =
      ((se, ty), [(IVar v, be)])

fun eta_expand (c as (_, (_, tys)), ts) k =
  let
    val j = length ts;
    val l = k - j;
    val ctxt = (fold o fold_varnames) Name.declare ts Name.context;
    val vs_tys = Name.names ctxt "a" ((curry Library.take l o curry Library.drop j) tys);
  in vs_tys `|--> IConst c `$$ ts @ map (fn (v, _) => IVar v) vs_tys end;

fun contains_dictvar t =
  let
    fun contains (DictConst (_, dss)) = (fold o fold) contains dss
      | contains (DictVar _) = K true;
  in
    fold_aiterms
      (fn IConst (_, (dss, _)) => (fold o fold) contains dss | _ => I) t false
  end;
  
fun locally_monomorphic (IConst _) = false
  | locally_monomorphic (IVar _) = true
  | locally_monomorphic (t `$ _) = locally_monomorphic t
  | locally_monomorphic (_ `|-> t) = locally_monomorphic t
  | locally_monomorphic (ICase ((_, ds), _)) = exists (locally_monomorphic o snd) ds;



(** definitions, transactions **)

type typscheme = (vname * sort) list * itype;
datatype stmt =
    Bot
  | Fun of typscheme * ((iterm list * iterm) * thm) list
  | Datatype of (vname * sort) list * (string * itype list) list
  | Datatypecons of string
  | Class of vname * ((class * string) list * (string * itype) list)
  | Classrel of class * class
  | Classparam of class
  | Classinst of (class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * ((string * const) * thm) list);

type code = stmt Graph.T;


(* abstract code *)

val empty_code = Graph.empty : code; (*read: "depends on"*)

fun ensure_bot name = Graph.default_node (name, Bot);

fun add_def_incr (name, Bot) code =
      (case the_default Bot (try (Graph.get_node code) name)
       of Bot => error "Attempted to add Bot to code"
        | _ => code)
  | add_def_incr (name, def) code =
      (case try (Graph.get_node code) name
       of NONE => Graph.new_node (name, def) code
        | SOME Bot => Graph.map_node name (K def) code
        | SOME _ => error ("Tried to overwrite definition " ^ quote name));

fun add_dep (NONE, _) = I
  | add_dep (SOME name1, name2) =
      if name1 = name2 then I else Graph.add_edge (name1, name2);

val merge_code : code * code -> code = Graph.merge (K true);

fun project_code delete_empty_funs hidden raw_selected code =
  let
    fun is_empty_fun name = case Graph.get_node code name
     of Fun (_, []) => true
      | _ => false;
    val names = subtract (op =) hidden (Graph.keys code);
    val deleted = Graph.all_preds code (filter is_empty_fun names);
    val selected = case raw_selected
     of NONE => names |> subtract (op =) deleted 
      | SOME sel => sel
          |> delete_empty_funs ? subtract (op =) deleted
          |> subtract (op =) hidden
          |> Graph.all_succs code
          |> delete_empty_funs ? subtract (op =) deleted
          |> subtract (op =) hidden;
  in
    code
    |> Graph.subgraph (member (op =) selected)
  end;

fun empty_funs code =
  Graph.fold (fn (name, (Fun (_, []), _)) => cons name
               | _ => I) code [];

fun is_cons code name = case Graph.get_node code name
 of Datatypecons _ => true
  | _ => false;

fun contr_classparam_typs code name = case Graph.get_node code name
 of Classparam class => let
        val Class (_, (_, params)) = Graph.get_node code class;
        val SOME ty = AList.lookup (op =) params name;
        val (tys, res_ty) = unfold_fun ty;
        fun no_tyvar (_ `%% tys) = forall no_tyvar tys
          | no_tyvar (ITyVar _) = false;
      in if no_tyvar res_ty
        then map (fn ty => if no_tyvar ty then NONE else SOME ty) tys
        else []
      end
  | _ => [];


(* transaction protocol *)

type transact = Graph.key option * code;

fun ensure_stmt stmtgen name (dep, code) =
  let
    fun add_def false =
          ensure_bot name
          #> add_dep (dep, name)
          #> curry stmtgen (SOME name)
          ##> snd
          #-> (fn def => add_def_incr (name, def))
      | add_def true =
          add_dep (dep, name);
  in
    code
    |> add_def (can (Graph.get_node code) name)
    |> pair dep
    |> pair name
  end;

fun transact thy funcgr f code =
  (NONE, code)
  |> f thy (Code.operational_algebra thy) funcgr
  |-> (fn x => fn (_, code) => (x, code));


(* translation kernel *)

fun not_wellsorted thy thm ty sort e =
  let
    val err_class = Sorts.class_error (Syntax.pp_global thy) e;
    val err_thm = case thm
     of SOME thm => "\n(in defining equation " ^ Display.string_of_thm thm ^ ")" | NONE => "";
    val err_typ = "Type " ^ Syntax.string_of_typ_global thy ty ^ " not of sort "
      ^ Syntax.string_of_sort_global thy sort;
  in error ("Wellsortedness error" ^ err_thm ^ ":\n" ^ err_typ ^ "\n" ^ err_class) end;

fun ensure_class thy (algbr as (_, algebra)) funcgr class =
  let
    val superclasses = (Sorts.certify_sort algebra o Sorts.super_classes algebra) class;
    val cs = #params (AxClass.get_info thy class);
    val class' = CodeName.class thy class;
    val stmt_class =
      fold_map (fn superclass => ensure_class thy algbr funcgr superclass
        ##>> ensure_classrel thy algbr funcgr (class, superclass)) superclasses
      ##>> fold_map (fn (c, ty) => ensure_const thy algbr funcgr c
        ##>> exprgen_typ thy algbr funcgr ty) cs
      #>> (fn info => Class (unprefix "'" Name.aT, info))
  in
    ensure_stmt stmt_class class'
  end
and ensure_classrel thy algbr funcgr (subclass, superclass) =
  let
    val classrel' = CodeName.classrel thy (subclass, superclass);
    val stmt_classrel =
      ensure_class thy algbr funcgr subclass
      ##>> ensure_class thy algbr funcgr superclass
      #>> Classrel;
  in
    ensure_stmt stmt_classrel classrel'
  end
and ensure_tyco thy algbr funcgr "fun" =
      pair "fun"
  | ensure_tyco thy algbr funcgr tyco =
      let
        val stmt_datatype =
          let
            val (vs, cos) = Code.get_datatype thy tyco;
          in
            fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
            ##>> fold_map (fn (c, tys) =>
              ensure_const thy algbr funcgr c
              ##>> fold_map (exprgen_typ thy algbr funcgr) tys) cos
            #>> Datatype
          end;
        val tyco' = CodeName.tyco thy tyco;
      in
        ensure_stmt stmt_datatype tyco'
      end
and exprgen_tyvar_sort thy (algbr as (proj_sort, _)) funcgr (v, sort) =
  fold_map (ensure_class thy algbr funcgr) (proj_sort sort)
  #>> (fn sort => (unprefix "'" v, sort))
and exprgen_typ thy algbr funcgr (TFree vs) =
      exprgen_tyvar_sort thy algbr funcgr vs
      #>> (fn (v, sort) => ITyVar v)
  | exprgen_typ thy algbr funcgr (Type (tyco, tys)) =
      ensure_tyco thy algbr funcgr tyco
      ##>> fold_map (exprgen_typ thy algbr funcgr) tys
      #>> (fn (tyco, tys) => tyco `%% tys)
and exprgen_dicts thy (algbr as (proj_sort, algebra)) funcgr thm (ty, sort) =
  let
    val pp = Syntax.pp_global thy;
    datatype typarg =
        Global of (class * string) * typarg list list
      | Local of (class * class) list * (string * (int * sort));
    fun class_relation (Global ((_, tyco), yss), _) class =
          Global ((class, tyco), yss)
      | class_relation (Local (classrels, v), subclass) superclass =
          Local ((subclass, superclass) :: classrels, v);
    fun type_constructor tyco yss class =
      Global ((class, tyco), (map o map) fst yss);
    fun type_variable (TFree (v, sort)) =
      let
        val sort' = proj_sort sort;
      in map_index (fn (n, class) => (Local ([], (v, (n, sort'))), class)) sort' end;
    val typargs = Sorts.of_sort_derivation pp algebra
      {class_relation = class_relation, type_constructor = type_constructor,
       type_variable = type_variable} (ty, proj_sort sort)
      handle Sorts.CLASS_ERROR e => not_wellsorted thy thm ty sort e;
    fun mk_dict (Global (inst, yss)) =
          ensure_inst thy algbr funcgr inst
          ##>> (fold_map o fold_map) mk_dict yss
          #>> (fn (inst, dss) => DictConst (inst, dss))
      | mk_dict (Local (classrels, (v, (k, sort)))) =
          fold_map (ensure_classrel thy algbr funcgr) classrels
          #>> (fn classrels => DictVar (classrels, (unprefix "'" v, (k, length sort))))
  in
    fold_map mk_dict typargs
  end
and exprgen_eq thy algbr funcgr thm =
  let
    val (args, rhs) = (apfst (snd o strip_comb) o Logic.dest_equals
      o Logic.unvarify o prop_of) thm;
  in
    fold_map (exprgen_term thy algbr funcgr (SOME thm)) args
    ##>> exprgen_term thy algbr funcgr (SOME thm) rhs
    #>> rpair thm
  end
and ensure_inst thy (algbr as (_, algebra)) funcgr (class, tyco) =
  let
    val superclasses = (Sorts.certify_sort algebra o Sorts.super_classes algebra) class;
    val classparams = these (try (#params o AxClass.get_info thy) class);
    val vs = Name.names Name.context "'a" (Sorts.mg_domain algebra tyco [class]);
    val sorts' = Sorts.mg_domain (Sign.classes_of thy) tyco [class];
    val vs' = map2 (fn (v, sort1) => fn sort2 => (v,
      Sorts.inter_sort (Sign.classes_of thy) (sort1, sort2))) vs sorts';
    val arity_typ = Type (tyco, map TFree vs);
    val arity_typ' = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort)) vs');
    fun exprgen_superarity superclass =
      ensure_class thy algbr funcgr superclass
      ##>> ensure_classrel thy algbr funcgr (class, superclass)
      ##>> exprgen_dicts thy algbr funcgr NONE (arity_typ, [superclass])
      #>> (fn ((superclass, classrel), [DictConst (inst, dss)]) =>
            (superclass, (classrel, (inst, dss))));
    fun exprgen_classparam_inst (c, ty) =
      let
        val c_inst = Const (c, map_type_tfree (K arity_typ') ty);
        val thm = AxClass.unoverload_conv thy (Thm.cterm_of thy c_inst);
        val c_ty = (apsnd Logic.unvarifyT o dest_Const o snd
          o Logic.dest_equals o Thm.prop_of) thm;
      in
        ensure_const thy algbr funcgr c
        ##>> exprgen_const thy algbr funcgr (SOME thm) c_ty
        #>> (fn (c, IConst c_inst) => ((c, c_inst), thm))
      end;
    val stmt_inst =
      ensure_class thy algbr funcgr class
      ##>> ensure_tyco thy algbr funcgr tyco
      ##>> fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
      ##>> fold_map exprgen_superarity superclasses
      ##>> fold_map exprgen_classparam_inst classparams
      #>> (fn ((((class, tyco), arity), superarities), classparams) =>
             Classinst ((class, (tyco, arity)), (superarities, classparams)));
    val inst = CodeName.instance thy (class, tyco);
  in
    ensure_stmt stmt_inst inst
  end
and ensure_const thy algbr funcgr c =
  let
    val c' = CodeName.const thy c;
    fun stmt_datatypecons tyco =
      ensure_tyco thy algbr funcgr tyco
      #>> Datatypecons;
    fun stmt_classparam class =
      ensure_class thy algbr funcgr class
      #>> Classparam;
    fun stmt_fun trns =
      let
        val raw_thms = CodeFuncgr.funcs funcgr c;
        val (vs, raw_ty) = CodeFuncgr.typ funcgr c;
        val ty = Logic.unvarifyT raw_ty;
        val thms = if (null o Term.typ_tfrees) ty orelse (null o fst o strip_type) ty
          then raw_thms
          else map (CodeUnit.expand_eta 1) raw_thms;
      in
        trns
        |> fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
        ||>> exprgen_typ thy algbr funcgr ty
        ||>> fold_map (exprgen_eq thy algbr funcgr) thms
        |>> (fn ((vs, ty), eqs) => Fun ((vs, ty), eqs))
      end;
    val stmtgen = case Code.get_datatype_of_constr thy c
     of SOME tyco => stmt_datatypecons tyco
      | NONE => (case AxClass.class_of_param thy c
         of SOME class => stmt_classparam class
          | NONE => stmt_fun)
  in
    ensure_stmt stmtgen c'
  end
and exprgen_term thy algbr funcgr thm (Const (c, ty)) =
      exprgen_app thy algbr funcgr thm ((c, ty), [])
  | exprgen_term thy algbr funcgr thm (Free (v, _)) =
      pair (IVar v)
  | exprgen_term thy algbr funcgr thm (Abs (abs as (_, ty, _))) =
      let
        val (v, t) = Syntax.variant_abs abs;
      in
        exprgen_typ thy algbr funcgr ty
        ##>> exprgen_term thy algbr funcgr thm t
        #>> (fn (ty, t) => (v, ty) `|-> t)
      end
  | exprgen_term thy algbr funcgr thm (t as _ $ _) =
      case strip_comb t
       of (Const (c, ty), ts) =>
            exprgen_app thy algbr funcgr thm ((c, ty), ts)
        | (t', ts) =>
            exprgen_term thy algbr funcgr thm t'
            ##>> fold_map (exprgen_term thy algbr funcgr thm) ts
            #>> (fn (t, ts) => t `$$ ts)
and exprgen_const thy algbr funcgr thm (c, ty) =
  let
    val tys = Sign.const_typargs thy (c, ty);
    val sorts = (map snd o fst o CodeFuncgr.typ funcgr) c;
    val tys_args = (fst o Term.strip_type) ty;
  in
    ensure_const thy algbr funcgr c
    ##>> fold_map (exprgen_dicts thy algbr funcgr thm) (tys ~~ sorts)
    ##>> fold_map (exprgen_typ thy algbr funcgr) tys_args
    #>> (fn ((c, iss), tys) => IConst (c, (iss, tys)))
  end
and exprgen_app_default thy algbr funcgr thm (c_ty, ts) =
  exprgen_const thy algbr funcgr thm c_ty
  ##>> fold_map (exprgen_term thy algbr funcgr thm) ts
  #>> (fn (t, ts) => t `$$ ts)
and exprgen_case thy algbr funcgr thm n cases (app as ((c, ty), ts)) =
  let
    val (tys, _) =
      (chop (1 + (if null cases then 1 else length cases)) o fst o strip_type) ty;
    val dt = nth ts n;
    val dty = nth tys n;
    fun is_undefined (Const (c, _)) = Code.is_undefined thy c
      | is_undefined _ = false;
    fun mk_case (co, n) t =
      let
        val (vs, body) = Term.strip_abs_eta n t;
        val selector = list_comb (Const (co, map snd vs ---> dty), map Free vs);
      in if is_undefined body then NONE else SOME (selector, body) end;
    fun mk_ds [] =
          let
            val ([v_ty], body) = Term.strip_abs_eta 1 (the_single (nth_drop n ts))
          in [(Free v_ty, body)] end
      | mk_ds cases = map_filter (uncurry mk_case)
          (AList.make (CodeUnit.no_args thy) cases ~~ nth_drop n ts);
  in
    exprgen_term thy algbr funcgr thm dt
    ##>> exprgen_typ thy algbr funcgr dty
    ##>> fold_map (fn (pat, body) => exprgen_term thy algbr funcgr thm pat
          ##>> exprgen_term thy algbr funcgr thm body) (mk_ds cases)
    ##>> exprgen_app_default thy algbr funcgr thm app
    #>> (fn (((dt, dty), ds), t0) => ICase (((dt, dty), ds), t0))
  end
and exprgen_app thy algbr funcgr thm ((c, ty), ts) = case Code.get_case_data thy c
 of SOME (n, cases) => let val i = 1 + (if null cases then 1 else length cases) in
      if length ts < i then
        let
          val k = length ts;
          val tys = (curry Library.take (i - k) o curry Library.drop k o fst o strip_type) ty;
          val ctxt = (fold o fold_aterms)
            (fn Free (v, _) => Name.declare v | _ => I) ts Name.context;
          val vs = Name.names ctxt "a" tys;
        in
          fold_map (exprgen_typ thy algbr funcgr) tys
          ##>> exprgen_case thy algbr funcgr thm n cases ((c, ty), ts @ map Free vs)
          #>> (fn (tys, t) => map2 (fn (v, _) => pair v) vs tys `|--> t)
        end
      else if length ts > i then
        exprgen_case thy algbr funcgr thm n cases ((c, ty), Library.take (i, ts))
        ##>> fold_map (exprgen_term thy algbr funcgr thm) (Library.drop (i, ts))
        #>> (fn (t, ts) => t `$$ ts)
      else
        exprgen_case thy algbr funcgr thm n cases ((c, ty), ts)
      end
  | NONE => exprgen_app_default thy algbr funcgr thm ((c, ty), ts);


(** evaluation **)

fun add_value_stmt (t, ty) code =
  code
  |> Graph.new_node (CodeName.value_name, Fun (([], ty), [(([], t), Drule.dummy_thm)]))
  |> fold (curry Graph.add_edge CodeName.value_name) (Graph.keys code);

fun ensure_value thy algbr funcgr t = 
  let
    val ty = fastype_of t;
    val vs = fold_term_types (K (fold_atyps (insert (eq_fst op =)
      o dest_TFree))) t [];
    val stmt_value =
      fold_map (exprgen_tyvar_sort thy algbr funcgr) vs
      ##>> exprgen_typ thy algbr funcgr ty
      ##>> exprgen_term thy algbr funcgr NONE t
      #>> (fn ((vs, ty), t) => Fun ((vs, ty), [(([], t), Drule.dummy_thm)]));
    fun term_value (dep, code1) =
      let
        val Fun ((vs, ty), [(([], t), _)]) =
          Graph.get_node code1 CodeName.value_name;
        val deps = Graph.imm_succs code1 CodeName.value_name;
        val code2 = Graph.del_nodes [CodeName.value_name] code1;
        val code3 = project_code false [] (SOME deps) code2;
      in ((code3, (((vs, ty), t), deps)), (dep, code2)) end;
  in
    ensure_stmt stmt_value CodeName.value_name
    #> snd
    #> term_value
  end;

end; (*struct*)


structure BasicCodeThingol: BASIC_CODE_THINGOL = CodeThingol;
