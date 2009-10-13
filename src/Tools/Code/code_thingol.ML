(*  Title:      Tools/code/code_thingol.ML
    Author:     Florian Haftmann, TU Muenchen

Intermediate language ("Thin-gol") representing executable code.
Representation and translation.
*)

infix 8 `%%;
infix 4 `$;
infix 4 `$$;
infixr 3 `|=>;
infixr 3 `|==>;

signature BASIC_CODE_THINGOL =
sig
  type vname = string;
  datatype dict =
      DictConst of string * dict list list
    | DictVar of string list * (vname * (int * int));
  datatype itype =
      `%% of string * itype list
    | ITyVar of vname;
  type const = string * ((itype list * dict list list) * itype list (*types of arguments*))
  datatype iterm =
      IConst of const
    | IVar of vname option
    | `$ of iterm * iterm
    | `|=> of (vname option * itype) * iterm
    | ICase of ((iterm * itype) * (iterm * iterm) list) * iterm;
        (*((term, type), [(selector pattern, body term )]), primitive term)*)
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
  val unfold_app: iterm -> iterm * iterm list
  val unfold_abs: iterm -> (vname option * itype) list * iterm
  val split_let: iterm -> (((iterm * itype) * iterm) * iterm) option
  val unfold_let: iterm -> ((iterm * itype) * iterm) list * iterm
  val split_pat_abs: iterm -> ((iterm * itype) * iterm) option
  val unfold_pat_abs: iterm -> (iterm * itype) list * iterm
  val unfold_const_app: iterm -> (const * iterm list) option
  val is_IVar: iterm -> bool
  val eta_expand: int -> const * iterm list -> iterm
  val contains_dictvar: iterm -> bool
  val locally_monomorphic: iterm -> bool
  val add_constnames: iterm -> string list -> string list
  val add_tyconames: iterm -> string list -> string list
  val fold_varnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a

  type naming
  val empty_naming: naming
  val lookup_class: naming -> class -> string option
  val lookup_classrel: naming -> class * class -> string option
  val lookup_tyco: naming -> string -> string option
  val lookup_instance: naming -> class * string -> string option
  val lookup_const: naming -> string -> string option
  val ensure_declared_const: theory -> string -> naming -> string * naming

  datatype stmt =
      NoStmt
    | Fun of string * (typscheme * ((iterm list * iterm) * (thm * bool)) list)
    | Datatype of string * ((vname * sort) list * (string * itype list) list)
    | Datatypecons of string * string
    | Class of class * (vname * ((class * string) list * (string * itype) list))
    | Classrel of class * class
    | Classparam of string * class
    | Classinst of (class * (string * (vname * sort) list))
          * ((class * (string * (string * dict list list))) list
        * ((string * const) * (thm * bool)) list)
  type program = stmt Graph.T
  val empty_funs: program -> string list
  val map_terms_bottom_up: (iterm -> iterm) -> iterm -> iterm
  val map_terms_stmt: (iterm -> iterm) -> stmt -> stmt
  val is_cons: program -> string -> bool
  val contr_classparam_typs: program -> string -> itype option list
  val labelled_name: theory -> program -> string -> string
  val group_stmts: theory -> program
    -> ((string * stmt) list * (string * stmt) list
      * ((string * stmt) list * (string * stmt) list)) list

  val expand_eta: theory -> int -> thm -> thm
  val clean_thms: theory -> thm list -> thm list
  val read_const_exprs: theory -> string list -> string list * string list
  val consts_program: theory -> string list -> string list * (naming * program)
  val cached_program: theory -> naming * program
  val eval_conv: theory
    -> (naming -> program -> ((string * sort) list * typscheme) * iterm -> string list -> cterm -> thm)
    -> cterm -> thm
  val eval: theory -> ((term -> term) -> 'a -> 'a)
    -> (naming -> program -> ((string * sort) list * typscheme) * iterm -> string list -> 'a)
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
        let val (xs', x') = unfoldr dest x2 in (x1::xs', x') end;


(** language core - types, terms **)

type vname = string;

datatype dict =
    DictConst of string * dict list list
  | DictVar of string list * (vname * (int * int));

datatype itype =
    `%% of string * itype list
  | ITyVar of vname;

type const = string * ((itype list * dict list list) * itype list (*types of arguments*))

datatype iterm =
    IConst of const
  | IVar of vname option
  | `$ of iterm * iterm
  | `|=> of (vname option * itype) * iterm
  | ICase of ((iterm * itype) * (iterm * iterm) list) * iterm;
    (*see also signature*)

fun is_IVar (IVar _) = true
  | is_IVar _ = false;

val op `$$ = Library.foldl (op `$);
val op `|==> = Library.foldr (op `|=>);

val unfold_app = unfoldl
  (fn op `$ t => SOME t
    | _ => NONE);

val unfold_abs = unfoldr
  (fn op `|=> t => SOME t
    | _ => NONE);

val split_let = 
  (fn ICase (((td, ty), [(p, t)]), _) => SOME (((p, ty), td), t)
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
      | fold' (ICase (((t, _), ds), _)) = fold' t
          #> fold (fn (pat, body) => fold' pat #> fold' body) ds
  in fold' end;

val add_constnames = fold_constexprs (fn (c, _) => insert (op =) c);

fun add_tycos (tyco `%% tys) = insert (op =) tyco #> fold add_tycos tys
  | add_tycos (ITyVar _) = I;

val add_tyconames = fold_constexprs (fn (_, ((tys, _), _)) => fold add_tycos tys);

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
          | fold_term vs (ICase (((t, _), ds), _)) = fold_term vs t #> fold (fold_case vs) ds
        and fold_case vs (p, t) = fold_term (add p vs) t;
      in fold_term [] end;
    fun add t = fold_aux add (insert (op =)) t;
  in fold_aux add f end;

fun exists_var t v = fold_varnames (fn w => fn b => v = w orelse b) t false;

fun split_pat_abs ((NONE, ty) `|=> t) = SOME ((IVar NONE, ty), t)
  | split_pat_abs ((SOME v, ty) `|=> t) = SOME (case t
     of ICase (((IVar (SOME w), _), [(p, t')]), _) =>
          if v = w andalso (exists_var p v orelse not (exists_var t' v))
          then ((p, ty), t')
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
        val vs_tys = (map o apfst) SOME (Name.names ctxt "a" tys);
      in (vs_tys, t `$$ map (IVar o fst) vs_tys) end;

fun eta_expand k (c as (_, (_, tys)), ts) =
  let
    val j = length ts;
    val l = k - j;
    val ctxt = (fold o fold_varnames) Name.declare ts Name.context;
    val vs_tys = (map o apfst) SOME
      (Name.names ctxt "a" ((curry Library.take l o curry Library.drop j) tys));
  in vs_tys `|==> IConst c `$$ ts @ map (IVar o fst) vs_tys end;

fun contains_dictvar t =
  let
    fun cont_dict (DictConst (_, dss)) = (exists o exists) cont_dict dss
      | cont_dict (DictVar _) = true;
    fun cont_term (IConst (_, ((_, dss), _))) = (exists o exists) cont_dict dss
      | cont_term (IVar _) = false
      | cont_term (t1 `$ t2) = cont_term t1 orelse cont_term t2
      | cont_term (_ `|=> t) = cont_term t
      | cont_term (ICase (_, t)) = cont_term t;
  in cont_term t end;
  
fun locally_monomorphic (IConst _) = false
  | locally_monomorphic (IVar _) = true
  | locally_monomorphic (t `$ _) = locally_monomorphic t
  | locally_monomorphic (_ `|=> t) = locally_monomorphic t
  | locally_monomorphic (ICase ((_, ds), _)) = exists (locally_monomorphic o snd) ds;


(** namings **)

(* policies *)

local
  fun thyname_of thy f x = the (AList.lookup (op =) (f x) Markup.theory_nameN);
  fun thyname_of_class thy =
    thyname_of thy (ProofContext.query_class (ProofContext.init thy));
  fun thyname_of_tyco thy =
    thyname_of thy (Type.the_tags (Sign.tsig_of thy));
  fun thyname_of_instance thy inst = case AxClass.arity_property thy inst Markup.theory_nameN
   of [] => error ("no such instance: " ^ quote (snd inst ^ " :: " ^ fst inst))
    | thyname :: _ => thyname;
  fun thyname_of_const thy c = case AxClass.class_of_param thy c
   of SOME class => thyname_of_class thy class
    | NONE => (case Code.get_datatype_of_constr thy c
       of SOME dtco => thyname_of_tyco thy dtco
        | NONE => thyname_of thy (Consts.the_tags (Sign.consts_of thy)) c);
  fun purify_base "op &" = "and"
    | purify_base "op |" = "or"
    | purify_base "op -->" = "implies"
    | purify_base "op :" = "member"
    | purify_base "op =" = "eq"
    | purify_base "*" = "product"
    | purify_base "+" = "sum"
    | purify_base s = Name.desymbolize false s;
  fun namify thy get_basename get_thyname name =
    let
      val prefix = get_thyname thy name;
      val base = (purify_base o get_basename) name;
    in Long_Name.append prefix base end;
in

fun namify_class thy = namify thy Long_Name.base_name thyname_of_class;
fun namify_classrel thy = namify thy (fn (class1, class2) => 
  Long_Name.base_name class2 ^ "_" ^ Long_Name.base_name class1) (fn thy => thyname_of_class thy o fst);
  (*order fits nicely with composed projections*)
fun namify_tyco thy "fun" = "Pure.fun"
  | namify_tyco thy tyco = namify thy Long_Name.base_name thyname_of_tyco tyco;
fun namify_instance thy = namify thy (fn (class, tyco) => 
  Long_Name.base_name class ^ "_" ^ Long_Name.base_name tyco) thyname_of_instance;
fun namify_const thy = namify thy Long_Name.base_name thyname_of_const;

end; (* local *)


(* data *)

datatype naming = Naming of {
  class: class Symtab.table * Name.context,
  classrel: string Symreltab.table * Name.context,
  tyco: string Symtab.table * Name.context,
  instance: string Symreltab.table * Name.context,
  const: string Symtab.table * Name.context
}

fun dest_Naming (Naming naming) = naming;

val empty_naming = Naming {
  class = (Symtab.empty, Name.context),
  classrel = (Symreltab.empty, Name.context),
  tyco = (Symtab.empty, Name.context),
  instance = (Symreltab.empty, Name.context),
  const = (Symtab.empty, Name.context)
};

local
  fun mk_naming (class, classrel, tyco, instance, const) =
    Naming { class = class, classrel = classrel,
      tyco = tyco, instance = instance, const = const };
  fun map_naming f (Naming { class, classrel, tyco, instance, const }) =
    mk_naming (f (class, classrel, tyco, instance, const));
in
  fun map_class f = map_naming
    (fn (class, classrel, tyco, inst, const) =>
      (f class, classrel, tyco, inst, const));
  fun map_classrel f = map_naming
    (fn (class, classrel, tyco, inst, const) =>
      (class, f classrel, tyco, inst, const));
  fun map_tyco f = map_naming
    (fn (class, classrel, tyco, inst, const) =>
      (class, classrel, f tyco, inst, const));
  fun map_instance f = map_naming
    (fn (class, classrel, tyco, inst, const) =>
      (class, classrel, tyco, f inst, const));
  fun map_const f = map_naming
    (fn (class, classrel, tyco, inst, const) =>
      (class, classrel, tyco, inst, f const));
end; (*local*)

fun add_variant update (thing, name) (tab, used) =
  let
    val (name', used') = yield_singleton Name.variants name used;
    val tab' = update (thing, name') tab;
  in (tab', used') end;

fun declare thy mapp lookup update namify thing =
  mapp (add_variant update (thing, namify thy thing))
  #> `(fn naming => the (lookup naming thing));


(* lookup and declare *)

local

val suffix_class = "class";
val suffix_classrel = "classrel"
val suffix_tyco = "tyco";
val suffix_instance = "inst";
val suffix_const = "const";

fun add_suffix nsp NONE = NONE
  | add_suffix nsp (SOME name) = SOME (Long_Name.append name nsp);

in

val lookup_class = add_suffix suffix_class
  oo Symtab.lookup o fst o #class o dest_Naming;
val lookup_classrel = add_suffix suffix_classrel
  oo Symreltab.lookup o fst o #classrel o dest_Naming;
val lookup_tyco = add_suffix suffix_tyco
  oo Symtab.lookup o fst o #tyco o dest_Naming;
val lookup_instance = add_suffix suffix_instance
  oo Symreltab.lookup o fst o #instance o dest_Naming;
val lookup_const = add_suffix suffix_const
  oo Symtab.lookup o fst o #const o dest_Naming;

fun declare_class thy = declare thy map_class
  lookup_class Symtab.update_new namify_class;
fun declare_classrel thy = declare thy map_classrel
  lookup_classrel Symreltab.update_new namify_classrel;
fun declare_tyco thy = declare thy map_tyco
  lookup_tyco Symtab.update_new namify_tyco;
fun declare_instance thy = declare thy map_instance
  lookup_instance Symreltab.update_new namify_instance;
fun declare_const thy = declare thy map_const
  lookup_const Symtab.update_new namify_const;

fun ensure_declared_const thy const naming =
  case lookup_const naming const
   of SOME const' => (const', naming)
    | NONE => declare_const thy const naming;

val unfold_fun = unfoldr
  (fn "Pure.fun.tyco" `%% [ty1, ty2] => SOME (ty1, ty2)
    | _ => NONE); (*depends on suffix_tyco and namify_tyco!*)

end; (* local *)


(** technical transformations of code equations **)

fun expand_eta thy k thm =
  let
    val (lhs, rhs) = (Logic.dest_equals o Thm.plain_prop_of) thm;
    val (head, args) = strip_comb lhs;
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
    val k = fold (curry Int.max o num_args_of o Thm.prop_of) thms 0;
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

fun desymbolize_all_vars thy = desymbolize_tvars thy #> map (desymbolize_vars thy);

fun clean_thms thy = map (Thm.transfer thy) #> same_arity thy #> desymbolize_all_vars thy;


(** statements, abstract programs **)

type typscheme = (vname * sort) list * itype;
datatype stmt =
    NoStmt
  | Fun of string * (typscheme * ((iterm list * iterm) * (thm * bool)) list)
  | Datatype of string * ((vname * sort) list * (string * itype list) list)
  | Datatypecons of string * string
  | Class of class * (vname * ((class * string) list * (string * itype) list))
  | Classrel of class * class
  | Classparam of string * class
  | Classinst of (class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * ((string * const) * (thm * bool)) list);

type program = stmt Graph.T;

fun empty_funs program =
  Graph.fold (fn (name, (Fun (c, (_, [])), _)) => cons c
               | _ => I) program [];

fun map_terms_bottom_up f (t as IConst _) = f t
  | map_terms_bottom_up f (t as IVar _) = f t
  | map_terms_bottom_up f (t1 `$ t2) = f
      (map_terms_bottom_up f t1 `$ map_terms_bottom_up f t2)
  | map_terms_bottom_up f ((v, ty) `|=> t) = f
      ((v, ty) `|=> map_terms_bottom_up f t)
  | map_terms_bottom_up f (ICase (((t, ty), ps), t0)) = f
      (ICase (((map_terms_bottom_up f t, ty), (map o pairself)
        (map_terms_bottom_up f) ps), map_terms_bottom_up f t0));

fun map_terms_stmt f NoStmt = NoStmt
  | map_terms_stmt f (Fun (c, (tysm, eqs))) = Fun (c, (tysm, (map o apfst)
      (fn (ts, t) => (map f ts, f t)) eqs))
  | map_terms_stmt f (stmt as Datatype _) = stmt
  | map_terms_stmt f (stmt as Datatypecons _) = stmt
  | map_terms_stmt f (stmt as Class _) = stmt
  | map_terms_stmt f (stmt as Classrel _) = stmt
  | map_terms_stmt f (stmt as Classparam _) = stmt
  | map_terms_stmt f (Classinst (arity, (superarities, classparms))) =
      Classinst (arity, (superarities, (map o apfst o apsnd) (fn const =>
        case f (IConst const) of IConst const' => const') classparms));

fun is_cons program name = case Graph.get_node program name
 of Datatypecons _ => true
  | _ => false;

fun contr_classparam_typs program name = case Graph.get_node program name
 of Classparam (_, class) => let
        val Class (_, (_, (_, params))) = Graph.get_node program class;
        val SOME ty = AList.lookup (op =) params name;
        val (tys, res_ty) = unfold_fun ty;
        fun no_tyvar (_ `%% tys) = forall no_tyvar tys
          | no_tyvar (ITyVar _) = false;
      in if no_tyvar res_ty
        then map (fn ty => if no_tyvar ty then NONE else SOME ty) tys
        else []
      end
  | _ => [];

fun labelled_name thy program name = case Graph.get_node program name
 of Fun (c, _) => quote (Code.string_of_const thy c)
  | Datatype (tyco, _) => "type " ^ quote (Sign.extern_type thy tyco)
  | Datatypecons (c, _) => quote (Code.string_of_const thy c)
  | Class (class, _) => "class " ^ quote (Sign.extern_class thy class)
  | Classrel (sub, super) => let
        val Class (sub, _) = Graph.get_node program sub
        val Class (super, _) = Graph.get_node program super
      in quote (Sign.extern_class thy sub ^ " < " ^ Sign.extern_class thy super) end
  | Classparam (c, _) => quote (Code.string_of_const thy c)
  | Classinst ((class, (tyco, _)), _) => let
        val Class (class, _) = Graph.get_node program class
        val Datatype (tyco, _) = Graph.get_node program tyco
      in quote (Sign.extern_type thy tyco ^ " :: " ^ Sign.extern_class thy class) end

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
      else error ("Illegal mutual dependencies: " ^
        (commas o map (labelled_name thy program o fst)) stmts)
  in
    rev (Graph.strong_conn program)
    |> map (AList.make (Graph.get_node program))
    |> map group
  end;


(** translation kernel **)

(* generic mechanisms *)

fun ensure_stmt lookup declare generate thing (dep, (naming, program)) =
  let
    fun add_dep name = case dep of NONE => I
      | SOME dep => Graph.add_edge (dep, name);
    val (name, naming') = case lookup naming thing
     of SOME name => (name, naming)
      | NONE => declare thing naming;
  in case try (Graph.get_node program) name
   of SOME stmt => program
        |> add_dep name
        |> pair naming'
        |> pair dep
        |> pair name
    | NONE => program
        |> Graph.default_node (name, NoStmt)
        |> add_dep name
        |> pair naming'
        |> curry generate (SOME name)
        ||> snd
        |-> (fn stmt => (apsnd o Graph.map_node name) (K stmt))
        |> pair dep
        |> pair name
  end;

fun not_wellsorted thy thm ty sort e =
  let
    val err_class = Sorts.class_error (Syntax.pp_global thy) e;
    val err_thm = case thm
     of SOME thm => "\n(in code equation " ^ Display.string_of_thm_global thy thm ^ ")" | NONE => "";
    val err_typ = "Type " ^ Syntax.string_of_typ_global thy ty ^ " not of sort "
      ^ Syntax.string_of_sort_global thy sort;
  in error ("Wellsortedness error" ^ err_thm ^ ":\n" ^ err_typ ^ "\n" ^ err_class) end;


(* translation *)

fun ensure_tyco thy algbr eqngr tyco =
  let
    val stmt_datatype =
      let
        val (vs, cos) = Code.get_datatype thy tyco;
      in
        fold_map (translate_tyvar_sort thy algbr eqngr) vs
        ##>> fold_map (fn (c, tys) =>
          ensure_const thy algbr eqngr c
          ##>> fold_map (translate_typ thy algbr eqngr) tys) cos
        #>> (fn info => Datatype (tyco, info))
      end;
  in ensure_stmt lookup_tyco (declare_tyco thy) stmt_datatype tyco end
and ensure_const thy algbr eqngr c =
  let
    fun stmt_datatypecons tyco =
      ensure_tyco thy algbr eqngr tyco
      #>> (fn tyco => Datatypecons (c, tyco));
    fun stmt_classparam class =
      ensure_class thy algbr eqngr class
      #>> (fn class => Classparam (c, class));
    fun stmt_fun raw_eqns =
      let
        val eqns = burrow_fst (clean_thms thy) raw_eqns;
        val (vs, ty) = Code.typscheme_eqns thy c (map fst eqns);
      in
        fold_map (translate_tyvar_sort thy algbr eqngr) vs
        ##>> translate_typ thy algbr eqngr ty
        ##>> fold_map (translate_eqn thy algbr eqngr) eqns
        #>> (fn info => Fun (c, info))
      end;
    val stmt_const = case Code.get_datatype_of_constr thy c
     of SOME tyco => stmt_datatypecons tyco
      | NONE => (case AxClass.class_of_param thy c
         of SOME class => stmt_classparam class
          | NONE => stmt_fun (Code_Preproc.eqns eqngr c))
  in ensure_stmt lookup_const (declare_const thy) stmt_const c end
and ensure_class thy (algbr as (_, algebra)) eqngr class =
  let
    val superclasses = (Sorts.minimize_sort algebra o Sorts.super_classes algebra) class;
    val cs = #params (AxClass.get_info thy class);
    val stmt_class =
      fold_map (fn superclass => ensure_class thy algbr eqngr superclass
        ##>> ensure_classrel thy algbr eqngr (class, superclass)) superclasses
      ##>> fold_map (fn (c, ty) => ensure_const thy algbr eqngr c
        ##>> translate_typ thy algbr eqngr ty) cs
      #>> (fn info => Class (class, (unprefix "'" Name.aT, info)))
  in ensure_stmt lookup_class (declare_class thy) stmt_class class end
and ensure_classrel thy algbr eqngr (subclass, superclass) =
  let
    val stmt_classrel =
      ensure_class thy algbr eqngr subclass
      ##>> ensure_class thy algbr eqngr superclass
      #>> Classrel;
  in ensure_stmt lookup_classrel (declare_classrel thy) stmt_classrel (subclass, superclass) end
and ensure_inst thy (algbr as (_, algebra)) eqngr (class, tyco) =
  let
    val superclasses = (Sorts.minimize_sort algebra o Sorts.super_classes algebra) class;
    val classparams = these (try (#params o AxClass.get_info thy) class);
    val vs = Name.names Name.context "'a" (Sorts.mg_domain algebra tyco [class]);
    val sorts' = Sorts.mg_domain (Sign.classes_of thy) tyco [class];
    val vs' = map2 (fn (v, sort1) => fn sort2 => (v,
      Sorts.inter_sort (Sign.classes_of thy) (sort1, sort2))) vs sorts';
    val arity_typ = Type (tyco, map TFree vs);
    val arity_typ' = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort)) vs');
    fun translate_superarity superclass =
      ensure_class thy algbr eqngr superclass
      ##>> ensure_classrel thy algbr eqngr (class, superclass)
      ##>> translate_dicts thy algbr eqngr NONE (arity_typ, [superclass])
      #>> (fn ((superclass, classrel), [DictConst (inst, dss)]) =>
            (superclass, (classrel, (inst, dss))));
    fun translate_classparam_inst (c, ty) =
      let
        val c_inst = Const (c, map_type_tfree (K arity_typ') ty);
        val thm = AxClass.unoverload_conv thy (Thm.cterm_of thy c_inst);
        val c_ty = (apsnd Logic.unvarifyT o dest_Const o snd
          o Logic.dest_equals o Thm.prop_of) thm;
      in
        ensure_const thy algbr eqngr c
        ##>> translate_const thy algbr eqngr (SOME thm) c_ty
        #>> (fn (c, IConst c_inst) => ((c, c_inst), (thm, true)))
      end;
    val stmt_inst =
      ensure_class thy algbr eqngr class
      ##>> ensure_tyco thy algbr eqngr tyco
      ##>> fold_map (translate_tyvar_sort thy algbr eqngr) vs
      ##>> fold_map translate_superarity superclasses
      ##>> fold_map translate_classparam_inst classparams
      #>> (fn ((((class, tyco), arity), superarities), classparams) =>
             Classinst ((class, (tyco, arity)), (superarities, classparams)));
  in ensure_stmt lookup_instance (declare_instance thy) stmt_inst (class, tyco) end
and translate_typ thy algbr eqngr (TFree (v, _)) =
      pair (ITyVar (unprefix "'" v))
  | translate_typ thy algbr eqngr (Type (tyco, tys)) =
      ensure_tyco thy algbr eqngr tyco
      ##>> fold_map (translate_typ thy algbr eqngr) tys
      #>> (fn (tyco, tys) => tyco `%% tys)
and translate_term thy algbr eqngr thm (Const (c, ty)) =
      translate_app thy algbr eqngr thm ((c, ty), [])
  | translate_term thy algbr eqngr thm (Free (v, _)) =
      pair (IVar (SOME v))
  | translate_term thy algbr eqngr thm (Abs (v, ty, t)) =
      let
        val (v', t') = Syntax.variant_abs (Name.desymbolize false v, ty, t);
        val v'' = if member (op =) (Term.add_free_names t' []) v'
          then SOME v' else NONE
      in
        translate_typ thy algbr eqngr ty
        ##>> translate_term thy algbr eqngr thm t'
        #>> (fn (ty, t) => (v'', ty) `|=> t)
      end
  | translate_term thy algbr eqngr thm (t as _ $ _) =
      case strip_comb t
       of (Const (c, ty), ts) =>
            translate_app thy algbr eqngr thm ((c, ty), ts)
        | (t', ts) =>
            translate_term thy algbr eqngr thm t'
            ##>> fold_map (translate_term thy algbr eqngr thm) ts
            #>> (fn (t, ts) => t `$$ ts)
and translate_eqn thy algbr eqngr (thm, proper) =
  let
    val (args, rhs) = (apfst (snd o strip_comb) o Logic.dest_equals
      o Logic.unvarify o prop_of) thm;
  in
    fold_map (translate_term thy algbr eqngr (SOME thm)) args
    ##>> translate_term thy algbr eqngr (SOME thm) rhs
    #>> rpair (thm, proper)
  end
and translate_const thy algbr eqngr thm (c, ty) =
  let
    val tys = Sign.const_typargs thy (c, ty);
    val sorts = Code_Preproc.sortargs eqngr c;
    val tys_args = (fst o Term.strip_type) ty;
  in
    ensure_const thy algbr eqngr c
    ##>> fold_map (translate_typ thy algbr eqngr) tys
    ##>> fold_map (translate_dicts thy algbr eqngr thm) (tys ~~ sorts)
    ##>> fold_map (translate_typ thy algbr eqngr) tys_args
    #>> (fn (((c, tys), iss), tys_args) => IConst (c, ((tys, iss), tys_args)))
  end
and translate_app_const thy algbr eqngr thm (c_ty, ts) =
  translate_const thy algbr eqngr thm c_ty
  ##>> fold_map (translate_term thy algbr eqngr thm) ts
  #>> (fn (t, ts) => t `$$ ts)
and translate_case thy algbr eqngr thm (num_args, (t_pos, case_pats)) (c_ty, ts) =
  let
    fun arg_types num_args ty = (fst o chop num_args o fst o strip_type) ty;
    val tys = arg_types num_args (snd c_ty);
    val ty = nth tys t_pos;
    fun mk_constr c t = let val n = Code.args_number thy c
      in ((c, arg_types n (fastype_of t) ---> ty), n) end;
    val constrs = if null case_pats then []
      else map2 mk_constr case_pats (nth_drop t_pos ts);
    fun casify naming constrs ty ts =
      let
        val undefineds = map_filter (lookup_const naming) (Code.undefineds thy);
        fun collapse_clause vs_map ts body =
          let
          in case body
           of IConst (c, _) => if member (op =) undefineds c
                then []
                else [(ts, body)]
            | ICase (((IVar (SOME v), _), subclauses), _) =>
                if forall (fn (pat', body') => exists_var pat' v
                  orelse not (exists_var body' v)) subclauses
                then case AList.lookup (op =) vs_map v
                 of SOME i => maps (fn (pat', body') =>
                      collapse_clause (AList.delete (op =) v vs_map)
                        (nth_map i (K pat') ts) body') subclauses
                  | NONE => [(ts, body)]
                else [(ts, body)]
            | _ => [(ts, body)]
          end;
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
          else maps (fn ((constr as IConst (_, (_, tys)), n), t) =>
            mk_clause (fn (ts, body) => (constr `$$ ts, body)) (curry Library.take n tys) t)
              (constrs ~~ ts_clause);
      in ((t, ty), clauses) end;
  in
    translate_const thy algbr eqngr thm c_ty
    ##>> fold_map (fn (constr, n) => translate_const thy algbr eqngr thm constr #>> rpair n) constrs
    ##>> translate_typ thy algbr eqngr ty
    ##>> fold_map (translate_term thy algbr eqngr thm) ts
    #-> (fn (((t, constrs), ty), ts) =>
      `(fn (_, (naming, _)) => ICase (casify naming constrs ty ts, t `$$ ts)))
  end
and translate_app_case thy algbr eqngr thm (case_scheme as (num_args, _)) ((c, ty), ts) =
  if length ts < num_args then
    let
      val k = length ts;
      val tys = (curry Library.take (num_args - k) o curry Library.drop k o fst o strip_type) ty;
      val ctxt = (fold o fold_aterms) Term.declare_term_frees ts Name.context;
      val vs = Name.names ctxt "a" tys;
    in
      fold_map (translate_typ thy algbr eqngr) tys
      ##>> translate_case thy algbr eqngr thm case_scheme ((c, ty), ts @ map Free vs)
      #>> (fn (tys, t) => map2 (fn (v, _) => pair (SOME v)) vs tys `|==> t)
    end
  else if length ts > num_args then
    translate_case thy algbr eqngr thm case_scheme ((c, ty), Library.take (num_args, ts))
    ##>> fold_map (translate_term thy algbr eqngr thm) (Library.drop (num_args, ts))
    #>> (fn (t, ts) => t `$$ ts)
  else
    translate_case thy algbr eqngr thm case_scheme ((c, ty), ts)
and translate_app thy algbr eqngr thm (c_ty_ts as ((c, _), _)) =
  case Code.get_case_scheme thy c
   of SOME case_scheme => translate_app_case thy algbr eqngr thm case_scheme c_ty_ts
    | NONE => translate_app_const thy algbr eqngr thm c_ty_ts
and translate_tyvar_sort thy (algbr as (proj_sort, _)) eqngr (v, sort) =
  fold_map (ensure_class thy algbr eqngr) (proj_sort sort)
  #>> (fn sort => (unprefix "'" v, sort))
and translate_dicts thy (algbr as (proj_sort, algebra)) eqngr thm (ty, sort) =
  let
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
    val typargs = Sorts.of_sort_derivation algebra
      {class_relation = class_relation, type_constructor = type_constructor,
       type_variable = type_variable} (ty, proj_sort sort)
      handle Sorts.CLASS_ERROR e => not_wellsorted thy thm ty sort e;
    fun mk_dict (Global (inst, yss)) =
          ensure_inst thy algbr eqngr inst
          ##>> (fold_map o fold_map) mk_dict yss
          #>> (fn (inst, dss) => DictConst (inst, dss))
      | mk_dict (Local (classrels, (v, (n, sort)))) =
          fold_map (ensure_classrel thy algbr eqngr) classrels
          #>> (fn classrels => DictVar (classrels, (unprefix "'" v, (n, length sort))))
  in fold_map mk_dict typargs end;


(* store *)

structure Program = Code_Data_Fun
(
  type T = naming * program;
  val empty = (empty_naming, Graph.empty);
  fun purge thy cs (naming, program) =
    let
      val names_delete = cs
        |> map_filter (lookup_const naming)
        |> filter (can (Graph.get_node program))
        |> Graph.all_preds program;
      val program' = Graph.del_nodes names_delete program;
    in (naming, program') end;
);

val cached_program = Program.get;

fun invoke_generation thy (algebra, eqngr) f name =
  Program.change_yield thy (fn naming_program => (NONE, naming_program)
    |> f thy algebra eqngr name
    |-> (fn name => fn (_, naming_program) => (name, naming_program)));


(* program generation *)

fun consts_program thy cs =
  let
    fun project_consts cs (naming, program) =
      let
        val cs_all = Graph.all_succs program cs;
      in (cs, (naming, Graph.subgraph (member (op =) cs_all) program)) end;
    fun generate_consts thy algebra eqngr =
      fold_map (ensure_const thy algebra eqngr);
  in
    invoke_generation thy (Code_Preproc.obtain thy cs []) generate_consts cs
    |-> project_consts
  end;


(* value evaluation *)

fun ensure_value thy algbr eqngr t =
  let
    val ty = fastype_of t;
    val vs = fold_term_types (K (fold_atyps (insert (eq_fst op =)
      o dest_TFree))) t [];
    val stmt_value =
      fold_map (translate_tyvar_sort thy algbr eqngr) vs
      ##>> translate_typ thy algbr eqngr ty
      ##>> translate_term thy algbr eqngr NONE t
      #>> (fn ((vs, ty), t) => Fun
        (Term.dummy_patternN, ((vs, ty), [(([], t), (Drule.dummy_thm, true))])));
    fun term_value (dep, (naming, program1)) =
      let
        val Fun (_, (vs_ty, [(([], t), _)])) =
          Graph.get_node program1 Term.dummy_patternN;
        val deps = Graph.imm_succs program1 Term.dummy_patternN;
        val program2 = Graph.del_nodes [Term.dummy_patternN] program1;
        val deps_all = Graph.all_succs program2 deps;
        val program3 = Graph.subgraph (member (op =) deps_all) program2;
      in (((naming, program3), ((vs_ty, t), deps)), (dep, (naming, program2))) end;
  in
    ensure_stmt ((K o K) NONE) pair stmt_value Term.dummy_patternN
    #> snd
    #> term_value
  end;

fun base_evaluator thy evaluator algebra eqngr vs t =
  let
    val (((naming, program), (((vs', ty'), t'), deps)), _) =
      invoke_generation thy (algebra, eqngr) ensure_value t;
    val vs'' = map (fn (v, _) => (v, (the o AList.lookup (op =) vs o prefix "'") v)) vs';
  in evaluator naming program ((vs'', (vs', ty')), t') deps end;

fun eval_conv thy = Code_Preproc.eval_conv thy o base_evaluator thy;
fun eval thy postproc = Code_Preproc.eval thy postproc o base_evaluator thy;


(** diagnostic commands **)

fun read_const_exprs thy =
  let
    fun consts_of some_thyname =
      let
        val thy' = case some_thyname
         of SOME thyname => ThyInfo.the_theory thyname thy
          | NONE => thy;
        val cs = Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
          ((snd o #constants o Consts.dest o #consts o Sign.rep_sg) thy') [];
        fun belongs_here c =
          not (exists (fn thy'' => Sign.declared_const thy'' c) (Theory.parents_of thy'))
      in case some_thyname
       of NONE => cs
        | SOME thyname => filter belongs_here cs
      end;
    fun read_const_expr "*" = ([], consts_of NONE)
      | read_const_expr s = if String.isSuffix ".*" s
          then ([], consts_of (SOME (unsuffix ".*" s)))
          else ([Code.read_const thy s], []);
  in pairself flat o split_list o map read_const_expr end;

fun code_depgr thy consts =
  let
    val (_, eqngr) = Code_Preproc.obtain thy consts [];
    val select = Graph.all_succs eqngr consts;
  in
    eqngr
    |> not (null consts) ? Graph.subgraph (member (op =) select) 
    |> Graph.map_nodes ((apsnd o map o apfst) (AxClass.overload thy))
  end;

fun code_thms thy = Pretty.writeln o Code_Preproc.pretty thy o code_depgr thy;

fun code_deps thy consts =
  let
    val eqngr = code_depgr thy consts;
    val constss = Graph.strong_conn eqngr;
    val mapping = Symtab.empty |> fold (fn consts => fold (fn const =>
      Symtab.update (const, consts)) consts) constss;
    fun succs consts = consts
      |> maps (Graph.imm_succs eqngr)
      |> subtract (op =) consts
      |> map (the o Symtab.lookup mapping)
      |> distinct (op =);
    val conn = [] |> fold (fn consts => cons (consts, succs consts)) constss;
    fun namify consts = map (Code.string_of_const thy) consts
      |> commas;
    val prgr = map (fn (consts, constss) =>
      { name = namify consts, ID = namify consts, dir = "", unfold = true,
        path = "", parents = map namify constss }) conn;
  in Present.display_graph prgr end;

local

structure P = OuterParse
and K = OuterKeyword

fun code_thms_cmd thy = code_thms thy o op @ o read_const_exprs thy;
fun code_deps_cmd thy = code_deps thy o op @ o read_const_exprs thy;

in

val _ =
  OuterSyntax.improper_command "code_thms" "print system of code equations for code" OuterKeyword.diag
    (Scan.repeat P.term_group
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_thms_cmd thy cs) o Toplevel.theory_of)));

val _ =
  OuterSyntax.improper_command "code_deps" "visualize dependencies of code equations for code" OuterKeyword.diag
    (Scan.repeat P.term_group
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_deps_cmd thy cs) o Toplevel.theory_of)));

end;

end; (*struct*)


structure Basic_Code_Thingol: BASIC_CODE_THINGOL = Code_Thingol;
