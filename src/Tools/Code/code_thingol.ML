(*  Title:      Tools/Code/code_thingol.ML
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
      Dict of string list * plain_dict
  and plain_dict = 
      Dict_Const of string * dict list list
    | Dict_Var of vname * (int * int)
  datatype itype =
      `%% of string * itype list
    | ITyVar of vname;
  type const = string * (((itype list * dict list list) * (itype list * itype)) * bool)
    (* (f [T1..Tn] {dicts} (_::S1) .. (_::Sm)) :: S =^= (f, ((([T1..Tn], dicts), ([S1..Sm], S)), ambiguous)) *)
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
  val fun_tyco: string
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
    | Fun of string * ((typscheme * ((iterm list * iterm) * (thm option * bool)) list) * thm option)
    | Datatype of string * (vname list *
        ((string * vname list (*type argument wrt. canonical order*)) * itype list) list)
    | Datatypecons of string * string
    | Class of class * (vname * ((class * string) list * (string * itype) list))
    | Classrel of class * class
    | Classparam of string * class
    | Classinst of (class * (string * (vname * sort) list) (*class and arity*))
          * ((class * (string * (string * dict list list))) list (*super instances*)
        * (((string * const) * (thm * bool)) list (*class parameter instances*)
          * ((string * const) * (thm * bool)) list (*super class parameter instances*)))
  type program = stmt Graph.T
  val empty_funs: program -> string list
  val map_terms_bottom_up: (iterm -> iterm) -> iterm -> iterm
  val map_terms_stmt: (iterm -> iterm) -> stmt -> stmt
  val is_cons: program -> string -> bool
  val is_case: stmt -> bool
  val labelled_name: theory -> program -> string -> string
  val group_stmts: theory -> program
    -> ((string * stmt) list * (string * stmt) list
      * ((string * stmt) list * (string * stmt) list)) list

  val read_const_exprs: theory -> string list -> string list * string list
  val consts_program: theory -> bool -> string list -> string list * (naming * program)
  val dynamic_conv: theory -> (naming -> program
    -> ((string * sort) list * typscheme) * iterm -> string list -> conv)
    -> conv
  val dynamic_value: theory -> ((term -> term) -> 'a -> 'a) -> (naming -> program
    -> ((string * sort) list * typscheme) * iterm -> string list -> 'a)
    -> term -> 'a
  val static_conv: theory -> string list -> (naming -> program -> string list
    -> ((string * sort) list * typscheme) * iterm -> string list -> conv)
    -> conv
  val static_conv_simple: theory -> string list
    -> (program -> (string * sort) list -> term -> conv) -> conv
  val static_value: theory -> ((term -> term) -> 'a -> 'a) -> string list ->
    (naming -> program -> string list
      -> ((string * sort) list * typscheme) * iterm -> string list -> 'a)
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
    Dict of string list * plain_dict
and plain_dict = 
    Dict_Const of string * dict list list
  | Dict_Var of vname * (int * int)

datatype itype =
    `%% of string * itype list
  | ITyVar of vname;

type const = string * (((itype list * dict list list) *
  (itype list (*types of arguments*) * itype (*result type*))) * bool (*requires type annotation*))

datatype iterm =
    IConst of const
  | IVar of vname option
  | `$ of iterm * iterm
  | `|=> of (vname option * itype) * iterm
  | ICase of ((iterm * itype) * (iterm * iterm) list) * iterm;
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

val add_tyconames = fold_constexprs (fn (_, (((tys, _), _), _)) => fold add_tycos tys);

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
        val vs_tys = (map o apfst) SOME (Name.invent_names ctxt "a" tys);
      in (vs_tys, t `$$ map (IVar o fst) vs_tys) end;

fun eta_expand k (c as (name, ((_, (tys, _)), _)), ts) =
  let
    val j = length ts;
    val l = k - j;
    val _ = if l > length tys
      then error ("Impossible eta-expansion for constant " ^ quote name) else ();
    val ctxt = (fold o fold_varnames) Name.declare ts Name.context;
    val vs_tys = (map o apfst) SOME
      (Name.invent_names ctxt "a" ((take l o drop j) tys));
  in vs_tys `|==> IConst c `$$ ts @ map (IVar o fst) vs_tys end;

fun contains_dict_var t =
  let
    fun cont_dict (Dict (_, d)) = cont_plain_dict d
    and cont_plain_dict (Dict_Const (_, dss)) = (exists o exists) cont_dict dss
      | cont_plain_dict (Dict_Var _) = true;
    fun cont_term (IConst (_, (((_, dss), _), _))) = (exists o exists) cont_dict dss
      | cont_term (IVar _) = false
      | cont_term (t1 `$ t2) = cont_term t1 orelse cont_term t2
      | cont_term (_ `|=> t) = cont_term t
      | cont_term (ICase (_, t)) = cont_term t;
  in cont_term t end;


(** namings **)

(* policies *)

local
  fun thyname_of_type thy = #theory_name o Name_Space.the_entry (Sign.type_space thy);
  fun thyname_of_class thy = #theory_name o Name_Space.the_entry (Sign.class_space thy);
  fun thyname_of_instance thy inst = case AxClass.thynames_of_arity thy inst
   of [] => error ("No such instance: " ^ quote (snd inst ^ " :: " ^ fst inst))
    | thyname :: _ => thyname;
  fun thyname_of_const thy c = case AxClass.class_of_param thy c
   of SOME class => thyname_of_class thy class
    | NONE => (case Code.get_type_of_constr_or_abstr thy c
       of SOME (tyco, _) => thyname_of_type thy tyco
        | NONE => #theory_name (Name_Space.the_entry (Sign.const_space thy) c));
  fun purify_base "==>" = "follows"
    | purify_base "==" = "meta_eq"
    | purify_base s = Name.desymbolize false s;
  fun namify thy get_basename get_thyname name =
    let
      val prefix = get_thyname thy name;
      val base = (purify_base o get_basename) name;
    in Long_Name.append prefix base end;
in

fun namify_class thy = namify thy Long_Name.base_name thyname_of_class;
fun namify_classrel thy = namify thy (fn (sub_class, super_class) => 
    Long_Name.base_name super_class ^ "_" ^ Long_Name.base_name sub_class)
  (fn thy => thyname_of_class thy o fst);
  (*order fits nicely with composed projections*)
fun namify_tyco thy "fun" = "Pure.fun"
  | namify_tyco thy tyco = namify thy Long_Name.base_name thyname_of_type tyco;
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
    val (name', used') = Name.variant name used;
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

val fun_tyco = Long_Name.append (namify_tyco Pure.thy "fun") suffix_tyco
  (*depends on add_suffix*);

val unfold_fun = unfoldr
  (fn tyco `%% [ty1, ty2] => if tyco = fun_tyco then SOME (ty1, ty2) else NONE
    | _ => NONE);

fun unfold_fun_n n ty =
  let
    val (tys1, ty1) = unfold_fun ty;
    val (tys3, tys2) = chop n tys1;
    val ty3 = Library.foldr (fn (ty1, ty2) => fun_tyco `%% [ty1, ty2]) (tys2, ty1);
  in (tys3, ty3) end;

end; (* local *)


(** statements, abstract programs **)

type typscheme = (vname * sort) list * itype;
datatype stmt =
    NoStmt
  | Fun of string * ((typscheme * ((iterm list * iterm) * (thm option * bool)) list) * thm option)
  | Datatype of string * (vname list * ((string * vname list) * itype list) list)
  | Datatypecons of string * string
  | Class of class * (vname * ((class * string) list * (string * itype) list))
  | Classrel of class * class
  | Classparam of string * class
  | Classinst of (class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * (((string * const) * (thm * bool)) list
        * ((string * const) * (thm * bool)) list))
      (*see also signature*);

type program = stmt Graph.T;

fun empty_funs program =
  Graph.fold (fn (_, (Fun (c, ((_, []), _)), _)) => cons c | _ => I) program [];

fun map_terms_bottom_up f (t as IConst _) = f t
  | map_terms_bottom_up f (t as IVar _) = f t
  | map_terms_bottom_up f (t1 `$ t2) = f
      (map_terms_bottom_up f t1 `$ map_terms_bottom_up f t2)
  | map_terms_bottom_up f ((v, ty) `|=> t) = f
      ((v, ty) `|=> map_terms_bottom_up f t)
  | map_terms_bottom_up f (ICase (((t, ty), ps), t0)) = f
      (ICase (((map_terms_bottom_up f t, ty), (map o pairself)
        (map_terms_bottom_up f) ps), map_terms_bottom_up f t0));

fun map_classparam_instances_as_term f =
  (map o apfst o apsnd) (fn const => case f (IConst const) of IConst const' => const')

fun map_terms_stmt f NoStmt = NoStmt
  | map_terms_stmt f (Fun (c, ((tysm, eqs), case_cong))) = Fun (c, ((tysm, (map o apfst)
      (fn (ts, t) => (map f ts, f t)) eqs), case_cong))
  | map_terms_stmt f (stmt as Datatype _) = stmt
  | map_terms_stmt f (stmt as Datatypecons _) = stmt
  | map_terms_stmt f (stmt as Class _) = stmt
  | map_terms_stmt f (stmt as Classrel _) = stmt
  | map_terms_stmt f (stmt as Classparam _) = stmt
  | map_terms_stmt f (Classinst (arity, (super_instances, classparam_instances))) =
      Classinst (arity, (super_instances, (pairself o map_classparam_instances_as_term) f classparam_instances));

fun is_cons program name = case Graph.get_node program name
 of Datatypecons _ => true
  | _ => false;

fun is_case (Fun (_, (_, SOME _))) = true
  | is_case _ = false;

fun labelled_name thy program name =
  let val ctxt = Proof_Context.init_global thy in
    case Graph.get_node program name of
      Fun (c, _) => quote (Code.string_of_const thy c)
    | Datatype (tyco, _) => "type " ^ quote (Proof_Context.extern_type ctxt tyco)
    | Datatypecons (c, _) => quote (Code.string_of_const thy c)
    | Class (class, _) => "class " ^ quote (Proof_Context.extern_class ctxt class)
    | Classrel (sub, super) =>
        let
          val Class (sub, _) = Graph.get_node program sub;
          val Class (super, _) = Graph.get_node program super;
        in
          quote (Proof_Context.extern_class ctxt sub ^ " < " ^ Proof_Context.extern_class ctxt super)
        end
    | Classparam (c, _) => quote (Code.string_of_const thy c)
    | Classinst ((class, (tyco, _)), _) =>
        let
          val Class (class, _) = Graph.get_node program class;
          val Datatype (tyco, _) = Graph.get_node program tyco;
        in
          quote (Proof_Context.extern_type ctxt tyco ^ " :: " ^ Proof_Context.extern_class ctxt class)
        end
  end;

fun linear_stmts program =
  rev (Graph.strong_conn program)
  |> map (AList.make (Graph.get_node program));

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
    linear_stmts program
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
  in
    if can (Graph.get_node program) name
    then
      program
      |> add_dep name
      |> pair naming'
      |> pair dep
      |> pair name
    else
      program
      |> Graph.default_node (name, NoStmt)
      |> add_dep name
      |> pair naming'
      |> curry generate (SOME name)
      ||> snd
      |-> (fn stmt => (apsnd o Graph.map_node name) (K stmt))
      |> pair dep
      |> pair name
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
      #>> (fn info => Datatype (tyco, info));
  in ensure_stmt lookup_tyco (declare_tyco thy) stmt_datatype tyco end
and ensure_const thy algbr eqngr permissive c =
  let
    fun stmt_datatypecons tyco =
      ensure_tyco thy algbr eqngr permissive tyco
      #>> (fn tyco => Datatypecons (c, tyco));
    fun stmt_classparam class =
      ensure_class thy algbr eqngr permissive class
      #>> (fn class => Classparam (c, class));
    fun stmt_fun cert =
      let
        val ((vs, ty), eqns) = Code.equations_of_cert thy cert;
        val eqns' = annotate_eqns thy algbr eqngr (c, ty) eqns
        val some_case_cong = Code.get_case_cong thy c;
      in
        fold_map (translate_tyvar_sort thy algbr eqngr permissive) vs
        ##>> translate_typ thy algbr eqngr permissive ty
        ##>> translate_eqns thy algbr eqngr permissive eqns'
        #>> (fn info => Fun (c, (info, some_case_cong)))
      end;
    val stmt_const = case Code.get_type_of_constr_or_abstr thy c
     of SOME (tyco, _) => stmt_datatypecons tyco
      | NONE => (case AxClass.class_of_param thy c
         of SOME class => stmt_classparam class
          | NONE => stmt_fun (Code_Preproc.cert eqngr c))
  in ensure_stmt lookup_const (declare_const thy) stmt_const c end
and ensure_class thy (algbr as (_, algebra)) eqngr permissive class =
  let
    val super_classes = (Sorts.minimize_sort algebra o Sorts.super_classes algebra) class;
    val cs = #params (AxClass.get_info thy class);
    val stmt_class =
      fold_map (fn super_class => ensure_class thy algbr eqngr permissive super_class
        ##>> ensure_classrel thy algbr eqngr permissive (class, super_class)) super_classes
      ##>> fold_map (fn (c, ty) => ensure_const thy algbr eqngr permissive c
        ##>> translate_typ thy algbr eqngr permissive ty) cs
      #>> (fn info => Class (class, (unprefix "'" Name.aT, info)))
  in ensure_stmt lookup_class (declare_class thy) stmt_class class end
and ensure_classrel thy algbr eqngr permissive (sub_class, super_class) =
  let
    val stmt_classrel =
      ensure_class thy algbr eqngr permissive sub_class
      ##>> ensure_class thy algbr eqngr permissive super_class
      #>> Classrel;
  in ensure_stmt lookup_classrel (declare_classrel thy) stmt_classrel (sub_class, super_class) end
and ensure_inst thy (algbr as (_, algebra)) eqngr permissive (class, tyco) =
  let
    val super_classes = (Sorts.minimize_sort algebra o Sorts.super_classes algebra) class;
    val these_classparams = these o try (#params o AxClass.get_info thy);
    val classparams = these_classparams class;
    val further_classparams = maps these_classparams
      ((Sorts.complete_sort algebra o Sorts.super_classes algebra) class);
    val vs = Name.invent_names Name.context "'a" (Sorts.mg_domain algebra tyco [class]);
    val sorts' = Sorts.mg_domain (Sign.classes_of thy) tyco [class];
    val vs' = map2 (fn (v, sort1) => fn sort2 => (v,
      Sorts.inter_sort (Sign.classes_of thy) (sort1, sort2))) vs sorts';
    val arity_typ = Type (tyco, map TFree vs);
    val arity_typ' = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort)) vs');
    fun translate_super_instance super_class =
      ensure_class thy algbr eqngr permissive super_class
      ##>> ensure_classrel thy algbr eqngr permissive (class, super_class)
      ##>> translate_dicts thy algbr eqngr permissive NONE (arity_typ, [super_class])
      #>> (fn ((super_class, classrel), [Dict ([], Dict_Const (inst, dss))]) =>
            (super_class, (classrel, (inst, dss))));
    fun translate_classparam_instance (c, ty) =
      let
        val raw_const = Const (c, map_type_tfree (K arity_typ') ty);
        val thm = AxClass.unoverload_conv thy (Thm.cterm_of thy raw_const);
        val const = (apsnd Logic.unvarifyT_global o dest_Const o snd
          o Logic.dest_equals o Thm.prop_of) thm;
      in
        ensure_const thy algbr eqngr permissive c
        ##>> translate_const thy algbr eqngr permissive (SOME thm) (const, NONE)
        #>> (fn (c, IConst const') => ((c, const'), (thm, true)))
      end;
    val stmt_inst =
      ensure_class thy algbr eqngr permissive class
      ##>> ensure_tyco thy algbr eqngr permissive tyco
      ##>> fold_map (translate_tyvar_sort thy algbr eqngr permissive) vs
      ##>> fold_map translate_super_instance super_classes
      ##>> fold_map translate_classparam_instance classparams
      ##>> fold_map translate_classparam_instance further_classparams
      #>> (fn (((((class, tyco), arity_args), super_instances),
        classparam_instances), further_classparam_instances) =>
          Classinst ((class, (tyco, arity_args)), (super_instances,
            (classparam_instances, further_classparam_instances))));
  in ensure_stmt lookup_instance (declare_instance thy) stmt_inst (class, tyco) end
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
and translate_eqns thy algbr eqngr permissive eqns prgrm =
  prgrm |> fold_map (translate_eqn thy algbr eqngr permissive) eqns
    handle PERMISSIVE () => ([], prgrm)
and translate_const thy algbr eqngr permissive some_thm ((c, ty), some_abs) =
  let
    val _ = if (case some_abs of NONE => true | SOME abs => not (c = abs))
        andalso Code.is_abstr thy c
        then translation_error thy permissive some_thm
          "Abstraction violation" ("constant " ^ Code.string_of_const thy c)
      else ()
    val (annotate, ty') = dest_tagged_type ty
    val arg_typs = Sign.const_typargs thy (c, ty');
    val sorts = Code_Preproc.sortargs eqngr c;
    val (function_typs, body_typ) = Term.strip_type ty';
  in
    ensure_const thy algbr eqngr permissive c
    ##>> fold_map (translate_typ thy algbr eqngr permissive) arg_typs
    ##>> fold_map (translate_dicts thy algbr eqngr permissive some_thm) (arg_typs ~~ sorts)
    ##>> fold_map (translate_typ thy algbr eqngr permissive) (body_typ :: function_typs)
    #>> (fn (((c, arg_typs), dss), body_typ :: function_typs) =>
      IConst (c, (((arg_typs, dss), (function_typs, body_typ)), annotate)))
  end
and translate_app_const thy algbr eqngr permissive some_thm ((c_ty, ts), some_abs) =
  translate_const thy algbr eqngr permissive some_thm (c_ty, some_abs)
  ##>> fold_map (translate_term thy algbr eqngr permissive some_thm o rpair NONE) ts
  #>> (fn (t, ts) => t `$$ ts)
and translate_case thy algbr eqngr permissive some_thm (num_args, (t_pos, case_pats)) (c_ty, ts) =
  let
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
          else maps (fn ((constr as IConst (_, ((_, (tys, _)), _)), n), t) =>
            mk_clause (fn (ts, body) => (constr `$$ ts, body)) (take n tys) t)
              (constrs ~~ (map_filter (fn (NONE, _) => NONE | (SOME _, t) => SOME t)
                (case_pats ~~ ts_clause)));
      in ((t, ty), clauses) end;
  in
    translate_const thy algbr eqngr permissive some_thm (c_ty, NONE)
    ##>> fold_map (fn (constr, n) => translate_const thy algbr eqngr permissive some_thm (constr, NONE)
      #>> rpair n) constrs
    ##>> translate_typ thy algbr eqngr permissive ty
    ##>> fold_map (translate_term thy algbr eqngr permissive some_thm o rpair NONE) ts
    #-> (fn (((t, constrs), ty), ts) =>
      `(fn (_, (naming, _)) => ICase (casify naming constrs ty ts, t `$$ ts)))
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
        Global of (class * string) * typarg_witness list list
      | Local of string * (int * sort);
    fun class_relation ((Weakening (classrels, x)), sub_class) super_class =
      Weakening ((sub_class, super_class) :: classrels, x);
    fun type_constructor (tyco, _) dss class =
      Weakening ([], Global ((class, tyco), (map o map) fst dss));
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
  type T = naming * program;
  val empty = (empty_naming, Graph.empty);
);

fun invoke_generation ignore_cache thy (algebra, eqngr) generate thing =
  Program.change_yield (if ignore_cache then NONE else SOME thy)
    (fn naming_program => (NONE, naming_program)
      |> generate thy algebra eqngr thing
      |-> (fn thing => fn (_, naming_program) => (thing, naming_program)));


(* program generation *)

fun consts_program thy permissive consts =
  let
    fun project_consts consts (naming, program) =
      if permissive then (consts, (naming, program))
      else (consts, (naming, Graph.restrict
        (member (op =) (Graph.all_succs program consts)) program));
    fun generate_consts thy algebra eqngr =
      fold_map (ensure_const thy algebra eqngr permissive);
  in
    invoke_generation permissive thy (Code_Preproc.obtain false thy consts [])
      generate_consts consts
    |-> project_consts
  end;


(* value evaluation *)

fun ensure_value thy algbr eqngr t =
  let
    val ty = fastype_of t;
    val vs = fold_term_types (K (fold_atyps (insert (eq_fst op =)
      o dest_TFree))) t [];
    val t' = annotate thy algbr eqngr (Term.dummy_patternN, ty) [] t;
    val stmt_value =
      fold_map (translate_tyvar_sort thy algbr eqngr false) vs
      ##>> translate_typ thy algbr eqngr false ty
      ##>> translate_term thy algbr eqngr false NONE (t', NONE)
      #>> (fn ((vs, ty), t) => Fun
        (Term.dummy_patternN, (((vs, ty), [(([], t), (NONE, true))]), NONE)));
    fun term_value (dep, (naming, program1)) =
      let
        val Fun (_, ((vs_ty, [(([], t), _)]), _)) =
          Graph.get_node program1 Term.dummy_patternN;
        val deps = Graph.immediate_succs program1 Term.dummy_patternN;
        val program2 = Graph.del_node Term.dummy_patternN program1;
        val deps_all = Graph.all_succs program2 deps;
        val program3 = Graph.restrict (member (op =) deps_all) program2;
      in (((naming, program3), ((vs_ty, t), deps)), (dep, (naming, program2))) end;
  in
    ensure_stmt ((K o K) NONE) pair stmt_value Term.dummy_patternN
    #> snd
    #> term_value
  end;

fun original_sorts vs =
  map (fn (v, _) => (v, (the o AList.lookup (op =) vs o prefix "'") v));

fun dynamic_evaluator thy evaluator algebra eqngr vs t =
  let
    val (((naming, program), (((vs', ty'), t'), deps)), _) =
      invoke_generation false thy (algebra, eqngr) ensure_value t;
  in evaluator naming program ((original_sorts vs vs', (vs', ty')), t') deps end;

fun dynamic_conv thy evaluator =
  Code_Preproc.dynamic_conv thy (dynamic_evaluator thy evaluator);

fun dynamic_value thy postproc evaluator =
  Code_Preproc.dynamic_value thy postproc (dynamic_evaluator thy evaluator);

fun lift_evaluation thy evaluation' algebra eqngr naming program vs t =
  let
    val (((_, _), (((vs', ty'), t'), deps)), _) =
      ensure_value thy algebra eqngr t (NONE, (naming, program));
  in evaluation' ((original_sorts vs vs', (vs', ty')), t') deps end;

fun lift_evaluator thy evaluator' consts algebra eqngr =
  let
    fun generate_consts thy algebra eqngr =
      fold_map (ensure_const thy algebra eqngr false);
    val (consts', (naming, program)) =
      invoke_generation true thy (algebra, eqngr) generate_consts consts;
    val evaluation' = evaluator' naming program consts';
  in lift_evaluation thy evaluation' algebra eqngr naming program end;

fun lift_evaluator_simple thy evaluator' consts algebra eqngr =
  let
    fun generate_consts thy algebra eqngr =
      fold_map (ensure_const thy algebra eqngr false);
    val (_, (_, program)) =
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
    fun read_const_expr "_" = ([], consts_of thy)
      | read_const_expr s = if String.isSuffix "._" s
          then ([], consts_of_select (Context.this_theory thy (unsuffix "._" s)))
          else ([Code.read_const thy s], []);
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
        path = "", parents = map namify constss }) conn;
  in Present.display_graph prgr end;

local

fun code_thms_cmd thy = code_thms thy o op @ o read_const_exprs thy;
fun code_deps_cmd thy = code_deps thy o op @ o read_const_exprs thy;

in

val _ =
  Outer_Syntax.improper_command @{command_spec "code_thms"}
    "print system of code equations for code"
    (Scan.repeat1 Parse.term_group
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_thms_cmd thy cs) o Toplevel.theory_of)));

val _ =
  Outer_Syntax.improper_command @{command_spec "code_deps"}
    "visualize dependencies of code equations for code"
    (Scan.repeat1 Parse.term_group
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_deps_cmd thy cs) o Toplevel.theory_of)));

end;

end; (*struct*)


structure Basic_Code_Thingol: BASIC_CODE_THINGOL = Code_Thingol;
