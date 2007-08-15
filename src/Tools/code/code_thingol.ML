(*  Title:      Tools/code/code_thingol.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Intermediate language ("Thin-gol") representing executable code.
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
  datatype iterm =
      IConst of string * (dict list list * itype list (*types of arguments*))
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
  val fold_constnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;
  val fold_varnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;
  val fold_unbound_varnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;

  datatype def =
      Bot
    | Fun of (iterm list * iterm) list * typscheme
    | Datatype of (vname * sort) list * (string * itype list) list
    | Datatypecons of string
    | Class of (class * string) list * (vname * (string * itype) list)
    | Classop of class
    | Classrel of class * class
    | Classinst of (class * (string * (vname * sort) list))
          * ((class * (string * (string * dict list list))) list
        * (string * iterm) list);
  type code = def Graph.T;
  type transact;
  val empty_code: code;
  val merge_code: code * code -> code;
  val project_code: bool (*delete empty funs*)
    -> string list (*hidden*) -> string list option (*selected*)
    -> code -> code;
  val empty_funs: code -> string list;
  val is_cons: code -> string -> bool;
  val add_eval_def: string (*bind name*) * (iterm * itype) -> code -> code;

  val ensure_def: (string -> string) -> (transact -> def * transact) -> string
    -> string -> transact -> transact;
  val start_transact: (transact -> 'a * transact) -> code -> 'a * code;
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

datatype iterm =
    IConst of string * (dict list list * itype list)
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
    const names (general)   c
    constructor names       co
    class operation names   clsop (op)
    arbitrary name          s

    v, c, co, clsop also annotated with types etc.

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


(** definitions, transactions **)

(* type definitions *)

type typscheme = (vname * sort) list * itype;
datatype def =
    Bot
  | Fun of (iterm list * iterm) list * typscheme
  | Datatype of (vname * sort) list * (string * itype list) list
  | Datatypecons of string
  | Class of (class * string) list * (vname * (string * itype) list)
  | Classop of class
  | Classrel of class * class
  | Classinst of (class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * (string * iterm) list);

type code = def Graph.T;


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

fun add_dep (dep as (name1, name2)) =
  if name1 = name2 then I else Graph.add_edge dep;

val merge_code : code * code -> code = Graph.merge (K true);

fun project_code delete_empty_funs hidden raw_selected code =
  let
    fun is_empty_fun name = case Graph.get_node code name
     of Fun ([], _) => true
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
  Graph.fold (fn (name, (Fun ([], _), _)) => cons name
               | _ => I) code [];

fun is_cons code name = case Graph.get_node code name
 of Datatypecons _ => true
  | _ => false;

fun check_samemodule names =
  fold (fn name =>
    let
      val module_name = (NameSpace.qualifier o NameSpace.qualifier) name
    in
     fn NONE => SOME module_name
      | SOME module_name' => if module_name = module_name' then SOME module_name
          else error ("Inconsistent name prefix for simultanous names: " ^ commas_quote names)
    end
  ) names NONE;

fun check_funeqs eqs =
  (fold (fn (pats, _) =>
    let
      val l = length pats
    in
     fn NONE => SOME l
      | SOME l' => if l = l' then SOME l
          else error "Function definition with different number of arguments"
    end
  ) eqs NONE; eqs);

fun check_prep_def code Bot =
      Bot
  | check_prep_def code (Fun (eqs, d)) =
      Fun (check_funeqs eqs, d)
  | check_prep_def code (d as Datatype _) =
      d
  | check_prep_def code (Datatypecons dtco) =
      error "Attempted to add bare term constructor"
  | check_prep_def code (d as Class _) =
      d
  | check_prep_def code (Classop _) =
      error "Attempted to add bare class operation"
  | check_prep_def code (Classrel _) =
      error "Attempted to add bare class relation"
  | check_prep_def code (d as Classinst ((class, (tyco, arity)), (_, inst_classops))) =
      let
        val Class (_, (_, classops)) = Graph.get_node code class;
        val _ = if length inst_classops > length classops
          then error "Too many class operations given"
          else ();
        fun check_classop (f, _) =
          if AList.defined (op =) inst_classops f
          then () else error ("Missing definition for class operation " ^ quote f);
        val _ = map check_classop classops;
      in d end;

fun postprocess_def (name, Datatype (_, constrs)) =
      tap (fn _ => check_samemodule (name :: map fst constrs))
      #> fold (fn (co, _) =>
        add_def_incr (co, Datatypecons name)
        #> add_dep (co, name)
        #> add_dep (name, co)
      ) constrs
  | postprocess_def (name, Class (classrels, (_, classops))) =
      tap (fn _ => check_samemodule (name :: map fst classops @ map snd classrels))
      #> fold (fn (f, _) =>
        add_def_incr (f, Classop name)
        #> add_dep (f, name)
        #> add_dep (name, f)
      ) classops
      #> fold (fn (superclass, classrel) =>
        add_def_incr (classrel, Classrel (name, superclass))
        #> add_dep (classrel, name)
        #> add_dep (name, classrel)
      ) classrels
  | postprocess_def _ =
      I;


(* transaction protocol *)

type transact = Graph.key option * code;

fun ensure_def labelled_name defgen msg name (dep, code) =
  let
    val msg' = (case dep
     of NONE => msg
      | SOME dep => msg ^ ", required for " ^ labelled_name dep);
    fun add_dp NONE = I
      | add_dp (SOME dep) = add_dep (dep, name);
    fun prep_def def code =
      (check_prep_def code def, code);
    fun add_def false =
          ensure_bot name
          #> add_dp dep
          #> curry defgen (SOME name)
          ##> snd
          #-> (fn def => prep_def def)
          #-> (fn def => add_def_incr (name, def)
          #> postprocess_def (name, def))
      | add_def true =
          add_dp dep;
  in
    code
    |> add_def (can (Graph.get_node code) name)
    |> pair dep
  end;

fun start_transact f code =
  (NONE, code)
  |> f
  |-> (fn x => fn (_, code) => (x, code));

fun add_eval_def (name, (t, ty)) code =
  code
  |> Graph.new_node (name, Fun ([([], t)], ([], ty)))
  |> fold (curry Graph.add_edge name) (Graph.keys code);

end; (*struct*)


structure BasicCodeThingol: BASIC_CODE_THINGOL = CodeThingol;
