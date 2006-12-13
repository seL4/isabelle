(*  Title:      Pure/Tools/codegen_thingol.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Intermediate language ("Thin-gol") representing extracted code.
*)

infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 3 `|->;
infixr 3 `|-->;

signature BASIC_CODEGEN_THINGOL =
sig
  type vname = string;
  datatype inst =
      Instance of string * inst list list
    | Context of class list * (vname * int);
  datatype itype =
      `%% of string * itype list
    | ITyVar of vname;
  datatype iterm =
      IConst of string * (inst list list * itype)
    | IVar of vname
    | `$ of iterm * iterm
    | `|-> of (vname * itype) * iterm
    | INum of IntInf.int
    | IChar of string (*length one!*)
    | ICase of (iterm * itype) * (iterm * iterm) list;
        (*(discriminendum term (td), discriminendum type (ty)),
                [(selector pattern (p), body term (t))] (bs))*)
  val `-> : itype * itype -> itype;
  val `--> : itype list * itype -> itype;
  val `$$ : iterm * iterm list -> iterm;
  val `|--> : (vname * itype) list * iterm -> iterm;
  type typscheme = (vname * sort) list * itype;
end;

signature CODEGEN_THINGOL =
sig
  include BASIC_CODEGEN_THINGOL;
  val unfoldl: ('a -> ('a * 'b) option) -> 'a -> 'a * 'b list;
  val unfoldr: ('a -> ('b * 'a) option) -> 'a -> 'b list * 'a;
  val unfold_fun: itype -> itype list * itype;
  val unfold_app: iterm -> iterm * iterm list;
  val unfold_abs: iterm -> ((vname * iterm option) * itype) list * iterm;
  val unfold_let: iterm -> ((iterm * itype) * iterm) list * iterm;
  val unfold_const_app: iterm ->
    ((string * (inst list list * itype)) * iterm list) option;
  val eta_expand: (string * (inst list list * itype)) * iterm list -> int -> iterm;
  val fold_constnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;
  val fold_varnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;
  val fold_unbound_varnames: (string -> 'a -> 'a) -> iterm -> 'a -> 'a;

  datatype def =
      Bot
    | Fun of (iterm list * iterm) list * typscheme
    | Datatype of (vname * sort) list * (string * itype list) list
    | Datatypecons of string
    | Class of class list * (vname * (string * itype) list)
    | Classop of class
    | Classinst of (class * (string * (vname * sort) list))
          * ((class * (string * inst list list)) list
        * (string * iterm) list);
  type code = def Graph.T;
  type transact;
  val empty_code: code;
  val get_def: code -> string -> def;
  val merge_code: code * code -> code;
  val project_code: string list (*hidden*) -> string list option (*selected*)
    -> code -> code;
  val add_eval_def: string (*bind name*) * iterm -> code -> code;

  val ensure_def: (transact -> def * code) -> bool -> string
    -> string -> transact -> transact;
  val succeed: 'a -> transact -> 'a * code;
  val fail: string -> transact -> 'a * code;
  val message: string -> (transact -> 'a) -> transact -> 'a;
  val start_transact: string option -> (transact -> 'a * transact) -> code -> 'a * code;

  type var_ctxt;
  val make_vars: string list -> var_ctxt;
  val intro_vars: string list -> var_ctxt -> var_ctxt;
  val lookup_var: var_ctxt -> string -> string;

  val trace: bool ref;
  val tracing: ('a -> string) -> 'a -> 'a;
end;

structure CodegenThingol: CODEGEN_THINGOL =
struct

(** auxiliary **)

val trace = ref false;
fun tracing f x = (if !trace then Output.tracing (f x) else (); x);

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

datatype inst =
    Instance of string * inst list list
  | Context of class list * (vname * int);

datatype itype =
    `%% of string * itype list
  | ITyVar of vname;

datatype iterm =
    IConst of string * (inst list list * itype)
  | IVar of vname
  | `$ of iterm * iterm
  | `|-> of (vname * itype) * iterm
  | INum of IntInf.int
  | IChar of string
  | ICase of (iterm * itype) * (iterm * iterm) list;
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

val unfold_abs = unfoldr
  (fn (v, ty) `|-> (t as ICase ((IVar w, _), [(p, t')])) =>
        if v = w then SOME (((v, SOME p), ty), t') else SOME (((v, NONE), ty), t)
    | (v, ty) `|-> t => SOME (((v, NONE), ty), t)
    | _ => NONE)

val unfold_let = unfoldr
  (fn ICase ((td, ty), [(p, t)]) => SOME (((p, ty), td), t)
    | _ => NONE);

fun unfold_const_app t =
 case unfold_app t
  of (IConst c, ts) => SOME (c, ts)
   | _ => NONE;

fun fold_aiterms f (t as IConst _) =
      f t
  | fold_aiterms f (t as IVar _) =
      f t
  | fold_aiterms f (t1 `$ t2) =
      fold_aiterms f t1 #> fold_aiterms f t2
  | fold_aiterms f (t as _ `|-> t') =
      f t #> fold_aiterms f t'
  | fold_aiterms f (t as INum _) =
      f t
  | fold_aiterms f (t as IChar _) =
      f t
  | fold_aiterms f (ICase ((td, _), bs)) =
      fold_aiterms f td #> fold (fn (p, t) => fold_aiterms f p #> fold_aiterms f t) bs;

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
    fun add _ (IConst _) =
          I
      | add vs (IVar v) =
          if not (member (op =) vs v) then f v else I
      | add vs (t1 `$ t2) =
          add vs t1 #> add vs t2
      | add vs ((v, _) `|-> t) =
          add (insert (op =) v vs) t
      | add vs (INum _) =
          I
      | add vs (IChar _) =
          I
      | add vs (ICase ((td, _), bs)) =
          add vs td #> fold (fn (p, t) => add vs p #> add vs t) bs;
  in add [] end;

fun eta_expand (c as (_, (_, ty)), ts) k =
  let
    val j = length ts;
    val l = k - j;
    val tys = (curry Library.take l o curry Library.drop j o fst o unfold_fun) ty;
    val ctxt = (fold o fold_varnames) Name.declare ts Name.context;
    val vs_tys = Name.names ctxt "a" tys;
  in vs_tys `|--> IConst c `$$ ts @ map (fn (v, _) => IVar v) vs_tys end;


(** definitions, transactions **)

(* type definitions *)

type typscheme = (vname * sort) list * itype;
datatype def =
    Bot
  | Fun of (iterm list * iterm) list * typscheme
  | Datatype of (vname * sort) list * (string * itype list) list
  | Datatypecons of string
  | Class of class list * (vname * (string * itype) list)
  | Classop of class
  | Classinst of (class * (string * (vname * sort) list))
        * ((class * (string * inst list list)) list
      * (string * iterm) list);
val eq_def = (op =) : def * def -> bool;

type code = def Graph.T;
type transact = Graph.key option * code;
exception FAIL of string list;


(* abstract code *)

val empty_code = Graph.empty : code; (*read: "depends on"*)

val get_def = Graph.get_node;

fun ensure_bot name = Graph.default_node (name, Bot);

fun add_def_incr strict (name, Bot) code =
      (case the_default Bot (try (get_def code) name)
       of Bot => if strict then error "Attempted to add Bot to code"
            else Graph.map_node name (K Bot) code
        | _ => code)
  | add_def_incr _ (name, def) code =
      (case try (get_def code) name
       of NONE => Graph.new_node (name, def) code
        | SOME Bot => Graph.map_node name (K def) code
        | SOME def' => if eq_def (def, def')
            then code
            else error ("Tried to overwrite definition " ^ quote name));

fun add_dep (dep as (name1, name2)) =
  if name1 = name2 then I else Graph.add_edge dep;

val merge_code = Graph.join (fn _ => fn def12 => if eq_def def12 then fst def12 else Bot);

fun project_code hidden raw_selected code =
  let
    fun is_bot name = case get_def code name
     of Bot => true
      | _ => false;
    val names = subtract (op =) hidden (Graph.keys code);
    val deleted = Graph.all_preds code (filter is_bot names);
    val selected = case raw_selected
     of NONE => names |> subtract (op =) deleted 
      | SOME sel => sel
          |> subtract (op =) deleted
          |> subtract (op =) hidden
          |> Graph.all_succs code
          |> subtract (op =) deleted
          |> subtract (op =) hidden;
  in
    code
    |> Graph.project (member (op =) selected)
  end;

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
      error "Attempted to add bare datatype constructor"
  | check_prep_def code (d as Class _) =
      d
  | check_prep_def code (Classop _) =
      error "Attempted to add bare class member"
  | check_prep_def code (d as Classinst ((class, (tyco, arity)), (_, memdefs))) =
      let
        val Class (_, (v, membrs)) = get_def code class;
        val _ = if length memdefs > length memdefs
          then error "Too many member definitions given"
          else ();
        fun check_memdef (m, _) =
          if AList.defined (op =) memdefs m
          then () else error ("Missing definition for member " ^ quote m);
        val _ = map check_memdef memdefs;
      in d end
  | check_prep_def code Classinstmember =
      error "Attempted to add bare class instance member";

fun postprocess_def (name, Datatype (_, constrs)) =
      (check_samemodule (name :: map fst constrs);
      fold (fn (co, _) =>
        add_def_incr true (co, Datatypecons name)
        #> add_dep (co, name)
        #> add_dep (name, co)
      ) constrs
      )
  | postprocess_def (name, Class (_, (_, membrs))) =
      (check_samemodule (name :: map fst membrs);
      fold (fn (m, _) =>
        add_def_incr true (m, Classop name)
        #> add_dep (m, name)
        #> add_dep (name, m)
      ) membrs
      )
  | postprocess_def _ =
      I;


(* transaction protocol *)

fun ensure_def defgen strict msg name (dep, code) =
  let
    (*FIXME represent dependencies as tuple (name, name -> string), for better error msgs*)
    val msg' = (case dep
     of NONE => msg
      | SOME dep => msg ^ ", required for " ^ quote dep)
      ^ (if strict then " (strict)" else " (non-strict)");
    fun add_dp NONE = I
      | add_dp (SOME dep) =
          tracing (fn _ => "adding dependency " ^ quote dep ^ " -> " ^ quote name)
          #> add_dep (dep, name);
    fun prep_def def code =
      (check_prep_def code def, code);
    fun invoke_generator name defgen code =
      defgen (SOME name, code)
        handle FAIL msgs =>
          if strict then raise FAIL (msg' :: msgs)
          else (Bot, code);
  in
    code
    |> (if can (get_def code) name
        then
          tracing (fn _ => "asserting node " ^ quote name)
          #> add_dp dep
        else
          tracing (fn _ => "allocating node " ^ quote name ^ (if strict then " (strict)" else " (non-strict)"))
          #> ensure_bot name
          #> add_dp dep
          #> tracing (fn _ => "creating node " ^ quote name)
          #> invoke_generator name defgen
          #-> (fn def => prep_def def)
          #-> (fn def =>
             tracing (fn _ => "adding")
          #> add_def_incr strict (name, def)
          #> tracing (fn _ => "postprocessing")
          #> postprocess_def (name, def)
          #> tracing (fn _ => "adding done")
       ))
    |> pair dep
  end;

fun succeed some (_, code) = (some, code);

fun fail msg (_, code) = raise FAIL [msg];

fun message msg f trns =
  f trns handle FAIL msgs =>
    raise FAIL (msg :: msgs);

fun start_transact init f code =
  let
    fun handle_fail f x =
      (f x
      handle FAIL msgs =>
        (error o cat_lines) ("Code generation failed, while:" :: msgs))
  in
    code
    |> (if is_some init then ensure_bot (the init) else I)
    |> pair init
    |> handle_fail f
    |-> (fn x => fn (_, code) => (x, code))
  end;

fun add_eval_def (name, t) code =
  code
  |> Graph.new_node (name, Fun ([([], t)], ([("_", [])], ITyVar "_")))
  |> fold (curry Graph.add_edge name) (Graph.keys code);


(** variable name contexts **)

type var_ctxt = string Symtab.table * Name.context;

fun make_vars names = (fold (fn name => Symtab.update_new (name, name)) names Symtab.empty,
  Name.make_context names);

fun intro_vars names (namemap, namectxt) =
  let
    val (names', namectxt') = Name.variants names namectxt;
    val namemap' = fold2 (curry Symtab.update) names names' namemap;
  in (namemap', namectxt') end;

fun lookup_var (namemap, _) name = case Symtab.lookup namemap name
 of SOME name' => name'
  | NONE => error ("invalid name in context: " ^ quote name);

end; (*struct*)


structure BasicCodegenThingol: BASIC_CODEGEN_THINGOL = CodegenThingol;
