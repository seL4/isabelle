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
    | `-> of itype * itype
    | ITyVar of vname;
  datatype iterm =
      IConst of string * (inst list list * itype)
    | IVar of vname
    | `$ of iterm * iterm
    | `|-> of (vname * itype) * iterm
    | INum of IntInf.int * iterm
    | IChar of string (*length one!*) * iterm
    | ICase of ((iterm * itype) * (iterm * iterm) list) * iterm;
        (*((discriminendum term (td), discriminendum type (ty)),
                [(selector pattern (p), body term (t))] (bs)),
                pure term (t0))*)
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
  val unfold_abs: iterm -> (iterm * itype) list * iterm;
  val unfold_let: iterm -> ((iterm * itype) * iterm) list * iterm;
  val unfold_const_app: iterm ->
    ((string * (inst list list * itype)) * iterm list) option;
  val map_pure: (iterm -> 'a) -> iterm -> 'a;
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
    | Classmember of class
    | Classinst of (class * (string * (vname * sort) list))
          * ((class * (string * inst list list)) list
        * (string * iterm) list);
  type code = def Graph.T;
  type transact;
  val empty_code: code;
  val get_def: code -> string -> def;
  val merge_code: code * code -> code;
  val project_code: string list -> code -> code;
  val add_eval_def: string (*shallow name space*) * iterm -> code -> string * code;
  val delete_garbage: string list (*hidden definitions*) -> code -> code;

  val ensure_def: (transact -> def * code) -> bool -> string
    -> string -> transact -> transact;
  val succeed: 'a -> transact -> 'a * code;
  val fail: string -> transact -> 'a * code;
  val message: string -> (transact -> 'a) -> transact -> 'a;
  val start_transact: string option -> (transact -> 'a * transact) -> code -> 'a * code;

  val trace: bool ref;
  val tracing: ('a -> string) -> 'a -> 'a;
  val soft_exc: bool ref;
end;

structure CodegenThingol: CODEGEN_THINGOL =
struct

(** auxiliary **)

val trace = ref false;
fun tracing f x = (if !trace then Output.tracing (f x) else (); x);
val soft_exc = ref true;

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
  | `-> of itype * itype
  | ITyVar of vname;

datatype iterm =
    IConst of string * (inst list list * itype)
  | IVar of vname
  | `$ of iterm * iterm
  | `|-> of (vname * itype) * iterm
  | INum of IntInf.int * iterm
  | IChar of string * iterm
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
    instance (classs, tyco) inst
 *)

val op `--> = Library.foldr (op `->);
val op `$$ = Library.foldl (op `$);
val op `|--> = Library.foldr (op `|->);

val unfold_fun = unfoldr
  (fn op `-> ty => SOME ty
    | _ => NONE);

val unfold_app = unfoldl
  (fn op `$ t => SOME t
    | _ => NONE);

val unfold_abs = unfoldr
  (fn (v, ty) `|-> (t as ICase (((IVar w, _), [(p, t')]), _)) =>
        if v = w then SOME ((p, ty), t') else SOME ((IVar v, ty), t)
    | (v, ty) `|-> t => SOME ((IVar v, ty), t)
    | _ => NONE)

val unfold_let = unfoldr
  (fn ICase (((td, ty), [(p, t)]), _) => SOME (((p, ty), td), t)
    | _ => NONE);

fun unfold_const_app t =
 case unfold_app t
  of (IConst c, ts) => SOME (c, ts)
   | _ => NONE;

fun map_pure f (t as IConst _) =
      f t
  | map_pure f (t as IVar _) =
      f t
  | map_pure f (t as _ `$ _) =
      f t
  | map_pure f (t as _ `|-> _) =
      f t
  | map_pure f (INum (_, t0)) =
      f t0
  | map_pure f (IChar (_, t0)) =
      f t0
  | map_pure f (ICase (_, t0)) =
      f t0;

fun fold_aiterms f (t as IConst _) =
      f t
  | fold_aiterms f (t as IVar _) =
      f t
  | fold_aiterms f (t1 `$ t2) =
      fold_aiterms f t1 #> fold_aiterms f t2
  | fold_aiterms f (t as _ `|-> t') =
      f t #> fold_aiterms f t'
  | fold_aiterms f (INum (_, t0)) =
      fold_aiterms f t0
  | fold_aiterms f (IChar (_, t0)) =
      fold_aiterms f t0
  | fold_aiterms f (ICase (_, t0)) =
      fold_aiterms f t0;

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
      | add vs (INum (_, t)) =
          add vs t
      | add vs (IChar (_, t)) =
          add vs t
      | add vs (ICase (_, t0)) =
          add vs t0
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
  | Classmember of class
  | Classinst of (class * (string * (vname * sort) list))
        * ((class * (string * inst list list)) list
      * (string * iterm) list);
val eq_def = (op =) : def * def -> bool;

type code = def Graph.T;
type transact = Graph.key option * code;
exception FAIL of string list * exn option;


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

fun project_code names code =
  Graph.project (member (op =) (Graph.all_succs code names)) code;

fun delete_garbage hidden code =
  let
    fun is_bot name = case get_def code name
     of Bot => true
      | _ => false;
    val names = subtract (op =) hidden (Graph.keys code);
    val names' = subtract (op =)
      (Graph.all_preds code (filter is_bot names)) names;
  in
    Graph.project (member (op =) names') code
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

fun check_prep_def modl Bot =
      Bot
  | check_prep_def modl (Fun (eqs, d)) =
      Fun (check_funeqs eqs, d)
  | check_prep_def modl (d as Datatype _) =
      d
  | check_prep_def modl (Datatypecons dtco) =
      error "Attempted to add bare datatype constructor"
  | check_prep_def modl (d as Class _) =
      d
  | check_prep_def modl (Classmember _) =
      error "Attempted to add bare class member"
  | check_prep_def modl (d as Classinst ((class, (tyco, arity)), (_, memdefs))) =
      let
        val Class (_, (v, membrs)) = get_def modl class;
        val _ = if length memdefs > length memdefs
          then error "Too many member definitions given"
          else ();
        fun check_memdef (m, _) =
          if AList.defined (op =) memdefs m
          then () else error ("Missing definition for member " ^ quote m);
        val _ = map check_memdef memdefs;
      in d end
  | check_prep_def modl Classinstmember =
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
        add_def_incr true (m, Classmember name)
        #> add_dep (m, name)
        #> add_dep (name, m)
      ) membrs
      )
  | postprocess_def _ =
      I;


(* transaction protocol *)

fun ensure_def defgen strict msg name (dep, modl) =
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
    fun prep_def def modl =
      (check_prep_def modl def, modl);
    fun invoke_generator name defgen modl =
      if ! soft_exc (*that "!" isn't a "not"...*)
      then defgen (SOME name, modl)
        handle FAIL (msgs, exc) =>
                if strict then raise FAIL (msg' :: msgs, exc)
                else (Bot, modl)
             | e => raise
                FAIL (["definition generator for " ^ quote name, msg'], SOME e)
      else defgen (SOME name, modl)
        handle FAIL (msgs, exc) =>
              if strict then raise FAIL (msg' :: msgs, exc)
              else (Bot, modl);
  in
    modl
    |> (if can (get_def modl) name
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

fun succeed some (_, modl) = (some, modl);

fun fail msg (_, modl) = raise FAIL ([msg], NONE);

fun message msg f trns =
  f trns handle FAIL (msgs, exc) =>
    raise FAIL (msg :: msgs, exc);

fun start_transact init f modl =
  let
    fun handle_fail f x =
      (f x
      handle FAIL (msgs, NONE) =>
        (error o cat_lines) ("Code generation failed, while:" :: msgs))
      handle FAIL (msgs, SOME e) =>
        ((Output.error_msg o cat_lines) ("Code generation failed, while:" :: msgs); raise e);
  in
    modl
    |> (if is_some init then ensure_bot (the init) else I)
    |> pair init
    |> handle_fail f
    |-> (fn x => fn (_, modl) => (x, modl))
  end;

fun add_eval_def (shallow, e) code =
  let
    val name = "VALUE";
    val sname = NameSpace.pack [shallow, name];
  in
    code
    |> Graph.new_node (sname, Fun ([([], e)], ([("_", [])], ITyVar "_")))
    |> fold (curry Graph.add_edge sname) (Graph.keys code) (*FIXME*)
    |> pair name
  end;

end; (*struct*)


structure BasicCodegenThingol: BASIC_CODEGEN_THINGOL = CodegenThingol;
