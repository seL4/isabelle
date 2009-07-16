(*  Title:      Pure/envir.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Environments.  The type of a term variable / sort of a type variable is
part of its name. The lookup function must apply type substitutions,
since they may change the identity of a variable.
*)

signature ENVIR =
sig
  type tenv = (typ * term) Vartab.table
  datatype env = Envir of {asol: tenv, iTs: Type.tyenv, maxidx: int}
  val type_env: env -> Type.tyenv
  val insert_sorts: env -> sort list -> sort list
  val genvars: string -> env * typ list -> env * term list
  val genvar: string -> env * typ -> env * term
  val lookup: env * (indexname * typ) -> term option
  val lookup': tenv * (indexname * typ) -> term option
  val update: ((indexname * typ) * term) * env -> env
  val empty: int -> env
  val is_empty: env -> bool
  val above: env -> int -> bool
  val vupdate: ((indexname * typ) * term) * env -> env
  val alist_of: env -> (indexname * (typ * term)) list
  val norm_type_same: Type.tyenv -> typ Same.operation
  val norm_types_same: Type.tyenv -> typ list Same.operation
  val norm_type: Type.tyenv -> typ -> typ
  val norm_term_same: env -> term Same.operation
  val norm_term: env -> term -> term
  val beta_norm: term -> term
  val head_norm: env -> term -> term
  val eta_contract: term -> term
  val beta_eta_contract: term -> term
  val fastype: env -> typ list -> term -> typ
  val typ_subst_TVars: Type.tyenv -> typ -> typ
  val subst_TVars: Type.tyenv -> term -> term
  val subst_Vars: tenv -> term -> term
  val subst_vars: Type.tyenv * tenv -> term -> term
  val expand_atom: typ -> typ * term -> term
  val expand_term: (term -> (typ * term) option) -> term -> term
  val expand_term_frees: ((string * typ) * term) list -> term -> term
end;

structure Envir : ENVIR =
struct

(*updating can destroy environment in 2 ways!!
   (1) variables out of range   (2) circular assignments
*)
type tenv = (typ * term) Vartab.table;

datatype env = Envir of
 {maxidx: int,      (*maximum index of vars*)
  asol: tenv,       (*assignments to Vars*)
  iTs: Type.tyenv}; (*assignments to TVars*)

fun type_env (Envir {iTs, ...}) = iTs;

(*NB: type unification may invent new sorts*)
val insert_sorts = Vartab.fold (fn (_, (_, T)) => Sorts.insert_typ T) o type_env;

(*Generate a list of distinct variables.
  Increments index to make them distinct from ALL present variables. *)
fun genvars name (Envir{maxidx, asol, iTs}, Ts) : env * term list =
  let
    fun genvs (_, [] : typ list) : term list = []
      | genvs (n, [T]) = [Var ((name, maxidx + 1), T)]
      | genvs (n, T :: Ts) =
          Var ((name ^ radixstring (26, "a" , n), maxidx + 1), T)
            :: genvs (n + 1, Ts);
  in (Envir {maxidx = maxidx + 1, asol = asol, iTs = iTs}, genvs (0, Ts)) end;

(*Generate a variable.*)
fun genvar name (env, T) : env * term =
  let val (env', [v]) = genvars name (env, [T])
  in (env', v) end;

fun var_clash ixn T T' = raise TYPE ("Variable " ^
    quote (Term.string_of_vname ixn) ^ " has two distinct types",
    [T', T], []);

fun gen_lookup f asol (xname, T) =
  (case Vartab.lookup asol xname of
    NONE => NONE
  | SOME (U, t) => if f (T, U) then SOME t else var_clash xname T U);

(* When dealing with environments produced by matching instead *)
(* of unification, there is no need to chase assigned TVars.   *)
(* In this case, we can simply ignore the type substitution    *)
(* and use = instead of eq_type.                               *)

fun lookup' (asol, p) = gen_lookup op = asol p;

fun lookup2 (iTs, asol) p =
  if Vartab.is_empty iTs then lookup' (asol, p)
  else gen_lookup (Type.eq_type iTs) asol p;

fun lookup (Envir {asol, iTs, ...}, p) = lookup2 (iTs, asol) p;

fun update (((xname, T), t), Envir {maxidx, asol, iTs}) =
  Envir {maxidx = maxidx, asol = Vartab.update_new (xname, (T, t)) asol, iTs = iTs};

(*The empty environment.  New variables will start with the given index+1.*)
fun empty m = Envir {maxidx = m, asol = Vartab.empty, iTs = Vartab.empty};

(*Test for empty environment*)
fun is_empty (Envir {asol, iTs, ...}) = Vartab.is_empty asol andalso Vartab.is_empty iTs;

(*Determine if the least index updated exceeds lim*)
fun above (Envir {asol, iTs, ...}) lim =
  (case Vartab.min_key asol of SOME (_, i) => i > lim | NONE => true) andalso
  (case Vartab.min_key iTs of SOME (_, i) => i > lim | NONE => true);

(*Update, checking Var-Var assignments: try to suppress higher indexes*)
fun vupdate ((aU as (a, U), t), env as Envir {iTs, ...}) = case t of
      Var (nT as (name', T)) =>
        if a = name' then env     (*cycle!*)
        else if TermOrd.indexname_ord (a, name') = LESS then
           (case lookup (env, nT) of  (*if already assigned, chase*)
                NONE => update ((nT, Var (a, T)), env)
              | SOME u => vupdate ((aU, u), env))
        else update ((aU, t), env)
    | _ => update ((aU, t), env);


(*Convert environment to alist*)
fun alist_of (Envir{asol,...}) = Vartab.dest asol;


(*** Beta normal form for terms (not eta normal form).
     Chases variables in env;  Does not exploit sharing of variable bindings
     Does not check types, so could loop. ***)

local

fun norm_type0 iTs : typ Same.operation =
  let
    fun norm (Type (a, Ts)) = Type (a, Same.map norm Ts)
      | norm (TFree _) = raise Same.SAME
      | norm (TVar v) =
          (case Type.lookup iTs v of
            SOME U => Same.commit norm U
          | NONE => raise Same.SAME);
  in norm end;

fun norm_term1 asol : term Same.operation =
  let
    fun norm (Var v) =
          (case lookup' (asol, v) of
            SOME u => Same.commit norm u
          | NONE => raise Same.SAME)
      | norm (Abs (a, T, body)) =  Abs (a, T, norm body)
      | norm (Abs (_, _, body) $ t) = Same.commit norm (subst_bound (t, body))
      | norm (f $ t) =
          ((case norm f of
             Abs (_, _, body) => Same.commit norm (subst_bound (t, body))
           | nf => nf $ Same.commit norm t)
          handle Same.SAME => f $ norm t)
      | norm _ = raise Same.SAME;
  in norm end;

fun norm_term2 asol iTs : term Same.operation =
  let
    val normT = norm_type0 iTs;
    fun norm (Const (a, T)) = Const (a, normT T)
      | norm (Free (a, T)) = Free (a, normT T)
      | norm (Var (xi, T)) =
          (case lookup2 (iTs, asol) (xi, T) of
            SOME u => Same.commit norm u
          | NONE => Var (xi, normT T))
      | norm (Abs (a, T, body)) =
          (Abs (a, normT T, Same.commit norm body)
            handle Same.SAME => Abs (a, T, norm body))
      | norm (Abs (_, _, body) $ t) = Same.commit norm (subst_bound (t, body))
      | norm (f $ t) =
          ((case norm f of
             Abs (_, _, body) => Same.commit norm (subst_bound (t, body))
           | nf => nf $ Same.commit norm t)
          handle Same.SAME => f $ norm t)
      | norm _ = raise Same.SAME;
  in norm end;

in

fun norm_type_same iTs T =
  if Vartab.is_empty iTs then raise Same.SAME
  else norm_type0 iTs T;

fun norm_types_same iTs Ts =
  if Vartab.is_empty iTs then raise Same.SAME
  else Same.map (norm_type0 iTs) Ts;

fun norm_type iTs T = norm_type_same iTs T handle Same.SAME => T;

fun norm_term_same (Envir {asol, iTs, ...}) =
  if Vartab.is_empty iTs then norm_term1 asol
  else norm_term2 asol iTs;

fun norm_term envir t = norm_term_same envir t handle Same.SAME => t;
fun beta_norm t = if Term.has_abs t then norm_term (empty 0) t else t;

end;


(*Put a term into head normal form for unification.*)

fun head_norm env =
  let
    fun norm (Var v) =
        (case lookup (env, v) of
          SOME u => head_norm env u
        | NONE => raise Same.SAME)
      | norm (Abs (a, T, body)) = Abs (a, T, norm body)
      | norm (Abs (_, _, body) $ t) = Same.commit norm (subst_bound (t, body))
      | norm (f $ t) =
          (case norm f of
            Abs (_, _, body) => Same.commit norm (subst_bound (t, body))
          | nf => nf $ t)
      | norm _ = raise Same.SAME;
  in Same.commit norm end;


(*Eta-contract a term (fully)*)

local

fun decr lev (Bound i) = if i >= lev then Bound (i - 1) else raise Same.SAME
  | decr lev (Abs (a, T, body)) = Abs (a, T, decr (lev + 1) body)
  | decr lev (t $ u) = (decr lev t $ decrh lev u handle Same.SAME => t $ decr lev u)
  | decr _ _ = raise Same.SAME
and decrh lev t = (decr lev t handle Same.SAME => t);

fun eta (Abs (a, T, body)) =
    ((case eta body of
        body' as (f $ Bound 0) =>
          if loose_bvar1 (f, 0) then Abs (a, T, body')
          else decrh 0 f
     | body' => Abs (a, T, body')) handle Same.SAME =>
        (case body of
          f $ Bound 0 =>
            if loose_bvar1 (f, 0) then raise Same.SAME
            else decrh 0 f
        | _ => raise Same.SAME))
  | eta (t $ u) = (eta t $ Same.commit eta u handle Same.SAME => t $ eta u)
  | eta _ = raise Same.SAME;

in

fun eta_contract t =
  if Term.has_abs t then Same.commit eta t else t;

val beta_eta_contract = eta_contract o beta_norm;

end;


(*finds type of term without checking that combinations are consistent
  Ts holds types of bound variables*)
fun fastype (Envir {iTs, ...}) =
let val funerr = "fastype: expected function type";
    fun fast Ts (f $ u) =
        (case fast Ts f of
           Type ("fun", [_, T]) => T
         | TVar ixnS =>
                (case Type.lookup iTs ixnS of
                   SOME (Type ("fun", [_, T])) => T
                 | _ => raise TERM (funerr, [f $ u]))
         | _ => raise TERM (funerr, [f $ u]))
      | fast Ts (Const (_, T)) = T
      | fast Ts (Free (_, T)) = T
      | fast Ts (Bound i) =
        (nth Ts i
         handle Subscript => raise TERM ("fastype: Bound", [Bound i]))
      | fast Ts (Var (_, T)) = T
      | fast Ts (Abs (_, T, u)) = T --> fast (T :: Ts) u
in fast end;


(*Substitute for type Vars in a type*)
fun typ_subst_TVars iTs T = if Vartab.is_empty iTs then T else
  let fun subst(Type(a, Ts)) = Type(a, map subst Ts)
        | subst(T as TFree _) = T
        | subst(T as TVar ixnS) =
            (case Type.lookup iTs ixnS of NONE => T | SOME(U) => U)
  in subst T end;

(*Substitute for type Vars in a term*)
val subst_TVars = map_types o typ_subst_TVars;

(*Substitute for Vars in a term *)
fun subst_Vars itms t = if Vartab.is_empty itms then t else
  let fun subst (v as Var ixnT) = the_default v (lookup' (itms, ixnT))
        | subst (Abs (a, T, t)) = Abs (a, T, subst t)
        | subst (f $ t) = subst f $ subst t
        | subst t = t
  in subst t end;

(*Substitute for type/term Vars in a term *)
fun subst_vars (iTs, itms) =
  if Vartab.is_empty iTs then subst_Vars itms else
  let fun subst (Const (a, T)) = Const(a, typ_subst_TVars iTs T)
        | subst (Free (a, T)) = Free (a, typ_subst_TVars iTs T)
        | subst (Var (ixn, T)) = (case lookup' (itms, (ixn, T)) of
            NONE   => Var (ixn, typ_subst_TVars iTs T)
          | SOME t => t)
        | subst (b as Bound _) = b
        | subst (Abs (a, T, t)) = Abs(a, typ_subst_TVars iTs T, subst t)
        | subst (f $ t) = subst f $ subst t
  in subst end;


(* expand defined atoms -- with local beta reduction *)

fun expand_atom T (U, u) =
  subst_TVars (Type.raw_match (U, T) Vartab.empty) u
  handle Type.TYPE_MATCH => raise TYPE ("expand_atom: ill-typed replacement", [T, U], [u]);

fun expand_term get =
  let
    fun expand tm =
      let
        val (head, args) = Term.strip_comb tm;
        val args' = map expand args;
        fun comb head' = Term.list_comb (head', args');
      in
        (case head of
          Abs (x, T, t) => comb (Abs (x, T, expand t))
        | _ =>
            (case get head of
              SOME def => Term.betapplys (expand_atom (Term.fastype_of head) def, args')
            | NONE => comb head)
        | _ => comb head)
      end;
  in expand end;

fun expand_term_frees defs =
  let
    val eqs = map (fn ((x, U), u) => (x, (U, u))) defs;
    val get = fn Free (x, _) => AList.lookup (op =) eqs x | _ => NONE;
  in expand_term get end;

end;
