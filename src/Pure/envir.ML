(*  Title:      Pure/envir.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1988  University of Cambridge

Environments.  The type of a term variable / sort of a type variable is
part of its name. The lookup function must apply type substitutions,
since they may change the identity of a variable.
*)

signature ENVIR =
sig
  type tenv
  datatype env = Envir of {asol: tenv, iTs: Type.tyenv, maxidx: int}
  val type_env: env -> Type.tyenv
  exception SAME
  val genvars: string -> env * typ list -> env * term list
  val genvar: string -> env * typ -> env * term
  val lookup: env * (indexname * typ) -> term option
  val lookup': tenv * (indexname * typ) -> term option
  val update: ((indexname * typ) * term) * env -> env
  val empty: int -> env
  val is_empty: env -> bool
  val above: int * env -> bool
  val vupdate: ((indexname * typ) * term) * env -> env
  val alist_of: env -> (indexname * (typ * term)) list
  val norm_term: env -> term -> term
  val norm_term_same: env -> term -> term
  val norm_type: Type.tyenv -> typ -> typ
  val norm_type_same: Type.tyenv -> typ -> typ
  val norm_types_same: Type.tyenv -> typ list -> typ list
  val beta_norm: term -> term
  val head_norm: env -> term -> term
  val fastype: env -> typ list -> term -> typ
  val typ_subst_TVars: Type.tyenv -> typ -> typ
  val subst_TVars: Type.tyenv -> term -> term
  val subst_Vars: tenv -> term -> term
  val subst_vars: Type.tyenv * tenv -> term -> term
end;

structure Envir : ENVIR =
struct

(*updating can destroy environment in 2 ways!!
   (1) variables out of range   (2) circular assignments
*)
type tenv = (typ * term) Vartab.table

datatype env = Envir of
    {maxidx: int,      (*maximum index of vars*)
     asol: tenv,       (*table of assignments to Vars*)
     iTs: Type.tyenv}  (*table of assignments to TVars*)

fun type_env (Envir {iTs, ...}) = iTs;

(*Generate a list of distinct variables.
  Increments index to make them distinct from ALL present variables. *)
fun genvars name (Envir{maxidx, asol, iTs}, Ts) : env * term list =
  let fun genvs (_, [] : typ list) : term list = []
        | genvs (n, [T]) = [ Var((name, maxidx+1), T) ]
        | genvs (n, T::Ts) =
            Var((name ^ radixstring(26,"a",n), maxidx+1), T)
            :: genvs(n+1,Ts)
  in  (Envir{maxidx=maxidx+1, asol=asol, iTs=iTs}, genvs (0,Ts))  end;

(*Generate a variable.*)
fun genvar name (env,T) : env * term =
  let val (env',[v]) = genvars name (env,[T])
  in  (env',v)  end;

fun var_clash ixn T T' = raise TYPE ("Variable " ^
  quote (Syntax.string_of_vname ixn) ^ " has two distinct types",
  [T', T], []);

fun gen_lookup f asol (xname, T) =
  (case Vartab.curried_lookup asol xname of
     NONE => NONE
   | SOME (U, t) => if f (T, U) then SOME t
       else var_clash xname T U);

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
  Envir{maxidx=maxidx, asol=Vartab.curried_update_new (xname, (T, t)) asol, iTs=iTs};

(*The empty environment.  New variables will start with the given index+1.*)
fun empty m = Envir{maxidx=m, asol=Vartab.empty, iTs=Vartab.empty};

(*Test for empty environment*)
fun is_empty (Envir {asol, iTs, ...}) = Vartab.is_empty asol andalso Vartab.is_empty iTs;

(*Determine if the least index updated exceeds lim*)
fun above (lim, Envir {asol, iTs, ...}) =
  (case (Vartab.min_key asol, Vartab.min_key iTs) of
     (NONE, NONE) => true
   | (SOME (_, i), NONE) => i > lim
   | (NONE, SOME (_, i')) => i' > lim
   | (SOME (_, i), SOME (_, i')) => i > lim andalso i' > lim);

(*Update, checking Var-Var assignments: try to suppress higher indexes*)
fun vupdate ((aU as (a, U), t), env as Envir {iTs, ...}) = case t of
      Var (nT as (name', T)) =>
        if a = name' then env     (*cycle!*)
        else if xless(a, name')  then
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

(*raised when norm has no effect on a term, to do sharing instead of copying*)
exception SAME;

fun norm_term1 same (asol,t) : term =
  let fun norm (Var wT) =
            (case lookup' (asol, wT) of
                SOME u => (norm u handle SAME => u)
              | NONE   => raise SAME)
        | norm (Abs(a,T,body)) =  Abs(a, T, norm body)
        | norm (Abs(_,_,body) $ t) = normh(subst_bound (t, body))
        | norm (f $ t) =
            ((case norm f of
               Abs(_,_,body) => normh(subst_bound (t, body))
             | nf => nf $ (norm t handle SAME => t))
            handle SAME => f $ norm t)
        | norm _ =  raise SAME
      and normh t = norm t handle SAME => t
  in (if same then norm else normh) t end

fun normT iTs (Type (a, Ts)) = Type (a, normTs iTs Ts)
  | normT iTs (TFree _) = raise SAME
  | normT iTs (TVar vS) = (case Type.lookup (iTs, vS) of
          SOME U => normTh iTs U
        | NONE => raise SAME)
and normTh iTs T = ((normT iTs T) handle SAME => T)
and normTs iTs [] = raise SAME
  | normTs iTs (T :: Ts) =
      ((normT iTs T :: (normTs iTs Ts handle SAME => Ts))
       handle SAME => T :: normTs iTs Ts);

fun norm_term2 same (asol, iTs, t) : term =
  let fun norm (Const (a, T)) = Const(a, normT iTs T)
        | norm (Free (a, T)) = Free(a, normT iTs T)
        | norm (Var (w, T)) =
            (case lookup2 (iTs, asol) (w, T) of
                SOME u => normh u
              | NONE   => Var(w, normT iTs T))
        | norm (Abs (a, T, body)) =
               (Abs (a, normT iTs T, normh body) handle SAME => Abs (a, T, norm body))
        | norm (Abs(_, _, body) $ t) = normh (subst_bound (t, body))
        | norm (f $ t) =
            ((case norm f of
               Abs(_, _, body) => normh (subst_bound (t, body))
             | nf => nf $ normh t)
            handle SAME => f $ norm t)
        | norm _ =  raise SAME
      and normh t = (norm t) handle SAME => t
  in (if same then norm else normh) t end;

fun gen_norm_term same (env as Envir{asol,iTs,...}) t : term =
  if Vartab.is_empty iTs then norm_term1 same (asol, t)
  else norm_term2 same (asol, iTs, t);

val norm_term = gen_norm_term false;
val norm_term_same = gen_norm_term true;

val beta_norm = norm_term (empty 0);

fun norm_type iTs = normTh iTs;
fun norm_type_same iTs =
  if Vartab.is_empty iTs then raise SAME else normT iTs;

fun norm_types_same iTs =
  if Vartab.is_empty iTs then raise SAME else normTs iTs;


(*Put a term into head normal form for unification.*)

fun head_norm env t =
  let
    fun hnorm (Var vT) = (case lookup (env, vT) of
          SOME u => head_norm env u
        | NONE => raise SAME)
      | hnorm (Abs (a, T, body)) =  Abs (a, T, hnorm body)
      | hnorm (Abs (_, _, body) $ t) =
          head_norm env (subst_bound (t, body))
      | hnorm (f $ t) = (case hnorm f of
          Abs (_, _, body) => head_norm env (subst_bound (t, body))
        | nf => nf $ t)
	  | hnorm _ =  raise SAME
  in hnorm t handle SAME => t end;


(*finds type of term without checking that combinations are consistent
  Ts holds types of bound variables*)
fun fastype (Envir {iTs, ...}) =
let val funerr = "fastype: expected function type";
    fun fast Ts (f $ u) =
	(case fast Ts f of
	   Type ("fun", [_, T]) => T
	 | TVar ixnS =>
		(case Type.lookup (iTs, ixnS) of
		   SOME (Type ("fun", [_, T])) => T
		 | _ => raise TERM (funerr, [f $ u]))
	 | _ => raise TERM (funerr, [f $ u]))
      | fast Ts (Const (_, T)) = T
      | fast Ts (Free (_, T)) = T
      | fast Ts (Bound i) =
	(List.nth (Ts, i)
  	 handle Subscript => raise TERM ("fastype: Bound", [Bound i]))
      | fast Ts (Var (_, T)) = T 
      | fast Ts (Abs (_, T, u)) = T --> fast (T :: Ts) u
in fast end;


(*Substitute for type Vars in a type*)
fun typ_subst_TVars iTs T = if Vartab.is_empty iTs then T else
  let fun subst(Type(a, Ts)) = Type(a, map subst Ts)
        | subst(T as TFree _) = T
        | subst(T as TVar ixnS) =
            (case Type.lookup (iTs, ixnS) of NONE => T | SOME(U) => U)
  in subst T end;

(*Substitute for type Vars in a term*)
val subst_TVars = map_term_types o typ_subst_TVars;

(*Substitute for Vars in a term *)
fun subst_Vars itms t = if Vartab.is_empty itms then t else
  let fun subst (v as Var ixnT) = getOpt (lookup' (itms, ixnT), v)
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

end;
