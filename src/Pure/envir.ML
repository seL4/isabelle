(*  Title:      Pure/envir.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1988  University of Cambridge
*)

(*Environments.  They don't take account that typ is part of variable name.
                 Therefore we check elsewhere that  two variables with same
		 names and different types cannot occur.
*)


signature ENVIR =
sig
  datatype env = Envir of {asol: term Vartab.table, iTs: typ Vartab.table, maxidx: int}
  val alist_of		: env -> (indexname * term) list
  val empty		: int->env
  val is_empty		: env -> bool
  val above		: int * env -> bool
  val genvar		: string -> env * typ -> env * term
  val genvars		: string -> env * typ list -> env * term list
  val lookup		: env * indexname -> term option
  val norm_term		: env -> term -> term
  val update		: (indexname * term) * env -> env
  val vupdate		: (indexname * term) * env -> env
end;

structure Envir : ENVIR =
struct

(*updating can destroy environment in 2 ways!!
   (1) variables out of range   (2) circular assignments
*)
datatype env = Envir of
    {maxidx: int,               (*maximum index of vars*)
     asol: term Vartab.table,   (*table of assignments to Vars*)
     iTs: typ Vartab.table}     (*table of assignments to TVars*)


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

fun lookup (Envir{asol,...}, xname) : term option = Vartab.lookup (asol, xname);

fun update ((xname, t), Envir{maxidx, asol, iTs}) =
  Envir{maxidx=maxidx, asol=Vartab.update_new ((xname,t), asol), iTs=iTs};

(*The empty environment.  New variables will start with the given index+1.*)
fun empty m = Envir{maxidx=m, asol=Vartab.empty, iTs=Vartab.empty};

(*Test for empty environment*)
fun is_empty (Envir {asol, iTs, ...}) = Vartab.is_empty asol andalso Vartab.is_empty iTs;

(*Determine if the least index updated exceeds lim*)
fun above (lim, Envir {asol, iTs, ...}) =
  (case (Vartab.min_key asol, Vartab.min_key iTs) of
     (None, None) => true
   | (Some (_, i), None) => i > lim
   | (None, Some (_, i')) => i' > lim
   | (Some (_, i), Some (_, i')) => i > lim andalso i' > lim);

(*Update, checking Var-Var assignments: try to suppress higher indexes*)
fun vupdate((a,t), env) = case t of
      Var(name',T) =>
        if a=name' then env     (*cycle!*)
        else if xless(a, name')  then
           (case lookup(env,name') of  (*if already assigned, chase*)
                None => update((name', Var(a,T)), env)
              | Some u => vupdate((a,u), env))
        else update((a,t), env)
    | _ => update((a,t), env);


(*Convert environment to alist*)
fun alist_of (Envir{asol,...}) = Vartab.dest asol;


(*** Beta normal form for terms (not eta normal form).
     Chases variables in env;  Does not exploit sharing of variable bindings
     Does not check types, so could loop. ***)

(*raised when norm has no effect on a term, to do sharing instead of copying*)
exception SAME;

fun norm_term1 (asol,t) : term =
  let fun norm (Var (w,T)) =
	    (case Vartab.lookup (asol, w) of
		Some u => (norm u handle SAME => u)
	      | None   => raise SAME)
	| norm (Abs(a,T,body)) =  Abs(a, T, norm body)
	| norm (Abs(_,_,body) $ t) = normh(subst_bound (t, body))
	| norm (f $ t) =
	    ((case norm f of
	       Abs(_,_,body) => normh(subst_bound (t, body))
	     | nf => nf $ (norm t handle SAME => t))
	    handle SAME => f $ norm t)
	| norm _ =  raise SAME
      and normh t = norm t handle SAME => t
  in normh t end

and norm_term2(asol,iTs,t) : term =
  let fun normT(Type(a,Ts)) = Type(a, normTs Ts)
	| normT(TFree _) = raise SAME
	| normT(TVar(v,_)) = (case Vartab.lookup (iTs, v) of
		Some(U) => normTh U
	      | None => raise SAME)
      and normTh T = ((normT T) handle SAME => T)
      and normTs([]) = raise SAME
	| normTs(T::Ts) = ((normT T :: (normTs Ts handle SAME => Ts))
			   handle SAME => T :: normTs Ts)
      and norm(Const(a,T)) = Const(a, normT T)
	| norm(Free(a,T)) = Free(a, normT T)
	| norm(Var (w,T)) =
	    (case Vartab.lookup (asol, w) of
		Some u => normh u
	      | None   => Var(w,normT T))
	| norm(Abs(a,T,body)) =
	      (Abs(a,normT T,normh body) handle SAME => Abs(a, T, norm body))
	| norm(Abs(_,_,body) $ t) = normh(subst_bound (t, body))
	| norm(f $ t) =
	    ((case norm f of
	       Abs(_,_,body) => normh(subst_bound (t, body))
	     | nf => nf $ normh t)
	    handle SAME => f $ norm t)
	| norm _ =  raise SAME
      and normh t = (norm t) handle SAME => t
  in normh t end;

(*curried version might be slower in recursive calls*)
fun norm_term (env as Envir{asol,iTs,...}) t : term =
        if Vartab.is_empty iTs then norm_term1(asol, t) else norm_term2(asol,iTs, t)

end;

