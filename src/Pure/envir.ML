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
  type 'a xolist
  exception ENVIR of string * indexname;
  datatype env = Envir of {asol: term xolist, iTs: typ xolist, maxidx: int}
  val alist_of		: env -> (indexname * term) list
  val alist_of_olist	: 'a xolist -> (indexname * 'a) list
  val empty		: int->env
  val is_empty		: env -> bool
  val above		: int * env -> bool
  val genvar		: string -> env * typ -> env * term
  val genvars		: string -> env * typ list -> env * term list
  val lookup		: env * indexname -> term option
  val norm_term		: env -> term -> term
  val null_olist	: 'a xolist
  val olist_of_alist	: (indexname * 'a) list -> 'a xolist
  val update		: (indexname * term) * env -> env
  val vupdate		: (indexname * term) * env -> env
end;

structure Envir : ENVIR =
struct

(*association lists with keys in ascending order, no repeated keys*)
type 'a xolist = (indexname * 'a) list;


exception ENVIR of string * indexname;

(*look up key in ordered list*)
fun xsearch ([], key) = None
  | xsearch (((keyi,xi)::pairs), key) =
      if xless(keyi,key) then xsearch (pairs, key)
      else if key=keyi then Some xi
      else None;

(*insert pair in ordered list, reject if key already present*)
fun xinsert_new (newpr as (key, x), al) =
  let fun insert [] = [newpr]
        | insert ((pair as (keyi,xi)) :: pairs) =
            if xless(keyi,key) then pair :: insert pairs
            else if key=keyi then
                raise ENVIR("xinsert_new: already present",key)
            else newpr::pair::pairs
  in  (insert al)  end;

(*insert pair in ordered list, overwrite if key already present*)
fun xinsert (newpr as (key, x), al) =
  let fun insert [] = [newpr]
        | insert ((pair as (keyi,xi)) :: pairs) =
            if xless(keyi,key) then pair :: insert pairs
            else if key=keyi then newpr::pairs
            else newpr::pair::pairs
  in  (insert al)  end;

(*apply function to the contents part of each pair*)
fun xmap f (pairs) =
  let fun xmp [] = []
        | xmp ((key,x)::pairs) = (key, f x) :: xmp pairs
  in (xmp pairs)  end;

(*allows redefinition of a key by "join"ing the contents parts*)
fun xmerge_olists join (pairsa, pairsb) =
  let fun xmrg ([],pairsb) = pairsb
        | xmrg (pairsa,[]) = pairsa
        | xmrg ((keya,x)::pairsa, (keyb,y)::pairsb) =
            if xless(keya,keyb) then
                (keya,x) :: xmrg (pairsa, (keyb,y)::pairsb)
            else if xless(keyb,keya) then
                (keyb,y) :: xmrg ((keya,x)::pairsa, pairsb)
            else (*equal*)  (keya, join(x,y)) :: xmrg (pairsa, pairsb)
  in  (xmrg (pairsa,pairsb))  end;

val null_olist = [];

fun alist_of_olist (pairs) = pairs;

fun olist_of_alist pairs = foldr xinsert (pairs, []);



(*updating can destroy environment in 2 ways!!
   (1) variables out of range   (2) circular assignments
*)
datatype env = Envir of
    {maxidx: int,               (*maximum index of vars*)
     asol: term xolist,         (*table of assignments to Vars*)
     iTs:  typ  xolist}         (*table of assignments to TVars*)


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

fun lookup (Envir{asol,...}, xname) : term option = xsearch (asol,xname);

fun update ((xname, t), Envir{maxidx, asol, iTs}) =
  Envir{maxidx=maxidx, asol=xinsert_new ((xname,t), asol), iTs=iTs};

(*The empty environment.  New variables will start with the given index.*)
fun empty m = Envir{maxidx=m, asol=null_olist, iTs=[]};

(*Test for empty environment*)
fun is_empty (Envir {asol = [], iTs = [], ...}) = true
  | is_empty _ = false;

(*Determine if the least index updated exceeds lim*)
fun above (lim, Envir {asol, iTs, ...}) = 
    let fun upd [] = true
	  | upd (i::is) = i>lim andalso upd is
    in  upd (map (#2 o #1) asol @ (map (#2 o #1) iTs))
    end;

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
fun alist_of (Envir{maxidx,asol,...}) = alist_of_olist asol;


(*** Beta normal form for terms (not eta normal form).
     Chases variables in env;  Does not exploit sharing of variable bindings
     Does not check types, so could loop. ***)

(*raised when norm has no effect on a term, to do sharing instead of copying*)
exception SAME;

fun norm_term1 (asol,t) : term =
  let fun norm (Var (w,T)) =
	    (case xsearch(asol,w) of
		Some u => normh u
	      | None   => raise SAME)
	| norm (Abs(a,T,body)) =  Abs(a, T, norm body)
	| norm (Abs(_,_,body) $ t) = normh(subst_bounds([t], body))
	| norm (f $ t) =
	    ((case norm f of
	       Abs(_,_,body) => normh(subst_bounds([t], body))
	     | nf => nf $ normh t)
	    handle SAME => f $ norm t)
	| norm _ =  raise SAME
      and normh t = (norm t) handle SAME => t
  in normh t end

and norm_term2(asol,iTs,t) : term =
  let fun normT(Type(a,Ts)) = Type(a, normTs Ts)
	| normT(TFree _) = raise SAME
	| normT(TVar(v,_)) = (case assoc(iTs,v) of
		Some(U) => normTh U
	      | None => raise SAME)
      and normTh T = ((normT T) handle SAME => T)
      and normTs([]) = raise SAME
	| normTs(T::Ts) = ((normT T :: normTsh Ts)
			   handle SAME => T :: normTs Ts)
      and normTsh Ts = ((normTs Ts) handle SAME => Ts)
      and norm(Const(a,T)) = Const(a, normT T)
	| norm(Free(a,T)) = Free(a, normT T)
	| norm(Var (w,T)) =
	    (case xsearch(asol,w) of
		Some u => normh u
	      | None   => Var(w,normT T))
	| norm(Abs(a,T,body)) =
	      (Abs(a,normT T,normh body) handle SAME => Abs(a, T, norm body))
	| norm(Abs(_,_,body) $ t) = normh(subst_bounds([t], body))
	| norm(f $ t) =
	    ((case norm f of
	       Abs(_,_,body) => normh(subst_bounds([t], body))
	     | nf => nf $ normh t)
	    handle SAME => f $ norm t)
	| norm _ =  raise SAME
      and normh t = (norm t) handle SAME => t
  in normh t end;

(*curried version might be slower in recursive calls*)
fun norm_term (env as Envir{asol,iTs,...}) t : term =
        if null iTs then norm_term1(asol, t) else norm_term2(asol,iTs, t)

end;

