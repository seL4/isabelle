(*  Title: 	unify
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   Cambridge University 1992

Higher-Order Unification

Potential problem: type of Vars is often ignored, so two Vars with same
indexname but different types can cause errors!

Types as well as terms are unified.  The outermost functions assume the
terms to be unified already have the same type.  In resolution, this is
assured because both have type "prop".
*)


signature UNIFY = 
  sig
  (*references for control and tracing*)
  val trace_bound: int ref
  val trace_simp: bool ref
  val trace_types: bool ref
  val search_bound: int ref
  (*other exports*)
  val combound : (term*int*int) -> term
  val rlist_abs: (string*typ)list * term -> term   
  val smash_unifiers : Sign.sg * Envir.env * (term*term)list
	-> (Envir.env Seq.seq)
  val unifiers: Sign.sg * Envir.env * ((term*term)list)
	-> (Envir.env * (term * term)list) Seq.seq
  end;

structure Unify	: UNIFY = 
struct

(*Unification options*)

val trace_bound = ref 10	(*tracing starts above this depth, 0 for full*)
and search_bound = ref 20	(*unification quits above this depth*)
and trace_simp = ref false	(*print dpairs before calling SIMPL*)
and trace_types = ref false	(*announce potential incompleteness
				  of type unification*)

val sgr = ref(Sign.pre_pure);

type binderlist = (string*typ) list;

type dpair = binderlist * term * term;

fun body_type(Envir.Envir{iTs,...}) = 
let fun bT(Type("fun",[_,T])) = bT T
      | bT(T as TVar(ixn,_)) = (case Vartab.lookup (iTs,ixn) of
		None => T | Some(T') => bT T')
      | bT T = T
in bT end;

fun binder_types(Envir.Envir{iTs,...}) = 
let fun bTs(Type("fun",[T,U])) = T :: bTs U
      | bTs(T as TVar(ixn,_)) = (case Vartab.lookup (iTs,ixn) of
		None => [] | Some(T') => bTs T')
      | bTs _ = []
in bTs end;

fun strip_type env T = (binder_types env T, body_type env T);

fun fastype env (Ts, t) = Envir.fastype env (map snd Ts) t;


(*Eta normal form*)
fun eta_norm(env as Envir.Envir{iTs,...}) =
  let fun etif (Type("fun",[T,U]), t) =
	    Abs("", T, etif(U, incr_boundvars 1 t $ Bound 0))
	| etif (TVar(ixn,_),t) = 
	    (case Vartab.lookup (iTs,ixn) of
		  None => t | Some(T) => etif(T,t))
	| etif (_,t) = t;
      fun eta_nm (rbinder, Abs(a,T,body)) =
	    Abs(a, T, eta_nm ((a,T)::rbinder, body))
	| eta_nm (rbinder, t) = etif(fastype env (rbinder,t), t)
  in eta_nm end;


(*OCCURS CHECK
  Does the uvar occur in the term t?  
  two forms of search, for whether there is a rigid path to the current term.
  "seen" is list of variables passed thru, is a memo variable for sharing.
  This version searches for nonrigid occurrence, returns true if found. *)
fun occurs_terms (seen: (indexname list) ref,
 		  env: Envir.env, v: indexname, ts: term list): bool =
  let fun occurs [] = false
	| occurs (t::ts) =  occur t  orelse  occurs ts
      and occur (Const _)  = false
	| occur (Bound _)  = false
	| occur (Free _)  = false
	| occur (Var (w,_))  = 
	    if mem_ix (w, !seen) then false
	    else if eq_ix(v,w) then true
	      (*no need to lookup: v has no assignment*)
	    else (seen := w:: !seen;  
	          case  Envir.lookup(env,w)  of
		      None    => false
		    | Some t => occur t)
	| occur (Abs(_,_,body)) = occur body
	| occur (f$t) = occur t  orelse   occur f
  in  occurs ts  end;



(* f(a1,...,an)  ---->   (f,  [a1,...,an])  using the assignments*)
fun head_of_in (env,t) : term = case t of
    f$_ => head_of_in(env,f)
  | Var (v,_) => (case  Envir.lookup(env,v)  of  
			Some u => head_of_in(env,u)  |  None   => t)
  | _ => t;


datatype occ = NoOcc | Nonrigid | Rigid;

(* Rigid occur check
Returns Rigid    if it finds a rigid occurrence of the variable,
        Nonrigid if it finds a nonrigid path to the variable.
        NoOcc    otherwise.
  Continues searching for a rigid occurrence even if it finds a nonrigid one.

Condition for detecting non-unifable terms: [ section 5.3 of Huet (1975) ]
   a rigid path to the variable, appearing with no arguments.
Here completeness is sacrificed in order to reduce danger of divergence:
   reject ALL rigid paths to the variable.
Could check for rigid paths to bound variables that are out of scope.  
Not necessary because the assignment test looks at variable's ENTIRE rbinder.

Treatment of head(arg1,...,argn):
If head is a variable then no rigid path, switch to nonrigid search
for arg1,...,argn. 
If head is an abstraction then possibly no rigid path (head could be a 
   constant function) so again use nonrigid search.  Happens only if
   term is not in normal form. 

Warning: finds a rigid occurrence of ?f in ?f(t).
  Should NOT be called in this case: there is a flex-flex unifier
*)
fun rigid_occurs_term (seen: (indexname list)ref, env, v: indexname, t) = 
  let fun nonrigid t = if occurs_terms(seen,env,v,[t]) then Nonrigid 
		       else NoOcc
      fun occurs [] = NoOcc
	| occurs (t::ts) =
            (case occur t of
               Rigid => Rigid
             | oc =>  (case occurs ts of NoOcc => oc  |  oc2 => oc2))
      and occomb (f$t) =
            (case occur t of
               Rigid => Rigid
             | oc =>  (case occomb f of NoOcc => oc  |  oc2 => oc2))
        | occomb t = occur t
      and occur (Const _)  = NoOcc
	| occur (Bound _)  = NoOcc
	| occur (Free _)  = NoOcc
	| occur (Var (w,_))  = 
	    if mem_ix (w, !seen) then NoOcc
	    else if eq_ix(v,w) then Rigid
	    else (seen := w:: !seen;  
	          case  Envir.lookup(env,w)  of
		      None    => NoOcc
		    | Some t => occur t)
	| occur (Abs(_,_,body)) = occur body
	| occur (t as f$_) =  (*switch to nonrigid search?*)
	   (case head_of_in (env,f) of
	      Var (w,_) => (*w is not assigned*)
		if eq_ix(v,w) then Rigid  
		else  nonrigid t
	    | Abs(_,_,body) => nonrigid t (*not in normal form*)
	    | _ => occomb t)
  in  occur t  end;


exception CANTUNIFY;	(*Signals non-unifiability.  Does not signal errors!*)
exception ASSIGN;	(*Raised if not an assignment*)


fun unify_types(T,U, env as Envir.Envir{asol,iTs,maxidx}) =
  if T=U then env
  else let val (iTs',maxidx') = Type.unify (Sign.tsig_of (!sgr)) (iTs, maxidx) (U, T)
       in Envir.Envir{asol=asol,maxidx=maxidx',iTs=iTs'} end
       handle Type.TUNIFY => raise CANTUNIFY;

fun test_unify_types(args as (T,U,_)) =
let val sot = Sign.string_of_typ (!sgr);
    fun warn() = tracing ("Potential loss of completeness: "^sot U^" = "^sot T);
    val env' = unify_types(args)
in if is_TVar(T) orelse is_TVar(U) then warn() else ();
   env'
end;

(*Is the term eta-convertible to a single variable with the given rbinder?
  Examples: ?a   ?f(B.0)   ?g(B.1,B.0)
  Result is var a for use in SIMPL. *)
fun get_eta_var ([], _, Var vT)  =  vT
  | get_eta_var (_::rbinder, n, f $ Bound i) =
	if  n=i  then  get_eta_var (rbinder, n+1, f) 
		 else  raise ASSIGN
  | get_eta_var _ = raise ASSIGN;


(* ([xn,...,x1], t)   ======>   (x1,...,xn)t *)
fun rlist_abs ([], body) = body
  | rlist_abs ((a,T)::pairs, body) = rlist_abs(pairs, Abs(a, T, body));


(*Solve v=u by assignment -- "fixedpoint" to Huet -- if v not in u.
  If v occurs rigidly then nonunifiable.
  If v occurs nonrigidly then must use full algorithm. *)
fun assignment (env, rbinder, t, u) =
    let val (v,T) = get_eta_var(rbinder,0,t)
    in  case rigid_occurs_term (ref[], env, v, u) of
	      NoOcc => let val env = unify_types(body_type env T,
						 fastype env (rbinder,u),env)
		in Envir.update ((v, rlist_abs(rbinder,u)), env) end
	    | Nonrigid =>  raise ASSIGN
	    | Rigid =>  raise CANTUNIFY
    end;


(*Extends an rbinder with a new disagreement pair, if both are abstractions.
  Tries to unify types of the bound variables!
  Checks that binders have same length, since terms should be eta-normal;
    if not, raises TERM, probably indicating type mismatch.
  Uses variable a (unless the null string) to preserve user's naming.*) 
fun new_dpair (rbinder, Abs(a,T,body1), Abs(b,U,body2), env) =
	let val env' = unify_types(T,U,env)
	    val c = if a="" then b else a
	in new_dpair((c,T) :: rbinder, body1, body2, env') end
    | new_dpair (_, Abs _, _, _) = raise TERM ("new_dpair", [])
    | new_dpair (_, _, Abs _, _) = raise TERM ("new_dpair", [])
    | new_dpair (rbinder, t1, t2, env) = ((rbinder, t1, t2), env);


fun head_norm_dpair (env, (rbinder,t,u)) : dpair * Envir.env =
     new_dpair (rbinder,
		eta_norm env (rbinder, Envir.head_norm env t),
	  	eta_norm env (rbinder, Envir.head_norm env u), env);



(*flexflex: the flex-flex pairs,  flexrigid: the flex-rigid pairs
  Does not perform assignments for flex-flex pairs:
    may create nonrigid paths, which prevent other assignments.
  Does not even identify Vars in dpairs such as ?a =?= ?b; an attempt to
    do so caused numerous problems with no compensating advantage.
*)
fun SIMPL0 (dp0, (env,flexflex,flexrigid))
	: Envir.env * dpair list * dpair list =
    let val (dp as (rbinder,t,u), env) = head_norm_dpair(env,dp0);
	    fun SIMRANDS(f$t, g$u, env) =
			SIMPL0((rbinder,t,u), SIMRANDS(f,g,env))
	      | SIMRANDS (t as _$_, _, _) =
		raise TERM ("SIMPL: operands mismatch", [t,u])
	      | SIMRANDS (t, u as _$_, _) =
		raise TERM ("SIMPL: operands mismatch", [t,u])
	      | SIMRANDS(_,_,env) = (env,flexflex,flexrigid);
    in case (head_of t, head_of u) of
       (Var(_,T), Var(_,U)) =>
	    let val T' = body_type env T and U' = body_type env U;
		val env = unify_types(T',U',env)
	    in (env, dp::flexflex, flexrigid) end
     | (Var _, _) =>
	    ((assignment (env,rbinder,t,u), flexflex, flexrigid)
	     handle ASSIGN => (env, flexflex, dp::flexrigid))
     | (_, Var _) =>
	    ((assignment (env,rbinder,u,t), flexflex, flexrigid)
	     handle ASSIGN => (env, flexflex, (rbinder,u,t)::flexrigid))
     | (Const(a,T), Const(b,U)) =>
	    if a=b then SIMRANDS(t,u, unify_types(T,U,env))
	    else raise CANTUNIFY
     | (Bound i,    Bound j)    =>
	    if i=j  then SIMRANDS(t,u,env) else raise CANTUNIFY
     | (Free(a,T),  Free(b,U))  =>
	    if a=b then SIMRANDS(t,u, unify_types(T,U,env))
	    else raise CANTUNIFY
     | _ => raise CANTUNIFY
    end;


(* changed(env,t) checks whether the head of t is a variable assigned in env*)
fun changed (env, f$_) = changed (env,f)
  | changed (env, Var (v,_)) =
      (case Envir.lookup(env,v) of None=>false  |  _ => true)
  | changed _ = false;


(*Recursion needed if any of the 'head variables' have been updated
  Clever would be to re-do just the affected dpairs*)
fun SIMPL (env,dpairs) : Envir.env * dpair list * dpair list =
    let val all as (env',flexflex,flexrigid) =
	    foldr SIMPL0 (dpairs, (env,[],[]));
	val dps = flexrigid@flexflex
    in if exists (fn ((_,t,u)) => changed(env',t) orelse changed(env',u)) dps
       then SIMPL(env',dps) else all
    end;


(*computes t(Bound(n+k-1),...,Bound(n))  *)
fun combound (t, n, k) = 
    if  k>0  then  combound (t,n+1,k-1) $ (Bound n)  else  t;


(*Makes the terms E1,...,Em,    where Ts = [T...Tm]. 
  Each Ei is   ?Gi(B.(n-1),...,B.0), and has type Ti
  The B.j are bound vars of binder.
  The terms are not made in eta-normal-form, SIMPL does that later.  
  If done here, eta-expansion must be recursive in the arguments! *)
fun make_args name (binder: typ list, env, []) = (env, [])   (*frequent case*)
  | make_args name (binder: typ list, env, Ts) : Envir.env * term list =
       let fun funtype T = binder--->T;
	   val (env', vars) = Envir.genvars name (env, map funtype Ts)
       in  (env',  map (fn var=> combound(var, 0, length binder)) vars)  end;


(*Abstraction over a list of types, like list_abs*)
fun types_abs ([],u) = u
  | types_abs (T::Ts, u) = Abs("", T, types_abs(Ts,u));

(*Abstraction over the binder of a type*)
fun type_abs (env,T,t) = types_abs(binder_types env T, t);


(*MATCH taking "big steps".
  Copies u into the Var v, using projection on targs or imitation.
  A projection is allowed unless SIMPL raises an exception.
  Allocates new variables in projection on a higher-order argument,
    or if u is a variable (flex-flex dpair).
  Returns long sequence of every way of copying u, for backtracking
  For example, projection in ?b'(?a) may be wrong if other dpairs constrain ?a.
  The order for trying projections is crucial in ?b'(?a)   
  NB "vname" is only used in the call to make_args!!   *)
fun matchcopy vname = let fun mc(rbinder, targs, u, ed as (env,dpairs)) 
	: (term * (Envir.env * dpair list))Seq.seq =
let (*Produce copies of uarg and cons them in front of uargs*)
    fun copycons uarg (uargs, (env, dpairs)) =
	Seq.map(fn (uarg', ed') => (uarg'::uargs, ed'))
	    (mc (rbinder, targs,eta_norm env (rbinder, Envir.head_norm env uarg),
		 (env, dpairs)));
	(*Produce sequence of all possible ways of copying the arg list*)
    fun copyargs [] = Seq.cons( ([],ed), Seq.empty)
      | copyargs (uarg::uargs) =
	    Seq.flat (Seq.map (copycons uarg) (copyargs uargs));
    val (uhead,uargs) = strip_comb u;
    val base = body_type env (fastype env (rbinder,uhead));
    fun joinargs (uargs',ed') = (list_comb(uhead,uargs'), ed');
    (*attempt projection on argument with given typ*)
    val Ts = map (curry (fastype env) rbinder) targs;
    fun projenv (head, (Us,bary), targ, tail) = 
	let val env = if !trace_types then test_unify_types(base,bary,env)
		      else unify_types(base,bary,env)
	in Seq.make (fn () =>  
	    let val (env',args) = make_args vname (Ts,env,Us);
		(*higher-order projection: plug in targs for bound vars*)
		fun plugin arg = list_comb(head_of arg, targs);
		val dp = (rbinder, list_comb(targ, map plugin args), u);
		val (env2,frigid,fflex) = SIMPL (env', dp::dpairs)
		    (*may raise exception CANTUNIFY*)
	    in  Some ((list_comb(head,args), (env2, frigid@fflex)),
			tail)
	    end  handle CANTUNIFY => Seq.pull tail)
	end handle CANTUNIFY => tail;
    (*make a list of projections*)
    fun make_projs (T::Ts, targ::targs) =
	      (Bound(length Ts), T, targ) :: make_projs (Ts,targs)
      | make_projs ([],[]) = []
      | make_projs _ = raise TERM ("make_projs", u::targs);
    (*try projections and imitation*)
    fun matchfun ((bvar,T,targ)::projs) =
	       (projenv(bvar, strip_type env T, targ, matchfun projs))
      | matchfun [] = (*imitation last of all*)
	      (case uhead of
		 Const _ => Seq.map joinargs (copyargs uargs)
	       | Free _  => Seq.map joinargs (copyargs uargs)
	       | _ => Seq.empty)  (*if Var, would be a loop!*)
in case uhead of
	Abs(a, T, body) =>
	    Seq.map(fn (body', ed') => (Abs (a,T,body'), ed')) 
		(mc ((a,T)::rbinder,
			(map (incr_boundvars 1) targs) @ [Bound 0], body, ed))
      | Var (w,uary) => 
	    (*a flex-flex dpair: make variable for t*)
	    let val (env', newhd) = Envir.genvar (#1 w) (env, Ts---> base)
		val tabs = combound(newhd, 0, length Ts)
		val tsub = list_comb(newhd,targs)
	    in  Seq.single (tabs, (env', (rbinder,tsub,u):: dpairs)) 
	    end
      | _ =>  matchfun(rev(make_projs(Ts, targs)))
end
in mc end;


(*Call matchcopy to produce assignments to the variable in the dpair*)
fun MATCH (env, (rbinder,t,u), dpairs)
	: (Envir.env * dpair list)Seq.seq = 
  let val (Var(v,T), targs) = strip_comb t;
      val Ts = binder_types env T;
      fun new_dset (u', (env',dpairs')) =
	  (*if v was updated to s, must unify s with u' *)
	  case Envir.lookup(env',v) of
	      None => (Envir.update ((v, types_abs(Ts, u')), env'),  dpairs')
	    | Some s => (env', ([], s, types_abs(Ts, u'))::dpairs')
  in Seq.map new_dset
         (matchcopy (#1 v) (rbinder, targs, u, (env,dpairs)))
  end;



(**** Flex-flex processing ****)

(*At end of unification, do flex-flex assignments like ?a -> ?f(?b) 
  Attempts to update t with u, raising ASSIGN if impossible*)
fun ff_assign(env, rbinder, t, u) : Envir.env = 
let val (v,T) = get_eta_var(rbinder,0,t)
in if occurs_terms (ref[], env, v, [u]) then raise ASSIGN
   else let val env = unify_types(body_type env T,
				  fastype env (rbinder,u),
				  env)
	in Envir.vupdate ((v, rlist_abs(rbinder, u)), env) end
end;


(*Flex argument: a term, its type, and the index that refers to it.*)
type flarg = {t: term,  T: typ,  j: int};


(*Form the arguments into records for deletion/sorting.*)
fun flexargs ([],[],[]) = [] : flarg list
  | flexargs (j::js, t::ts, T::Ts) = {j=j, t=t, T=T} :: flexargs(js,ts,Ts)
  | flexargs _ = error"flexargs";


(*If an argument contains a banned Bound, then it should be deleted.
  But if the only path is flexible, this is difficult; the code gives up!
  In  %x y.?a(x) =?= %x y.?b(?c(y)) should we instantiate ?b or ?c *)
exception CHANGE_FAIL;   (*flexible occurrence of banned variable*)


(*Check whether the 'banned' bound var indices occur rigidly in t*)
fun rigid_bound (lev, banned) t = 
  let val (head,args) = strip_comb t 
  in  
      case head of
	  Bound i => (i-lev) mem_int banned  orelse
	      	     exists (rigid_bound (lev, banned)) args
	| Var _ => false	(*no rigid occurrences here!*)
	| Abs (_,_,u) => 
	       rigid_bound(lev+1, banned) u  orelse
	       exists (rigid_bound (lev, banned)) args
	| _ => exists (rigid_bound (lev, banned)) args
  end;

(*Squash down indices at level >=lev to delete the banned from a term.*)
fun change_bnos banned =
  let fun change lev (Bound i) = 
	    if i<lev then Bound i
	    else  if (i-lev) mem_int banned  
		  then raise CHANGE_FAIL (**flexible occurrence: give up**)
	    else  Bound (i - length (filter (fn j => j < i-lev) banned))
	| change lev (Abs (a,T,t)) = Abs (a, T, change(lev+1) t)
	| change lev (t$u) = change lev t $ change lev u
	| change lev t = t
  in  change 0  end;

(*Change indices, delete the argument if it contains a banned Bound*)
fun change_arg banned ({j,t,T}, args) : flarg list =
    if rigid_bound (0, banned) t  then  args	(*delete argument!*)
    else  {j=j, t= change_bnos banned t, T=T} :: args;


(*Sort the arguments to create assignments if possible:
  create eta-terms like ?g(B.1,B.0) *)
fun arg_less ({t= Bound i1,...}, {t= Bound i2,...}) = (i2<i1)
  | arg_less (_:flarg, _:flarg) = false;

(*Test whether the new term would be eta-equivalent to a variable --
  if so then there is no point in creating a new variable*)
fun decreasing n ([]: flarg list) = (n=0)
  | decreasing n ({j,...}::args) = j=n-1 andalso decreasing (n-1) args;

(*Delete banned indices in the term, simplifying it.
  Force an assignment, if possible, by sorting the arguments.
  Update its head; squash indices in arguments. *)
fun clean_term banned (env,t) =
    let val (Var(v,T), ts) = strip_comb t
	val (Ts,U) = strip_type env T
	and js = length ts - 1  downto 0
	val args = sort (make_ord arg_less)
		(foldr (change_arg banned) (flexargs (js,ts,Ts), []))
	val ts' = map (#t) args
    in
    if decreasing (length Ts) args then (env, (list_comb(Var(v,T), ts')))
    else let val (env',v') = Envir.genvar (#1v) (env, map (#T) args ---> U)
	     val body = list_comb(v', map (Bound o #j) args)
	     val env2 = Envir.vupdate (((v, types_abs(Ts, body)),   env'))
	     (*the vupdate affects ts' if they contain v*)
	 in  
	     (env2, Envir.norm_term env2 (list_comb(v',ts')))
         end
    end;


(*Add tpair if not trivial or already there.
  Should check for swapped pairs??*)
fun add_tpair (rbinder, (t0,u0), tpairs) : (term*term) list =
  if t0 aconv u0 then tpairs  
  else
  let val t = rlist_abs(rbinder, t0)  and  u = rlist_abs(rbinder, u0);
      fun same(t',u') = (t aconv t') andalso (u aconv u')
  in  if exists same tpairs  then tpairs  else (t,u)::tpairs  end;


(*Simplify both terms and check for assignments.
  Bound vars in the binder are "banned" unless used in both t AND u *)
fun clean_ffpair ((rbinder, t, u), (env,tpairs)) = 
  let val loot = loose_bnos t  and  loou = loose_bnos u
      fun add_index (((a,T), j), (bnos, newbinder)) = 
            if  j mem_int loot  andalso  j mem_int loou 
            then  (bnos, (a,T)::newbinder)	(*needed by both: keep*)
            else  (j::bnos, newbinder);		(*remove*)
      val indices = 0 upto (length rbinder - 1);
      val (banned,rbin') = foldr add_index (rbinder~~indices, ([],[]));
      val (env', t') = clean_term banned (env, t);
      val (env'',u') = clean_term banned (env',u)
  in  (ff_assign(env'', rbin', t', u'), tpairs)
      handle ASSIGN => (ff_assign(env'', rbin', u', t'), tpairs)
      handle ASSIGN => (env'', add_tpair(rbin', (t',u'), tpairs))
  end
  handle CHANGE_FAIL => (env, add_tpair(rbinder, (t,u), tpairs));


(*IF the flex-flex dpair is an assignment THEN do it  ELSE  put in tpairs
  eliminates trivial tpairs like t=t, as well as repeated ones
  trivial tpairs can easily escape SIMPL:  ?A=t, ?A=?B, ?B=t gives t=t 
  Resulting tpairs MAY NOT be in normal form:  assignments may occur here.*)
fun add_ffpair ((rbinder,t0,u0), (env,tpairs)) 
      : Envir.env * (term*term)list =
  let val t = Envir.norm_term env t0  and  u = Envir.norm_term env u0
  in  case  (head_of t, head_of u) of
      (Var(v,T), Var(w,U)) =>  (*Check for identical variables...*)
	if eq_ix(v,w) then     (*...occur check would falsely return true!*)
	    if T=U then (env, add_tpair (rbinder, (t,u), tpairs))
	    else raise TERM ("add_ffpair: Var name confusion", [t,u])
	else if xless(v,w) then (*prefer to update the LARGER variable*)
	     clean_ffpair ((rbinder, u, t), (env,tpairs))
        else clean_ffpair ((rbinder, t, u), (env,tpairs))
    | _ => raise TERM ("add_ffpair: Vars expected", [t,u])
  end;


(*Print a tracing message + list of dpairs.
  In t==u print u first because it may be rigid or flexible --
    t is always flexible.*)
fun print_dpairs msg (env,dpairs) =
  let fun pdp (rbinder,t,u) =
        let fun termT t = Sign.pretty_term (!sgr)
                              (Envir.norm_term env (rlist_abs(rbinder,t)))
            val bsymbs = [termT u, Pretty.str" =?=", Pretty.brk 1,
                          termT t];
        in tracing(Pretty.string_of(Pretty.blk(0,bsymbs))) end;
  in  tracing msg;  seq pdp dpairs  end;


(*Unify the dpairs in the environment.
  Returns flex-flex disagreement pairs NOT IN normal form. 
  SIMPL may raise exception CANTUNIFY. *)
fun hounifiers (sg,env, tus : (term*term)list) 
  : (Envir.env * (term*term)list)Seq.seq =
  let fun add_unify tdepth ((env,dpairs), reseq) =
	  Seq.make (fn()=>
	  let val (env',flexflex,flexrigid) = 
	       (if tdepth> !trace_bound andalso !trace_simp
		then print_dpairs "Enter SIMPL" (env,dpairs)  else ();
		SIMPL (env,dpairs))
	  in case flexrigid of
	      [] => Some (foldr add_ffpair (flexflex, (env',[])), reseq)
	    | dp::frigid' => 
		if tdepth > !search_bound then
		    (warning "Unification bound exceeded"; Seq.pull reseq)
		else
		(if tdepth > !trace_bound then
		    print_dpairs "Enter MATCH" (env',flexrigid@flexflex)
		 else ();
		 Seq.pull (Seq.it_right (add_unify (tdepth+1))
			   (MATCH (env',dp, frigid'@flexflex), reseq)))
	  end
	  handle CANTUNIFY => 
	    (if tdepth > !trace_bound then tracing"Failure node" else ();
	     Seq.pull reseq));
     val dps = map (fn(t,u)=> ([],t,u)) tus
  in sgr := sg;
     add_unify 1 ((env,dps), Seq.empty) 
  end;

fun unifiers(params) =
      Seq.cons((Pattern.unify(params), []),   Seq.empty)
      handle Pattern.Unif => Seq.empty
           | Pattern.Pattern => hounifiers(params);


(*For smash_flexflex1*)
fun var_head_of (env,t) : indexname * typ =
  case head_of (strip_abs_body (Envir.norm_term env t)) of
      Var(v,T) => (v,T)
    | _ => raise CANTUNIFY;  (*not flexible, cannot use trivial substitution*)


(*Eliminate a flex-flex pair by the trivial substitution, see Huet (1975)
  Unifies ?f(t1...rm) with ?g(u1...un) by ?f -> %x1...xm.?a, ?g -> %x1...xn.?a
  Unfortunately, unifies ?f(t,u) with ?g(t,u) by ?f, ?g -> %(x,y)?a, 
	though just ?g->?f is a more general unifier.
  Unlike Huet (1975), does not smash together all variables of same type --
    requires more work yet gives a less general unifier (fewer variables).
  Handles ?f(t1...rm) with ?f(u1...um) to avoid multiple updates. *)
fun smash_flexflex1 ((t,u), env) : Envir.env =
  let val (v,T) = var_head_of (env,t)
      and (w,U) = var_head_of (env,u);
      val (env', var) = Envir.genvar (#1v) (env, body_type env T)
      val env'' = Envir.vupdate((w, type_abs(env',U,var)),  env')
  in  if (v,T)=(w,U) then env''  (*the other update would be identical*)
      else Envir.vupdate((v, type_abs(env',T,var)), env'')
  end;


(*Smash all flex-flexpairs.  Should allow selection of pairs by a predicate?*)
fun smash_flexflex (env,tpairs) : Envir.env =
  foldr smash_flexflex1 (tpairs, env);

(*Returns unifiers with no remaining disagreement pairs*)
fun smash_unifiers (sg, env, tus) : Envir.env Seq.seq =
    Seq.map smash_flexflex (unifiers(sg,env,tus));

end;
