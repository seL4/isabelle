(*  Title:      Pure/pattern.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Christine Heinzelmann, and Stefan Berghofer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Unification of Higher-Order Patterns.

See also:
Tobias Nipkow. Functional Unification of Higher-Order Patterns.
In Proceedings of the 8th IEEE Symposium Logic in Computer Science, 1993.

TODO: optimize red by special-casing it
*)

infix aeconv;

signature PATTERN =
  sig
  type type_sig
  type sg
  type env
  val trace_unify_fail  : bool ref
  val aeconv            : term * term -> bool
  val eta_contract      : term -> term
  val eta_long          : typ list -> term -> term
  val beta_eta_contract : term -> term
  val eta_contract_atom : term -> term
  val match             : type_sig -> term * term
                          -> (indexname*typ)list * (indexname*term)list
  val first_order_match : type_sig -> term * term
                          -> (indexname*typ)list * (indexname*term)list
  val matches           : type_sig -> term * term -> bool
  val matches_subterm   : type_sig -> term * term -> bool
  val unify             : sg * env * (term * term)list -> env
  val first_order       : term -> bool
  val pattern           : term -> bool
  val rewrite_term      : type_sig -> (term * term) list -> (term -> term option) list
                          -> term -> term
  exception Unif
  exception MATCH
  exception Pattern
  end;

structure Pattern : PATTERN =
struct

type type_sig = Type.type_sig
type sg = Sign.sg
type env = Envir.env

exception Unif;
exception Pattern;

val trace_unify_fail = ref false;

(* Only for communication between unification and error message printing *)
val sgr = ref Sign.pre_pure

fun string_of_term env binders t = Sign.string_of_term (!sgr)
  (Envir.norm_term env (subst_bounds(map Free binders,t)));

fun bname binders i = fst(nth_elem(i,binders));
fun bnames binders is = space_implode " " (map (bname binders) is);

fun typ_clash(tye,T,U) =
  if !trace_unify_fail
  then let val t = Sign.string_of_typ (!sgr) (Envir.norm_type tye T)
           and u = Sign.string_of_typ (!sgr) (Envir.norm_type tye U)
       in tracing("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ()

fun clash a b =
  if !trace_unify_fail then tracing("Clash: " ^ a ^ " =/= " ^ b) else ()

fun boundVar binders i =
  "bound variable " ^ bname binders i ^ " (depth " ^ string_of_int i ^ ")";

fun clashBB binders i j =
  if !trace_unify_fail then clash (boundVar binders i) (boundVar binders j)
  else ()

fun clashB binders i s =
  if !trace_unify_fail then clash (boundVar binders i) s
  else ()

fun proj_fail(env,binders,F,is,t) =
  if !trace_unify_fail
  then let val f = Syntax.string_of_vname F
           val xs = bnames binders is
           val u = string_of_term env binders t
           val ys = bnames binders (loose_bnos t \\ is)
       in tracing("Cannot unify variable " ^ f ^
               " (depending on bound variables " ^ xs ^ ")\nwith term " ^ u ^
               "\nTerm contains additional bound variable(s) " ^ ys)
       end
  else ()

fun ocheck_fail(F,t,binders,env) =
  if !trace_unify_fail
  then let val f = Syntax.string_of_vname F
           val u = string_of_term env binders t
       in tracing("Variable " ^ f ^ " occurs in term\n" ^ u ^
                  "\nCannot unify!\n")
       end
  else ()

fun occurs(F,t,env) =
    let fun occ(Var(G,_))   = (case Envir.lookup(env,G) of
                                 Some(t) => occ t
                               | None    => F=G)
          | occ(t1$t2)      = occ t1 orelse occ t2
          | occ(Abs(_,_,t)) = occ t
          | occ _           = false
    in occ t end;


fun mapbnd f =
    let fun mpb d (Bound(i))     = if i < d then Bound(i) else Bound(f(i-d)+d)
          | mpb d (Abs(s,T,t))   = Abs(s,T,mpb(d+1) t)
          | mpb d ((u1 $ u2))    = (mpb d u1)$(mpb d u2)
          | mpb _ atom           = atom
    in mpb 0 end;

fun idx [] j     = ~10000
  | idx(i::is) j = if i=j then length is else idx is j;

fun at xs i = nth_elem (i,xs);

fun mkabs (binders,is,t)  =
    let fun mk(i::is) = let val (x,T) = nth_elem(i,binders)
                        in Abs(x,T,mk is) end
          | mk []     = t
    in mk is end;

val incr = mapbnd (fn i => i+1);

fun ints_of []             = []
  | ints_of (Bound i ::bs) =
      let val is = ints_of bs
      in if i mem_int is then raise Pattern else i::is end
  | ints_of _              = raise Pattern;

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts);


fun app (s,(i::is)) = app (s$Bound(i),is)
  | app (s,[])      = s;

fun red (Abs(_,_,s)) (i::is) js = red s is (i::js)
  | red t            []      [] = t
  | red t            is      jn = app (mapbnd (at jn) t,is);


(* split_type ([T1,....,Tn]---> T,n,[]) = ([Tn,...,T1],T) *)
fun split_type (T,0,Ts)                    = (Ts,T)
  | split_type (Type ("fun",[T1,T2]),n,Ts) = split_type (T2,n-1,T1::Ts)
  | split_type _                           = error("split_type");

fun type_of_G (env as Envir.Envir {iTs, ...}) (T,n,is) =
  let val (Ts, U) = split_type (Envir.norm_type iTs T, n, [])
  in map (at Ts) is ---> U end;

fun mkhnf (binders,is,G,js) = mkabs (binders, is, app(G,js));

fun mknewhnf(env,binders,is,F as (a,_),T,js) =
  let val (env',G) = Envir.genvar a (env,type_of_G env (T,length is,js))
  in Envir.update((F,mkhnf(binders,is,G,js)),env') end;


(* mk_proj_list(is) = [ |is| - k | 1 <= k <= |is| and is[k] >= 0 ] *)
fun mk_proj_list is =
    let fun mk(i::is,j) = if i >= 0 then j :: mk(is,j-1) else mk(is,j-1)
          | mk([],_)    = []
    in mk(is,length is - 1) end;

fun proj(s,env,binders,is) =
    let fun trans d i = if i<d then i else (idx is (i-d))+d;
        fun pr(s,env,d,binders) = (case Envir.head_norm env s of
              Abs(a,T,t) => let val (t',env') = pr(t,env,d+1,((a,T)::binders))
                            in (Abs(a,T,t'),env') end
            | t => (case strip_comb t of
                (c as Const _,ts) =>
                         let val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(c,ts'),env') end
                 | (f as Free _,ts) =>
                         let val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(f,ts'),env') end
                 | (Bound(i),ts) =>
                         let val j = trans d i
                         in if j < 0 then raise Unif
                            else let val (ts',env') = prs(ts,env,d,binders)
                                 in (list_comb(Bound j,ts'),env') end
                         end
                 | (Var(F as (a,_),Fty),ts) =>
                      let val js = ints_of' env ts;
                          val js' = map (trans d) js;
                          val ks = mk_proj_list js';
                          val ls = filter (fn i => i >= 0) js'
                          val Hty = type_of_G env (Fty,length js,ks)
                          val (env',H) = Envir.genvar a (env,Hty)
                          val env'' =
                                Envir.update((F,mkhnf(binders,js,H,ks)),env')
                      in (app(H,ls),env'') end
                 | _  => raise Pattern))
        and prs(s::ss,env,d,binders) =
              let val (s',env1) = pr(s,env,d,binders)
                  val (ss',env2) = prs(ss,env1,d,binders)
              in (s'::ss',env2) end
          | prs([],env,_,_) = ([],env)
   in if downto0(is,length binders - 1) then (s,env)
      else pr(s,env,0,binders)
   end;


(* mk_ff_list(is,js) = [ length(is) - k | 1 <= k <= |is| and is[k] = js[k] ] *)
fun mk_ff_list(is,js) =
    let fun mk([],[],_)        = []
          | mk(i::is,j::js, k) = if i=j then k :: mk(is,js,k-1)
                                        else mk(is,js,k-1)
          | mk _               = error"mk_ff_list"
    in mk(is,js,length is-1) end;

fun flexflex1(env,binders,F,Fty,is,js) =
  if is=js then env
  else let val ks = mk_ff_list(is,js)
       in mknewhnf(env,binders,is,F,Fty,ks) end;

fun flexflex2(env,binders,F,Fty,is,G,Gty,js) =
  let fun ff(F,Fty,is,G as (a,_),Gty,js) =
            if js subset_int is
            then let val t= mkabs(binders,is,app(Var(G,Gty),map (idx is) js))
                 in Envir.update((F,t),env) end
            else let val ks = is inter_int js
                     val Hty = type_of_G env (Fty,length is,map (idx is) ks)
                     val (env',H) = Envir.genvar a (env,Hty)
                     fun lam(is) = mkabs(binders,is,app(H,map (idx is) ks));
                 in Envir.update((G,lam js), Envir.update((F,lam is),env'))
                 end;
  in if xless(G,F) then ff(F,Fty,is,G,Gty,js) else ff(G,Gty,js,F,Fty,is) end

val tsgr = ref(Type.tsig0);

fun unify_types(T,U, env as Envir.Envir{asol,iTs,maxidx}) =
  if T=U then env
  else let val (iTs',maxidx') = Type.unify (!tsgr) (iTs, maxidx) (U, T)
       in Envir.Envir{asol=asol,maxidx=maxidx',iTs=iTs'} end
       handle Type.TUNIFY => (typ_clash(iTs,T,U); raise Unif);

fun unif binders (env,(s,t)) = case (Envir.head_norm env s, Envir.head_norm env t) of
      (Abs(ns,Ts,ts),Abs(nt,Tt,tt)) =>
         let val name = if ns = "" then nt else ns
         in unif ((name,Ts)::binders) (env,(ts,tt)) end
    | (Abs(ns,Ts,ts),t) => unif ((ns,Ts)::binders) (env,(ts,(incr t)$Bound(0)))
    | (t,Abs(nt,Tt,tt)) => unif ((nt,Tt)::binders) (env,((incr t)$Bound(0),tt))
    | p => cases(binders,env,p)

and cases(binders,env,(s,t)) = case (strip_comb s,strip_comb t) of
       ((Var(F,Fty),ss),(Var(G,Gty),ts)) =>
         if F = G then flexflex1(env,binders,F,Fty,ints_of' env ss,ints_of' env ts)
                  else flexflex2(env,binders,F,Fty,ints_of' env ss,G,Gty,ints_of' env ts)
      | ((Var(F,_),ss),_)             => flexrigid(env,binders,F,ints_of' env ss,t)
      | (_,(Var(F,_),ts))             => flexrigid(env,binders,F,ints_of' env ts,s)
      | ((Const c,ss),(Const d,ts))   => rigidrigid(env,binders,c,d,ss,ts)
      | ((Free(f),ss),(Free(g),ts))   => rigidrigid(env,binders,f,g,ss,ts)
      | ((Bound(i),ss),(Bound(j),ts)) => rigidrigidB (env,binders,i,j,ss,ts)
      | ((Abs(_),_),_)                => raise Pattern
      | (_,(Abs(_),_))                => raise Pattern
      | ((Const(c,_),_),(Free(f,_),_)) => (clash c f; raise Unif)
      | ((Const(c,_),_),(Bound i,_))   => (clashB binders i c; raise Unif)
      | ((Free(f,_),_),(Const(c,_),_)) => (clash f c; raise Unif)
      | ((Free(f,_),_),(Bound i,_))    => (clashB binders i f; raise Unif)
      | ((Bound i,_),(Const(c,_),_))   => (clashB binders i c; raise Unif)
      | ((Bound i,_),(Free(f,_),_))    => (clashB binders i f; raise Unif)


and rigidrigid (env,binders,(a,Ta),(b,Tb),ss,ts) =
      if a<>b then (clash a b; raise Unif)
      else foldl (unif binders) (unify_types(Ta,Tb,env), ss~~ts)

and rigidrigidB (env,binders,i,j,ss,ts) =
     if i <> j then (clashBB binders i j; raise Unif)
     else foldl (unif binders) (env ,ss~~ts)

and flexrigid (params as (env,binders,F,is,t)) =
      if occurs(F,t,env) then (ocheck_fail(F,t,binders,env); raise Unif)
      else (let val (u,env') = proj(t,env,binders,is)
            in Envir.update((F,mkabs(binders,is,u)),env') end
            handle Unif => (proj_fail params; raise Unif));

fun unify(sg,env,tus) = (sgr := sg; tsgr := Sign.tsig_of sg;
                         foldl (unif []) (env,tus));


(*Eta-contract a term (fully)*)

fun eta_contract t =
  let
    exception SAME;
    fun eta (Abs (a, T, body)) = 
      ((case eta body of
          body' as (f $ Bound 0) => 
	    if loose_bvar1 (f, 0) then Abs(a, T, body')
	    else incr_boundvars ~1 f
        | body' => Abs (a, T, body')) handle SAME =>
       (case body of
          (f $ Bound 0) => 
	    if loose_bvar1 (f, 0) then raise SAME
	    else incr_boundvars ~1 f
        | _ => raise SAME))
      | eta (f $ t) =
          (let val f' = eta f
           in f' $ etah t end handle SAME => f $ eta t)
      | eta _ = raise SAME
    and etah t = (eta t handle SAME => t)
  in etah t end;

val beta_eta_contract = eta_contract o Envir.beta_norm;

(*Eta-contract a term from outside: just enough to reduce it to an atom
DOESN'T QUITE WORK!
*)
fun eta_contract_atom (t0 as Abs(a, T, body)) =
      (case  eta_contract2 body  of
        body' as (f $ Bound 0) =>
            if loose_bvar1(f,0) then Abs(a,T,body')
            else eta_contract_atom (incr_boundvars ~1 f)
      | _ => t0)
  | eta_contract_atom t = t
and eta_contract2 (f$t) = f $ eta_contract_atom t
  | eta_contract2 t     = eta_contract_atom t;

(* put a term into eta long beta normal form *)
fun eta_long Ts (Abs (s, T, t)) = Abs (s, T, eta_long (T :: Ts) t)
  | eta_long Ts t = (case strip_comb t of
      (Abs _, _) => eta_long Ts (Envir.beta_norm t)
    | (u, ts) => 
      let
        val Us = binder_types (fastype_of1 (Ts, t));
        val i = length Us
      in list_abs (map (pair "x") Us,
        list_comb (incr_boundvars i u, map (eta_long (rev Us @ Ts))
          (map (incr_boundvars i) ts @ map Bound (i - 1 downto 0))))
      end);


(*Tests whether 2 terms are alpha/eta-convertible and have same type.
  Note that Consts and Vars may have more than one type.*)
fun t aeconv u = aconv_aux (eta_contract_atom t, eta_contract_atom u)
and aconv_aux (Const(a,T), Const(b,U)) = a=b  andalso  T=U
  | aconv_aux (Free(a,T),  Free(b,U))  = a=b  andalso  T=U
  | aconv_aux (Var(v,T),   Var(w,U))   = eq_ix(v,w) andalso  T=U
  | aconv_aux (Bound i,    Bound j)    = i=j
  | aconv_aux (Abs(_,T,t), Abs(_,U,u)) = (t aeconv u)  andalso  T=U
  | aconv_aux (f$t,        g$u)        = (f aeconv g)  andalso (t aeconv u)
  | aconv_aux _ =  false;


(*** Matching ***)

exception MATCH;

fun typ_match tsig args = (Type.typ_match tsig args)
                          handle Type.TYPE_MATCH => raise MATCH;

(*First-order matching;
  fomatch tsig (pattern, object) returns a (tyvar,typ)list and (var,term)list.
  The pattern and object may have variables in common.
  Instantiation does not affect the object, so matching ?a with ?a+1 works.
  Object is eta-contracted on the fly (by eta-expanding the pattern).
  Precondition: the pattern is already eta-contracted!
  Note: types are matched on the fly *)
fun fomatch tsig =
  let
    fun mtch (instsp as (tyinsts,insts)) = fn
        (Var(ixn,T), t)  =>
          if loose_bvar(t,0) then raise MATCH
          else (case assoc_string_int(insts,ixn) of
                  None => (typ_match tsig (tyinsts, (T, fastype_of t)),
                           (ixn,t)::insts)
                | Some u => if t aeconv u then instsp else raise MATCH)
      | (Free (a,T), Free (b,U)) =>
          if a=b then (typ_match tsig (tyinsts,(T,U)), insts) else raise MATCH
      | (Const (a,T), Const (b,U))  =>
          if a=b then (typ_match tsig (tyinsts,(T,U)), insts) else raise MATCH
      | (Bound i, Bound j)  =>  if  i=j  then  instsp  else raise MATCH
      | (Abs(_,T,t), Abs(_,U,u))  =>
          mtch (typ_match tsig (tyinsts,(T,U)),insts) (t,u)
      | (f$t, g$u) => mtch (mtch instsp (f,g)) (t, u)
      | (t, Abs(_,U,u))  =>  mtch instsp ((incr t)$(Bound 0), u)
      | _ => raise MATCH
  in mtch end;

fun first_order_match tsig = apfst Vartab.dest o fomatch tsig (Vartab.empty, []);

(* Matching of higher-order patterns *)

fun match_bind(itms,binders,ixn,is,t) =
  let val js = loose_bnos t
  in if null is
     then if null js then (ixn,t)::itms else raise MATCH
     else if js subset_int is
          then let val t' = if downto0(is,length binders - 1) then t
                            else mapbnd (idx is) t
               in (ixn, mkabs(binders,is,t')) :: itms end
          else raise MATCH
  end;

fun match tsg (po as (pat,obj)) =
let
  (* Pre: pat and obj have same type *)
  fun mtch binders (env as (iTs,itms),(pat,obj)) =
    case pat of
      Abs(ns,Ts,ts) =>
        (case obj of
           Abs(nt,Tt,tt) => mtch ((nt,Tt)::binders) (env,(ts,tt))
         | _ => let val Tt = typ_subst_TVars_Vartab iTs Ts
                in mtch((ns,Tt)::binders)(env,(ts,(incr obj)$Bound(0))) end)
    | _ => (case obj of
              Abs(nt,Tt,tt) =>
                mtch((nt,Tt)::binders)(env,((incr pat)$Bound(0),tt))
            | _ => cases(binders,env,pat,obj))

  and cases(binders,env as (iTs,itms),pat,obj) =
    let val (ph,pargs) = strip_comb pat
        fun rigrig1(iTs,oargs) =
              foldl (mtch binders) ((iTs,itms), pargs~~oargs)
        fun rigrig2((a,Ta),(b,Tb),oargs) =
              if a<> b then raise MATCH
              else rigrig1(typ_match tsg (iTs,(Ta,Tb)), oargs)
    in case ph of
         Var(ixn,_) =>
           let val is = ints_of pargs
           in case assoc_string_int(itms,ixn) of
                None => (iTs,match_bind(itms,binders,ixn,is,obj))
              | Some u => if obj aeconv (red u is []) then env
                          else raise MATCH
           end
       | _ =>
           let val (oh,oargs) = strip_comb obj
           in case (ph,oh) of
                (Const c,Const d) => rigrig2(c,d,oargs)
              | (Free f,Free g)   => rigrig2(f,g,oargs)
              | (Bound i,Bound j) => if i<>j then raise MATCH
                                     else rigrig1(iTs,oargs)
              | (Abs _, _)        => raise Pattern
              | (_, Abs _)        => raise Pattern
              | _                 => raise MATCH
           end
    end;

  val pT = fastype_of pat
  and oT = fastype_of obj
  val iTs = typ_match tsg (Vartab.empty, (pT,oT))
  val insts2 = (iTs,[])

in apfst Vartab.dest (mtch [] (insts2, po)
   handle Pattern => fomatch tsg insts2 po)
end;

(*Predicate: does the pattern match the object?*)
fun matches tsig po = (match tsig po; true) handle MATCH => false;

(* Does pat match a subterm of obj? *)
fun matches_subterm tsig (pat,obj) =
  let fun msub(bounds,obj) = matches tsig (pat,obj) orelse
            case obj of
              Abs(x,T,t) => let val y = variant bounds x
                                val f = Free(":" ^ y,T)
                            in msub(x::bounds,subst_bound(f,t)) end
            | s$t => msub(bounds,s) orelse msub(bounds,t)
            | _ => false
  in msub([],obj) end;

fun first_order(Abs(_,_,t)) = first_order t
  | first_order(t $ u) = first_order t andalso first_order u andalso
                         not(is_Var t)
  | first_order _ = true;

fun pattern(Abs(_,_,t)) = pattern t
  | pattern(t) = let val (head,args) = strip_comb t
                 in if is_Var head
                    then let val _ = ints_of args in true end
                         handle Pattern => false
                    else forall pattern args
                 end;


(* rewriting -- simple but fast *)

fun rewrite_term tsig rules procs tm =
  let
    val skel0 = Bound 0;

    val rhs_names =
      foldr (fn ((_, rhs), names) => add_term_free_names (rhs, names)) (rules, []);

    fun variant_absfree (x, T, t) =
      let
        val x' = variant (add_term_free_names (t, rhs_names)) x;
        val t' = subst_bound (Free (x', T), t);
      in (fn u => Abs (x, T, abstract_over (Free (x', T), u)), t') end;

    fun match_rew tm (tm1, tm2) =
      let val rtm = if_none (Term.rename_abs tm1 tm tm2) tm2
      in Some (subst_vars (match tsig (tm1, tm)) rtm, rtm)
        handle MATCH => None
      end;

    fun rew (Abs (_, _, body) $ t) = Some (subst_bound (t, body), skel0)
      | rew tm = (case get_first (match_rew tm) rules of
          None => apsome (rpair skel0) (get_first (fn p => p tm) procs)
        | x => x);

    fun rew1 (Var _) _ = None
      | rew1 skel tm = (case rew2 skel tm of
          Some tm1 => (case rew tm1 of
              Some (tm2, skel') => Some (if_none (rew1 skel' tm2) tm2)
            | None => Some tm1)
        | None => (case rew tm of
              Some (tm1, skel') => Some (if_none (rew1 skel' tm1) tm1)
            | None => None))

    and rew2 skel (tm1 $ tm2) = (case tm1 of
            Abs (_, _, body) =>
              let val tm' = subst_bound (tm2, body)
              in Some (if_none (rew2 skel0 tm') tm') end
          | _ => 
            let val (skel1, skel2) = (case skel of
                skel1 $ skel2 => (skel1, skel2)
              | _ => (skel0, skel0))
            in case rew1 skel1 tm1 of
                Some tm1' => (case rew1 skel2 tm2 of
                    Some tm2' => Some (tm1' $ tm2')
                  | None => Some (tm1' $ tm2))
              | None => (case rew1 skel2 tm2 of
                    Some tm2' => Some (tm1 $ tm2')
                  | None => None)
            end)
      | rew2 skel (Abs (x, T, tm)) =
          let
            val (abs, tm') = variant_absfree (x, T, tm);
            val skel' = (case skel of Abs (_, _, skel') => skel' | _ => skel0)
          in case rew1 skel' tm' of
              Some tm'' => Some (abs tm'')
            | None => None
          end
      | rew2 _ _ = None

  in if_none (rew1 skel0 tm) tm end;

end;

val trace_unify_fail = Pattern.trace_unify_fail;
