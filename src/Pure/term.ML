(*  Title: 	Pure/term.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   Cambridge University 1992

Simply typed lambda-calculus: types, terms, and basic operations
*)

infix 9  $;
infixr 5 -->;
infixr   --->;
infix    aconv;


structure Term =
struct

(*Indexnames can be quickly renamed by adding an offset to the integer part,
  for resolution.*)
type indexname = string*int;

(* Types are classified by classes. *)
type class = string;
type sort  = class list;

(* The sorts attached to TFrees and TVars specify the sort of that variable *)
datatype typ = Type  of string * typ list
             | TFree of string * sort
	     | TVar  of indexname * sort;

fun S --> T = Type("fun",[S,T]);

(*handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)*)
val op ---> = foldr (op -->);


(*terms.  Bound variables are indicated by depth number.
  Free variables, (scheme) variables and constants have names.
  An term is "closed" if there every bound variable of level "lev"
  is enclosed by at least "lev" abstractions. 

  It is possible to create meaningless terms containing loose bound vars
  or type mismatches.  But such terms are not allowed in rules. *)



datatype term = 
    Const of string * typ
  | Free  of string * typ 
  | Var   of indexname * typ
  | Bound of int
  | Abs   of string*typ*term
  | op $  of term*term;


(*For errors involving type mismatches*)
exception TYPE of string * typ list * term list;

fun raise_type msg tys ts = raise TYPE (msg, tys, ts);

(*For system errors involving terms*)
exception TERM of string * term list;

fun raise_term msg ts = raise TERM (msg, ts);


(*Note variable naming conventions!
    a,b,c: string
    f,g,h: functions (including terms of function type)
    i,j,m,n: int
    t,u: term
    v,w: indexnames
    x,y: any
    A,B,C: term (denoting formulae)
    T,U: typ
*)


(** Discriminators **)

fun is_Const (Const _) = true
  | is_Const _ = false;

fun is_Free (Free _) = true
  | is_Free _ = false;

fun is_Var (Var _) = true
  | is_Var _ = false;

fun is_TVar (TVar _) = true
  | is_TVar _ = false;

(** Destructors **)

fun dest_Const (Const x) =  x
  | dest_Const t = raise TERM("dest_Const", [t]);

fun dest_Free (Free x) =  x
  | dest_Free t = raise TERM("dest_Free", [t]);

fun dest_Var (Var x) =  x
  | dest_Var t = raise TERM("dest_Var", [t]);


(* maps  [T1,...,Tn]--->T  to the list  [T1,T2,...,Tn]*)
fun binder_types (Type("fun",[S,T])) = S :: binder_types T
  | binder_types _   =  [];

(* maps  [T1,...,Tn]--->T  to T*)
fun body_type (Type("fun",[S,T])) = body_type T
  | body_type T   =  T;

(* maps  [T1,...,Tn]--->T  to   ([T1,T2,...,Tn], T)  *)
fun strip_type T : typ list * typ =
  (binder_types T, body_type T);


(*Compute the type of the term, checking that combinations are well-typed
  Ts = [T0,T1,...] holds types of bound variables 0, 1, ...*)
fun type_of1 (Ts, Const (_,T)) = T
  | type_of1 (Ts, Free  (_,T)) = T
  | type_of1 (Ts, Bound i) = (nth_elem (i,Ts)  
  	handle LIST _ => raise TYPE("type_of: bound variable", [], [Bound i]))
  | type_of1 (Ts, Var (_,T)) = T
  | type_of1 (Ts, Abs (_,T,body)) = T --> type_of1(T::Ts, body)
  | type_of1 (Ts, f$u) = 
      let val U = type_of1(Ts,u)
          and T = type_of1(Ts,f)
      in case T of
	    Type("fun",[T1,T2]) =>
	      if T1=U then T2  else raise TYPE
	            ("type_of: type mismatch in application", [T1,U], [f$u])
	  | _ => raise TYPE 
		    ("type_of: function type is expected in application",
		     [T,U], [f$u])
      end;

fun type_of t : typ = type_of1 ([],t);

(*Determines the type of a term, with minimal checking*)
fun fastype_of1 (Ts, f$u) = 
    (case fastype_of1 (Ts,f) of
	Type("fun",[_,T]) => T
	| _ => raise TERM("fastype_of: expected function type", [f$u]))
  | fastype_of1 (_, Const (_,T)) = T
  | fastype_of1 (_, Free (_,T)) = T
  | fastype_of1 (Ts, Bound i) = (nth_elem(i,Ts)
  	 handle LIST _ => raise TERM("fastype_of: Bound", [Bound i]))
  | fastype_of1 (_, Var (_,T)) = T 
  | fastype_of1 (Ts, Abs (_,T,u)) = T --> fastype_of1 (T::Ts, u);

fun fastype_of t : typ = fastype_of1 ([],t);


(* maps  (x1,...,xn)t   to   t  *)
fun strip_abs_body (Abs(_,_,t))  =  strip_abs_body t  
  | strip_abs_body u  =  u;


(* maps  (x1,...,xn)t   to   [x1, ..., xn]  *)
fun strip_abs_vars (Abs(a,T,t))  =  (a,T) :: strip_abs_vars t 
  | strip_abs_vars u  =  [] : (string*typ) list;


fun strip_qnt_body qnt =
let fun strip(tm as Const(c,_)$Abs(_,_,t)) = if c=qnt then strip t else tm
      | strip t = t
in strip end;

fun strip_qnt_vars qnt =
let fun strip(Const(c,_)$Abs(a,T,t)) = if c=qnt then (a,T)::strip t else []
      | strip t  =  [] : (string*typ) list
in strip end;


(* maps   (f, [t1,...,tn])  to  f(t1,...,tn) *)
val list_comb : term * term list -> term = foldl (op $);


(* maps   f(t1,...,tn)  to  (f, [t1,...,tn]) ; naturally tail-recursive*)
fun strip_comb u : term * term list = 
    let fun stripc (f$t, ts) = stripc (f, t::ts)
        |   stripc  x =  x 
    in  stripc(u,[])  end;


(* maps   f(t1,...,tn)  to  f , which is never a combination *)
fun head_of (f$t) = head_of f
  | head_of u = u;


(*Number of atoms and abstractions in a term*)
fun size_of_term (Abs (_,_,body)) = 1 + size_of_term body
  | size_of_term (f$t) = size_of_term f  +  size_of_term t
  | size_of_term _ = 1;

fun map_type_tvar f (Type(a,Ts)) = Type(a, map (map_type_tvar f) Ts)
  | map_type_tvar f (T as TFree _) = T
  | map_type_tvar f (TVar x) = f x;

fun map_type_tfree f (Type(a,Ts)) = Type(a, map (map_type_tfree f) Ts)
  | map_type_tfree f (TFree x) = f x
  | map_type_tfree f (T as TVar _) = T;

(* apply a function to all types in a term *)
fun map_term_types f =
let fun map(Const(a,T)) = Const(a, f T)
      | map(Free(a,T)) = Free(a, f T)
      | map(Var(v,T)) = Var(v, f T)
      | map(t as Bound _)  = t
      | map(Abs(a,T,t)) = Abs(a, f T, map t)
      | map(f$t) = map f $ map t;
in map end;

(* iterate a function over all types in a term *)
fun it_term_types f =
let fun iter(Const(_,T), a) = f(T,a)
      | iter(Free(_,T), a) = f(T,a)
      | iter(Var(_,T), a) = f(T,a)
      | iter(Abs(_,T,t), a) = iter(t,f(T,a))
      | iter(f$u, a) = iter(f, iter(u, a))
      | iter(Bound _, a) = a
in iter end


(** Connectives of higher order logic **)

val logicC: class = "logic";
val logicS: sort = [logicC];

fun itselfT ty = Type ("itself", [ty]);
val a_itselfT = itselfT (TFree ("'a", logicS));

val propT : typ = Type("prop",[]);

val implies = Const("==>", propT-->propT-->propT);

fun all T = Const("all", (T-->propT)-->propT);

fun equals T = Const("==", T-->T-->propT);

fun flexpair T = Const("=?=", T-->T-->propT);

(* maps  !!x1...xn. t   to   t  *)
fun strip_all_body (Const("all",_)$Abs(_,_,t))  =  strip_all_body t  
  | strip_all_body t  =  t;

(* maps  !!x1...xn. t   to   [x1, ..., xn]  *)
fun strip_all_vars (Const("all",_)$Abs(a,T,t))  =
		(a,T) :: strip_all_vars t 
  | strip_all_vars t  =  [] : (string*typ) list;

(*increments a term's non-local bound variables
  required when moving a term within abstractions
     inc is  increment for bound variables
     lev is  level at which a bound variable is considered 'loose'*)
fun incr_bv (inc, lev, u as Bound i) = if i>=lev then Bound(i+inc) else u 
  | incr_bv (inc, lev, Abs(a,T,body)) =
	Abs(a, T, incr_bv(inc,lev+1,body))
  | incr_bv (inc, lev, f$t) = 
      incr_bv(inc,lev,f) $ incr_bv(inc,lev,t)
  | incr_bv (inc, lev, u) = u;

fun incr_boundvars  0  t = t
  | incr_boundvars inc t = incr_bv(inc,0,t);


(*Accumulate all 'loose' bound vars referring to level 'lev' or beyond.
   (Bound 0) is loose at level 0 *)
fun add_loose_bnos (Bound i, lev, js) = 
	if i<lev then js  else  (i-lev) ins_int js
  | add_loose_bnos (Abs (_,_,t), lev, js) = add_loose_bnos (t, lev+1, js)
  | add_loose_bnos (f$t, lev, js) =
	add_loose_bnos (f, lev, add_loose_bnos (t, lev, js)) 
  | add_loose_bnos (_, _, js) = js;

fun loose_bnos t = add_loose_bnos (t, 0, []);

(* loose_bvar(t,k) iff t contains a 'loose' bound variable referring to
   level k or beyond. *)
fun loose_bvar(Bound i,k) = i >= k
  | loose_bvar(f$t, k) = loose_bvar(f,k) orelse loose_bvar(t,k)
  | loose_bvar(Abs(_,_,t),k) = loose_bvar(t,k+1)
  | loose_bvar _ = false;


(*Substitute arguments for loose bound variables.
  Beta-reduction of arg(n-1)...arg0 into t replacing (Bound i) with (argi).
  Note that for ((x,y)c)(a,b), the bound vars in c are x=1 and y=0
	and the appropriate call is  subst_bounds([b,a], c) .
  Loose bound variables >=n are reduced by "n" to
     compensate for the disappearance of lambdas.
*)
fun subst_bounds (args: term list, t) : term = 
  let val n = length args;
      fun subst (t as Bound i, lev) =
 	   (if i<lev then  t    (*var is locally bound*)
	    else  incr_boundvars lev (List.nth(args, i-lev))
		    handle Subscript => Bound(i-n)  (*loose: change it*))
	| subst (Abs(a,T,body), lev) = Abs(a, T,  subst(body,lev+1))
	| subst (f$t, lev) =  subst(f,lev)  $  subst(t,lev)
	| subst (t,lev) = t
  in   case args of [] => t  | _ => subst (t,0)  end;

(*Special case: one argument*)
fun subst_bound (arg, t) : term = 
  let fun subst (t as Bound i, lev) =
 	    if i<lev then  t    (*var is locally bound*)
	    else  if i=lev then incr_boundvars lev arg
		           else Bound(i-1)  (*loose: change it*)
	| subst (Abs(a,T,body), lev) = Abs(a, T,  subst(body,lev+1))
	| subst (f$t, lev) =  subst(f,lev)  $  subst(t,lev)
	| subst (t,lev) = t
  in  subst (t,0)  end;

(*beta-reduce if possible, else form application*)
fun betapply (Abs(_,_,t), u) = subst_bound (u,t)
  | betapply (f,u) = f$u;

(** Equality, membership and insertion of indexnames (string*ints) **)

(*optimized equality test for indexnames.  Yields a huge gain under Poly/ML*)
fun eq_ix ((a:string, i:int), (a',i')) = (a=a') andalso i=i';

(*membership in a list, optimized version for indexnames*)
fun mem_ix (x:string*int, []) = false
  | mem_ix (x, y :: ys) = eq_ix(x,y) orelse mem_ix (x, ys);

(*insertion into list, optimized version for indexnames*)
fun ins_ix (x,xs) = if mem_ix (x, xs) then xs else x :: xs;

(*Tests whether 2 terms are alpha-convertible and have same type.
  Note that constants and Vars may have more than one type.*)
fun (Const(a,T)) aconv (Const(b,U)) = a=b  andalso  T=U
  | (Free(a,T)) aconv (Free(b,U)) = a=b  andalso  T=U
  | (Var(v,T)) aconv (Var(w,U)) =   eq_ix(v,w)  andalso  T=U
  | (Bound i) aconv (Bound j)  =   i=j
  | (Abs(_,T,t)) aconv (Abs(_,U,u)) = t aconv u  andalso  T=U
  | (f$t) aconv (g$u) = (f aconv g) andalso (t aconv u)
  | _ aconv _  =  false;

(** Membership, insertion, union for terms **)

fun mem_term (_, []) = false
  | mem_term (t, t'::ts) = t aconv t' orelse mem_term(t,ts);

fun subset_term ([], ys) = true
  | subset_term (x :: xs, ys) = mem_term (x, ys) andalso subset_term(xs, ys);

fun eq_set_term (xs, ys) =
    xs = ys orelse (subset_term (xs, ys) andalso subset_term (ys, xs));

fun ins_term(t,ts) = if mem_term(t,ts) then ts else t :: ts;

fun union_term (xs, []) = xs
  | union_term ([], ys) = ys
  | union_term ((x :: xs), ys) = union_term (xs, ins_term (x, ys));

(** Equality, membership and insertion of sorts (string lists) **)

fun eq_sort ([]:sort, []) = true
  | eq_sort ((s::ss), (t::ts)) = s=t andalso eq_sort(ss,ts)
  | eq_sort (_, _) = false;

fun mem_sort (_:sort, []) = false
  | mem_sort (S, S'::Ss) = eq_sort (S, S') orelse mem_sort(S,Ss);

fun ins_sort(S,Ss) = if mem_sort(S,Ss) then Ss else S :: Ss;

fun union_sort (xs, []) = xs
  | union_sort ([], ys) = ys
  | union_sort ((x :: xs), ys) = union_sort (xs, ins_sort (x, ys));

fun subset_sort ([], ys) = true
  | subset_sort (x :: xs, ys) = mem_sort (x, ys) andalso subset_sort(xs, ys);

fun eq_set_sort (xs, ys) =
    xs = ys orelse (subset_sort (xs, ys) andalso subset_sort (ys, xs));

(*are two term lists alpha-convertible in corresponding elements?*)
fun aconvs ([],[]) = true
  | aconvs (t::ts, u::us) = t aconv u andalso aconvs(ts,us)
  | aconvs _ = false;

(*A fast unification filter: true unless the two terms cannot be unified. 
  Terms must be NORMAL.  Treats all Vars as distinct. *)
fun could_unify (t,u) =
  let fun matchrands (f$t, g$u) = could_unify(t,u) andalso  matchrands(f,g)
	| matchrands _ = true
  in case (head_of t , head_of u) of
	(_, Var _) => true
      | (Var _, _) => true
      | (Const(a,_), Const(b,_)) =>  a=b andalso matchrands(t,u)
      | (Free(a,_), Free(b,_)) =>  a=b andalso matchrands(t,u)
      | (Bound i, Bound j) =>  i=j andalso matchrands(t,u)
      | (Abs _, _) =>  true   (*because of possible eta equality*)
      | (_, Abs _) =>  true
      | _ => false
  end;

(*Substitute new for free occurrences of old in a term*)
fun subst_free [] = (fn t=>t)
  | subst_free pairs =
      let fun substf u = 
	    case gen_assoc (op aconv) (pairs, u) of
		Some u' => u'
	      | None => (case u of Abs(a,T,t) => Abs(a, T, substf t)
				 | t$u' => substf t $ substf u'
				 | _ => u)
      in  substf  end;

(*a total, irreflexive ordering on index names*)
fun xless ((a,i), (b,j): indexname) = i<j  orelse  (i=j andalso a<b);


(*Abstraction of the term "body" over its occurrences of v, 
    which must contain no loose bound variables.
  The resulting term is ready to become the body of an Abs.*)
fun abstract_over (v,body) =
  let fun abst (lev,u) = if (v aconv u) then (Bound lev) else
      (case u of
          Abs(a,T,t) => Abs(a, T, abst(lev+1, t))
	| f$rand => abst(lev,f) $ abst(lev,rand)
	| _ => u)
  in  abst(0,body)  end;


(*Form an abstraction over a free variable.*)
fun absfree (a,T,body) = Abs(a, T, abstract_over (Free(a,T), body));

(*Abstraction over a list of free variables*)
fun list_abs_free ([ ] ,     t) = t
  | list_abs_free ((a,T)::vars, t) = 
      absfree(a, T, list_abs_free(vars,t));

(*Quantification over a list of free variables*)
fun list_all_free ([], t: term) = t
  | list_all_free ((a,T)::vars, t) = 
        (all T) $ (absfree(a, T, list_all_free(vars,t)));

(*Quantification over a list of variables (already bound in body) *)
fun list_all ([], t) = t
  | list_all ((a,T)::vars, t) = 
        (all T) $ (Abs(a, T, list_all(vars,t)));

(*Replace the ATOMIC term ti by ui;    instl = [(t1,u1), ..., (tn,un)]. 
  A simultaneous substitution:  [ (a,b), (b,a) ] swaps a and b.  *)
fun subst_atomic [] t = t : term
  | subst_atomic (instl: (term*term) list) t =
      let fun subst (Abs(a,T,body)) = Abs(a, T, subst body)
	    | subst (f$t') = subst f $ subst t'
	    | subst t = (case assoc(instl,t) of
		           Some u => u  |  None => t)
      in  subst t  end;

(*Substitute for type Vars in a type*)
fun typ_subst_TVars iTs T = if null iTs then T else
  let fun subst(Type(a,Ts)) = Type(a, map subst Ts)
	| subst(T as TFree _) = T
	| subst(T as TVar(ixn,_)) =
            (case assoc(iTs,ixn) of None => T | Some(U) => U)
  in subst T end;

(*Substitute for type Vars in a term*)
val subst_TVars = map_term_types o typ_subst_TVars;

(*Substitute for Vars in a term; see also envir/norm_term*)
fun subst_Vars itms t = if null itms then t else
  let fun subst(v as Var(ixn,_)) =
            (case assoc(itms,ixn) of None => v | Some t => t)
        | subst(Abs(a,T,t)) = Abs(a,T,subst t)
        | subst(f$t) = subst f $ subst t
        | subst(t) = t
  in subst t end;

(*Substitute for type/term Vars in a term; see also envir/norm_term*)
fun subst_vars(iTs,itms) = if null iTs then subst_Vars itms else
  let fun subst(Const(a,T)) = Const(a,typ_subst_TVars iTs T)
        | subst(Free(a,T)) = Free(a,typ_subst_TVars iTs T)
        | subst(v as Var(ixn,T)) = (case assoc(itms,ixn) of
            None   => Var(ixn,typ_subst_TVars iTs T)
          | Some t => t)
        | subst(b as Bound _) = b
        | subst(Abs(a,T,t)) = Abs(a,typ_subst_TVars iTs T,subst t)
        | subst(f$t) = subst f $ subst t
  in subst end;


(*Computing the maximum index of a typ*)
fun maxidx_of_typ(Type(_,Ts)) = maxidx_of_typs Ts
  | maxidx_of_typ(TFree _) = ~1
  | maxidx_of_typ(TVar((_,i),_)) = i
and maxidx_of_typs [] = ~1
  | maxidx_of_typs (T::Ts) = Int.max(maxidx_of_typ T, maxidx_of_typs Ts);


(*Computing the maximum index of a term*)
fun maxidx_of_term (Const(_,T)) = maxidx_of_typ T
  | maxidx_of_term (Bound _) = ~1
  | maxidx_of_term (Free(_,T)) = maxidx_of_typ T
  | maxidx_of_term (Var ((_,i), T)) = Int.max(i, maxidx_of_typ T)
  | maxidx_of_term (Abs (_,T,u)) = Int.max(maxidx_of_term u, maxidx_of_typ T)
  | maxidx_of_term (f$t) = Int.max(maxidx_of_term f,  maxidx_of_term t);


(* Increment the index of all Poly's in T by k *)
fun incr_tvar k = map_type_tvar (fn ((a,i),S) => TVar((a,i+k),S));


(**** Syntax-related declarations ****)


(*Dummy type for parsing.  Will be replaced during type inference. *)
val dummyT = Type("dummy",[]);

(*scan a numeral of the given radix, normally 10*)
fun scan_radixint (radix: int, cs) : int * string list =
  let val zero = ord"0"
      val limit = zero+radix
      fun scan (num,[]) = (num,[])
	| scan (num, c::cs) =
	      if  zero <= ord c  andalso  ord c < limit
	      then scan(radix*num + ord c - zero, cs)
	      else (num, c::cs)
  in  scan(0,cs)  end;

fun scan_int cs = scan_radixint(10,cs);


(*** Printing ***)


(*Makes a variant of the name c distinct from the names in bs.
  First attaches the suffix "a" and then increments this. *)
fun variant bs c : string =
  let fun vary2 c = if (c mem_string bs) then  vary2 (bump_string c)  else  c
      fun vary1 c = if (c mem_string bs) then  vary2 (c ^ "a")  else  c
  in  vary1 (if c="" then "u" else c)  end;

(*Create variants of the list of names, with priority to the first ones*)
fun variantlist ([], used) = []
  | variantlist(b::bs, used) = 
      let val b' = variant used b
      in  b' :: variantlist (bs, b'::used)  end;

(** TFrees and TVars **)

(*maps  (bs,v)  to   v'::bs    this reverses the identifiers bs*)
fun add_new_id (bs, c) : string list =  variant bs c  ::  bs;

(*Accumulates the names in the term, suppressing duplicates.
  Includes Frees and Consts.  For choosing unambiguous bound var names.*)
fun add_term_names (Const(a,_), bs) = a ins_string bs
  | add_term_names (Free(a,_), bs) = a ins_string bs
  | add_term_names (f$u, bs) = add_term_names (f, add_term_names(u, bs))
  | add_term_names (Abs(_,_,t), bs) = add_term_names(t,bs)
  | add_term_names (_, bs) = bs;

(*Accumulates the TVars in a type, suppressing duplicates. *)
fun add_typ_tvars(Type(_,Ts),vs) = foldr add_typ_tvars (Ts,vs)
  | add_typ_tvars(TFree(_),vs) = vs
  | add_typ_tvars(TVar(v),vs) = v ins vs;

(*Accumulates the TFrees in a type, suppressing duplicates. *)
fun add_typ_tfree_names(Type(_,Ts),fs) = foldr add_typ_tfree_names (Ts,fs)
  | add_typ_tfree_names(TFree(f,_),fs) = f ins_string fs
  | add_typ_tfree_names(TVar(_),fs) = fs;

fun add_typ_tfrees(Type(_,Ts),fs) = foldr add_typ_tfrees (Ts,fs)
  | add_typ_tfrees(TFree(f),fs) = f ins fs
  | add_typ_tfrees(TVar(_),fs) = fs;

fun add_typ_varnames(Type(_,Ts),nms) = foldr add_typ_varnames (Ts,nms)
  | add_typ_varnames(TFree(nm,_),nms) = nm ins_string nms
  | add_typ_varnames(TVar((nm,_),_),nms) = nm ins_string nms;

(*Accumulates the TVars in a term, suppressing duplicates. *)
val add_term_tvars = it_term_types add_typ_tvars;

(*Accumulates the TFrees in a term, suppressing duplicates. *)
val add_term_tfrees = it_term_types add_typ_tfrees;
val add_term_tfree_names = it_term_types add_typ_tfree_names;

val add_term_tvarnames = it_term_types add_typ_varnames;

(*Non-list versions*)
fun typ_tfrees T = add_typ_tfrees(T,[]);
fun typ_tvars T = add_typ_tvars(T,[]);
fun term_tfrees t = add_term_tfrees(t,[]);
fun term_tvars t = add_term_tvars(t,[]);

(*special code to enforce left-to-right collection of TVar-indexnames*)

fun add_typ_ixns(ixns,Type(_,Ts)) = foldl add_typ_ixns (ixns,Ts)
  | add_typ_ixns(ixns,TVar(ixn,_)) = if mem_ix (ixn, ixns) then ixns 
				     else ixns@[ixn]
  | add_typ_ixns(ixns,TFree(_)) = ixns;

fun add_term_tvar_ixns(Const(_,T),ixns) = add_typ_ixns(ixns,T)
  | add_term_tvar_ixns(Free(_,T),ixns) = add_typ_ixns(ixns,T)
  | add_term_tvar_ixns(Var(_,T),ixns) = add_typ_ixns(ixns,T)
  | add_term_tvar_ixns(Bound _,ixns) = ixns
  | add_term_tvar_ixns(Abs(_,T,t),ixns) =
      add_term_tvar_ixns(t,add_typ_ixns(ixns,T))
  | add_term_tvar_ixns(f$t,ixns) =
      add_term_tvar_ixns(t,add_term_tvar_ixns(f,ixns));

(** Frees and Vars **)

(*a partial ordering (not reflexive) for atomic terms*)
fun atless (Const (a,_), Const (b,_))  =  a<b
  | atless (Free (a,_), Free (b,_)) =  a<b
  | atless (Var(v,_), Var(w,_))  =  xless(v,w)
  | atless (Bound i, Bound j)  =   i<j
  | atless _  =  false;

(*insert atomic term into partially sorted list, suppressing duplicates (?)*)
fun insert_aterm (t,us) =
  let fun inserta [] = [t]
        | inserta (us as u::us') = 
	      if atless(t,u) then t::us
	      else if t=u then us (*duplicate*)
	      else u :: inserta(us')
  in  inserta us  end;

(*Accumulates the Vars in the term, suppressing duplicates*)
fun add_term_vars (t, vars: term list) = case t of
    Var   _ => insert_aterm(t,vars)
  | Abs (_,_,body) => add_term_vars(body,vars)
  | f$t =>  add_term_vars (f, add_term_vars(t, vars))
  | _ => vars;

fun term_vars t = add_term_vars(t,[]);

(*Accumulates the Frees in the term, suppressing duplicates*)
fun add_term_frees (t, frees: term list) = case t of
    Free   _ => insert_aterm(t,frees)
  | Abs (_,_,body) => add_term_frees(body,frees)
  | f$t =>  add_term_frees (f, add_term_frees(t, frees))
  | _ => frees;

fun term_frees t = add_term_frees(t,[]);

(*Given an abstraction over P, replaces the bound variable by a Free variable
  having a unique name. *)
fun variant_abs (a,T,P) =
  let val b = variant (add_term_names(P,[])) a
  in  (b,  subst_bound (Free(b,T), P))  end;

(* renames and reverses the strings in vars away from names *)
fun rename_aTs names vars : (string*typ)list =
  let fun rename_aT (vars,(a,T)) =
		(variant (map #1 vars @ names) a, T) :: vars
  in foldl rename_aT ([],vars) end;

fun rename_wrt_term t = rename_aTs (add_term_names(t,[]));



(*** Compression of terms and types by sharing common subtrees.  
     Saves 50-75% on storage requirements.  As it is fairly slow, 
     it is called only for axioms, stored theorems, etc. ***)

(** Sharing of types **)

fun atomic_tag (Type (a,_)) = if a<>"fun" then a else raise Match
  | atomic_tag (TFree (a,_)) = a
  | atomic_tag (TVar ((a,_),_)) = a;

fun type_tag (Type("fun",[S,T])) = atomic_tag S ^ type_tag T
  | type_tag T = atomic_tag T;

val memo_types = ref (Symtab.null : typ list Symtab.table);

fun find_type (T, []: typ list) = None
  | find_type (T, T'::Ts) =
       if T=T' then Some T'
       else find_type (T, Ts);

fun compress_type T =
  let val tag = type_tag T
      val tylist = the (Symtab.lookup (!memo_types, tag))
	           handle _ => []
  in  
      case find_type (T,tylist) of
	Some T' => T'
      | None => 
	    let val T' =
		case T of
		    Type (a,Ts) => Type (a, map compress_type Ts)
		  | _ => T
	    in  memo_types := Symtab.update ((tag, T'::tylist), !memo_types);
		T
	    end
  end
  handle Match =>
      let val Type (a,Ts) = T
      in  Type (a, map compress_type Ts)  end;

(** Sharing of atomic terms **)

val memo_terms = ref (Symtab.null : term list Symtab.table);

fun find_term (t, []: term list) = None
  | find_term (t, t'::ts) =
       if t=t' then Some t'
       else find_term (t, ts);

fun const_tag (Const (a,_)) = a
  | const_tag (Free (a,_))  = a
  | const_tag (Var ((a,i),_)) = a
  | const_tag (t as Bound _)  = ".B.";

fun share_term (t $ u) = share_term t $ share_term u
  | share_term (Abs (a,T,u)) = Abs (a, T, share_term u)
  | share_term t =
      let val tag = const_tag t
	  val ts = the (Symtab.lookup (!memo_terms, tag))
	               handle _ => []
      in 
	  case find_term (t,ts) of
	      Some t' => t'
	    | None => (memo_terms := Symtab.update ((tag, t::ts), !memo_terms);
		       t)
      end;

val compress_term = share_term o map_term_types compress_type;

end;

open Term;
