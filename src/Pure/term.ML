(*  Title:      Pure/term.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   Cambridge University 1992

Simply typed lambda-calculus: types, terms, and basic operations.
*)

infix 9  $;
infixr 5 -->;
infixr --->;
infix aconv;

signature BASIC_TERM =
sig
  type indexname
  type class
  type sort
  datatype typ =
    Type  of string * typ list |
    TFree of string * sort |
    TVar  of indexname * sort
  val --> : typ * typ -> typ
  val ---> : typ list * typ -> typ
  val is_TVar: typ -> bool
  val domain_type: typ -> typ
  val range_type: typ -> typ
  val binder_types: typ -> typ list
  val body_type: typ -> typ
  val strip_type: typ -> typ list * typ
  datatype term =
    Const of string * typ |
    Free of string * typ |
    Var of indexname * typ |
    Bound of int |
    Abs of string * typ * term |
    $ of term * term
  structure Vartab : TABLE
  structure Typtab : TABLE
  structure Termtab : TABLE
  exception TYPE of string * typ list * term list
  exception TERM of string * term list
  val is_Bound: term -> bool
  val is_Const: term -> bool
  val is_Free: term -> bool
  val is_Var: term -> bool
  val dest_Type: typ -> string * typ list
  val dest_Const: term -> string * typ
  val dest_Free: term -> string * typ
  val dest_Var: term -> indexname * typ
  val type_of: term -> typ
  val type_of1: typ list * term -> typ
  val fastype_of: term -> typ
  val fastype_of1: typ list * term -> typ
  val list_abs: (string * typ) list * term -> term
  val strip_abs_body: term -> term
  val strip_abs_vars: term -> (string * typ) list
  val strip_qnt_body: string -> term -> term
  val strip_qnt_vars: string -> term -> (string * typ) list
  val list_comb: term * term list -> term
  val strip_comb: term -> term * term list
  val head_of: term -> term
  val size_of_term: term -> int
  val map_type_tvar: (indexname * sort -> typ) -> typ -> typ
  val map_type_tfree: (string * sort -> typ) -> typ -> typ
  val map_term_types: (typ -> typ) -> term -> term
  val it_term_types: (typ * 'a -> 'a) -> term * 'a -> 'a
  val map_typ: (class -> class) -> (string -> string) -> typ -> typ
  val map_term:
     (class -> class) ->
     (string -> string) -> (string -> string) -> term -> term
  val foldl_atyps: ('a * typ -> 'a) -> 'a * typ -> 'a
  val foldl_term_types: (term -> 'a * typ -> 'a) -> 'a * term -> 'a
  val foldl_types: ('a * typ -> 'a) -> 'a * term -> 'a
  val foldl_aterms: ('a * term -> 'a) -> 'a * term -> 'a
  val foldl_map_aterms: ('a * term -> 'a * term) -> 'a * term -> 'a * term
  val dummyT: typ
  val logicC: class
  val logicS: sort
  val itselfT: typ -> typ
  val a_itselfT: typ
  val propT: typ
  val implies: term
  val all: typ -> term
  val equals: typ -> term
  val flexpair: typ -> term
  val strip_all_body: term -> term
  val strip_all_vars: term -> (string * typ) list
  val incr_bv: int * int * term -> term
  val incr_boundvars: int -> term -> term
  val add_loose_bnos: term * int * int list -> int list
  val loose_bnos: term -> int list
  val loose_bvar: term * int -> bool
  val loose_bvar1: term * int -> bool
  val subst_bounds: term list * term -> term
  val subst_bound: term * term -> term
  val subst_TVars: (indexname * typ) list -> term -> term
  val subst_TVars_Vartab: typ Vartab.table -> term -> term
  val betapply: term * term -> term
  val eq_ix: indexname * indexname -> bool
  val ins_ix: indexname * indexname list -> indexname list
  val mem_ix: indexname * indexname list -> bool
  val eq_sort: sort * class list -> bool
  val mem_sort: sort * class list list -> bool
  val subset_sort: sort list * class list list -> bool
  val eq_set_sort: sort list * sort list -> bool
  val ins_sort: sort * class list list -> class list list
  val union_sort: sort list * sort list -> sort list
  val rems_sort: sort list * sort list -> sort list
  val aconv: term * term -> bool
  val aconvs: term list * term list -> bool
  val mem_term: term * term list -> bool
  val subset_term: term list * term list -> bool
  val eq_set_term: term list * term list -> bool
  val ins_term: term * term list -> term list
  val union_term: term list * term list -> term list
  val inter_term: term list * term list -> term list
  val could_unify: term * term -> bool
  val subst_free: (term * term) list -> term -> term
  val subst_atomic: (term * term) list -> term -> term
  val subst_vars: (indexname * typ) list * (indexname * term) list -> term -> term
  val typ_subst_TVars: (indexname * typ) list -> typ -> typ
  val typ_subst_TVars_Vartab : typ Vartab.table -> typ -> typ
  val subst_Vars: (indexname * term) list -> term -> term
  val incr_tvar: int -> typ -> typ
  val xless: (string * int) * indexname -> bool
  val atless: term * term -> bool
  val insert_aterm: term * term list -> term list
  val abstract_over: term * term -> term
  val lambda: term -> term -> term
  val absfree: string * typ * term -> term
  val list_abs_free: (string * typ) list * term -> term
  val list_all_free: (string * typ) list * term -> term
  val list_all: (string * typ) list * term -> term
  val maxidx_of_typ: typ -> int
  val maxidx_of_typs: typ list -> int
  val maxidx_of_term: term -> int
  val read_radixint: int * string list -> int * string list
  val read_int: string list -> int * string list
  val oct_char: string -> string
  val variant: string list -> string -> string
  val variantlist: string list * string list -> string list
  val variant_abs: string * typ * term -> string * term
  val rename_wrt_term: term -> (string * typ) list -> (string * typ) list
  val add_new_id: string list * string -> string list
  val add_typ_classes: typ * class list -> class list
  val add_typ_ixns: indexname list * typ -> indexname list
  val add_typ_tfree_names: typ * string list -> string list
  val add_typ_tfrees: typ * (string * sort) list -> (string * sort) list
  val typ_tfrees: typ -> (string * sort) list
  val add_typ_tvars: typ * (indexname * sort) list -> (indexname * sort) list
  val typ_tvars: typ -> (indexname * sort) list
  val add_typ_tycons: typ * string list -> string list
  val add_typ_varnames: typ * string list -> string list
  val add_term_classes: term * class list -> class list
  val add_term_consts: term * string list -> string list
  val add_term_frees: term * term list -> term list
  val term_frees: term -> term list
  val add_term_free_names: term * string list -> string list
  val add_term_names: term * string list -> string list
  val add_term_tfree_names: term * string list -> string list
  val add_term_tfrees: term * (string * sort) list -> (string * sort) list
  val term_tfrees: term -> (string * sort) list
  val add_term_tvar_ixns: term * indexname list -> indexname list
  val add_term_tvarnames: term * string list -> string list
  val add_term_tvars: term * (indexname * sort) list -> (indexname * sort) list
  val term_tvars: term -> (indexname * sort) list
  val add_term_tycons: term * string list -> string list
  val add_term_vars: term * term list -> term list
  val term_vars: term -> term list
  val exists_Const: (string * typ -> bool) -> term -> bool
  val exists_subterm: (term -> bool) -> term -> bool
  val compress_type: typ -> typ
  val compress_term: term -> term
end;

signature TERM =
sig
  include BASIC_TERM
  val match_bvars: (term * term) * (string * string) list -> (string * string) list
  val rename_abs: term -> term -> term -> term option
  val invent_names: string list -> string -> int -> string list
  val invent_type_names: string list -> int -> string list
  val add_tvarsT: (indexname * sort) list * typ -> (indexname * sort) list
  val add_tvars: (indexname * sort) list * term -> (indexname * sort) list
  val add_vars: (indexname * typ) list * term -> (indexname * typ) list
  val add_frees: (string * typ) list * term -> (string * typ) list
  val indexname_ord: indexname * indexname -> order
  val typ_ord: typ * typ -> order
  val typs_ord: typ list * typ list -> order
  val term_ord: term * term -> order
  val terms_ord: term list * term list -> order
  val termless: term * term -> bool
  val dummy_patternN: string
  val no_dummy_patterns: term -> term
  val replace_dummy_patterns: int * term -> int * term
  val is_replaced_dummy_pattern: indexname -> bool
  val adhoc_freeze_vars: term -> term * string list
end;

structure Term: TERM =
struct

(*Indexnames can be quickly renamed by adding an offset to the integer part,
  for resolution.*)
type indexname = string*int;

(* Types are classified by sorts. *)
type class = string;
type sort  = class list;

(* The sorts attached to TFrees and TVars specify the sort of that variable *)
datatype typ = Type  of string * typ list
             | TFree of string * sort
             | TVar  of indexname * sort;

(*Terms.  Bound variables are indicated by depth number.
  Free variables, (scheme) variables and constants have names.
  An term is "closed" if every bound variable of level "lev"
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

(*For system errors involving terms*)
exception TERM of string * term list;


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


(** Types **)

fun S --> T = Type("fun",[S,T]);

(*handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)*)
val op ---> = foldr (op -->);

fun dest_Type (Type x) = x
  | dest_Type T = raise TYPE ("dest_Type", [T], []);


(** Discriminators **)

fun is_Bound (Bound _) = true
  | is_Bound _         = false;

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


fun domain_type (Type("fun", [T,_])) = T
and range_type  (Type("fun", [_,T])) = T;

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


val list_abs = foldr (fn ((x, T), t) => Abs (x, T, t));

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

(*Scan a pair of terms; while they are similar,
  accumulate corresponding bound vars in "al"*)
fun match_bvs(Abs(x,_,s),Abs(y,_,t), al) =
      match_bvs(s, t, if x="" orelse y="" then al
                                          else (x,y)::al)
  | match_bvs(f$s, g$t, al) = match_bvs(f,g,match_bvs(s,t,al))
  | match_bvs(_,_,al) = al;

(* strip abstractions created by parameters *)
fun match_bvars((s,t),al) = match_bvs(strip_abs_body s, strip_abs_body t, al);

fun rename_abs pat obj t =
  let
    val ren = match_bvs (pat, obj, []);
    fun ren_abs (Abs (x, T, b)) =
          Abs (if_none (assoc_string (ren, x)) x, T, ren_abs b)
      | ren_abs (f $ t) = ren_abs f $ ren_abs t
      | ren_abs t = t
  in if null ren then None else Some (ren_abs t) end;

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

fun loose_bvar1(Bound i,k) = i = k
  | loose_bvar1(f$t, k) = loose_bvar1(f,k) orelse loose_bvar1(t,k)
  | loose_bvar1(Abs(_,_,t),k) = loose_bvar1(t,k+1)
  | loose_bvar1 _ = false;

(*Substitute arguments for loose bound variables.
  Beta-reduction of arg(n-1)...arg0 into t replacing (Bound i) with (argi).
  Note that for ((%x y. c) a b), the bound vars in c are x=1 and y=0
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
fun eq_ix ((a, i):indexname, (a',i'):indexname) = (a=a') andalso i=i';

(*membership in a list, optimized version for indexnames*)
fun mem_ix (_, []) = false
  | mem_ix (x, y :: ys) = eq_ix(x,y) orelse mem_ix (x, ys);

(*insertion into list, optimized version for indexnames*)
fun ins_ix (x,xs) = if mem_ix (x, xs) then xs else x :: xs;

(*Tests whether 2 terms are alpha-convertible and have same type.
  Note that constants may have more than one type.*)
fun (Const(a,T)) aconv (Const(b,U)) = a=b  andalso  T=U
  | (Free(a,T))  aconv (Free(b,U))  = a=b  andalso  T=U
  | (Var(v,T))   aconv (Var(w,U))   = eq_ix(v,w)  andalso  T=U
  | (Bound i)    aconv (Bound j)    = i=j
  | (Abs(_,T,t)) aconv (Abs(_,U,u)) = t aconv u  andalso  T=U
  | (f$t)        aconv (g$u)        = (f aconv g) andalso (t aconv u)
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

fun inter_term ([], ys) = []
  | inter_term (x::xs, ys) =
      if mem_term (x,ys) then x :: inter_term(xs,ys) else inter_term(xs,ys);

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

val rems_sort = gen_rems eq_sort;

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

fun lambda v t =
  let val (x, T) = dest_Free v
  in Abs (x, T, abstract_over (v, t)) end;

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
            | subst t = if_none (assoc(instl,t)) t
      in  subst t  end;

(*Substitute for type Vars in a type*)
fun typ_subst_TVars iTs T = if null iTs then T else
  let fun subst(Type(a,Ts)) = Type(a, map subst Ts)
        | subst(T as TFree _) = T
        | subst(T as TVar(ixn,_)) = if_none (assoc(iTs,ixn)) T
  in subst T end;

(*Substitute for type Vars in a term*)
val subst_TVars = map_term_types o typ_subst_TVars;

(*Substitute for Vars in a term; see also envir/norm_term*)
fun subst_Vars itms t = if null itms then t else
  let fun subst(v as Var(ixn,_)) = if_none (assoc(itms,ixn)) v
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


(*Dummy type for parsing and printing.  Will be replaced during type inference. *)
val dummyT = Type("dummy",[]);

(*read a numeral of the given radix, normally 10*)
fun read_radixint (radix: int, cs) : int * string list =
  let val zero = ord"0"
      val limit = zero+radix
      fun scan (num,[]) = (num,[])
        | scan (num, c::cs) =
              if  zero <= ord c  andalso  ord c < limit
              then scan(radix*num + ord c - zero, cs)
              else (num, c::cs)
  in  scan(0,cs)  end;

fun read_int cs = read_radixint (10, cs);

fun octal s = #1 (read_radixint (8, explode s));
val oct_char = chr o octal;


(*** Printing ***)

(*Makes a variant of the name c distinct from the names in bs.
  First attaches the suffix "a" and then increments this;
  preserves a suffix of underscores "_". *)
fun variant bs name =
  let
    val (c, u) = pairself implode (Library.take_suffix (equal "_") (Symbol.explode name));
    fun vary2 c = if ((c ^ u) mem_string bs) then vary2 (Symbol.bump_string c) else c;
    fun vary1 c = if ((c ^ u) mem_string bs) then vary2 (c ^ "a") else c;
  in vary1 (if c = "" then "u" else c) ^ u end;

(*Create variants of the list of names, with priority to the first ones*)
fun variantlist ([], used) = []
  | variantlist(b::bs, used) =
      let val b' = variant used b
      in  b' :: variantlist (bs, b'::used)  end;

fun invent_names used prfx n = variantlist (Library.replicate n prfx, prfx :: used);
fun invent_type_names used = invent_names used "'";



(** Consts etc. **)

fun add_typ_classes (Type (_, Ts), cs) = foldr add_typ_classes (Ts, cs)
  | add_typ_classes (TFree (_, S), cs) = S union cs
  | add_typ_classes (TVar (_, S), cs) = S union cs;

fun add_typ_tycons (Type (c, Ts), cs) = foldr add_typ_tycons (Ts, c ins cs)
  | add_typ_tycons (_, cs) = cs;

val add_term_classes = it_term_types add_typ_classes;
val add_term_tycons = it_term_types add_typ_tycons;

fun add_term_consts (Const (c, _), cs) = c ins_string cs
  | add_term_consts (t $ u, cs) = add_term_consts (t, add_term_consts (u, cs))
  | add_term_consts (Abs (_, _, t), cs) = add_term_consts (t, cs)
  | add_term_consts (_, cs) = cs;

fun exists_Const P t = let
        fun ex (Const c      ) = P c
        |   ex (t $ u        ) = ex t orelse ex u
        |   ex (Abs (_, _, t)) = ex t
        |   ex _               = false
    in ex t end;

fun exists_subterm P =
  let fun ex t = P t orelse
                 (case t of
                    u $ v        => ex u orelse ex v
                  | Abs(_, _, u) => ex u
                  | _            => false)
  in ex end;

(*map classes, tycons*)
fun map_typ f g (Type (c, Ts)) = Type (g c, map (map_typ f g) Ts)
  | map_typ f _ (TFree (x, S)) = TFree (x, map f S)
  | map_typ f _ (TVar (xi, S)) = TVar (xi, map f S);

(*map classes, tycons, consts*)
fun map_term f g h (Const (c, T)) = Const (h c, map_typ f g T)
  | map_term f g _ (Free (x, T)) = Free (x, map_typ f g T)
  | map_term f g _ (Var (xi, T)) = Var (xi, map_typ f g T)
  | map_term _ _ _ (t as Bound _) = t
  | map_term f g h (Abs (x, T, t)) = Abs (x, map_typ f g T, map_term f g h t)
  | map_term f g h (t $ u) = map_term f g h t $ map_term f g h u;



(** TFrees and TVars **)

(*maps  (bs,v)  to   v'::bs    this reverses the identifiers bs*)
fun add_new_id (bs, c) : string list =  variant bs c  ::  bs;

(*Accumulates the names of Frees in the term, suppressing duplicates.*)
fun add_term_free_names (Free(a,_), bs) = a ins_string bs
  | add_term_free_names (f$u, bs) = add_term_free_names (f, add_term_free_names(u, bs))
  | add_term_free_names (Abs(_,_,t), bs) = add_term_free_names(t,bs)
  | add_term_free_names (_, bs) = bs;

(*Accumulates the names in the term, suppressing duplicates.
  Includes Frees and Consts.  For choosing unambiguous bound var names.*)
fun add_term_names (Const(a,_), bs) = NameSpace.base a ins_string bs
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


(* left-ro-right traversal *)

(*foldl atoms of type*)
fun foldl_atyps f (x, Type (_, Ts)) = foldl (foldl_atyps f) (x, Ts)
  | foldl_atyps f x_atom = f x_atom;

(*foldl atoms of term*)
fun foldl_aterms f (x, t $ u) = foldl_aterms f (foldl_aterms f (x, t), u)
  | foldl_aterms f (x, Abs (_, _, t)) = foldl_aterms f (x, t)
  | foldl_aterms f x_atom = f x_atom;

fun foldl_map_aterms f (x, t $ u) =
      let val (x', t') = foldl_map_aterms f (x, t); val (x'', u') = foldl_map_aterms f (x', u);
      in (x'', t' $ u') end
  | foldl_map_aterms f (x, Abs (a, T, t)) =
      let val (x', t') = foldl_map_aterms f (x, t) in (x', Abs (a, T, t')) end
  | foldl_map_aterms f x_atom = f x_atom;

(*foldl types of term*)
fun foldl_term_types f (x, t as Const (_, T)) = f t (x, T)
  | foldl_term_types f (x, t as Free (_, T)) = f t (x, T)
  | foldl_term_types f (x, t as Var (_, T)) = f t (x, T)
  | foldl_term_types f (x, Bound _) = x
  | foldl_term_types f (x, t as Abs (_, T, b)) = foldl_term_types f (f t (x, T), b)
  | foldl_term_types f (x, t $ u) = foldl_term_types f (foldl_term_types f (x, t), u);

fun foldl_types f = foldl_term_types (fn _ => f);

(*collect variables*)
val add_tvarsT = foldl_atyps (fn (vs, TVar v) => v ins vs | (vs, _) => vs);
val add_tvars = foldl_types add_tvarsT;
val add_vars = foldl_aterms (fn (vs, Var v) => v ins vs | (vs, _) => vs);
val add_frees = foldl_aterms (fn (vs, Free v) => v ins vs | (vs, _) => vs);



(** type and term orders **)

fun indexname_ord ((x, i), (y, j)) =
  (case int_ord (i, j) of EQUAL => string_ord (x, y) | ord => ord);

val sort_ord = list_ord string_ord;


(* typ_ord *)

fun typ_ord (Type x, Type y) = prod_ord string_ord typs_ord (x, y)
  | typ_ord (Type _, _) = GREATER
  | typ_ord (TFree _, Type _) = LESS
  | typ_ord (TFree x, TFree y) = prod_ord string_ord sort_ord (x, y)
  | typ_ord (TFree _, TVar _) = GREATER
  | typ_ord (TVar _, Type _) = LESS
  | typ_ord (TVar _, TFree _) = LESS
  | typ_ord (TVar x, TVar y) = prod_ord indexname_ord sort_ord (x, y)
and typs_ord Ts_Us = list_ord typ_ord Ts_Us;


(* term_ord *)

(*a linear well-founded AC-compatible ordering for terms:
  s < t <=> 1. size(s) < size(t) or
            2. size(s) = size(t) and s=f(...) and t=g(...) and f<g or
            3. size(s) = size(t) and s=f(s1..sn) and t=f(t1..tn) and
               (s1..sn) < (t1..tn) (lexicographically)*)

fun dest_hd (Const (a, T)) = (((a, 0), T), 0)
  | dest_hd (Free (a, T)) = (((a, 0), T), 1)
  | dest_hd (Var v) = (v, 2)
  | dest_hd (Bound i) = ((("", i), dummyT), 3)
  | dest_hd (Abs (_, T, _)) = ((("", 0), T), 4);

fun term_ord (Abs (_, T, t), Abs(_, U, u)) =
      (case term_ord (t, u) of EQUAL => typ_ord (T, U) | ord => ord)
  | term_ord (t, u) =
      (case int_ord (size_of_term t, size_of_term u) of
        EQUAL =>
          let val (f, ts) = strip_comb t and (g, us) = strip_comb u in
            (case hd_ord (f, g) of EQUAL => terms_ord (ts, us) | ord => ord)
          end
      | ord => ord)
and hd_ord (f, g) =
  prod_ord (prod_ord indexname_ord typ_ord) int_ord (dest_hd f, dest_hd g)
and terms_ord (ts, us) = list_ord term_ord (ts, us);

fun termless tu = (term_ord tu = LESS);

structure Vartab = TableFun(type key = indexname val ord = indexname_ord);
structure Typtab = TableFun(type key = typ val ord = typ_ord);
structure Termtab = TableFun(type key = term val ord = term_ord);

(*Substitute for type Vars in a type, version using Vartab*)
fun typ_subst_TVars_Vartab iTs T = if Vartab.is_empty iTs then T else
  let fun subst(Type(a, Ts)) = Type(a, map subst Ts)
        | subst(T as TFree _) = T
        | subst(T as TVar(ixn, _)) =
            (case Vartab.lookup (iTs, ixn) of None => T | Some(U) => U)
  in subst T end;

(*Substitute for type Vars in a term, version using Vartab*)
val subst_TVars_Vartab = map_term_types o typ_subst_TVars_Vartab;


(*** Compression of terms and types by sharing common subtrees.
     Saves 50-75% on storage requirements.  As it is a bit slow,
     it should be called only for axioms, stored theorems, etc.
     Recorded term and type fragments are never disposed. ***)

(** Sharing of types **)

val memo_types = ref (Typtab.empty: typ Typtab.table);

fun compress_type T =
  (case Typtab.lookup (! memo_types, T) of
    Some T' => T'
  | None =>
      let val T' = (case T of Type (a, Ts) => Type (a, map compress_type Ts) | _ => T)
      in memo_types := Typtab.update ((T', T'), ! memo_types); T' end);


(** Sharing of atomic terms **)

val memo_terms = ref (Termtab.empty : term Termtab.table);

fun share_term (t $ u) = share_term t $ share_term u
  | share_term (Abs (a, T, u)) = Abs (a, T, share_term u)
  | share_term t =
      (case Termtab.lookup (! memo_terms, t) of
        Some t' => t'
      | None => (memo_terms := Termtab.update ((t, t), ! memo_terms); t));

val compress_term = share_term o map_term_types compress_type;


(* dummy patterns *)

val dummy_patternN = "dummy_pattern";

fun is_dummy_pattern (Const ("dummy_pattern", _)) = true
  | is_dummy_pattern _ = false;

fun no_dummy_patterns tm =
  if not (foldl_aterms (fn (b, t) => b orelse is_dummy_pattern t) (false, tm)) then tm
  else raise TERM ("Illegal occurrence of '_' dummy pattern", [tm]);

fun replace_dummy Ts (i, Const ("dummy_pattern", T)) =
      (i + 1, list_comb (Var (("_dummy_", i), Ts ---> T), map Bound (0 upto length Ts - 1)))
  | replace_dummy Ts (i, Abs (x, T, t)) =
      let val (i', t') = replace_dummy (T :: Ts) (i, t)
      in (i', Abs (x, T, t')) end
  | replace_dummy Ts (i, t $ u) =
      let val (i', t') = replace_dummy Ts (i, t); val (i'', u') = replace_dummy Ts (i', u)
      in (i'', t' $ u') end
  | replace_dummy _ (i, a) = (i, a);

val replace_dummy_patterns = replace_dummy [];

fun is_replaced_dummy_pattern ("_dummy_", _) = true
  | is_replaced_dummy_pattern _ = false;


(* adhoc freezing *)

fun adhoc_freeze_vars tm =
  let
    fun mk_inst (var as Var ((a, i), T)) =
      let val x = a ^ Library.gensym "_" ^ string_of_int i
      in ((var,  Free(x, T)), x) end;
    val (insts, xs) = split_list (map mk_inst (term_vars tm));
  in (subst_atomic insts tm, xs) end;


end;


structure BasicTerm: BASIC_TERM = Term;
open BasicTerm;
