(*  Title:      TFL/dcterm
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

(*---------------------------------------------------------------------------
 * Derived efficient cterm destructors.
 *---------------------------------------------------------------------------*)

structure Dcterm :
sig
    val mk_conj : cterm * cterm -> cterm
    val mk_disj : cterm * cterm -> cterm
    val mk_exists : cterm * cterm -> cterm

    val dest_conj : cterm -> cterm * cterm
    val dest_const : cterm -> {Name:string, Ty:typ}
    val dest_disj : cterm -> cterm * cterm
    val dest_eq : cterm -> cterm * cterm
    val dest_exists : cterm -> cterm * cterm
    val dest_forall : cterm -> cterm * cterm
    val dest_imp : cterm -> cterm * cterm
    val dest_let : cterm -> cterm * cterm
    val dest_neg : cterm -> cterm
    val dest_pair : cterm -> cterm * cterm
    val dest_var : cterm -> {Name:string, Ty:typ}
    val is_conj : cterm -> bool
    val is_cons : cterm -> bool
    val is_disj : cterm -> bool
    val is_eq : cterm -> bool
    val is_exists : cterm -> bool
    val is_forall : cterm -> bool
    val is_imp : cterm -> bool
    val is_let : cterm -> bool
    val is_neg : cterm -> bool
    val is_pair : cterm -> bool
    val list_mk_abs : cterm list -> cterm -> cterm
    val list_mk_exists : cterm list * cterm -> cterm
    val list_mk_disj : cterm list -> cterm
    val strip_abs : cterm -> cterm list * cterm
    val strip_comb : cterm -> cterm * cterm list
    val strip_disj : cterm -> cterm list
    val strip_exists : cterm -> cterm list * cterm
    val strip_forall : cterm -> cterm list * cterm
    val strip_imp : cterm -> cterm list * cterm
    val drop_prop : cterm -> cterm
    val mk_prop : cterm -> cterm
  end =
struct

fun ERR func mesg = Utils.ERR{module = "Dcterm", func = func, mesg = mesg};

(*---------------------------------------------------------------------------
 * General support routines
 *---------------------------------------------------------------------------*)
val can = Utils.can;
fun swap (x,y) = (y,x);

fun itlist f L base_value =
   let fun it [] = base_value
         | it (a::rst) = f a (it rst)
   in it L 
   end;

val end_itlist = Utils.end_itlist;


(*---------------------------------------------------------------------------
 * Some simple constructor functions.
 *---------------------------------------------------------------------------*)

fun mk_const sign pr = cterm_of sign (Const pr);
val mk_hol_const = mk_const (sign_of HOL.thy);

fun mk_exists (r as (Bvar,Body)) = 
  let val ty = #T(rep_cterm Bvar)
      val c = mk_hol_const("Ex", (ty --> HOLogic.boolT) --> HOLogic.boolT)
  in capply c (uncurry cabs r)
  end;


local val c = mk_hol_const("op &", HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT)
in fun mk_conj(conj1,conj2) = capply (capply c conj1) conj2
end;

local val c = mk_hol_const("op |", HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT)
in fun mk_disj(disj1,disj2) = capply (capply c disj1) disj2
end;


(*---------------------------------------------------------------------------
 * The primitives.
 *---------------------------------------------------------------------------*)
fun dest_const ctm = 
   (case #t(rep_cterm ctm)
      of Const(s,ty) => {Name = s, Ty = ty}
       | _ => raise ERR "dest_const" "not a constant");

fun dest_var ctm = 
   (case #t(rep_cterm ctm)
      of Var((s,i),ty) => {Name=s, Ty=ty}
       | Free(s,ty)    => {Name=s, Ty=ty}
       |             _ => raise ERR "dest_var" "not a variable");


(*---------------------------------------------------------------------------
 * Derived destructor operations. 
 *---------------------------------------------------------------------------*)

fun dest_monop expected tm = 
 let exception Fail
     val (c,N) = dest_comb tm
 in if (#Name(dest_const c) = expected) then N else raise Fail
 end handle e => raise ERR "dest_monop" ("Not a(n) "^quote expected);

fun dest_binop expected tm =
 let val (M,N) = dest_comb tm
 in (dest_monop expected M, N)
 end handle e => raise ERR "dest_binop" ("Not a(n) "^quote expected);

(* For "if-then-else" 
fun dest_triop expected tm =
 let val (MN,P) = dest_comb tm
     val (M,N) = dest_binop expected MN
 in (M,N,P)
 end handle e => raise ERR "dest_triop" ("Not a(n) "^quote expected);
*)

fun dest_binder expected tm = 
  dest_abs(dest_monop expected tm)
  handle e => raise ERR "dest_binder" ("Not a(n) "^quote expected);


val dest_neg    = dest_monop "not"
val dest_pair   = dest_binop "Pair";
val dest_eq     = dest_binop "op ="
val dest_imp    = dest_binop "op -->"
val dest_conj   = dest_binop "op &"
val dest_disj   = dest_binop "op |"
val dest_cons   = dest_binop "op #"
val dest_let    = swap o dest_binop "Let";
(* val dest_cond   = dest_triop "if" *)
val dest_select = dest_binder "Eps"
val dest_exists = dest_binder "Ex"
val dest_forall = dest_binder "All"

(* Query routines *)

val is_eq     = can dest_eq
val is_imp    = can dest_imp
val is_select = can dest_select
val is_forall = can dest_forall
val is_exists = can dest_exists
val is_neg    = can dest_neg
val is_conj   = can dest_conj
val is_disj   = can dest_disj
(* val is_cond   = can dest_cond *)
val is_pair   = can dest_pair
val is_let    = can dest_let
val is_cons   = can dest_cons


(*---------------------------------------------------------------------------
 * Iterated creation.
 *---------------------------------------------------------------------------*)
val list_mk_abs = itlist cabs;

fun list_mk_exists(V,t) = itlist(fn v => fn b => mk_exists(v, b)) V t;
val list_mk_disj = end_itlist(fn d1 => fn tm => mk_disj(d1, tm))

(*---------------------------------------------------------------------------
 * Iterated destruction. (To the "right" in a term.)
 *---------------------------------------------------------------------------*)
fun strip break tm = 
  let fun dest (p as (ctm,accum)) = 
        let val (M,N) = break ctm
        in dest (N, M::accum)
        end handle _ => p
  in dest (tm,[])
  end;

fun rev2swap (x,l) = (rev l, x);

val strip_comb   = strip (swap o dest_comb)  (* Goes to the "left" *)
val strip_imp    = rev2swap o strip dest_imp
val strip_abs    = rev2swap o strip dest_abs
val strip_forall = rev2swap o strip dest_forall
val strip_exists = rev2swap o strip dest_exists

val strip_disj   = rev o (op::) o strip dest_disj


(*---------------------------------------------------------------------------
 * Going into and out of prop
 *---------------------------------------------------------------------------*)
local val prop = cterm_of (sign_of HOL.thy) (read"Trueprop")
in fun mk_prop ctm =
     case (#t(rep_cterm ctm))
       of (Const("Trueprop",_)$_) => ctm
        |  _ => capply prop ctm
end;

fun drop_prop ctm = dest_monop "Trueprop" ctm handle _ => ctm;

end;
