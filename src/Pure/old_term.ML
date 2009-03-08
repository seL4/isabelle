(*  Title:      Pure/old_term.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Some old-style term operations.
*)

signature OLD_TERM =
sig
  val it_term_types: (typ * 'a -> 'a) -> term * 'a -> 'a
  val add_term_names: term * string list -> string list
  val add_typ_tvars: typ * (indexname * sort) list -> (indexname * sort) list
  val add_typ_tfree_names: typ * string list -> string list
  val add_typ_tfrees: typ * (string * sort) list -> (string * sort) list
  val add_term_tvars: term * (indexname * sort) list -> (indexname * sort) list
  val add_term_tfrees: term * (string * sort) list -> (string * sort) list
  val add_term_tfree_names: term * string list -> string list
  val typ_tfrees: typ -> (string * sort) list
  val typ_tvars: typ -> (indexname * sort) list
  val term_tfrees: term -> (string * sort) list
  val term_tvars: term -> (indexname * sort) list
  val add_term_vars: term * term list -> term list
  val term_vars: term -> term list
  val add_term_frees: term * term list -> term list
  val term_frees: term -> term list
end;

structure OldTerm: OLD_TERM =
struct

(*iterate a function over all types in a term*)
fun it_term_types f =
let fun iter(Const(_,T), a) = f(T,a)
      | iter(Free(_,T), a) = f(T,a)
      | iter(Var(_,T), a) = f(T,a)
      | iter(Abs(_,T,t), a) = iter(t,f(T,a))
      | iter(f$u, a) = iter(f, iter(u, a))
      | iter(Bound _, a) = a
in iter end

(*Accumulates the names in the term, suppressing duplicates.
  Includes Frees and Consts.  For choosing unambiguous bound var names.*)
fun add_term_names (Const(a,_), bs) = insert (op =) (Long_Name.base_name a) bs
  | add_term_names (Free(a,_), bs) = insert (op =) a bs
  | add_term_names (f$u, bs) = add_term_names (f, add_term_names(u, bs))
  | add_term_names (Abs(_,_,t), bs) = add_term_names(t,bs)
  | add_term_names (_, bs) = bs;

(*Accumulates the TVars in a type, suppressing duplicates.*)
fun add_typ_tvars(Type(_,Ts),vs) = List.foldr add_typ_tvars vs Ts
  | add_typ_tvars(TFree(_),vs) = vs
  | add_typ_tvars(TVar(v),vs) = insert (op =) v vs;

(*Accumulates the TFrees in a type, suppressing duplicates.*)
fun add_typ_tfree_names(Type(_,Ts),fs) = List.foldr add_typ_tfree_names fs Ts
  | add_typ_tfree_names(TFree(f,_),fs) = insert (op =) f fs
  | add_typ_tfree_names(TVar(_),fs) = fs;

fun add_typ_tfrees(Type(_,Ts),fs) = List.foldr add_typ_tfrees fs Ts
  | add_typ_tfrees(TFree(f),fs) = insert (op =) f fs
  | add_typ_tfrees(TVar(_),fs) = fs;

(*Accumulates the TVars in a term, suppressing duplicates.*)
val add_term_tvars = it_term_types add_typ_tvars;

(*Accumulates the TFrees in a term, suppressing duplicates.*)
val add_term_tfrees = it_term_types add_typ_tfrees;
val add_term_tfree_names = it_term_types add_typ_tfree_names;

(*Non-list versions*)
fun typ_tfrees T = add_typ_tfrees(T,[]);
fun typ_tvars T = add_typ_tvars(T,[]);
fun term_tfrees t = add_term_tfrees(t,[]);
fun term_tvars t = add_term_tvars(t,[]);


(*Accumulates the Vars in the term, suppressing duplicates.*)
fun add_term_vars (t, vars: term list) = case t of
    Var   _ => OrdList.insert TermOrd.term_ord t vars
  | Abs (_,_,body) => add_term_vars(body,vars)
  | f$t =>  add_term_vars (f, add_term_vars(t, vars))
  | _ => vars;

fun term_vars t = add_term_vars(t,[]);

(*Accumulates the Frees in the term, suppressing duplicates.*)
fun add_term_frees (t, frees: term list) = case t of
    Free   _ => OrdList.insert TermOrd.term_ord t frees
  | Abs (_,_,body) => add_term_frees(body,frees)
  | f$t =>  add_term_frees (f, add_term_frees(t, frees))
  | _ => frees;

fun term_frees t = add_term_frees(t,[]);

end;
