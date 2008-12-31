(*  Title:      Pure/old_term.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Some old-style term operations.
*)

signature OLD_TERM =
sig
  val add_term_vars: term * term list -> term list
  val term_vars: term -> term list
  val add_term_frees: term * term list -> term list
  val term_frees: term -> term list
end;

structure OldTerm: OLD_TERM =
struct

(*Accumulates the Vars in the term, suppressing duplicates*)
fun add_term_vars (t, vars: term list) = case t of
    Var   _ => OrdList.insert TermOrd.term_ord t vars
  | Abs (_,_,body) => add_term_vars(body,vars)
  | f$t =>  add_term_vars (f, add_term_vars(t, vars))
  | _ => vars;

fun term_vars t = add_term_vars(t,[]);

(*Accumulates the Frees in the term, suppressing duplicates*)
fun add_term_frees (t, frees: term list) = case t of
    Free   _ => OrdList.insert TermOrd.term_ord t frees
  | Abs (_,_,body) => add_term_frees(body,frees)
  | f$t =>  add_term_frees (f, add_term_frees(t, frees))
  | _ => frees;

fun term_frees t = add_term_frees(t,[]);

end;
