(*  Title:      HOL/Tools/function_package/lib.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Some fairly general functions that should probably go somewhere else... 
*)



structure FundefLib = struct

fun map_option f NONE = NONE 
  | map_option f (SOME x) = SOME (f x);

fun fold_option f NONE y = y
  | fold_option f (SOME x) y = f x y;

fun fold_map_option f NONE y = (NONE, y)
  | fold_map_option f (SOME x) y = apfst SOME (f x y);

(* ??? *)
fun eq_str (s : string, t) = (s = t) (* monomorphic equality on strings *)

(* ==> logic.ML? *)
fun mk_forall v t = all (fastype_of v) $ lambda v t

(* lambda-abstracts over an arbitrarily nested tuple
  ==> hologic.ML? *)
fun tupled_lambda vars t =
    case vars of
      (Free v) => lambda (Free v) t
    | (Var v) => lambda (Var v) t
    | (Const ("Pair", Type ("fun", [Ta, Type ("fun", [Tb, _])]))) $ us $ vs =>  
      (HOLogic.split_const (Ta,Tb, fastype_of t)) $ (tupled_lambda us (tupled_lambda vs t))
    | _ => raise Match
                 
                 
fun dest_all (Const ("all", _) $ Abs (a as (_,T,_))) =
    let
      val (n, body) = Term.dest_abs a
    in
      (Free (n, T), body)
    end
  | dest_all _ = raise Match
                         

(* Removes all quantifiers from a term, replacing bound variables by frees. *)
fun dest_all_all (t as (Const ("all",_) $ _)) = 
    let
      val (v,b) = dest_all t
      val (vs, b') = dest_all_all b
    in
      (v :: vs, b')
    end
  | dest_all_all t = ([],t)
                     

(* FIXME: similar to Variable.focus *)
fun dest_all_all_ctx ctx (Const ("all", _) $ Abs (a as (n,T,b))) =
    let
      val [(n', _)] = Variable.variant_frees ctx [] [(n,T)]
      val (_, ctx') = ProofContext.add_fixes_i [(n', SOME T, NoSyn)] ctx

      val (n'', body) = Term.dest_abs (n', T, b) 
      val _ = (n' = n'') orelse error "dest_all_ctx"
      (* Note: We assume that n' does not occur in the body. Otherwise it would be fixed. *)

      val (ctx'', vs, bd) = dest_all_all_ctx ctx' body
    in
      (ctx'', (n', T) :: vs, bd)
    end
  | dest_all_all_ctx ctx t = 
    (ctx, [], t)


fun implies_elim_swp a b = implies_elim b a

fun map3 _ [] [] [] = []
  | map3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: map3 f xs ys zs
  | map3 _ _ _ _ = raise Library.UnequalLengths;

fun map4 _ [] [] [] [] = []
  | map4 f (x :: xs) (y :: ys) (z :: zs) (u :: us) = f x y z u :: map4 f xs ys zs us
  | map4 _ _ _ _ _ = raise Library.UnequalLengths;

fun map6 _ [] [] [] [] [] [] = []
  | map6 f (x :: xs) (y :: ys) (z :: zs) (u :: us) (v :: vs) (w :: ws) = f x y z u v w :: map6 f xs ys zs us vs ws
  | map6 _ _ _ _ _ _ _ = raise Library.UnequalLengths;

fun map7 _ [] [] [] [] [] [] [] = []
  | map7 f (x :: xs) (y :: ys) (z :: zs) (u :: us) (v :: vs) (w :: ws) (b :: bs) = f x y z u v w b :: map7 f xs ys zs us vs ws bs
  | map7 _ _ _ _ _ _ _ _ = raise Library.UnequalLengths;



(* forms all "unordered pairs": [1, 2, 3] ==> [(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)] *)
(* ==> library *)
fun unordered_pairs [] = []
  | unordered_pairs (x::xs) = map (pair x) (x::xs) @ unordered_pairs xs


(* term.ML *)
fun forall_aterms P (t $ u) = forall_aterms P t andalso forall_aterms P u
  | forall_aterms P (Abs (_, _, t)) = forall_aterms P t
  | forall_aterms P a = P a

fun exists_aterm P = not o forall_aterms (not o P)



(* Replaces Frees by name. Probably quicker than Pattern.rewrite_terms, and works with loose Bounds. *)
fun replace_frees assoc =
    map_aterms (fn c as Free (n, _) => the_default c (AList.lookup (op =) assoc n)
                 | t => t)


fun rename_bound n (Q $ Abs(_, T, b)) = (Q $ Abs(n, T, b))
  | rename_bound n _ = raise Match

fun mk_forall_rename (n, v) =
    rename_bound n o mk_forall v 

val dummy_term = Free ("", dummyT)

fun forall_intr_rename (n, cv) thm =
    let
      val allthm = forall_intr cv thm
      val (_ $ abs) = prop_of allthm
    in
      Thm.rename_boundvars abs (Abs (n, dummyT, dummy_term)) allthm
    end


(* Returns the frees in a term in canonical order, excluding the fixes from the context *)
fun frees_in_term ctxt t =
    Term.add_frees t []
    |> filter_out (Variable.is_fixed ctxt o fst)
    |> rev


end
