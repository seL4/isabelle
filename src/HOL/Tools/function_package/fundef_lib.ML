(*  Title:      HOL/Tools/function_package/lib.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Some fairly general functions that should probably go somewhere else... 
*)


fun mk_forall (var as Free (v,T)) t =
    all T $ Abs (v,T, abstract_over (var,t))
  | mk_forall v _ = let val _ = print v in sys_error "mk_forall" end

(* Builds a quantification with a new name for the variable. *)
fun mk_forall_rename (v as Free (_,T),newname) t =
    all T $ Abs (newname, T, abstract_over (v, t))
  | mk_forall_rename (v, _) _ = let val _ = print v in sys_error "mk_forall_rename" end

(* Constructs a tupled abstraction from an arbitrarily nested tuple of variables and a term. *)
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


fun dest_all_all_ctx ctx (Const ("all", _) $ Abs (a as (n,T,b))) =
    let
      val [(n', _)] = Variable.rename_wrt ctx [] [(n,T)]
      val (_, ctx') = ProofContext.add_fixes_i [(n', SOME T, NoSyn)] ctx

      val (n'', body) = Term.dest_abs (n', T, b) 
      val _ = assert (n' = n'') "dest_all_ctx" (* Note: We assume that n' does not occur in the body. Otherwise it would be fixed. *)

      val (ctx'', vs, bd) = dest_all_all_ctx ctx' body
    in
	(ctx'', (n', T) :: vs, bd)
    end
  | dest_all_all_ctx ctx t = 
    (ctx, [], t)



(* unfold *)
fun unfold P f g b x = if (P x) then ((f x)::(unfold P f g b (g x))) else (b x)

val dest_implies_list = 
    split_last o (unfold Logic.is_implies (fst o Logic.dest_implies) (snd o Logic.dest_implies) single)

fun implies_elim_swp a b = implies_elim b a

fun map3 _ [] [] [] = []
  | map3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: map3 f xs ys zs
  | map3 _ _ _ _ = raise Library.UnequalLengths;

fun map6 _ [] [] [] [] [] [] = []
  | map6 f (x :: xs) (y :: ys) (z :: zs) (u :: us) (v :: vs) (w :: ws) = f x y z u v w :: map6 f xs ys zs us vs ws
  | map6 _ _ _ _ _ _ _ = raise Library.UnequalLengths;



(* forms all "unordered pairs": [1, 2, 3] ==> [(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)] *)
fun unordered_pairs [] = []
  | unordered_pairs (x::xs) = map (pair x) (x::xs) @ unordered_pairs xs


fun the_single [x] = x
  | the_single _ = sys_error "the_single"
