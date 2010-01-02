(*  Title:      HOL/Tools/Function/fundef_lib.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions.
Some fairly general functions that should probably go somewhere else...
*)

structure Function_Lib =
struct

fun map_option f NONE = NONE
  | map_option f (SOME x) = SOME (f x);

fun fold_option f NONE y = y
  | fold_option f (SOME x) y = f x y;

(* Ex: "The variable" ^ plural " is" "s are" vs *)
fun plural sg pl [x] = sg
  | plural sg pl _ = pl

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
fun dest_all_all_ctx ctx (Const ("all", _) $ Abs (n,T,b)) =
  let
    val [(n', _)] = Variable.variant_frees ctx [] [(n,T)]
    val (_, ctx') = ProofContext.add_fixes [(Binding.name n', SOME T, NoSyn)] ctx

    val (n'', body) = Term.dest_abs (n', T, b)
    val _ = (n' = n'') orelse error "dest_all_ctx"
      (* Note: We assume that n' does not occur in the body. Otherwise it would be fixed. *)

    val (ctx'', vs, bd) = dest_all_all_ctx ctx' body
  in
    (ctx'', (n', T) :: vs, bd)
  end
  | dest_all_all_ctx ctx t =
  (ctx, [], t)


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
fun unordered_pairs [] = []
  | unordered_pairs (x::xs) = map (pair x) (x::xs) @ unordered_pairs xs


(* Replaces Frees by name. Works with loose Bounds. *)
fun replace_frees assoc =
  map_aterms (fn c as Free (n, _) => the_default c (AList.lookup (op =) assoc n)
    | t => t)


fun rename_bound n (Q $ Abs (_, T, b)) = (Q $ Abs (n, T, b))
  | rename_bound n _ = raise Match

fun mk_forall_rename (n, v) =
  rename_bound n o Logic.all v

fun forall_intr_rename (n, cv) thm =
  let
    val allthm = forall_intr cv thm
    val (_ $ abs) = prop_of allthm
  in
    Thm.rename_boundvars abs (Abs (n, dummyT, Term.dummy_pattern dummyT)) allthm
  end


(* Returns the frees in a term in canonical order, excluding the fixes from the context *)
fun frees_in_term ctxt t =
  Term.add_frees t []
  |> filter_out (Variable.is_fixed ctxt o fst)
  |> rev


datatype proof_attempt = Solved of thm | Stuck of thm | Fail

fun try_proof cgoal tac =
  case SINGLE tac (Goal.init cgoal) of
    NONE => Fail
  | SOME st =>
    if Thm.no_prems st
    then Solved (Goal.finish (Syntax.init_pretty_global (Thm.theory_of_cterm cgoal)) st)
    else Stuck st


fun dest_binop_list cn (t as (Const (n, _) $ a $ b)) =
  if cn = n then dest_binop_list cn a @ dest_binop_list cn b else [ t ]
  | dest_binop_list _ t = [ t ]


(* separate two parts in a +-expression:
   "a + b + c + d + e" --> "(a + b + d) + (c + e)"

   Here, + can be any binary operation that is AC.

   cn - The name of the binop-constructor (e.g. @{const_name Un})
   ac - the AC rewrite rules for cn
   is - the list of indices of the expressions that should become the first part
        (e.g. [0,1,3] in the above example)
*)

fun regroup_conv neu cn ac is ct =
 let
   val mk = HOLogic.mk_binop cn
   val t = term_of ct
   val xs = dest_binop_list cn t
   val js = subtract (op =) is (0 upto (length xs) - 1)
   val ty = fastype_of t
   val thy = theory_of_cterm ct
 in
   Goal.prove_internal []
     (cterm_of thy
       (Logic.mk_equals (t,
          if null is
          then mk (Const (neu, ty), foldr1 mk (map (nth xs) js))
          else if null js
            then mk (foldr1 mk (map (nth xs) is), Const (neu, ty))
            else mk (foldr1 mk (map (nth xs) is), foldr1 mk (map (nth xs) js)))))
     (K (rewrite_goals_tac ac
         THEN rtac Drule.reflexive_thm 1))
 end

(* instance for unions *)
val regroup_union_conv =
  regroup_conv @{const_name Set.empty} @{const_name Lattices.sup}
    (map (fn t => t RS eq_reflection)
      (@{thms Un_ac} @ @{thms Un_empty_right} @ @{thms Un_empty_left}))


end
