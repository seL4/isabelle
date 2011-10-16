(*  Title:      HOL/Tools/Function/function_lib.ML
    Author:     Alexander Krauss, TU Muenchen

Ad-hoc collection of function waiting to be eliminated, generalized,
moved elsewhere or otherwise cleaned up.
*)

signature FUNCTION_LIB =
sig
  val plural: string -> string -> 'a list -> string

  val dest_all_all: term -> term list * term

  val map4: ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list -> 'd list -> 'e list
  val map7: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h) -> 'a list -> 'b list -> 'c list ->
    'd list -> 'e list -> 'f list -> 'g list -> 'h list

  val unordered_pairs: 'a list -> ('a * 'a) list

  val rename_bound: string -> term -> term
  val mk_forall_rename: (string * term) -> term -> term
  val forall_intr_rename: (string * cterm) -> thm -> thm

  datatype proof_attempt = Solved of thm | Stuck of thm | Fail
  val try_proof: cterm -> tactic -> proof_attempt

  val dest_binop_list: string -> term -> term list
  val regroup_conv: string -> string -> thm list -> int list -> conv
  val regroup_union_conv: int list -> conv
end

structure Function_Lib: FUNCTION_LIB =
struct

(* "The variable" ^ plural " is" "s are" vs *)
fun plural sg pl [x] = sg
  | plural sg pl _ = pl


(* Removes all quantifiers from a term, replacing bound variables by frees. *)
fun dest_all_all (t as (Const ("all",_) $ _)) =
  let
    val (v,b) = Logic.dest_all t |> apfst Free
    val (vs, b') = dest_all_all b
  in
    (v :: vs, b')
  end
  | dest_all_all t = ([],t)


fun map4 _ [] [] [] [] = []
  | map4 f (x :: xs) (y :: ys) (z :: zs) (u :: us) = f x y z u :: map4 f xs ys zs us
  | map4 _ _ _ _ _ = raise ListPair.UnequalLengths;

fun map7 _ [] [] [] [] [] [] [] = []
  | map7 f (x :: xs) (y :: ys) (z :: zs) (u :: us) (v :: vs) (w :: ws) (b :: bs) = f x y z u v w b :: map7 f xs ys zs us vs ws bs
  | map7 _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;



(* forms all "unordered pairs": [1, 2, 3] ==> [(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)] *)
fun unordered_pairs [] = []
  | unordered_pairs (x::xs) = map (pair x) (x::xs) @ unordered_pairs xs


(* renaming bound variables *)

fun rename_bound n (Q $ Abs (_, T, b)) = (Q $ Abs (n, T, b))
  | rename_bound n _ = raise Match

fun mk_forall_rename (n, v) =
  rename_bound n o Logic.all v

fun forall_intr_rename (n, cv) thm =
  let
    val allthm = Thm.forall_intr cv thm
    val (_ $ abs) = prop_of allthm
  in Thm.rename_boundvars abs (Abs (n, dummyT, Term.dummy)) allthm end


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
  regroup_conv @{const_abbrev Set.empty} @{const_name Lattices.sup}
    (map (fn t => t RS eq_reflection)
      (@{thms Un_ac} @ @{thms Un_empty_right} @ @{thms Un_empty_left}))


end
