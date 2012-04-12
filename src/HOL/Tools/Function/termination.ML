(*  Title:       HOL/Tools/Function/termination.ML
    Author:      Alexander Krauss, TU Muenchen

Context data for termination proofs.
*)

signature TERMINATION =
sig

  type data
  datatype cell = Less of thm | LessEq of thm * thm | None of thm * thm | False of thm

  val mk_sumcases : data -> typ -> term list -> term

  val get_num_points : data -> int
  val get_types      : data -> int -> typ
  val get_measures   : data -> int -> term list

  val get_chain      : data -> term -> term -> thm option option
  val get_descent    : data -> term -> term -> term -> cell option

  val dest_call : data -> term -> ((string * typ) list * int * term * int * term * term)

  val CALLS : (term list * int -> tactic) -> int -> tactic

  (* Termination tactics *)
  type ttac = data -> int -> tactic

  val TERMINATION : Proof.context -> tactic -> ttac -> int -> tactic

  val wf_union_tac : Proof.context -> tactic

  val decompose_tac : ttac
end



structure Termination : TERMINATION =
struct

open Function_Lib

val term2_ord = prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord
structure Term2tab = Table(type key = term * term val ord = term2_ord);
structure Term3tab =
  Table(type key = term * (term * term) val ord = prod_ord Term_Ord.fast_term_ord term2_ord);

(** Analyzing binary trees **)

(* Skeleton of a tree structure *)

datatype skel =
  SLeaf of int (* index *)
| SBranch of (skel * skel)


(* abstract make and dest functions *)
fun mk_tree leaf branch =
  let fun mk (SLeaf i) = leaf i
        | mk (SBranch (s, t)) = branch (mk s, mk t)
  in mk end


fun dest_tree split =
  let fun dest (SLeaf i) x = [(i, x)]
        | dest (SBranch (s, t)) x =
          let val (l, r) = split x
          in dest s l @ dest t r end
  in dest end


(* concrete versions for sum types *)
fun is_inj (Const (@{const_name Sum_Type.Inl}, _) $ _) = true
  | is_inj (Const (@{const_name Sum_Type.Inr}, _) $ _) = true
  | is_inj _ = false

fun dest_inl (Const (@{const_name Sum_Type.Inl}, _) $ t) = SOME t
  | dest_inl _ = NONE

fun dest_inr (Const (@{const_name Sum_Type.Inr}, _) $ t) = SOME t
  | dest_inr _ = NONE


fun mk_skel ps =
  let
    fun skel i ps =
      if forall is_inj ps andalso not (null ps)
      then let
          val (j, s) = skel i (map_filter dest_inl ps)
          val (k, t) = skel j (map_filter dest_inr ps)
        in (k, SBranch (s, t)) end
      else (i + 1, SLeaf i)
  in
    snd (skel 0 ps)
  end

(* compute list of types for nodes *)
fun node_types sk T = dest_tree (fn Type (@{type_name Sum_Type.sum}, [LT, RT]) => (LT, RT)) sk T |> map snd

(* find index and raw term *)
fun dest_inj (SLeaf i) trm = (i, trm)
  | dest_inj (SBranch (s, t)) trm =
    case dest_inl trm of
      SOME trm' => dest_inj s trm'
    | _ => dest_inj t (the (dest_inr trm))



(** Matrix cell datatype **)

datatype cell = Less of thm | LessEq of thm * thm | None of thm * thm | False of thm;


type data =
  skel                            (* structure of the sum type encoding "program points" *)
  * (int -> typ)                  (* types of program points *)
  * (term list Inttab.table)      (* measures for program points *)
  * (term * term -> thm option)   (* which calls form chains? (cached) *)
  * (term * (term * term) -> cell)(* local descents (cached) *)


(* Build case expression *)
fun mk_sumcases (sk, _, _, _, _) T fs =
  mk_tree (fn i => (nth fs i, domain_type (fastype_of (nth fs i))))
          (fn ((f, fT), (g, gT)) => (SumTree.mk_sumcase fT gT T f g, SumTree.mk_sumT fT gT))
          sk
  |> fst

fun mk_sum_skel rel =
  let
    val cs = Function_Lib.dest_binop_list @{const_name Lattices.sup} rel
    fun collect_pats (Const (@{const_name Collect}, _) $ Abs (_, _, c)) =
      let
        val (Const (@{const_name HOL.conj}, _) $ (Const (@{const_name HOL.eq}, _) $ _ $ (Const (@{const_name Pair}, _) $ r $ l)) $ _)
          = Term.strip_qnt_body @{const_name Ex} c
      in cons r o cons l end
  in
    mk_skel (fold collect_pats cs [])
  end

fun prove_chain thy chain_tac (c1, c2) =
  let
    val goal =
      HOLogic.mk_eq (HOLogic.mk_binop @{const_name Relation.relcomp} (c1, c2),
        Const (@{const_abbrev Set.empty}, fastype_of c1))
      |> HOLogic.mk_Trueprop (* "C1 O C2 = {}" *)
  in
    case Function_Lib.try_proof (cterm_of thy goal) chain_tac of
      Function_Lib.Solved thm => SOME thm
    | _ => NONE
  end


fun dest_call' sk (Const (@{const_name Collect}, _) $ Abs (_, _, c)) =
  let
    val vs = Term.strip_qnt_vars @{const_name Ex} c

    (* FIXME: throw error "dest_call" for malformed terms *)
    val (Const (@{const_name HOL.conj}, _) $ (Const (@{const_name HOL.eq}, _) $ _ $ (Const (@{const_name Pair}, _) $ r $ l)) $ Gam)
      = Term.strip_qnt_body @{const_name Ex} c
    val (p, l') = dest_inj sk l
    val (q, r') = dest_inj sk r
  in
    (vs, p, l', q, r', Gam)
  end
  | dest_call' _ _ = error "dest_call"

fun dest_call (sk, _, _, _, _) = dest_call' sk

fun mk_desc thy tac vs Gam l r m1 m2 =
  let
    fun try rel =
      try_proof (cterm_of thy
        (Logic.list_all (vs,
           Logic.mk_implies (HOLogic.mk_Trueprop Gam,
             HOLogic.mk_Trueprop (Const (rel, @{typ "nat => nat => bool"})
               $ (m2 $ r) $ (m1 $ l)))))) tac
  in
    case try @{const_name Orderings.less} of
       Solved thm => Less thm
     | Stuck thm =>
       (case try @{const_name Orderings.less_eq} of
          Solved thm2 => LessEq (thm2, thm)
        | Stuck thm2 =>
          if prems_of thm2 = [HOLogic.Trueprop $ @{term False}]
          then False thm2 else None (thm2, thm)
        | _ => raise Match) (* FIXME *)
     | _ => raise Match
end

fun prove_descent thy tac sk (c, (m1, m2)) =
  let
    val (vs, _, l, _, r, Gam) = dest_call' sk c
  in 
    mk_desc thy tac vs Gam l r m1 m2
  end

fun create ctxt chain_tac descent_tac T rel =
  let
    val thy = Proof_Context.theory_of ctxt
    val sk = mk_sum_skel rel
    val Ts = node_types sk T
    val M = Inttab.make (map_index (apsnd (MeasureFunctions.get_measure_functions ctxt)) Ts)
    val chain_cache = Cache.create Term2tab.empty Term2tab.lookup Term2tab.update
      (prove_chain thy chain_tac)
    val descent_cache = Cache.create Term3tab.empty Term3tab.lookup Term3tab.update
      (prove_descent thy descent_tac sk)
  in
    (sk, nth Ts, M, chain_cache, descent_cache)
  end

fun get_num_points (sk, _, _, _, _) =
  let
    fun num (SLeaf i) = i + 1
      | num (SBranch (s, t)) = num t
  in num sk end

fun get_types (_, T, _, _, _) = T
fun get_measures (_, _, M, _, _) = Inttab.lookup_list M

fun get_chain (_, _, _, C, _) c1 c2 =
  SOME (C (c1, c2))

fun get_descent (_, _, _, _, D) c m1 m2 =
  SOME (D (c, (m1, m2)))

fun CALLS tac i st =
  if Thm.no_prems st then all_tac st
  else case Thm.term_of (Thm.cprem_of st i) of
    (_ $ (_ $ rel)) => tac (Function_Lib.dest_binop_list @{const_name Lattices.sup} rel, i) st
  |_ => no_tac st

type ttac = data -> int -> tactic

fun TERMINATION ctxt atac tac =
  SUBGOAL (fn (_ $ (Const (@{const_name wf}, wfT) $ rel), i) =>
  let
    val (T, _) = HOLogic.dest_prodT (HOLogic.dest_setT (domain_type wfT))
  in
    tac (create ctxt atac atac T rel) i
  end)


(* A tactic to convert open to closed termination goals *)
local
fun dest_term (t : term) = (* FIXME, cf. Lexicographic order *)
  let
    val (vars, prop) = Function_Lib.dest_all_all t
    val (prems, concl) = Logic.strip_horn prop
    val (lhs, rhs) = concl
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_mem |> fst
      |> HOLogic.dest_prod
  in
    (vars, prems, lhs, rhs)
  end

fun mk_pair_compr (T, qs, l, r, conds) =
  let
    val pT = HOLogic.mk_prodT (T, T)
    val n = length qs
    val peq = HOLogic.eq_const pT $ Bound n $ (HOLogic.pair_const T T $ l $ r)
    val conds' = if null conds then [@{term True}] else conds
  in
    HOLogic.Collect_const pT $
    Abs ("uu_", pT,
      (foldr1 HOLogic.mk_conj (peq :: conds')
      |> fold_rev (fn v => fn t => HOLogic.exists_const (fastype_of v) $ lambda v t) qs))
  end

in

fun wf_union_tac ctxt st =
  let
    val thy = Proof_Context.theory_of ctxt
    val cert = cterm_of (theory_of_thm st)
    val ((_ $ (_ $ rel)) :: ineqs) = prems_of st

    fun mk_compr ineq =
      let
        val (vars, prems, lhs, rhs) = dest_term ineq
      in
        mk_pair_compr (fastype_of lhs, vars, lhs, rhs, map (Object_Logic.atomize_term thy) prems)
      end

    val relation =
      if null ineqs
      then Const (@{const_abbrev Set.empty}, fastype_of rel)
      else map mk_compr ineqs
        |> foldr1 (HOLogic.mk_binop @{const_name Lattices.sup})

    fun solve_membership_tac i =
      (EVERY' (replicate (i - 2) (rtac @{thm UnI2}))  (* pick the right component of the union *)
      THEN' (fn j => TRY (rtac @{thm UnI1} j))
      THEN' (rtac @{thm CollectI})                    (* unfold comprehension *)
      THEN' (fn i => REPEAT (rtac @{thm exI} i))      (* Turn existentials into schematic Vars *)
      THEN' ((rtac @{thm refl})                       (* unification instantiates all Vars *)
        ORELSE' ((rtac @{thm conjI})
          THEN' (rtac @{thm refl})
          THEN' (blast_tac ctxt)))    (* Solve rest of context... not very elegant *)
      ) i
  in
    ((PRIMITIVE (Drule.cterm_instantiate [(cert rel, cert relation)])
     THEN ALLGOALS (fn i => if i = 1 then all_tac else solve_membership_tac i))) st
  end

end



(*** DEPENDENCY GRAPHS ***)

fun mk_dgraph D cs =
  Term_Graph.empty
  |> fold (fn c => Term_Graph.new_node (c, ())) cs
  |> fold_product (fn c1 => fn c2 =>
     if is_none (get_chain D c1 c2 |> the_default NONE)
     then Term_Graph.add_edge (c1, c2) else I)
     cs cs

fun ucomp_empty_tac T =
  REPEAT_ALL_NEW (rtac @{thm union_comp_emptyR}
    ORELSE' rtac @{thm union_comp_emptyL}
    ORELSE' SUBGOAL (fn (_ $ (_ $ (_ $ c1 $ c2) $ _), i) => rtac (T c1 c2) i))

fun regroup_calls_tac cs = CALLS (fn (cs', i) =>
 let
   val is = map (fn c => find_index (curry op aconv c) cs') cs
 in
   CONVERSION (Conv.arg_conv (Conv.arg_conv
     (Function_Lib.regroup_union_conv is))) i
 end)


fun solve_trivial_tac D = CALLS (fn ([c], i) =>
  (case get_chain D c c of
     SOME (SOME thm) => rtac @{thm wf_no_loop} i
                        THEN rtac thm i
   | _ => no_tac)
  | _ => no_tac)

fun decompose_tac D = CALLS (fn (cs, i) =>
  let
    val G = mk_dgraph D cs
    val sccs = Term_Graph.strong_conn G

    fun split [SCC] i = TRY (solve_trivial_tac D i)
      | split (SCC::rest) i =
        regroup_calls_tac SCC i
        THEN rtac @{thm wf_union_compatible} i
        THEN rtac @{thm less_by_empty} (i + 2)
        THEN ucomp_empty_tac (the o the oo get_chain D) (i + 2)
        THEN split rest (i + 1)
        THEN TRY (solve_trivial_tac D i)
  in
    if length sccs > 1 then split sccs i
    else solve_trivial_tac D i
  end)


end
