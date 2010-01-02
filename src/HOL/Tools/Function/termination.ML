(*  Title:       HOL/Tools/Function/termination.ML
    Author:      Alexander Krauss, TU Muenchen

Context data for termination proofs
*)


signature TERMINATION =
sig

  type data
  datatype cell = Less of thm | LessEq of (thm * thm) | None of (thm * thm) | False of thm

  val mk_sumcases : data -> typ -> term list -> term

  val get_num_points : data -> int
  val get_types      : data -> int -> typ
  val get_measures   : data -> int -> term list

  (* read from cache *)
  val get_chain      : data -> term -> term -> thm option option
  val get_descent    : data -> term -> term -> term -> cell option

  val dest_call : data -> term -> ((string * typ) list * int * term * int * term * term)

  val CALLS : (term list * int -> tactic) -> int -> tactic

  (* Termination tactics. Sequential composition via continuations. (2nd argument is the error continuation) *)
  type ttac = (data -> int -> tactic) -> (data -> int -> tactic) -> data -> int -> tactic

  val TERMINATION : Proof.context -> (data -> int -> tactic) -> int -> tactic

  val REPEAT : ttac -> ttac

  val wf_union_tac : Proof.context -> tactic

  val decompose_tac : Proof.context -> tactic -> ttac

  val derive_diag : Proof.context -> tactic -> 
    (data -> int -> tactic) -> data -> int -> tactic

  val derive_all  : Proof.context -> tactic ->
    (data -> int -> tactic) -> data -> int -> tactic

end



structure Termination : TERMINATION =
struct

open Function_Lib

val term2_ord = prod_ord TermOrd.fast_term_ord TermOrd.fast_term_ord
structure Term2tab = Table(type key = term * term val ord = term2_ord);
structure Term3tab = Table(type key = term * (term * term) val ord = prod_ord TermOrd.fast_term_ord term2_ord);

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
fun node_types sk T = dest_tree (fn Type ("+", [LT, RT]) => (LT, RT)) sk T |> map snd

(* find index and raw term *)
fun dest_inj (SLeaf i) trm = (i, trm)
  | dest_inj (SBranch (s, t)) trm =
    case dest_inl trm of
      SOME trm' => dest_inj s trm'
    | _ => dest_inj t (the (dest_inr trm))



(** Matrix cell datatype **)

datatype cell = Less of thm | LessEq of (thm * thm) | None of (thm * thm) | False of thm;


type data =
  skel                            (* structure of the sum type encoding "program points" *)
  * (int -> typ)                  (* types of program points *)
  * (term list Inttab.table)      (* measures for program points *)
  * (thm option Term2tab.table)   (* which calls form chains? *)
  * (cell Term3tab.table)         (* local descents *)


fun map_chains f (p, T, M, C, D) = (p, T, M, f C, D)
fun map_descent f (p, T, M, C, D) = (p, T, M, C, f D)

fun note_chain c1 c2 res = map_chains (Term2tab.update ((c1, c2), res))
fun note_descent c m1 m2 res = map_descent (Term3tab.update ((c,(m1, m2)), res))

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
        val (Const ("op &", _) $ (Const ("op =", _) $ _ $ (Const ("Pair", _) $ r $ l)) $ _)
          = Term.strip_qnt_body "Ex" c
      in cons r o cons l end
  in
    mk_skel (fold collect_pats cs [])
  end

fun create ctxt T rel =
  let
    val sk = mk_sum_skel rel
    val Ts = node_types sk T
    val M = Inttab.make (map_index (apsnd (MeasureFunctions.get_measure_functions ctxt)) Ts)
  in
    (sk, nth Ts, M, Term2tab.empty, Term3tab.empty)
  end

fun get_num_points (sk, _, _, _, _) =
  let
    fun num (SLeaf i) = i + 1
      | num (SBranch (s, t)) = num t
  in num sk end

fun get_types (_, T, _, _, _) = T
fun get_measures (_, _, M, _, _) = Inttab.lookup_list M

fun get_chain (_, _, _, C, _) c1 c2 =
  Term2tab.lookup C (c1, c2)

fun get_descent (_, _, _, _, D) c m1 m2 =
  Term3tab.lookup D (c, (m1, m2))

fun dest_call D (Const (@{const_name Collect}, _) $ Abs (_, _, c)) =
  let
    val (sk, _, _, _, _) = D
    val vs = Term.strip_qnt_vars "Ex" c

    (* FIXME: throw error "dest_call" for malformed terms *)
    val (Const ("op &", _) $ (Const ("op =", _) $ _ $ (Const ("Pair", _) $ r $ l)) $ Gam)
      = Term.strip_qnt_body "Ex" c
    val (p, l') = dest_inj sk l
    val (q, r') = dest_inj sk r
  in
    (vs, p, l', q, r', Gam)
  end
  | dest_call D t = error "dest_call"


fun mk_desc thy tac vs Gam l r m1 m2 =
  let
    fun try rel =
      try_proof (cterm_of thy
        (Term.list_all (vs,
           Logic.mk_implies (HOLogic.mk_Trueprop Gam,
             HOLogic.mk_Trueprop (Const (rel, @{typ "nat => nat => bool"})
               $ (m2 $ r) $ (m1 $ l)))))) tac
  in
    case try @{const_name HOL.less} of
       Solved thm => Less thm
     | Stuck thm =>
       (case try @{const_name HOL.less_eq} of
          Solved thm2 => LessEq (thm2, thm)
        | Stuck thm2 =>
          if prems_of thm2 = [HOLogic.Trueprop $ HOLogic.false_const]
          then False thm2 else None (thm2, thm)
        | _ => raise Match) (* FIXME *)
     | _ => raise Match
end

fun derive_descent thy tac c m1 m2 D =
  case get_descent D c m1 m2 of
    SOME _ => D
  | NONE => 
    let
      val (vs, _, l, _, r, Gam) = dest_call D c
    in 
      note_descent c m1 m2 (mk_desc thy tac vs Gam l r m1 m2) D
    end

fun CALLS tac i st =
  if Thm.no_prems st then all_tac st
  else case Thm.term_of (Thm.cprem_of st i) of
    (_ $ (_ $ rel)) => tac (Function_Lib.dest_binop_list @{const_name Lattices.sup} rel, i) st
  |_ => no_tac st

type ttac = (data -> int -> tactic) -> (data -> int -> tactic) -> data -> int -> tactic

fun TERMINATION ctxt tac =
  SUBGOAL (fn (_ $ (Const (@{const_name wf}, wfT) $ rel), i) =>
  let
    val (T, _) = HOLogic.dest_prodT (HOLogic.dest_setT (domain_type wfT))
  in
    tac (create ctxt T rel) i
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
    val conds' = if null conds then [HOLogic.true_const] else conds
  in
    HOLogic.Collect_const pT $
    Abs ("uu_", pT,
      (foldr1 HOLogic.mk_conj (peq :: conds')
      |> fold_rev (fn v => fn t => HOLogic.exists_const (fastype_of v) $ lambda v t) qs))
  end

in

fun wf_union_tac ctxt st =
  let
    val thy = ProofContext.theory_of ctxt
    val cert = cterm_of (theory_of_thm st)
    val ((_ $ (_ $ rel)) :: ineqs) = prems_of st

    fun mk_compr ineq =
      let
        val (vars, prems, lhs, rhs) = dest_term ineq
      in
        mk_pair_compr (fastype_of lhs, vars, lhs, rhs, map (ObjectLogic.atomize_term thy) prems)
      end

    val relation =
      if null ineqs
      then Const (@{const_name Set.empty}, fastype_of rel)
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
          THEN' (blast_tac (claset_of ctxt))))  (* Solve rest of context... not very elegant *)
      ) i
  in
    ((PRIMITIVE (Drule.cterm_instantiate [(cert rel, cert relation)])
     THEN ALLGOALS (fn i => if i = 1 then all_tac else solve_membership_tac i))) st
  end

end


(* continuation passing repeat combinator *)
fun REPEAT ttac cont err_cont =
    ttac (fn D => fn i => (REPEAT ttac cont cont D i)) err_cont

(*** DEPENDENCY GRAPHS ***)

structure TermGraph = Graph(type key = term val ord = TermOrd.fast_term_ord);


fun prove_chain thy chain_tac c1 c2 =
  let
    val goal =
      HOLogic.mk_eq (HOLogic.mk_binop @{const_name Relation.rel_comp} (c1, c2),
        Const (@{const_name Set.empty}, fastype_of c1))
      |> HOLogic.mk_Trueprop (* "C1 O C2 = {}" *)
  in
    case Function_Lib.try_proof (cterm_of thy goal) chain_tac of
      Function_Lib.Solved thm => SOME thm
    | _ => NONE
  end

fun derive_chains ctxt chain_tac cont D = CALLS (fn (cs, i) =>
  let
    val thy = ProofContext.theory_of ctxt

    fun derive_chain c1 c2 D =
      if is_some (get_chain D c1 c2) then D else
      note_chain c1 c2 (prove_chain thy chain_tac c1 c2) D
  in
    cont (fold_product derive_chain cs cs D) i
  end)


fun mk_dgraph D cs =
  TermGraph.empty
  |> fold (fn c => TermGraph.new_node (c,())) cs
  |> fold_product (fn c1 => fn c2 =>
     if is_none (get_chain D c1 c2 |> the_default NONE)
     then TermGraph.add_edge (c1, c2) else I)
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

fun decompose_tac' cont err_cont D = CALLS (fn (cs, i) =>
  let
    val G = mk_dgraph D cs
    val sccs = TermGraph.strong_conn G

    fun split [SCC] i = (solve_trivial_tac D i ORELSE cont D i)
      | split (SCC::rest) i =
        regroup_calls_tac SCC i
        THEN rtac @{thm wf_union_compatible} i
        THEN rtac @{thm less_by_empty} (i + 2)
        THEN ucomp_empty_tac (the o the oo get_chain D) (i + 2)
        THEN split rest (i + 1)
        THEN (solve_trivial_tac D i ORELSE cont D i)
  in
    if length sccs > 1 then split sccs i
    else solve_trivial_tac D i ORELSE err_cont D i
  end)

fun decompose_tac ctxt chain_tac cont err_cont =
  derive_chains ctxt chain_tac (decompose_tac' cont err_cont)


(*** Local Descent Proofs ***)

fun gen_descent diag ctxt tac cont D = CALLS (fn (cs, i) =>
  let
    val thy = ProofContext.theory_of ctxt
    val measures_of = get_measures D

    fun derive c D =
      let
        val (_, p, _, q, _, _) = dest_call D c
      in
        if diag andalso p = q
        then fold (fn m => derive_descent thy tac c m m) (measures_of p) D
        else fold_product (derive_descent thy tac c)
               (measures_of p) (measures_of q) D
      end
  in
    cont (Function_Common.PROFILE "deriving descents" (fold derive cs) D) i
  end)

val derive_diag = gen_descent true
val derive_all = gen_descent false


end
