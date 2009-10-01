(*  Title:       HOL/Tools/Function/decompose.ML
    Author:      Alexander Krauss, TU Muenchen

Graph decomposition using "Shallow Dependency Pairs".
*)

signature DECOMPOSE =
sig

  val derive_chains : Proof.context -> tactic
                      -> (Termination.data -> int -> tactic)
                      -> Termination.data -> int -> tactic

  val decompose_tac : Proof.context -> tactic
                      -> Termination.ttac

end

structure Decompose : DECOMPOSE =
struct

structure TermGraph = Graph(type key = term val ord = TermOrd.fast_term_ord);


fun derive_chains ctxt chain_tac cont D = Termination.CALLS (fn (cs, i) =>
  let
      val thy = ProofContext.theory_of ctxt

      fun prove_chain c1 c2 D =
          if is_some (Termination.get_chain D c1 c2) then D else
          let
            val goal = HOLogic.mk_eq (HOLogic.mk_binop @{const_name Relation.rel_comp} (c1, c2),
                                      Const (@{const_name Set.empty}, fastype_of c1))
                       |> HOLogic.mk_Trueprop (* "C1 O C2 = {}" *)

            val chain = case FundefLib.try_proof (cterm_of thy goal) chain_tac of
                          FundefLib.Solved thm => SOME thm
                        | _ => NONE
          in
            Termination.note_chain c1 c2 chain D
          end
  in
    cont (fold_product prove_chain cs cs D) i
  end)


fun mk_dgraph D cs =
    TermGraph.empty
    |> fold (fn c => TermGraph.new_node (c,())) cs
    |> fold_product (fn c1 => fn c2 =>
         if is_none (Termination.get_chain D c1 c2 |> the_default NONE)
         then TermGraph.add_edge (c1, c2) else I)
       cs cs


fun ucomp_empty_tac T =
    REPEAT_ALL_NEW (rtac @{thm union_comp_emptyR}
                    ORELSE' rtac @{thm union_comp_emptyL}
                    ORELSE' SUBGOAL (fn (_ $ (_ $ (_ $ c1 $ c2) $ _), i) => rtac (T c1 c2) i))

fun regroup_calls_tac cs = Termination.CALLS (fn (cs', i) =>
   let
     val is = map (fn c => find_index (curry op aconv c) cs') cs
   in
     CONVERSION (Conv.arg_conv (Conv.arg_conv (FundefLib.regroup_union_conv is))) i
   end)


fun solve_trivial_tac D = Termination.CALLS
(fn ([c], i) =>
    (case Termination.get_chain D c c of
       SOME (SOME thm) => rtac @{thm wf_no_loop} i
                          THEN rtac thm i
     | _ => no_tac)
  | _ => no_tac)

fun decompose_tac' ctxt cont err_cont D = Termination.CALLS (fn (cs, i) =>
    let
      val G = mk_dgraph D cs
      val sccs = TermGraph.strong_conn G

      fun split [SCC] i = (solve_trivial_tac D i ORELSE cont D i)
        | split (SCC::rest) i =
            regroup_calls_tac SCC i
            THEN rtac @{thm wf_union_compatible} i
            THEN rtac @{thm less_by_empty} (i + 2)
            THEN ucomp_empty_tac (the o the oo Termination.get_chain D) (i + 2)
            THEN split rest (i + 1)
            THEN (solve_trivial_tac D i ORELSE cont D i)
    in
      if length sccs > 1 then split sccs i
      else solve_trivial_tac D i ORELSE err_cont D i
    end)

fun decompose_tac ctxt chain_tac cont err_cont =
    derive_chains ctxt chain_tac
    (decompose_tac' ctxt cont err_cont)

fun auto_decompose_tac ctxt =
    Termination.TERMINATION ctxt
      (decompose_tac ctxt (auto_tac (clasimpset_of ctxt))
                     (K (K all_tac)) (K (K no_tac)))


end
