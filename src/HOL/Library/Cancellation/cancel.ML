(*  Title:      HOL/Library/Cancellation/cancel.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Mathias Fleury, MPII

This simproc allows handling of types with constructors (e.g., add_mset for
multisets) and iteration of the addition (e.g., repeat_mset for multisets).

Beware that this simproc should not compete with any more specialised especially:
  - nat: the handling for Suc is more complicated than what can be done here
  - int: some normalisation is done (after the cancelation) and linarith relies on these.

Instead of "*", we have "iterate_add".


To quote Provers/Arith/cancel_numerals.ML:

    Cancel common coefficients in balanced expressions:

         i + #m*u + j ~~ i' + #m'*u + j'  ==  #(m-m')*u + i + j ~~ i' + j'

    where ~~ is an appropriate balancing operation (e.g. =, <=, <, -).

    It works by (a) massaging both sides to bring the selected term to the front:

         #m*u + (i + j) ~~ #m'*u + (i' + j')

    (b) then using bal_add1 or bal_add2 to reach

         #(m-m')*u + i + j ~~ i' + j'       (if m'<=m)

    or

         i + j ~~ #(m'-m)*u + i' + j'       (otherwise)
*)

signature CANCEL =
sig
  val proc: Simplifier.proc
end;

functor Cancel_Fun(Data: CANCEL_NUMERALS_DATA): CANCEL =
struct

structure Cancel_Numerals_Fun = CancelNumeralsFun(open Data)
exception SORT_NOT_GENERAL_ENOUGH of string * typ * term
(*the simplification procedure*)
fun proc ctxt ct =
  let
    val t = Thm.term_of ct
    val (t', ctxt') = yield_singleton (Variable.import_terms true) t ctxt
    val pre_simplified_ct =
      Simplifier.full_rewrite (clear_simpset ctxt
        addsimps Named_Theorems.get ctxt \<^named_theorems>\<open>cancelation_simproc_pre\<close>
        |> Simplifier.add_proc \<^simproc>\<open>NO_MATCH\<close>) (Thm.cterm_of ctxt t');
    val t' = Thm.term_of (Thm.rhs_of pre_simplified_ct)
    val export = singleton (Variable.export ctxt' ctxt)

    val (t1,_) = Data.dest_bal t'
    val sort_not_general_enough = ((fastype_of t1) = \<^typ>\<open>nat\<close>) orelse
        Sorts.of_sort (Sign.classes_of (Proof_Context.theory_of ctxt))
         (fastype_of t1, \<^sort>\<open>comm_ring_1\<close>)
    val _ =
       if sort_not_general_enough
       then raise SORT_NOT_GENERAL_ENOUGH("type too precise, another simproc should do the job",
          fastype_of t1, t1)
       else ()
    val canceled_thm = Cancel_Numerals_Fun.proc ctxt (Thm.rhs_of pre_simplified_ct)
    fun add_pre_simplification thm = @{thm Pure.transitive} OF [pre_simplified_ct, thm]
    fun add_post_simplification thm =
      let val post_simplified_ct =
        Simplifier.full_rewrite (clear_simpset ctxt
          addsimps Named_Theorems.get ctxt \<^named_theorems>\<open>cancelation_simproc_post\<close>
          |> Simplifier.add_proc \<^simproc>\<open>NO_MATCH\<close>) (Thm.rhs_of thm)
      in @{thm Pure.transitive} OF [thm, post_simplified_ct] end
  in
    Option.map (export o add_post_simplification o add_pre_simplification) canceled_thm
  end
  (* FIXME avoid handling of generic exceptions *)
  handle TERM _ => NONE
       | TYPE _ => NONE
       | SORT_NOT_GENERAL_ENOUGH _ => NONE

end;
