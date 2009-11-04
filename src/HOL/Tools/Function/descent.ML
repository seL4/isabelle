(*  Title:       HOL/Tools/Function/descent.ML
    Author:      Alexander Krauss, TU Muenchen

Descent proofs for termination
*)


signature DESCENT =
sig

  val derive_diag : Proof.context -> tactic -> (Termination.data -> int -> tactic)
                    -> Termination.data -> int -> tactic

  val derive_all  : Proof.context -> tactic -> (Termination.data -> int -> tactic)
                    -> Termination.data -> int -> tactic

end


structure Descent : DESCENT =
struct

fun gen_descent diag ctxt tac cont D = Termination.CALLS (fn (cs, i) =>
  let
    val thy = ProofContext.theory_of ctxt
    val measures_of = Termination.get_measures D

    fun derive c D =
      let
        val (_, p, _, q, _, _) = Termination.dest_call D c
      in
        if diag andalso p = q
        then fold (fn m => Termination.derive_descent thy tac c m m) (measures_of p) D
        else fold_product (Termination.derive_descent thy tac c)
               (measures_of p) (measures_of q) D
      end
  in
    cont (Function_Common.PROFILE "deriving descents" (fold derive cs) D) i
  end)

val derive_diag = gen_descent true
val derive_all = gen_descent false

end
