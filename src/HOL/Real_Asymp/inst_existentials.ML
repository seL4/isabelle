signature INST_EXISTENTIALS =
sig
  val tac : Proof.context -> term list -> int -> tactic
end

structure Inst_Existentials : INST_EXISTENTIALS =
struct

fun tac ctxt [] = TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms HOL.conjI})
  | tac ctxt (t :: ts) =
      (TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms HOL.conjI}))
      THEN_ALL_NEW (TRY o (
        let
          val thm = Drule.infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt t)] @{thm HOL.exI}
        in
          resolve_tac ctxt [thm] THEN' tac ctxt ts
        end))

end