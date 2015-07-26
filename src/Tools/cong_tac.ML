(*  Title:      Tools/cong_tac.ML
    Author:     Stefan Berghofer, TU Muenchen

Congruence tactic based on explicit instantiation.
*)

signature CONG_TAC =
sig
  val cong_tac: Proof.context -> thm -> int -> tactic
end;

structure Cong_Tac: CONG_TAC =
struct

fun cong_tac ctxt cong = CSUBGOAL (fn (cgoal, i) =>
  let
    val goal = Thm.term_of cgoal;
  in
    (case Logic.strip_assums_concl goal of
      _ $ (_ $ (f $ x) $ (g $ y)) =>
        let
          val cong' = Thm.lift_rule cgoal cong;
          val _ $ (_ $ (f' $ x') $ (g' $ y')) = Logic.strip_assums_concl (Thm.prop_of cong');
          val ps = Logic.strip_params (Thm.concl_of cong');
          val insts =
            [(f', f), (g', g), (x', x), (y', y)] |> map (fn (t, u) =>
              (#1 (dest_Var (head_of t)), Thm.cterm_of ctxt (fold_rev Term.abs ps u)));
        in
          fn st =>
            compose_tac ctxt (false, infer_instantiate ctxt insts cong', 2) i st
              handle THM _ => no_tac st
        end
    | _ => no_tac)
  end);

end;

