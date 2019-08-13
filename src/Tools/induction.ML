(*  Title:      Tools/induction.ML
    Author:     Tobias Nipkow, TU Muenchen

Alternative proof method "induction" that gives induction hypotheses the
name "IH".
*)

signature INDUCTION =
sig
  val induction_context_tactic: bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> context_tactic
  val induction_tac: Proof.context -> bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> tactic
end

structure Induction: INDUCTION =
struct

val ind_hypsN = "IH";

fun preds_of t =
  (case strip_comb t of
    (p as Var _, _) => [p]
  | (p as Free _, _) => [p]
  | (_, ts) => maps preds_of ts);

val induction_context_tactic =
  Induct.gen_induct_context_tactic (fn arg as ((cases, consumes), th) =>
    if not (forall (null o #2 o #1) cases) then arg
    else
      let
        val (prems, concl) = Logic.strip_horn (Thm.prop_of th);
        val prems' = drop consumes prems;
        val ps = preds_of concl;
  
        fun hname_of t =
          if exists_subterm (member (op aconv) ps) t
          then ind_hypsN else Rule_Cases.case_hypsN;
  
        val hnamess = map (map hname_of o Logic.strip_assums_hyp) prems';
        val n = Int.min (length hnamess, length cases);
        val cases' =
          map (fn (((cn, _), concls), hns) => ((cn, hns), concls))
            (take n cases ~~ take n hnamess);
      in ((cases', consumes), th) end);

fun induction_tac ctxt x1 x2 x3 x4 x5 x6 x7 =
  NO_CONTEXT_TACTIC ctxt (induction_context_tactic x1 x2 x3 x4 x5 x6 x7);

val _ =
  Theory.local_setup (Induct.gen_induct_setup \<^binding>\<open>induction\<close> induction_context_tactic);

end
