signature INDUCTION =
sig
  val induction_tac: Proof.context -> bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> cases_tactic
  val setup: theory -> theory
end

structure Induction: INDUCTION =
struct

val ind_hypsN = "IH";

fun preds_of t =
 (case strip_comb t of
    (p as Var _, _) => [p]
  | (p as Free _, _) => [p]
  | (_, ts) => flat(map preds_of ts))

fun name_hyps thy (arg as ((cases,consumes),th)) =
  if not(forall (null o #2 o #1) cases) then arg
  else
    let
      val (prems, concl) = Logic.strip_horn (prop_of th);
      val prems' = drop consumes prems;
      val ps = preds_of concl;

      fun hname_of t =
        if exists_subterm (member (op =) ps) t
        then ind_hypsN else Rule_Cases.case_hypsN

      val hnamess = map (map hname_of o Logic.strip_assums_hyp) prems'
      val n = Int.min (length hnamess, length cases) 
      val cases' = map (fn (((cn,_),concls),hns) => ((cn,hns),concls))
        (take n cases ~~ take n hnamess)
    in ((cases',consumes),th) end

val induction_tac = Induct.gen_induct_tac name_hyps

val setup = Induct.gen_induct_setup @{binding induction} induction_tac

end

