(*$Id$
  theory Main includes everything except AC*)

theory Main = Update + List + EquivClass + IntDiv + CardinalArith:

(* belongs to theory Trancl *)
lemmas rtrancl_induct = rtrancl_induct [case_names initial step, induct set: rtrancl]
  and trancl_induct = trancl_induct [case_names initial step, induct set: trancl]
  and converse_trancl_induct = converse_trancl_induct [case_names initial step, consumes 1]
  and rtrancl_full_induct = rtrancl_full_induct [case_names initial step, consumes 1]

(* belongs to theory WF *)
lemmas wf_induct = wf_induct [induct set: wf]
  and wf_induct_rule = wf_induct [rule_format, induct set: wf]
  and wf_on_induct = wf_on_induct [consumes 2, induct set: wf_on]
  and wf_on_induct_rule = wf_on_induct [rule_format, consumes 2, induct set: wf_on]

(* belongs to theory Ordinal *)
lemmas Ord_induct = Ord_induct [consumes 2]
  and Ord_induct_rule = Ord_induct [rule_format, consumes 2]
  and trans_induct = trans_induct [consumes 1]
  and trans_induct_rule = trans_induct [rule_format, consumes 1]
  and trans_induct3 = trans_induct3 [case_names 0 succ limit, consumes 1]
  and trans_induct3_rule = trans_induct3 [rule_format, case_names 0 succ limit, consumes 1]

(* belongs to theory Nat *)
lemmas nat_induct = nat_induct [case_names 0 succ, induct set: nat]
  and complete_induct = complete_induct [case_names less, consumes 1]
  and complete_induct_rule = complete_induct [rule_format, case_names less, consumes 1]
  and diff_induct = diff_induct [case_names 0 0_succ succ_succ, consumes 2]

(* belongs to theory Epsilon *)
lemmas eclose_induct = eclose_induct [induct set: eclose]
  and eclose_induct_down = eclose_induct_down [consumes 1]

(* belongs to theory Finite *)
lemmas Fin_induct = Fin_induct [case_names 0 cons, induct set: Fin]

(* belongs to theory CardinalArith *)
lemmas Finite_induct = Finite_induct [case_names 0 cons, induct set: Finite]

(* belongs to theory List *)
lemmas list_append_induct = list_append_induct [case_names Nil snoc, consumes 1]

(* belongs to theory IntDiv *)
lemmas posDivAlg_induct = posDivAlg_induct [consumes 2]
  and negDivAlg_induct = negDivAlg_induct [consumes 2]

end
