(*  Title:      HOL/Nat.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen

Nat is a partial order
*)

Nat = NatDef +

(*install 'automatic' induction tactic, pretending nat is a datatype
  except for induct_tac and exhaust_tac, everything is dummy*)

MLtext {|
|> Dtype.add_datatype_info
("nat", {case_const = Bound 0, case_rewrites = [],
  constructors = [], induct_tac = nat_ind_tac,
  exhaustion = natE,
  exhaust_tac = fn v => ALLNEWSUBGOALS (res_inst_tac [("n",v)] natE)
                                       (rotate_tac ~1),
  nchotomy = ProtoPure.flexpair_def, case_cong = ProtoPure.flexpair_def})
|}


instance nat :: order (le_refl,le_trans,le_anti_sym,nat_less_le)

consts
  "^"           :: ['a::power,nat] => 'a            (infixr 80)

end
