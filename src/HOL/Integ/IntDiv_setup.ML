(*  Title:      HOL/Integ/IntDiv_setup.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Informatik, TU Muenchen
    Copyright   2002  TU Muenchen

Simproc for cancelling div and mod
*)


structure CancelDivModData =
struct

val div_name = "Divides.op div";
val mod_name = "Divides.op mod";
val mk_binop = HOLogic.mk_binop;
val mk_sum = Int_Numeral_Simprocs.mk_sum HOLogic.intT;
val dest_sum = Int_Numeral_Simprocs.dest_sum;

(*logic*)

val div_mod_eqs =
  map mk_meta_eq [thm"zdiv_zmod_equality",thm"zdiv_zmod_equality2"]

val trans = trans

val prove_eq_sums =
  let val simps = zdiff_def :: Int_Numeral_Simprocs.add_0s @ zadd_ac
  in NatArithUtils.prove_conv all_tac (NatArithUtils.simp_all simps) end

end;

structure CancelDivMod = CancelDivModFun(CancelDivModData);

val cancel_zdiv_zmod_proc = NatArithUtils.prep_simproc
      ("cancel_zdiv_zmod", ["(m::int) + n"], CancelDivMod.proc);

Addsimprocs[cancel_zdiv_zmod_proc];
