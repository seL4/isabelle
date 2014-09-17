(*  Title:      HOL/Tools/SMT/cvc4_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to CVC4 based on an extended version of SMT-LIB.
*)

signature CVC4_INTERFACE =
sig
  val smtlib_cvc4C: SMT_Util.class
end;

structure CVC4_Interface: CVC4_INTERFACE =
struct

val smtlib_cvc4C = SMTLIB_Interface.smtlibC @ ["cvc4"]


(* interface *)

local
  fun translate_config ctxt =
    {logic = K "", fp_kinds = [BNF_Util.Least_FP, BNF_Util.Greatest_FP],
     serialize = #serialize (SMTLIB_Interface.translate_config ctxt)}
in

val _ =
  Theory.setup (Context.theory_map (SMT_Translate.add_config (smtlib_cvc4C, translate_config)))

end

end;
