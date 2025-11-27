(*  Title:      HOL/Tools/SMT/cvc_interface.ML
    Author:     Jasmin Blanchette, TU Muenchen

Interface to CVC4 and cvc5 based on an extended version of SMT-LIB.
*)

signature CVC_INTERFACE =
sig
  val smtlib_cvcC: SMT_Util.class
  val hosmtlib_cvcC: SMT_Util.class
end;

structure CVC_Interface: CVC_INTERFACE =
struct

val cvcC = ["cvc"]
val smtlib_cvcC = SMTLIB_Interface.smtlibC @ cvcC
val hosmtlib_cvcC = SMTLIB_Interface.hosmtlibC @ cvcC


(* interface *)

local
  fun translate_config order (_ : Proof.context) =
    {order = order,
     logic = K (K "(set-logic ALL_SUPPORTED)\n"),
     fp_kinds = [BNF_Util.Least_FP, BNF_Util.Greatest_FP],
     serialize = SMTLIB_Interface.serialize SMTLIB_Interface.serialize_datatypes}
in

val _ = Theory.setup (Context.theory_map
  (SMT_Translate.add_config (smtlib_cvcC, translate_config SMT_Util.First_Order) #>
   SMT_Translate.add_config (hosmtlib_cvcC, translate_config SMT_Util.Higher_Order)))

end

end;
