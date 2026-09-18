(*  Title:      HOL/Tools/SMT/alethe/cvc_interface.ML
    Author:     Jasmin Blanchette, TU Muenchen

Interface to CVC4 and cvc5 based on an extended version of SMT-LIB.
*)

signature CVC_INTERFACE =
sig
  val hosmtlib_cvcC: SMT_Util.class
end;

structure CVC_Interface: CVC_INTERFACE =
struct

val cvcC = ["cvc"]
val hosmtlib_cvcC = SMTLIB_Interface.hosmtlibC @ cvcC


(* interface *)

local
  fun translate_config order ctxt =
    {order = order,
     (*logic = K (K "(set-logic ALL_SUPPORTED)\n"),*)
     logic = K (K SMT_Translate.ALL),
     fp_kinds = [],
     serialize = #serialize (SMTLIB_Interface.translate_config order [] ctxt)}
in

val _ = Theory.setup (Context.theory_map
  (SMT_Translate.add_config (hosmtlib_cvcC, translate_config SMT_Util.Higher_Order)))

end

end;
