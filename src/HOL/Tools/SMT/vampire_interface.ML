(*  Title:      HOL/Tools/SMT/vampire_interface.ML
    Author:     Jasmin Blanchette, LMU Muenchen
    Author:     Elisabeth Lempa, LMU Muenchen

Interface to Vampire as an SMT prover.
*)

signature VAMPIRE_INTERFACE =
sig
  val smtlib_vampire_dtC: SMT_Util.class
  val smtlib_vampire_nodtC: SMT_Util.class
end;

structure Vampire_Interface : VAMPIRE_INTERFACE =
struct

val vampire_dtC = ["vampire_dt"]
val vampire_nodtC = ["vampire_nodt"]
val smtlib_vampire_dtC = SMTLIB_Interface.smtlibC @ vampire_dtC
val smtlib_vampire_nodtC = SMTLIB_Interface.smtlibC @ vampire_nodtC

fun sctrarg (sel, typ) = "(" ^ sel ^ " " ^ typ ^ ")"
fun sctr (name, args) = enclose "(" ")" (implode_space (name :: map sctrarg args))
fun sdatatype (_, ctrs) = enclose "(" ")" (implode_space (map sctr ctrs))
fun sarity (name, _) = enclose "(" ")" (name ^ " 0")

fun sdtyp ((fp, dtyps : SMTLIB_Interface.dtype_decls)) =
  Buffer.add (enclose ("(declare-" ^ BNF_FP_Util.co_prefix fp ^ "datatypes (" ^
    implode_space (map sarity dtyps) ^ ") (") "))\n"
  (space_implode"\n  " (map sdatatype dtyps)))

(* interface *)

local
  fun translate_config fp_kinds (_ : Proof.context) : SMT_Translate.config =
    {order = SMT_Util.First_Order,
     logic = K (K ""),
     fp_kinds = fp_kinds,
     serialize = SMTLIB_Interface.serialize sdtyp}
in

val _ = Theory.setup (Context.theory_map
  (SMT_Translate.add_config (smtlib_vampire_dtC, translate_config [BNF_Util.Least_FP]) #>
   SMT_Translate.add_config (smtlib_vampire_nodtC, translate_config [])))

end

end;
