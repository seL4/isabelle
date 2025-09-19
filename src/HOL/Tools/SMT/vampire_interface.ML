(*  Title:      HOL/Tools/SMT/vampire_interface.ML
    Author:     Jasmin Blanchette, LMU Muenchen
    Author:     Elisabeth Lempa, LMU Muenchen

Interface to Vampire as an SMT prover.
*)

signature VAMPIRE_INTERFACE =
sig
  val smtlib_vampireC: SMT_Util.class
end;

structure Vampire_Interface : VAMPIRE_INTERFACE =
struct

val vampireC = ["vampire"]
val smtlib_vampireC = SMTLIB_Interface.smtlibC @ vampireC

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
  fun translate_config ctxt : SMT_Translate.config =
    {order = SMT_Util.First_Order,
     logic = K (K ""),
     fp_kinds = [BNF_Util.Least_FP],
     serialize = SMTLIB_Interface.serialize sdtyp}
in

val _ = Theory.setup (Context.theory_map
  (SMT_Translate.add_config (smtlib_vampireC, translate_config)))

end

end;
