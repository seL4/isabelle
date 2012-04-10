(*  Title:      HOL/TPTP/TPTP_Parser/tptp_proof.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Collection of functions for handling TPTP proofs.
*)

signature TPTP_PROOF =
sig
  val extract_inference_info : (TPTP_Syntax.general_term * 'a list) option ->
                               (string * string list) option
end


structure TPTP_Proof : TPTP_PROOF =
struct

open TPTP_Syntax

(*Extract name of inference rule, and the inferences it relies on*)
(*This is tuned to work with LEO-II, and is brittle wrt upstream
  changes of the proof protocol.*)
fun extract_inference_info annot =
  let
    fun get_line_id (General_Data (Number (Int_num, num))) = [num]
      | get_line_id (General_Data (Atomic_Word name)) = [name]
      | get_line_id (General_Term (Number (Int_num, num), _ (*e.g. a bind*))) = [num]
      | get_line_id _ = []
        (*e.g. General_Data (Application ("theory", [General_Data
          (Atomic_Word "equality")])) -- which would come from E through LEO-II*)
  in
    case annot of
      NONE => NONE
    | SOME annot =>
      (case annot of
        (General_Data (Application ("inference",
        [General_Data (Atomic_Word inference_name),
         _,
         General_List related_lines])), _) =>
          (SOME (inference_name, map get_line_id related_lines |> List.concat))
      | _ => NONE)
  end

end
