(*  Title:      HOL/TPTP/TPTP_Parser/tptp_proof.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Collection of functions for handling TPTP proofs.
Specialised for handling LEO-II proofs.
*)

(*FIXME actually this is more general than proofs*)
signature TPTP_PROOF =
sig
  datatype parent_detail =
    Bind of string(*variable name*) * TPTP_Syntax.tptp_formula
  datatype parent_info_as =
      Parent of string(*node name*)
    | ParentWithDetails of string(*node name*) *
        parent_detail list
  datatype useful_info_as = Status of TPTP_Syntax.status_value
  datatype source_info =
      File of string * string
    | Inference of
       string *
       useful_info_as list *
       parent_info_as list
  val extract_source_info : (TPTP_Syntax.general_term * 'a list) option ->
                               source_info option

  val is_inference_called : string -> source_info -> bool

  val parent_name : parent_info_as -> string
end


structure TPTP_Proof : TPTP_PROOF =
struct

datatype parent_detail =
  Bind of string(*variable name*) * TPTP_Syntax.tptp_formula
datatype parent_info_as =
    Parent of string(*node name*)
  | ParentWithDetails of string(*node name*) *
      parent_detail list
datatype useful_info_as = Status of TPTP_Syntax.status_value
datatype source_info =
    File of string * string
  | Inference of
     string *
     useful_info_as list *
     parent_info_as list

open TPTP_Syntax

exception ANNOT_STRUCTURE of general_term

(*Extract name of inference rule, and the inferences it relies on*)
(*This is tuned to work with LEO-II, and is brittle wrt upstream
  changes of the proof protocol.*)
fun extract_source_info annot =
  let
      fun analyse_parent_details [] acc = acc
        | analyse_parent_details (x :: xs) acc =
            case x of
                General_Data
                 (Application
                  ("bind",
                   [General_Data (V var),
                    General_Data (Formula_Data (THF, fmla))])) =>
                  analyse_parent_details xs (Bind (var, fmla) :: acc)
              (*FIXME incomplete*)
            | _ => analyse_parent_details xs acc

      fun analyse_parent_info [] acc = acc
        | analyse_parent_info (x :: xs) acc =
            case x of
                General_Data (Number (Int_num, num)) =>
                  analyse_parent_info
                    xs (Parent num :: acc)
              | General_Data (Atomic_Word name) =>
                  analyse_parent_info
                    xs (Parent name :: acc)
              | General_Term
                  (Number (Int_num, num),
                   General_List
                    parent_details) =>
                  let
                    val parent_details' = analyse_parent_details parent_details []
                  in
                    analyse_parent_info
                      xs (ParentWithDetails
                          (num, parent_details') :: acc)
                  end
              (*FIXME incomplete*)
              | _ => analyse_parent_info xs acc

      fun analyse_useful_info [] acc = acc
        | analyse_useful_info (x :: xs) acc =
          case x of
            General_Data
              (Application
                 ("status", [General_Data (Atomic_Word status_str)])) =>
              analyse_useful_info
                xs (Status (read_status status_str) :: acc)
            (*FIXME incomplete*)
            | _ => analyse_useful_info xs acc

    fun analyse_annot
        (General_Data
          (Application
            ("inference",
             [General_Data (Atomic_Word inference_name),
              General_List useful_info,
              General_List parent_info])), _) =
                (SOME (Inference
                       (inference_name,
                        analyse_useful_info useful_info [],
                        analyse_parent_info parent_info [])))

      | analyse_annot
         (General_Data
          (Application
            ("file",
             [General_Data (Atomic_Word filename),
              General_Data (Atomic_Word defname)])), _) =
                (SOME (File (filename, defname)))

      | analyse_annot
         (General_Data
           (Application
             ("file",
              [General_Data (Atomic_Word filename),
               General_Data (Number (Int_num, defname))])), _) =
                (SOME (File (filename, defname)))

      (*This was added to support Satallax proofs.*)
      | analyse_annot
         (General_Data
           (Application
             ("introduced",
              [General_Data (Atomic_Word "assumption"),
               General_List []])), _) =
                (SOME (Inference
                       ("assumption", [], [])))


      | analyse_annot (other, _) = raise (ANNOT_STRUCTURE other)
  in
    case annot of
      NONE => NONE
    | SOME annot => analyse_annot annot
  end

fun is_inference_called s src =
  case src of
      Inference (n, _, _) => s = n
    | _ => false

fun parent_name (Parent n) = n
  | parent_name (ParentWithDetails (n, _)) = n

end
