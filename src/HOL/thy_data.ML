(*  Title:      HOL/thy_data.ML
    ID:         $Id$
    Author:     Carsten Clasohm
    Copyright   1995 TU Muenchen

Definitions that have to be reread after init_thy_reader has been invoked
*)

fun simpset_of tname =
  case get_thydata tname "simpset" of
      None => empty_ss
    | Some (SS_DATA ss) => ss;

fun claset_of tname =
  case get_thydata tname "claset" of
      None => empty_cs
    | Some (CS_DATA cs) => cs;


(** Information about datatypes **)

(* Retrieve information for a specific datatype *)
fun datatype_info thy tname =
  case get_thydata (thyname_of_sign (sign_of thy)) "datatypes" of
      None => None
    | Some (DT_DATA ds) => assoc (ds, tname);

fun match_info thy tname =
  case datatype_info thy tname of
      Some {case_const, constructors, ...} =>
        {case_const=case_const, constructors=constructors}
    | None => error ("No datatype \"" ^ tname ^ "\" defined in this theory.");

fun induct_info thy tname =
  case datatype_info thy tname of
      Some {constructors, nchotomy, ...} =>
        {constructors=constructors, nchotomy=nchotomy}
    | None => error ("No datatype \"" ^ tname ^ "\" defined in this theory.");


(* Retrieve information for all datatypes defined in a theory and its
   ancestors *)
fun extract_info thy =
  let val (congs, rewrites) =
        case get_thydata (thyname_of_sign (sign_of thy)) "datatypes" of
            None => ([], [])
          | Some (DT_DATA ds) =>
              let val info = map snd ds
              in (map #case_cong info, flat (map #case_rewrites info)) end;
  in {case_congs = congs, case_rewrites = rewrites} end;
