(*  Title:      TFL/thry
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

signature Thry_sig =
sig
  type 'a binding

  structure USyntax : USyntax_sig
  val match_term : theory -> term -> term 
                    -> term binding list * typ binding list

  val match_type : theory -> typ -> typ -> typ binding list

  val typecheck : theory -> term -> cterm

  val make_definition: theory -> string -> term -> thm * theory

  (* Datatype facts of various flavours *)
  val match_info: theory -> string -> {constructors:term list,
                                     case_const:term} option

  val induct_info: theory -> string -> {constructors:term list,
                                      nchotomy:thm} option

  val extract_info: theory -> {case_congs:thm list, case_rewrites:thm list}

end;


