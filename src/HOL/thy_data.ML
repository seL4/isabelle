(*  Title:      HOL/thy_data.ML
    ID:         $Id$
    Author:     Carsten Clasohm
    Copyright   1995 TU Muenchen

Definitions that have to be reread after init_thy_reader has been invoked
*)

fun simpset_of tname =
  case get_thydata (theory_of tname) "simpset" of
      None => empty_ss
    | Some (SS_DATA ss) => ss;

fun datatypes_of tname =
  case get_thydata (theory_of tname) "datatypes" of
      None => []
    | Some (DT_DATA ds) => ds;
