(*  Title:      FOL/thy_data.ML
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


