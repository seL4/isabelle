(*  Title:      ZF/thy_data.ML
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   1996 TU Muenchen

Definitions that have to be reread after init_thy_reader has been invoked
*)

fun claset_of tname =
  case get_thydata tname "claset" of
      None => empty_cs
    | Some (CS_DATA cs) => cs;


