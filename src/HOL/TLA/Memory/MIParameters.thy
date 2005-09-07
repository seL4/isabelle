(*
    File:        MIParameters.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: MIParameters
    Logic Image: TLA

    RPC-Memory example: Parameters of the memory implementation.
*)

MIParameters = Main +

datatype  histState  =  histA | histB

ML {* use_legacy_bindings (the_context ()) *}

end
