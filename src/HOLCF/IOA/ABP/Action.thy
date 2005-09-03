(*  Title:      HOLCF/IOA/ABP/Action.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The set of all actions of the system *}

theory Action
imports Packet
begin

datatype 'm action =
    Next | S_msg 'm | R_msg 'm
  | S_pkt "'m packet" | R_pkt "'m packet"
  | S_ack bool | R_ack bool

ML {* use_legacy_bindings (the_context ()) *}

end
