(*  Title:      HOL/IOA/NTP/Action.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The set of all actions of the system.
*)

Action = Packet + Datatype +
datatype 'm action = S_msg ('m) | R_msg ('m)
                   | S_pkt ('m packet) | R_pkt ('m packet)
                   | S_ack (bool) | R_ack (bool)
                   | C_m_s | C_m_r | C_r_s | C_r_r ('m)
end
