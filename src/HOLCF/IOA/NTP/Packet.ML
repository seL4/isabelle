(*  Title:      HOL/IOA/NTP/Packet.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Packets.
*)

(* Instantiation of a tautology? *)
Goal "!x. x = packet --> hdr(x) = hdr(packet)";
 by (simp_tac (simpset() addsimps [Packet.hdr_def]) 1);
qed "eq_packet_imp_eq_hdr"; 

Addsimps [Packet.hdr_def,Packet.msg_def];
