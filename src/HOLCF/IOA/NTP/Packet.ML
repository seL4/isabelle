(*  Title:      HOL/IOA/NTP/Packet.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind

Packets.
*)

(* Instantiation of a tautology? *)
Goal "!x. x = packet --> hdr(x) = hdr(packet)";
 by (simp_tac (simpset() addsimps [hdr_def]) 1);
qed "eq_packet_imp_eq_hdr"; 

Addsimps [hdr_def,msg_def];
