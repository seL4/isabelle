(*  Title:      HOL/IOA/NTP/Packet.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Packets
*)


(* Instantiation of a tautology? *)
goal Packet.thy "!x. x = packet --> hdr(x) = hdr(packet)";
 by (simp_tac (!simpset addsimps [Packet.hdr_def]) 1);
qed "eq_packet_imp_eq_hdr"; 