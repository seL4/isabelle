(*  Title:      HOL/IOA/NTP/Packet.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Packets
*)

Packet = Arith + Multiset +  

types

   'msg packet = "bool * 'msg"

consts

  hdr  :: "'msg packet => bool"
  msg :: "'msg packet => 'msg"

defs

  hdr_def "hdr == fst"
  msg_def "msg == snd"

end
