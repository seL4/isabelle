(*  Title:      HOL/IOA/NTP/Packet.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Packets
*)

Packet = Multiset +  

types

   'msg packet = "bool * 'msg"

constdefs

  hdr  :: 'msg packet => bool
  "hdr == fst"

  msg :: 'msg packet => 'msg
  "msg == snd"

end
