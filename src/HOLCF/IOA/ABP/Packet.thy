(*  Title:      HOLCF/IOA/ABP/Packet.thy
    ID:         $Id$
    Author:     Olaf Müller

Packets.
*)

Packet = NatArith +

types

   'msg packet = "bool * 'msg"

constdefs

  hdr  :: 'msg packet => bool
  "hdr == fst"

  msg :: 'msg packet => 'msg
  "msg == snd"

end
