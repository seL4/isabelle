(*  Title:      HOLCF/IOA/ABP/Packet.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1995  TU Muenchen

Packets
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
