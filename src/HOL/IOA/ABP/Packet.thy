(*  Title:      HOL/IOA/ABP/Packet.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Olaf Mueller
    Copyright   1995  TU Muenchen

Packets
*)

Packet = Arith +

types

   'msg packet = "bool * 'msg"

consts

  hdr  :: "'msg packet => bool"
  msg :: "'msg packet => 'msg"

defs

  hdr_def "hdr == fst"
  msg_def "msg == snd"

end
