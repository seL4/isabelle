(*  Title:      HOLCF/IOA/ABP/Packet.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Packets *}

theory Packet
imports Main
begin

types
  'msg packet = "bool * 'msg"

definition
  hdr :: "'msg packet => bool" where
  "hdr = fst"

definition
  msg :: "'msg packet => 'msg" where
  "msg = snd"

end
