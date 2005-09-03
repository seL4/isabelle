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

constdefs
  hdr  :: "'msg packet => bool"
  "hdr == fst"

  msg :: "'msg packet => 'msg"
  "msg == snd"

ML {* use_legacy_bindings (the_context ()) *}

end
