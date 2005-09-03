(*  Title:      HOL/IOA/NTP/Packet.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
*)

theory Packet
imports Multiset
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
