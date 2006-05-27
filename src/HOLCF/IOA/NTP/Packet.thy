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


text {* Instantiation of a tautology? *}
lemma eq_packet_imp_eq_hdr: "!x. x = packet --> hdr(x) = hdr(packet)"
  by simp

declare hdr_def [simp] msg_def [simp]

end
