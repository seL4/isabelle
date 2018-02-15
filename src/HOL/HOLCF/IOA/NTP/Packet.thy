(*  Title:      HOL/HOLCF/IOA/NTP/Packet.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

theory Packet
imports Multiset
begin

type_synonym
  'msg packet = "bool * 'msg"

definition
  hdr :: "'msg packet \<Rightarrow> bool" where
  "hdr \<equiv> fst"

definition
  msg :: "'msg packet \<Rightarrow> 'msg" where
  "msg \<equiv> snd"


text \<open>Instantiation of a tautology?\<close>
lemma eq_packet_imp_eq_hdr: "\<forall>x. x = packet \<longrightarrow> hdr(x) = hdr(packet)"
  by simp

declare hdr_def [simp] msg_def [simp]

end
