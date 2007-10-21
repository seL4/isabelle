(*  Title:      HOLCF/IOA/ABP/Spec.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The specification of reliable transmission *}

theory Spec
imports IOA Action
begin

definition
  spec_sig :: "'m action signature" where
  sig_def: "spec_sig = (UN m.{S_msg(m)},
                       UN m.{R_msg(m)} Un {Next},
                       {})"

definition
  spec_trans :: "('m action, 'm list)transition set" where
  trans_def: "spec_trans =
   {tr. let s = fst(tr);
            t = snd(snd(tr))
        in
        case fst(snd(tr))
        of
        Next =>  t=s |            (* Note that there is condition as in Sender *)
        S_msg(m) => t = s@[m]  |
        R_msg(m) => s = (m#t)  |
        S_pkt(pkt) => False |
        R_pkt(pkt) => False |
        S_ack(b) => False |
        R_ack(b) => False}"

definition
  spec_ioa :: "('m action, 'm list)ioa" where
  ioa_def: "spec_ioa = (spec_sig, {[]}, spec_trans)"

end
