(*  Title:      HOLCF/IOA/ABP/Abschannel.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The transmission channel *}

theory Abschannel
imports IOA Action Lemmas
begin

datatype 'a abs_action = S 'a | R 'a


(**********************************************************
       G e n e r i c   C h a n n e l
 *********************************************************)

definition
  ch_asig :: "'a abs_action signature" where
  "ch_asig = (UN b. {S(b)}, UN b. {R(b)}, {})"

definition
  ch_trans :: "('a abs_action, 'a list)transition set" where
  "ch_trans =
   {tr. let s = fst(tr);
            t = snd(snd(tr))
        in
        case fst(snd(tr))
          of S(b) => ((t = s) | (t = s @ [b]))  |
             R(b) => s ~= [] &
                      b = hd(s) &
                      ((t = s) | (t = tl(s)))}"

definition
  ch_ioa :: "('a abs_action, 'a list)ioa" where
  "ch_ioa = (ch_asig, {[]}, ch_trans,{},{})"


(**********************************************************
  C o n c r e t e  C h a n n e l s  b y   R e n a m i n g
 *********************************************************)

definition
  rsch_actions :: "'m action => bool abs_action option" where
  "rsch_actions (akt) =
          (case akt of
           Next    =>  None |
           S_msg(m) => None |
            R_msg(m) => None |
           S_pkt(packet) => None |
            R_pkt(packet) => None |
            S_ack(b) => Some(S(b)) |
            R_ack(b) => Some(R(b)))"

definition
  srch_actions :: "'m action =>(bool * 'm) abs_action option" where
  "srch_actions akt =
          (case akt of
            Next    =>  None |
           S_msg(m) => None |
            R_msg(m) => None |
           S_pkt(p) => Some(S(p)) |
            R_pkt(p) => Some(R(p)) |
            S_ack(b) => None |
            R_ack(b) => None)"

definition
  srch_ioa :: "('m action, 'm packet list)ioa" where
  "srch_ioa = rename ch_ioa srch_actions"
definition
  rsch_ioa :: "('m action, bool list)ioa" where
  "rsch_ioa = rename ch_ioa rsch_actions"

definition
  srch_asig :: "'m action signature" where
  "srch_asig = asig_of(srch_ioa)"

definition
  rsch_asig :: "'m action signature" where
  "rsch_asig = asig_of(rsch_ioa)"

definition
  srch_trans :: "('m action, 'm packet list)transition set" where
  "srch_trans = trans_of(srch_ioa)"
definition
  rsch_trans :: "('m action, bool list)transition set" where
  "rsch_trans = trans_of(rsch_ioa)"

end
