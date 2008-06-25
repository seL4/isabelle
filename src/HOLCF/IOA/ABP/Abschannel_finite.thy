(*  Title:      HOLCF/IOA/ABP/Abschannels.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* The transmission channel -- finite version *}

theory Abschannel_finite
imports Abschannel IOA Action Lemmas
begin

primrec reverse :: "'a list => 'a list"
where
  reverse_Nil:  "reverse([]) = []"
| reverse_Cons: "reverse(x#xs) =  reverse(xs)@[x]"

definition
  ch_fin_asig :: "'a abs_action signature" where
  "ch_fin_asig = ch_asig"

definition
  ch_fin_trans :: "('a abs_action, 'a list)transition set" where
  "ch_fin_trans =
   {tr. let s = fst(tr);
            t = snd(snd(tr))
        in
        case fst(snd(tr))
          of S(b) => ((t = s) |
                     (if (b=hd(reverse(s)) & s~=[]) then  t=s else  t=s@[b])) |
             R(b) => s ~= [] &
                      b = hd(s) &
                      ((t = s) | (t = tl(s)))}"

definition
  ch_fin_ioa :: "('a abs_action, 'a list)ioa" where
  "ch_fin_ioa = (ch_fin_asig, {[]}, ch_fin_trans,{},{})"

definition
  srch_fin_ioa :: "('m action, 'm packet list)ioa" where
  "srch_fin_ioa = rename ch_fin_ioa  srch_actions"

definition
  rsch_fin_ioa :: "('m action, bool list)ioa" where
  "rsch_fin_ioa = rename ch_fin_ioa  rsch_actions"

definition
  srch_fin_asig :: "'m action signature" where
  "srch_fin_asig = asig_of(srch_fin_ioa)"

definition
  rsch_fin_asig :: "'m action signature" where
  "rsch_fin_asig = asig_of(rsch_fin_ioa)"

definition
  srch_fin_trans :: "('m action, 'm packet list)transition set" where
  "srch_fin_trans = trans_of(srch_fin_ioa)"

definition
  rsch_fin_trans :: "('m action, bool list)transition set" where
  "rsch_fin_trans = trans_of(rsch_fin_ioa)"

end
