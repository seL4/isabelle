(*  Title:      HOLCF/HOLCF.thy
    ID:         $Id$
    Author:     Franz Regensburger

Top theory for HOLCF system.
*)

theory HOLCF
imports Sprod Ssum Up Lift Discrete One Tr
begin

text {*
  Remove continuity lemmas from simp set, so continuity subgoals
  are handled by the @{text cont_proc} simplifier procedure.
*}
declare cont_lemmas1 [simp del]
declare cont_lemmas_ext [simp del]

end
