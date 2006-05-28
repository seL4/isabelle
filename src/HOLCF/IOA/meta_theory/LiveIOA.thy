(*  Title:      HOLCF/IOA/meta_theory/LiveIOA.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Live I/O automata -- specified by temproal formulas *}

theory LiveIOA
imports TLS
begin

defaultsort type

types
  ('a, 's) live_ioa = "('a,'s)ioa * ('a,'s)ioa_temp"

consts

validLIOA   :: "('a,'s)live_ioa => ('a,'s)ioa_temp  => bool"

WF         :: "('a,'s)ioa => 'a set => ('a,'s)ioa_temp"
SF         :: "('a,'s)ioa => 'a set => ('a,'s)ioa_temp"

liveexecutions    :: "('a,'s)live_ioa => ('a,'s)execution set"
livetraces        :: "('a,'s)live_ioa => 'a trace set"
live_implements   :: "('a,'s1)live_ioa => ('a,'s2)live_ioa => bool"
is_live_ref_map   :: "('s1 => 's2) => ('a,'s1)live_ioa => ('a,'s2)live_ioa => bool"


defs

validLIOA_def:
  "validLIOA AL P == validIOA (fst AL) ((snd AL) .--> P)"


WF_def:
  "WF A acts ==  <> [] <%(s,a,t) . Enabled A acts s> .--> [] <> <xt2 (plift (%a. a : acts))>"

SF_def:
  "SF A acts ==  [] <> <%(s,a,t) . Enabled A acts s> .--> [] <> <xt2 (plift (%a. a : acts))>"


liveexecutions_def:
   "liveexecutions AP == {exec. exec : executions (fst AP) & (exec |== (snd AP))}"

livetraces_def:
  "livetraces AP == {mk_trace (fst AP)$(snd ex) | ex. ex:liveexecutions AP}"

live_implements_def:
  "live_implements CL AM == (inp (fst CL) = inp (fst AM)) &
                            (out (fst CL) = out (fst AM)) &
                            livetraces CL <= livetraces AM"

is_live_ref_map_def:
   "is_live_ref_map f CL AM ==
            is_ref_map f (fst CL ) (fst AM) &
            (! exec : executions (fst CL). (exec |== (snd CL)) -->
                                           ((corresp_ex (fst AM) f exec) |== (snd AM)))"


declare split_paired_Ex [simp del]

lemma live_implements_trans: 
"!!LC. [| live_implements (A,LA) (B,LB); live_implements (B,LB) (C,LC) |]  
      ==> live_implements (A,LA) (C,LC)"
apply (unfold live_implements_def)
apply auto
done


subsection "Correctness of live refmap"
	
lemma live_implements: "[| inp(C)=inp(A); out(C)=out(A);  
                   is_live_ref_map f (C,M) (A,L) |]  
                ==> live_implements (C,M) (A,L)"
apply (simp add: is_live_ref_map_def live_implements_def livetraces_def liveexecutions_def)
apply (tactic "safe_tac set_cs")
apply (rule_tac x = "corresp_ex A f ex" in exI)
apply (tactic "safe_tac set_cs")
  (* Traces coincide, Lemma 1 *)
  apply (tactic {* pair_tac "ex" 1 *})
  apply (erule lemma_1 [THEN spec, THEN mp])
  apply (simp (no_asm) add: externals_def)
  apply (auto)[1]
  apply (simp add: executions_def reachable.reachable_0)
 
  (* corresp_ex is execution, Lemma 2 *)
  apply (tactic {* pair_tac "ex" 1 *})
  apply (simp add: executions_def)
  (* start state *) 
  apply (rule conjI)
  apply (simp add: is_ref_map_def corresp_ex_def)
  (* is-execution-fragment *)
  apply (erule lemma_2 [THEN spec, THEN mp])
  apply (simp add: reachable.reachable_0)

 (* Liveness *)
apply auto
done

end
