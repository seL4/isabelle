(*  Title:      HOLCF/IOA/meta_theory/LiveIOA.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Live I/O automata -- specified by temproal formulas

*) 
  
LiveIOA = TLS + 

default term

types

 ('a,'s)live_ioa       = "('a,'s)ioa * ('a,'s)ioa_temp"
 
consts

validLIOA   :: "('a,'s)live_ioa => ('a,'s)ioa_temp  => bool"

WF         :: "('a,'s)ioa => 'a set => ('a,'s)ioa_temp"
SF         :: "('a,'s)ioa => 'a set => ('a,'s)ioa_temp"

liveexecutions    :: "('a,'s)live_ioa => ('a,'s)execution set"
livetraces        :: "('a,'s)live_ioa => 'a trace set"
live_implements   :: "('a,'s1)live_ioa => ('a,'s2)live_ioa => bool"
is_live_ref_map   :: "('s1 => 's2) => ('a,'s1)live_ioa => ('a,'s2)live_ioa => bool"

 
defs

validLIOA_def
  "validLIOA AL P == validIOA (fst AL) ((snd AL) .--> P)"


WF_def
  "WF A acts ==  <> [] <%(s,a,t) . Enabled A acts s> .--> [] <> <xt2 (plift (%a. a : acts))>"

SF_def
  "SF A acts ==  [] <> <%(s,a,t) . Enabled A acts s> .--> [] <> <xt2 (plift (%a. a : acts))>"
 

liveexecutions_def
   "liveexecutions AP == {exec. exec : executions (fst AP) & (exec |== (snd AP))}"

livetraces_def
  "livetraces AP == {mk_trace (fst AP)$(snd ex) | ex. ex:liveexecutions AP}"

live_implements_def
  "live_implements CL AM == (inp (fst CL) = inp (fst AM)) & 
                            (out (fst CL) = out (fst AM)) &
                            livetraces CL <= livetraces AM"

is_live_ref_map_def
   "is_live_ref_map f CL AM ==  
            is_ref_map f (fst CL ) (fst AM) & 
            (! exec : executions (fst CL). (exec |== (snd CL)) --> 
                                           ((corresp_ex (fst AM) f exec) |== (snd AM)))"


end