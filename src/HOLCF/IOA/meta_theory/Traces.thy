(*  Title:      HOLCF/IOA/meta_theory/Traces.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Executions and Traces of I/O automata in HOLCF.
*)   

		       
Traces = Sequence + Automata +

default term
 
types  
   ('a,'s)pairs            =    "('a * 's) Seq"
   ('a,'s)execution        =    "'s * ('a,'s)pairs"
   'a trace                =    "'a Seq"
 
consts

   (* Executions *)
  is_ex_fr      ::"('a,'s)ioa => ('a,'s)pairs -> ('s => tr)"
  is_execution_fragment,
  has_execution ::"[('a,'s)ioa, ('a,'s)execution] => bool"
  executions    :: "('a,'s)ioa => ('a,'s)execution set"

  (* Schedules and traces *)
  filter_act    ::"('a,'s)pairs -> 'a trace"
  has_schedule,
  has_trace     :: "[('a,'s)ioa, 'a trace] => bool"
  schedules,
  traces        :: "('a,'s)ioa => 'a trace set"
 
  mk_trace      :: "('a,'s)ioa => ('a,'s)pairs -> 'a trace"

  (* Notion of implementation *)
  "=<|" :: "[('a,'s1)ioa, ('a,'s2)ioa] => bool"   (infixr 12) 

(*
(* FIX: introduce good symbol *)
syntax (symbols)

  "op <<|"       ::"[('a,'s1)ioa, ('a,'s2)ioa] => bool" (infixr "\\<parallel>" 10)
*)


defs


(*  ------------------- Executions ------------------------------ *)


is_execution_fragment_def
  "is_execution_fragment A ex == ((is_ex_fr A`(snd ex)) (fst ex) ~= FF)"

is_ex_fr_def
  "is_ex_fr A ==(fix`(LAM h ex. (%s. case ex of 
      nil => TT
    | x##xs => (flift1 
            (%p.Def ((s,p):trans_of A) andalso (h`xs) (snd p)) 
             `x)
   )))" 
  
executions_def
  "executions ioa == {e. ((fst e) : starts_of(ioa)) &               
                         is_execution_fragment ioa e}"


(*  ------------------- Schedules ------------------------------ *)


filter_act_def
  "filter_act == Map fst"

has_schedule_def
  "has_schedule ioa sch ==                                               
     (? ex:executions ioa. sch = filter_act`(snd ex))"

schedules_def
  "schedules ioa == {sch. has_schedule ioa sch}"


(*  ------------------- Traces ------------------------------ *)

has_trace_def
  "has_trace ioa tr ==                                               
     (? sch:schedules ioa. tr = Filter (%a.a:ext(ioa))`sch)"

traces_def
  "traces ioa == {tr. has_trace ioa tr}"


mk_trace_def
  "mk_trace ioa == LAM tr. 
     Filter (%a.a:ext(ioa))`(filter_act`tr)"


(*  ------------------- Implementation ------------------------------ *)

ioa_implements_def
  "ioa1 =<| ioa2 ==   
    (((inputs(asig_of(ioa1)) = inputs(asig_of(ioa2))) &   
     (outputs(asig_of(ioa1)) = outputs(asig_of(ioa2)))) &
      traces(ioa1) <= traces(ioa2))"


end