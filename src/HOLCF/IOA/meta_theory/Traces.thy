(*  Title:      HOLCF/IOA/meta_theory/Traces.thy
    ID:         $Id$
    Author:     Olaf Müller

Executions and Traces of I/O automata in HOLCF.
*)   

		       
Traces = Sequence + Automata +

default type
 
types  
   ('a,'s)pairs            =    "('a * 's) Seq"
   ('a,'s)execution        =    "'s * ('a,'s)pairs"
   'a trace                =    "'a Seq"

   ('a,'s)execution_module = "('a,'s)execution set * 'a signature"
   'a schedule_module      = "'a trace set * 'a signature"
   'a trace_module         = "'a trace set * 'a signature"
 
consts

   (* Executions *)

  is_exec_fragC      ::"('a,'s)ioa => ('a,'s)pairs -> 's => tr"
  is_exec_frag,
  has_execution ::"[('a,'s)ioa, ('a,'s)execution] => bool"
  executions    :: "('a,'s)ioa => ('a,'s)execution set"

  (* Schedules and traces *)
  filter_act    ::"('a,'s)pairs -> 'a trace"
  has_schedule,
  has_trace     :: "[('a,'s)ioa, 'a trace] => bool"
  schedules,
  traces        :: "('a,'s)ioa => 'a trace set"
  mk_trace      :: "('a,'s)ioa => ('a,'s)pairs -> 'a trace"

  laststate    ::"('a,'s)execution => 's"

  (* A predicate holds infinitely (finitely) often in a sequence *)

  inf_often      ::"('a => bool) => 'a Seq => bool"
  fin_often      ::"('a => bool) => 'a Seq => bool"

  (* fairness of executions *)

  wfair_ex       ::"('a,'s)ioa => ('a,'s)execution => bool"
  sfair_ex       ::"('a,'s)ioa => ('a,'s)execution => bool"
  is_wfair       ::"('a,'s)ioa => 'a set => ('a,'s)execution => bool"
  is_sfair       ::"('a,'s)ioa => 'a set => ('a,'s)execution => bool"
  fair_ex        ::"('a,'s)ioa => ('a,'s)execution => bool"

  (* fair behavior sets *)
 
  fairexecutions ::"('a,'s)ioa => ('a,'s)execution set"
  fairtraces     ::"('a,'s)ioa => 'a trace set"

  (* Notions of implementation *)
  "=<|" :: "[('a,'s1)ioa, ('a,'s2)ioa] => bool"   (infixr 12) 
  fair_implements  :: "('a,'s1)ioa => ('a,'s2)ioa => bool"

  (* Execution, schedule and trace modules *)
  Execs         ::  "('a,'s)ioa => ('a,'s)execution_module"
  Scheds        ::  "('a,'s)ioa => 'a schedule_module"
  Traces        ::  "('a,'s)ioa => 'a trace_module"


defs


(*  ------------------- Executions ------------------------------ *)


is_exec_frag_def
  "is_exec_frag A ex ==  ((is_exec_fragC A$(snd ex)) (fst ex) ~= FF)"


is_exec_fragC_def
  "is_exec_fragC A ==(fix$(LAM h ex. (%s. case ex of 
      nil => TT
    | x##xs => (flift1 
            (%p. Def ((s,p):trans_of A) andalso (h$xs) (snd p)) 
             $x)
   )))" 



executions_def
  "executions ioa == {e. ((fst e) : starts_of(ioa)) &               
                         is_exec_frag ioa e}"


(*  ------------------- Schedules ------------------------------ *)


filter_act_def
  "filter_act == Map fst"

has_schedule_def
  "has_schedule ioa sch ==                                               
     (? ex:executions ioa. sch = filter_act$(snd ex))"

schedules_def
  "schedules ioa == {sch. has_schedule ioa sch}"


(*  ------------------- Traces ------------------------------ *)

has_trace_def
  "has_trace ioa tr ==                                               
     (? sch:schedules ioa. tr = Filter (%a. a:ext(ioa))$sch)"
 
traces_def
  "traces ioa == {tr. has_trace ioa tr}"


mk_trace_def
  "mk_trace ioa == LAM tr. 
     Filter (%a. a:ext(ioa))$(filter_act$tr)"


(*  ------------------- Fair Traces ------------------------------ *)

laststate_def
  "laststate ex == case Last$(snd ex) of
                      UU  => fst ex
                    | Def at => snd at"

inf_often_def
  "inf_often P s == Infinite (Filter P$s)"

(*  filtering P yields a finite or partial sequence *)
fin_often_def
  "fin_often P s == ~inf_often P s"

(* Note that partial execs cannot be wfair as the inf_often predicate in the 
   else branch prohibits it. However they can be sfair in the case when all W 
   are only finitely often enabled: Is this the right model?  
   See LiveIOA for solution conforming with the literature and superseding this one *)
wfair_ex_def
  "wfair_ex A ex == ! W : wfair_of A.  
                      if   Finite (snd ex) 
                      then ~Enabled A W (laststate ex)
                      else is_wfair A W ex"

is_wfair_def
  "is_wfair A W ex == (inf_often (%x. fst x:W) (snd ex)
                     | inf_often (%x.~Enabled A W (snd x)) (snd ex))"

sfair_ex_def
  "sfair_ex A ex == ! W : sfair_of A.
                      if   Finite (snd ex) 
                      then ~Enabled A W (laststate ex)
                      else is_sfair A W ex"

is_sfair_def
  "is_sfair A W ex ==  (inf_often (%x. fst x:W) (snd ex)
                      | fin_often (%x. Enabled A W (snd x)) (snd ex))"

fair_ex_def
  "fair_ex A ex == wfair_ex A ex & sfair_ex A ex"

fairexecutions_def
  "fairexecutions A == {ex. ex:executions A & fair_ex A ex}"

fairtraces_def
  "fairtraces A == {mk_trace A$(snd ex) | ex. ex:fairexecutions A}"


(*  ------------------- Implementation ------------------------------ *)

ioa_implements_def
  "ioa1 =<| ioa2 ==   
    (((inputs(asig_of(ioa1)) = inputs(asig_of(ioa2))) &   
     (outputs(asig_of(ioa1)) = outputs(asig_of(ioa2)))) &
      traces(ioa1) <= traces(ioa2))"

fair_implements_def
  "fair_implements C A == inp(C) = inp(A) &  out(C)=out(A) &
                          fairtraces(C) <= fairtraces(A)"

(*  ------------------- Modules ------------------------------ *)

Execs_def
  "Execs A  == (executions A, asig_of A)"

Scheds_def
  "Scheds A == (schedules A, asig_of A)"

Traces_def
  "Traces A == (traces A,asig_of A)"


end