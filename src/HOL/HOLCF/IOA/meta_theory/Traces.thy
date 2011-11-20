(*  Title:      HOL/HOLCF/IOA/meta_theory/Traces.thy
    Author:     Olaf Müller
*)

header {* Executions and Traces of I/O automata in HOLCF *}

theory Traces
imports Sequence Automata
begin

default_sort type

type_synonym
   ('a,'s)pairs            =    "('a * 's) Seq"

type_synonym
   ('a,'s)execution        =    "'s * ('a,'s)pairs"

type_synonym
   'a trace                =    "'a Seq"

type_synonym
   ('a,'s)execution_module = "('a,'s)execution set * 'a signature"

type_synonym
   'a schedule_module      = "'a trace set * 'a signature"

type_synonym
   'a trace_module         = "'a trace set * 'a signature"

consts

   (* Executions *)

  is_exec_fragC ::"('a,'s)ioa => ('a,'s)pairs -> 's => tr"
  is_exec_frag  ::"[('a,'s)ioa, ('a,'s)execution] => bool"
  has_execution ::"[('a,'s)ioa, ('a,'s)execution] => bool"
  executions    :: "('a,'s)ioa => ('a,'s)execution set"

  (* Schedules and traces *)
  filter_act    ::"('a,'s)pairs -> 'a trace"
  has_schedule  :: "[('a,'s)ioa, 'a trace] => bool"
  has_trace     :: "[('a,'s)ioa, 'a trace] => bool"
  schedules     :: "('a,'s)ioa => 'a trace set"
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
  ioa_implements :: "[('a,'s1)ioa, ('a,'s2)ioa] => bool"   (infixr "=<|" 12)
  fair_implements  :: "('a,'s1)ioa => ('a,'s2)ioa => bool"

  (* Execution, schedule and trace modules *)
  Execs         ::  "('a,'s)ioa => ('a,'s)execution_module"
  Scheds        ::  "('a,'s)ioa => 'a schedule_module"
  Traces        ::  "('a,'s)ioa => 'a trace_module"


defs


(*  ------------------- Executions ------------------------------ *)


is_exec_frag_def:
  "is_exec_frag A ex ==  ((is_exec_fragC A$(snd ex)) (fst ex) ~= FF)"


is_exec_fragC_def:
  "is_exec_fragC A ==(fix$(LAM h ex. (%s. case ex of
      nil => TT
    | x##xs => (flift1
            (%p. Def ((s,p):trans_of A) andalso (h$xs) (snd p))
             $x)
   )))"



executions_def:
  "executions ioa == {e. ((fst e) : starts_of(ioa)) &
                         is_exec_frag ioa e}"


(*  ------------------- Schedules ------------------------------ *)


filter_act_def:
  "filter_act == Map fst"

has_schedule_def:
  "has_schedule ioa sch ==
     (? ex:executions ioa. sch = filter_act$(snd ex))"

schedules_def:
  "schedules ioa == {sch. has_schedule ioa sch}"


(*  ------------------- Traces ------------------------------ *)

has_trace_def:
  "has_trace ioa tr ==
     (? sch:schedules ioa. tr = Filter (%a. a:ext(ioa))$sch)"

traces_def:
  "traces ioa == {tr. has_trace ioa tr}"


mk_trace_def:
  "mk_trace ioa == LAM tr.
     Filter (%a. a:ext(ioa))$(filter_act$tr)"


(*  ------------------- Fair Traces ------------------------------ *)

laststate_def:
  "laststate ex == case Last$(snd ex) of
                      UU  => fst ex
                    | Def at => snd at"

inf_often_def:
  "inf_often P s == Infinite (Filter P$s)"

(*  filtering P yields a finite or partial sequence *)
fin_often_def:
  "fin_often P s == ~inf_often P s"

(* Note that partial execs cannot be wfair as the inf_often predicate in the
   else branch prohibits it. However they can be sfair in the case when all W
   are only finitely often enabled: Is this the right model?
   See LiveIOA for solution conforming with the literature and superseding this one *)
wfair_ex_def:
  "wfair_ex A ex == ! W : wfair_of A.
                      if   Finite (snd ex)
                      then ~Enabled A W (laststate ex)
                      else is_wfair A W ex"

is_wfair_def:
  "is_wfair A W ex == (inf_often (%x. fst x:W) (snd ex)
                     | inf_often (%x.~Enabled A W (snd x)) (snd ex))"

sfair_ex_def:
  "sfair_ex A ex == ! W : sfair_of A.
                      if   Finite (snd ex)
                      then ~Enabled A W (laststate ex)
                      else is_sfair A W ex"

is_sfair_def:
  "is_sfair A W ex ==  (inf_often (%x. fst x:W) (snd ex)
                      | fin_often (%x. Enabled A W (snd x)) (snd ex))"

fair_ex_def:
  "fair_ex A ex == wfair_ex A ex & sfair_ex A ex"

fairexecutions_def:
  "fairexecutions A == {ex. ex:executions A & fair_ex A ex}"

fairtraces_def:
  "fairtraces A == {mk_trace A$(snd ex) | ex. ex:fairexecutions A}"


(*  ------------------- Implementation ------------------------------ *)

ioa_implements_def:
  "ioa1 =<| ioa2 ==
    (((inputs(asig_of(ioa1)) = inputs(asig_of(ioa2))) &
     (outputs(asig_of(ioa1)) = outputs(asig_of(ioa2)))) &
      traces(ioa1) <= traces(ioa2))"

fair_implements_def:
  "fair_implements C A == inp(C) = inp(A) &  out(C)=out(A) &
                          fairtraces(C) <= fairtraces(A)"

(*  ------------------- Modules ------------------------------ *)

Execs_def:
  "Execs A  == (executions A, asig_of A)"

Scheds_def:
  "Scheds A == (schedules A, asig_of A)"

Traces_def:
  "Traces A == (traces A,asig_of A)"


lemmas [simp del] = HOL.ex_simps HOL.all_simps split_paired_Ex
declare Let_def [simp]
declaration {* fn _ => Classical.map_cs (fn cs => cs delSWrapper "split_all_tac") *}

lemmas exec_rws = executions_def is_exec_frag_def



subsection "recursive equations of operators"

(* ---------------------------------------------------------------- *)
(*                               filter_act                         *)
(* ---------------------------------------------------------------- *)


lemma filter_act_UU: "filter_act$UU = UU"
apply (simp add: filter_act_def)
done

lemma filter_act_nil: "filter_act$nil = nil"
apply (simp add: filter_act_def)
done

lemma filter_act_cons: "filter_act$(x>>xs) = (fst x) >> filter_act$xs"
apply (simp add: filter_act_def)
done

declare filter_act_UU [simp] filter_act_nil [simp] filter_act_cons [simp]


(* ---------------------------------------------------------------- *)
(*                             mk_trace                             *)
(* ---------------------------------------------------------------- *)

lemma mk_trace_UU: "mk_trace A$UU=UU"
apply (simp add: mk_trace_def)
done

lemma mk_trace_nil: "mk_trace A$nil=nil"
apply (simp add: mk_trace_def)
done

lemma mk_trace_cons: "mk_trace A$(at >> xs) =     
             (if ((fst at):ext A)            
                  then (fst at) >> (mk_trace A$xs)     
                  else mk_trace A$xs)"

apply (simp add: mk_trace_def)
done

declare mk_trace_UU [simp] mk_trace_nil [simp] mk_trace_cons [simp]

(* ---------------------------------------------------------------- *)
(*                             is_exec_fragC                             *)
(* ---------------------------------------------------------------- *)


lemma is_exec_fragC_unfold: "is_exec_fragC A = (LAM ex. (%s. case ex of  
       nil => TT  
     | x##xs => (flift1   
             (%p. Def ((s,p):trans_of A) andalso (is_exec_fragC A$xs) (snd p))  
              $x)  
    ))"
apply (rule trans)
apply (rule fix_eq2)
apply (rule is_exec_fragC_def)
apply (rule beta_cfun)
apply (simp add: flift1_def)
done

lemma is_exec_fragC_UU: "(is_exec_fragC A$UU) s=UU"
apply (subst is_exec_fragC_unfold)
apply simp
done

lemma is_exec_fragC_nil: "(is_exec_fragC A$nil) s = TT"
apply (subst is_exec_fragC_unfold)
apply simp
done

lemma is_exec_fragC_cons: "(is_exec_fragC A$(pr>>xs)) s =  
                         (Def ((s,pr):trans_of A)  
                 andalso (is_exec_fragC A$xs)(snd pr))"
apply (rule trans)
apply (subst is_exec_fragC_unfold)
apply (simp add: Consq_def flift1_def)
apply simp
done


declare is_exec_fragC_UU [simp] is_exec_fragC_nil [simp] is_exec_fragC_cons [simp]


(* ---------------------------------------------------------------- *)
(*                        is_exec_frag                              *)
(* ---------------------------------------------------------------- *)

lemma is_exec_frag_UU: "is_exec_frag A (s, UU)"
apply (simp add: is_exec_frag_def)
done

lemma is_exec_frag_nil: "is_exec_frag A (s, nil)"
apply (simp add: is_exec_frag_def)
done

lemma is_exec_frag_cons: "is_exec_frag A (s, (a,t)>>ex) =  
                                (((s,a,t):trans_of A) &  
                                is_exec_frag A (t, ex))"
apply (simp add: is_exec_frag_def)
done


(* Delsimps [is_exec_fragC_UU,is_exec_fragC_nil,is_exec_fragC_cons]; *)
declare is_exec_frag_UU [simp] is_exec_frag_nil [simp] is_exec_frag_cons [simp]

(* ---------------------------------------------------------------------------- *)
                           section "laststate"
(* ---------------------------------------------------------------------------- *)

lemma laststate_UU: "laststate (s,UU) = s"
apply (simp add: laststate_def)
done

lemma laststate_nil: "laststate (s,nil) = s"
apply (simp add: laststate_def)
done

lemma laststate_cons: "!! ex. Finite ex ==> laststate (s,at>>ex) = laststate (snd at,ex)"
apply (simp (no_asm) add: laststate_def)
apply (case_tac "ex=nil")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply (drule Finite_Last1 [THEN mp])
apply assumption
apply defined
done

declare laststate_UU [simp] laststate_nil [simp] laststate_cons [simp]

lemma exists_laststate: "!!ex. Finite ex ==> (! s. ? u. laststate (s,ex)=u)"
apply (tactic "Seq_Finite_induct_tac @{context} 1")
done


subsection "has_trace, mk_trace"

(* alternative definition of has_trace tailored for the refinement proof, as it does not 
   take the detour of schedules *)

lemma has_trace_def2: 
"has_trace A b = (? ex:executions A. b = mk_trace A$(snd ex))"
apply (unfold executions_def mk_trace_def has_trace_def schedules_def has_schedule_def)
apply auto
done


subsection "signatures and executions, schedules"

(* All executions of A have only actions of A. This is only true because of the 
   predicate state_trans (part of the predicate IOA): We have no dependent types.
   For executions of parallel automata this assumption is not needed, as in par_def
   this condition is included once more. (see Lemmas 1.1.1c in CompoExecs for example) *)

lemma execfrag_in_sig: 
  "!! A. is_trans_of A ==>  
  ! s. is_exec_frag A (s,xs) --> Forall (%a. a:act A) (filter_act$xs)"
apply (tactic {* pair_induct_tac @{context} "xs" [@{thm is_exec_frag_def},
  @{thm Forall_def}, @{thm sforall_def}] 1 *})
(* main case *)
apply (auto simp add: is_trans_of_def)
done

lemma exec_in_sig: 
  "!! A.[|  is_trans_of A; x:executions A |] ==>  
  Forall (%a. a:act A) (filter_act$(snd x))"
apply (simp add: executions_def)
apply (tactic {* pair_tac @{context} "x" 1 *})
apply (rule execfrag_in_sig [THEN spec, THEN mp])
apply auto
done

lemma scheds_in_sig: 
  "!! A.[|  is_trans_of A; x:schedules A |] ==>  
    Forall (%a. a:act A) x"
apply (unfold schedules_def has_schedule_def)
apply (fast intro!: exec_in_sig)
done


subsection "executions are prefix closed"

(* only admissible in y, not if done in x !! *)
lemma execfrag_prefixclosed: "!x s. is_exec_frag A (s,x) & y<<x  --> is_exec_frag A (s,y)"
apply (tactic {* pair_induct_tac @{context} "y" [@{thm is_exec_frag_def}] 1 *})
apply (intro strip)
apply (tactic {* Seq_case_simp_tac @{context} "xa" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
apply auto
done

lemmas exec_prefixclosed =
  conjI [THEN execfrag_prefixclosed [THEN spec, THEN spec, THEN mp]]


(* second prefix notion for Finite x *)

lemma exec_prefix2closed [rule_format]:
  "! y s. is_exec_frag A (s,x@@y) --> is_exec_frag A (s,x)"
apply (tactic {* pair_induct_tac @{context} "x" [@{thm is_exec_frag_def}] 1 *})
apply (intro strip)
apply (tactic {* Seq_case_simp_tac @{context} "s" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
apply auto
done

end
