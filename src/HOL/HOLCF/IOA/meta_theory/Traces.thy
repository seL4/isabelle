(*  Title:      HOL/HOLCF/IOA/meta_theory/Traces.thy
    Author:     Olaf Müller
*)

section \<open>Executions and Traces of I/O automata in HOLCF\<close>

theory Traces
imports Sequence Automata
begin

default_sort type

type_synonym ('a, 's) pairs = "('a * 's) Seq"
type_synonym ('a, 's) execution = "'s * ('a, 's) pairs"
type_synonym 'a trace = "'a Seq"
type_synonym ('a, 's) execution_module = "('a, 's) execution set * 'a signature"
type_synonym 'a schedule_module = "'a trace set * 'a signature"
type_synonym 'a trace_module = "'a trace set * 'a signature"


(*  ------------------- Executions ------------------------------ *)

definition is_exec_fragC :: "('a, 's) ioa \<Rightarrow> ('a, 's) pairs \<rightarrow> 's \<Rightarrow> tr"
where
  "is_exec_fragC A = (fix $ (LAM h ex. (%s. case ex of
      nil => TT
    | x##xs => (flift1
            (%p. Def ((s,p):trans_of A) andalso (h$xs) (snd p))
             $x)
   )))"

definition is_exec_frag :: "[('a,'s)ioa, ('a,'s)execution] \<Rightarrow> bool"
  where "is_exec_frag A ex = ((is_exec_fragC A $ (snd ex)) (fst ex) ~= FF)"

definition executions :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution set"
  where "executions ioa = {e. ((fst e) \<in> starts_of(ioa)) \<and> is_exec_frag ioa e}"


(*  ------------------- Schedules ------------------------------ *)

definition filter_act :: "('a, 's) pairs \<rightarrow> 'a trace"
  where "filter_act = Map fst"

definition has_schedule :: "[('a, 's) ioa, 'a trace] \<Rightarrow> bool"
  where "has_schedule ioa sch \<longleftrightarrow> (\<exists>ex \<in> executions ioa. sch = filter_act $ (snd ex))"

definition schedules :: "('a, 's) ioa \<Rightarrow> 'a trace set"
  where "schedules ioa = {sch. has_schedule ioa sch}"


(*  ------------------- Traces ------------------------------ *)

definition has_trace :: "[('a, 's) ioa, 'a trace] \<Rightarrow> bool"
  where "has_trace ioa tr = (\<exists>sch \<in> schedules ioa. tr = Filter (\<lambda>a. a \<in> ext ioa) $ sch)"

definition traces :: "('a, 's) ioa \<Rightarrow> 'a trace set"
  where "traces ioa \<equiv> {tr. has_trace ioa tr}"

definition mk_trace :: "('a, 's) ioa \<Rightarrow> ('a, 's) pairs \<rightarrow> 'a trace"
  where "mk_trace ioa = (LAM tr. Filter (\<lambda>a. a \<in> ext ioa) $ (filter_act $ tr))"


(*  ------------------- Fair Traces ------------------------------ *)

definition laststate :: "('a, 's) execution \<Rightarrow> 's"
where
  "laststate ex = (case Last $ (snd ex) of
                    UU  => fst ex
                  | Def at => snd at)"

(* A predicate holds infinitely (finitely) often in a sequence *)

definition inf_often :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Seq \<Rightarrow> bool"
  where "inf_often P s \<longleftrightarrow> Infinite (Filter P $ s)"

(*  filtering P yields a finite or partial sequence *)
definition fin_often :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Seq \<Rightarrow> bool"
  where "fin_often P s \<longleftrightarrow> \<not> inf_often P s"


(* fairness of executions *)

(* Note that partial execs cannot be wfair as the inf_often predicate in the
   else branch prohibits it. However they can be sfair in the case when all W
   are only finitely often enabled: Is this the right model?
   See LiveIOA for solution conforming with the literature and superseding this one *)
definition is_wfair :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
where
  "is_wfair A W ex \<longleftrightarrow>
    (inf_often (\<lambda>x. fst x \<in> W) (snd ex) \<or> inf_often (\<lambda>x. \<not> Enabled A W (snd x)) (snd ex))"
definition wfair_ex :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
where
  "wfair_ex A ex \<longleftrightarrow> (\<forall>W \<in> wfair_of A.
                      if Finite (snd ex)
                      then \<not> Enabled A W (laststate ex)
                      else is_wfair A W ex)"

definition is_sfair :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
where
  "is_sfair A W ex \<longleftrightarrow>
    (inf_often (\<lambda>x. fst x:W) (snd ex) \<or> fin_often (\<lambda>x. Enabled A W (snd x)) (snd ex))"
definition sfair_ex :: "('a, 's)ioa \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
where
  "sfair_ex A ex \<longleftrightarrow> (\<forall>W \<in> sfair_of A.
                      if   Finite (snd ex)
                      then ~Enabled A W (laststate ex)
                      else is_sfair A W ex)"

definition fair_ex :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
  where "fair_ex A ex \<longleftrightarrow> wfair_ex A ex \<and> sfair_ex A ex"


(* fair behavior sets *)

definition fairexecutions :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution set"
  where "fairexecutions A = {ex. ex \<in> executions A \<and> fair_ex A ex}"

definition fairtraces :: "('a, 's) ioa \<Rightarrow> 'a trace set"
  where "fairtraces A = {mk_trace A $ (snd ex) | ex. ex \<in> fairexecutions A}"


(*  ------------------- Implementation ------------------------------ *)

(* Notions of implementation *)

definition ioa_implements :: "[('a, 's1) ioa, ('a, 's2) ioa] \<Rightarrow> bool"  (infixr "=<|" 12)
where
  "(ioa1 =<| ioa2) \<longleftrightarrow>
    (((inputs(asig_of(ioa1)) = inputs(asig_of(ioa2))) \<and>
     (outputs(asig_of(ioa1)) = outputs(asig_of(ioa2)))) \<and>
      traces(ioa1) \<subseteq> traces(ioa2))"

definition fair_implements :: "('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
where
  "fair_implements C A \<longleftrightarrow> inp C = inp A \<and> out C = out A \<and> fairtraces C \<subseteq> fairtraces A"


(*  ------------------- Modules ------------------------------ *)

(* Execution, schedule and trace modules *)

definition Execs :: "('a, 's) ioa \<Rightarrow> ('a, 's) execution_module"
  where "Execs A = (executions A, asig_of A)"

definition Scheds :: "('a, 's) ioa \<Rightarrow> 'a schedule_module"
  where "Scheds A = (schedules A, asig_of A)"

definition Traces :: "('a, 's) ioa \<Rightarrow> 'a trace_module"
  where "Traces A = (traces A, asig_of A)"


lemmas [simp del] = HOL.ex_simps HOL.all_simps split_paired_Ex
declare Let_def [simp]
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

lemmas exec_rws = executions_def is_exec_frag_def



subsection "recursive equations of operators"

(* ---------------------------------------------------------------- *)
(*                               filter_act                         *)
(* ---------------------------------------------------------------- *)


lemma filter_act_UU: "filter_act$UU = UU"
  by (simp add: filter_act_def)

lemma filter_act_nil: "filter_act$nil = nil"
  by (simp add: filter_act_def)

lemma filter_act_cons: "filter_act$(x\<leadsto>xs) = (fst x) \<leadsto> filter_act$xs"
  by (simp add: filter_act_def)

declare filter_act_UU [simp] filter_act_nil [simp] filter_act_cons [simp]


(* ---------------------------------------------------------------- *)
(*                             mk_trace                             *)
(* ---------------------------------------------------------------- *)

lemma mk_trace_UU: "mk_trace A$UU=UU"
  by (simp add: mk_trace_def)

lemma mk_trace_nil: "mk_trace A$nil=nil"
  by (simp add: mk_trace_def)

lemma mk_trace_cons: "mk_trace A$(at \<leadsto> xs) =
             (if ((fst at):ext A)
                  then (fst at) \<leadsto> (mk_trace A$xs)
                  else mk_trace A$xs)"

  by (simp add: mk_trace_def)

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
  apply (rule fix_eq4)
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

lemma is_exec_fragC_cons: "(is_exec_fragC A$(pr\<leadsto>xs)) s =
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
  by (simp add: is_exec_frag_def)

lemma is_exec_frag_nil: "is_exec_frag A (s, nil)"
  by (simp add: is_exec_frag_def)

lemma is_exec_frag_cons: "is_exec_frag A (s, (a,t)\<leadsto>ex) =
                                (((s,a,t):trans_of A) &
                                is_exec_frag A (t, ex))"
  by (simp add: is_exec_frag_def)


(* Delsimps [is_exec_fragC_UU,is_exec_fragC_nil,is_exec_fragC_cons]; *)
declare is_exec_frag_UU [simp] is_exec_frag_nil [simp] is_exec_frag_cons [simp]

(* ---------------------------------------------------------------------------- *)
                           section "laststate"
(* ---------------------------------------------------------------------------- *)

lemma laststate_UU: "laststate (s,UU) = s"
  by (simp add: laststate_def)

lemma laststate_nil: "laststate (s,nil) = s"
  by (simp add: laststate_def)

lemma laststate_cons: "!! ex. Finite ex ==> laststate (s,at\<leadsto>ex) = laststate (snd at,ex)"
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
  apply (unfold executions_def mk_trace_def has_trace_def schedules_def has_schedule_def [abs_def])
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
  apply (tactic \<open>pair_induct_tac @{context} "xs" [@{thm is_exec_frag_def},
    @{thm Forall_def}, @{thm sforall_def}] 1\<close>)
  (* main case *)
  apply (auto simp add: is_trans_of_def)
  done

lemma exec_in_sig:
  "!! A.[|  is_trans_of A; x:executions A |] ==>
  Forall (%a. a:act A) (filter_act$(snd x))"
  apply (simp add: executions_def)
  apply (tactic \<open>pair_tac @{context} "x" 1\<close>)
  apply (rule execfrag_in_sig [THEN spec, THEN mp])
  apply auto
  done

lemma scheds_in_sig:
  "!! A.[|  is_trans_of A; x:schedules A |] ==>
    Forall (%a. a:act A) x"
  apply (unfold schedules_def has_schedule_def [abs_def])
  apply (fast intro!: exec_in_sig)
  done


subsection "executions are prefix closed"

(* only admissible in y, not if done in x !! *)
lemma execfrag_prefixclosed: "!x s. is_exec_frag A (s,x) & y<<x  --> is_exec_frag A (s,y)"
  apply (tactic \<open>pair_induct_tac @{context} "y" [@{thm is_exec_frag_def}] 1\<close>)
  apply (intro strip)
  apply (tactic \<open>Seq_case_simp_tac @{context} "x" 1\<close>)
  apply (tactic \<open>pair_tac @{context} "a" 1\<close>)
  apply auto
  done

lemmas exec_prefixclosed =
  conjI [THEN execfrag_prefixclosed [THEN spec, THEN spec, THEN mp]]


(* second prefix notion for Finite x *)

lemma exec_prefix2closed [rule_format]:
  "! y s. is_exec_frag A (s,x@@y) --> is_exec_frag A (s,x)"
  apply (tactic \<open>pair_induct_tac @{context} "x" [@{thm is_exec_frag_def}] 1\<close>)
  apply (intro strip)
  apply (tactic \<open>Seq_case_simp_tac @{context} "s" 1\<close>)
  apply (tactic \<open>pair_tac @{context} "a" 1\<close>)
  apply auto
  done

end
