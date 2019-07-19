(*  Title:      HOL/HOLCF/IOA/Abstraction.thy
    Author:     Olaf Müller
*)

section \<open>Abstraction Theory -- tailored for I/O automata\<close>

theory Abstraction
imports LiveIOA
begin

default_sort type

definition cex_abs :: "('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) execution \<Rightarrow> ('a, 's2) execution"
  where "cex_abs f ex = (f (fst ex), Map (\<lambda>(a, t). (a, f t)) \<cdot> (snd ex))"

text \<open>equals cex_abs on Sequences -- after ex2seq application\<close>
definition cex_absSeq ::
    "('s1 \<Rightarrow> 's2) \<Rightarrow> ('a option, 's1) transition Seq \<Rightarrow> ('a option, 's2)transition Seq"
  where "cex_absSeq f = (\<lambda>s. Map (\<lambda>(s, a, t). (f s, a, f t)) \<cdot> s)"

definition is_abstraction :: "('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_abstraction f C A \<longleftrightarrow>
    ((\<forall>s \<in> starts_of C. f s \<in> starts_of A) \<and>
    (\<forall>s t a. reachable C s \<and> s \<midarrow>a\<midarrow>C\<rightarrow> t \<longrightarrow> f s \<midarrow>a\<midarrow>A\<rightarrow> f t))"

definition weakeningIOA :: "('a, 's2) ioa \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> bool"
  where "weakeningIOA A C h \<longleftrightarrow> (\<forall>ex. ex \<in> executions C \<longrightarrow> cex_abs h ex \<in> executions A)"

definition temp_strengthening :: "('a, 's2) ioa_temp \<Rightarrow> ('a, 's1) ioa_temp \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> bool"
  where "temp_strengthening Q P h \<longleftrightarrow> (\<forall>ex. (cex_abs h ex \<TTurnstile> Q) \<longrightarrow> (ex \<TTurnstile> P))"

definition temp_weakening :: "('a, 's2) ioa_temp \<Rightarrow> ('a, 's1) ioa_temp \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> bool"
  where "temp_weakening Q P h \<longleftrightarrow> temp_strengthening (\<^bold>\<not> Q) (\<^bold>\<not> P) h"

definition state_strengthening :: "('a, 's2) step_pred \<Rightarrow> ('a, 's1) step_pred \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> bool"
  where "state_strengthening Q P h \<longleftrightarrow> (\<forall>s t a. Q (h s, a, h t) \<longrightarrow> P (s, a, t))"

definition state_weakening :: "('a, 's2) step_pred \<Rightarrow> ('a, 's1) step_pred \<Rightarrow> ('s1 \<Rightarrow> 's2) \<Rightarrow> bool"
  where "state_weakening Q P h \<longleftrightarrow> state_strengthening (\<^bold>\<not> Q) (\<^bold>\<not> P) h"

definition is_live_abstraction :: "('s1 \<Rightarrow> 's2) \<Rightarrow> ('a, 's1) live_ioa \<Rightarrow> ('a, 's2) live_ioa \<Rightarrow> bool"
  where "is_live_abstraction h CL AM \<longleftrightarrow>
    is_abstraction h (fst CL) (fst AM) \<and> temp_weakening (snd AM) (snd CL) h"


(* thm about ex2seq which is not provable by induction as ex2seq is not continuous *)
axiomatization where
  ex2seq_abs_cex: "ex2seq (cex_abs h ex) = cex_absSeq h (ex2seq ex)"

(* analog to the proved thm strength_Box - proof skipped as trivial *)
axiomatization where
  weak_Box: "temp_weakening P Q h \<Longrightarrow> temp_weakening (\<box>P) (\<box>Q) h"

(* analog to the proved thm strength_Next - proof skipped as trivial *)
axiomatization where
  weak_Next: "temp_weakening P Q h \<Longrightarrow> temp_weakening (\<circle>P) (\<circle>Q) h"


subsection \<open>\<open>cex_abs\<close>\<close>

lemma cex_abs_UU [simp]: "cex_abs f (s, UU) = (f s, UU)"
  by (simp add: cex_abs_def)

lemma cex_abs_nil [simp]: "cex_abs f (s,nil) = (f s, nil)"
  by (simp add: cex_abs_def)

lemma cex_abs_cons [simp]:
  "cex_abs f (s, (a, t) \<leadsto> ex) = (f s, (a, f t) \<leadsto> (snd (cex_abs f (t, ex))))"
  by (simp add: cex_abs_def)


subsection \<open>Lemmas\<close>

lemma temp_weakening_def2: "temp_weakening Q P h \<longleftrightarrow> (\<forall>ex. (ex \<TTurnstile> P) \<longrightarrow> (cex_abs h ex \<TTurnstile> Q))"
  apply (simp add: temp_weakening_def temp_strengthening_def NOT_def temp_sat_def satisfies_def)
  apply auto
  done

lemma state_weakening_def2: "state_weakening Q P h \<longleftrightarrow> (\<forall>s t a. P (s, a, t) \<longrightarrow> Q (h s, a, h t))"
  apply (simp add: state_weakening_def state_strengthening_def NOT_def)
  apply auto
  done


subsection \<open>Abstraction Rules for Properties\<close>

lemma exec_frag_abstraction [rule_format]:
  "is_abstraction h C A \<Longrightarrow>
    \<forall>s. reachable C s \<and> is_exec_frag C (s, xs) \<longrightarrow> is_exec_frag A (cex_abs h (s, xs))"
  apply (simp add: cex_abs_def)
  apply (pair_induct xs simp: is_exec_frag_def)
  txt \<open>main case\<close>
  apply (auto dest: reachable.reachable_n simp add: is_abstraction_def)
  done

lemma abs_is_weakening: "is_abstraction h C A \<Longrightarrow> weakeningIOA A C h"
  apply (simp add: weakeningIOA_def)
  apply auto
  apply (simp add: executions_def)
  txt \<open>start state\<close>
  apply (rule conjI)
  apply (simp add: is_abstraction_def cex_abs_def)
  txt \<open>is-execution-fragment\<close>
  apply (erule exec_frag_abstraction)
  apply (simp add: reachable.reachable_0)
  done


lemma AbsRuleT1:
  "is_abstraction h C A \<Longrightarrow> validIOA A Q \<Longrightarrow> temp_strengthening Q P h \<Longrightarrow> validIOA C P"
  apply (drule abs_is_weakening)
  apply (simp add: weakeningIOA_def validIOA_def temp_strengthening_def)
  apply (auto simp add: split_paired_all)
  done


lemma AbsRuleT2:
  "is_live_abstraction h (C, L) (A, M) \<Longrightarrow> validLIOA (A, M) Q \<Longrightarrow> temp_strengthening Q P h
    \<Longrightarrow> validLIOA (C, L) P"
  apply (unfold is_live_abstraction_def)
  apply auto
  apply (drule abs_is_weakening)
  apply (simp add: weakeningIOA_def temp_weakening_def2 validLIOA_def validIOA_def temp_strengthening_def)
  apply (auto simp add: split_paired_all)
  done


lemma AbsRuleTImprove:
  "is_live_abstraction h (C, L) (A, M) \<Longrightarrow> validLIOA (A,M) (H1 \<^bold>\<longrightarrow> Q) \<Longrightarrow>
    temp_strengthening Q P h \<Longrightarrow> temp_weakening H1 H2 h \<Longrightarrow> validLIOA (C, L) H2 \<Longrightarrow>
    validLIOA (C, L) P"
  apply (unfold is_live_abstraction_def)
  apply auto
  apply (drule abs_is_weakening)
  apply (simp add: weakeningIOA_def temp_weakening_def2 validLIOA_def validIOA_def temp_strengthening_def)
  apply (auto simp add: split_paired_all)
  done


subsection \<open>Correctness of safe abstraction\<close>

lemma abstraction_is_ref_map: "is_abstraction h C A \<Longrightarrow> is_ref_map h C A"
  apply (auto simp: is_abstraction_def is_ref_map_def)
  apply (rule_tac x = "(a,h t) \<leadsto>nil" in exI)
  apply (simp add: move_def)
  done

lemma abs_safety: "inp C = inp A \<Longrightarrow> out C = out A \<Longrightarrow> is_abstraction h C A \<Longrightarrow> C =<| A"
  apply (simp add: ioa_implements_def)
  apply (rule trace_inclusion)
  apply (simp (no_asm) add: externals_def)
  apply (auto)[1]
  apply (erule abstraction_is_ref_map)
  done


subsection \<open>Correctness of life abstraction\<close>

text \<open>
  Reduces to \<open>Filter (Map fst x) = Filter (Map fst (Map (\<lambda>(a, t). (a, x)) x)\<close>,
  that is to special Map Lemma.
\<close>
lemma traces_coincide_abs:
  "ext C = ext A \<Longrightarrow> mk_trace C \<cdot> xs = mk_trace A \<cdot> (snd (cex_abs f (s, xs)))"
  apply (unfold cex_abs_def mk_trace_def filter_act_def)
  apply simp
  apply (pair_induct xs)
  done


text \<open>
  Does not work with \<open>abstraction_is_ref_map\<close> as proof of \<open>abs_safety\<close>, because
  \<open>is_live_abstraction\<close> includes \<open>temp_strengthening\<close> which is necessarily based
  on \<open>cex_abs\<close> and not on \<open>corresp_ex\<close>. Thus, the proof is redone in a more specific
  way for \<open>cex_abs\<close>.
\<close>
lemma abs_liveness:
  "inp C = inp A \<Longrightarrow> out C = out A \<Longrightarrow> is_live_abstraction h (C, M) (A, L) \<Longrightarrow>
    live_implements (C, M) (A, L)"
  apply (simp add: is_live_abstraction_def live_implements_def livetraces_def liveexecutions_def)
  apply auto
  apply (rule_tac x = "cex_abs h ex" in exI)
  apply auto
  text \<open>Traces coincide\<close>
  apply (pair ex)
  apply (rule traces_coincide_abs)
  apply (simp (no_asm) add: externals_def)
  apply (auto)[1]

  text \<open>\<open>cex_abs\<close> is execution\<close>
  apply (pair ex)
  apply (simp add: executions_def)
  text \<open>start state\<close>
  apply (rule conjI)
  apply (simp add: is_abstraction_def cex_abs_def)
  text \<open>\<open>is_execution_fragment\<close>\<close>
  apply (erule exec_frag_abstraction)
  apply (simp add: reachable.reachable_0)

  text \<open>Liveness\<close>
  apply (simp add: temp_weakening_def2)
   apply (pair ex)
  done


subsection \<open>Abstraction Rules for Automata\<close>

lemma AbsRuleA1:
  "inp C = inp A \<Longrightarrow> out C = out A \<Longrightarrow> inp Q = inp P \<Longrightarrow> out Q = out P \<Longrightarrow>
    is_abstraction h1 C A \<Longrightarrow> A =<| Q \<Longrightarrow> is_abstraction h2 Q P \<Longrightarrow> C =<| P"
  apply (drule abs_safety)
  apply assumption+
  apply (drule abs_safety)
  apply assumption+
  apply (erule implements_trans)
  apply (erule implements_trans)
  apply assumption
  done

lemma AbsRuleA2:
  "inp C = inp A \<Longrightarrow> out C = out A \<Longrightarrow> inp Q = inp P \<Longrightarrow> out Q = out P \<Longrightarrow>
    is_live_abstraction h1 (C, LC) (A, LA) \<Longrightarrow> live_implements (A, LA) (Q, LQ) \<Longrightarrow>
    is_live_abstraction h2 (Q, LQ) (P, LP) \<Longrightarrow> live_implements (C, LC) (P, LP)"
  apply (drule abs_liveness)
  apply assumption+
  apply (drule abs_liveness)
  apply assumption+
  apply (erule live_implements_trans)
  apply (erule live_implements_trans)
  apply assumption
  done


declare split_paired_All [simp del]


subsection \<open>Localizing Temporal Strengthenings and Weakenings\<close>

lemma strength_AND:
  "temp_strengthening P1 Q1 h \<Longrightarrow> temp_strengthening P2 Q2 h \<Longrightarrow>
    temp_strengthening (P1 \<^bold>\<and> P2) (Q1 \<^bold>\<and> Q2) h"
  by (auto simp: temp_strengthening_def)

lemma strength_OR:
  "temp_strengthening P1 Q1 h \<Longrightarrow> temp_strengthening P2 Q2 h \<Longrightarrow>
    temp_strengthening (P1 \<^bold>\<or> P2) (Q1 \<^bold>\<or> Q2) h"
  by (auto simp: temp_strengthening_def)

lemma strength_NOT: "temp_weakening P Q h \<Longrightarrow> temp_strengthening (\<^bold>\<not> P) (\<^bold>\<not> Q) h"
  by (auto simp: temp_weakening_def2 temp_strengthening_def)

lemma strength_IMPLIES:
  "temp_weakening P1 Q1 h \<Longrightarrow> temp_strengthening P2 Q2 h \<Longrightarrow>
    temp_strengthening (P1 \<^bold>\<longrightarrow> P2) (Q1 \<^bold>\<longrightarrow> Q2) h"
  by (simp add: temp_weakening_def2 temp_strengthening_def)


lemma weak_AND:
  "temp_weakening P1 Q1 h \<Longrightarrow> temp_weakening P2 Q2 h \<Longrightarrow>
    temp_weakening (P1 \<^bold>\<and> P2) (Q1 \<^bold>\<and> Q2) h"
  by (simp add: temp_weakening_def2)

lemma weak_OR:
  "temp_weakening P1 Q1 h \<Longrightarrow> temp_weakening P2 Q2 h \<Longrightarrow>
    temp_weakening (P1 \<^bold>\<or> P2) (Q1 \<^bold>\<or> Q2) h"
  by (simp add: temp_weakening_def2)

lemma weak_NOT:
  "temp_strengthening P Q h \<Longrightarrow> temp_weakening (\<^bold>\<not> P) (\<^bold>\<not> Q) h"
  by (auto simp add: temp_weakening_def2 temp_strengthening_def)

lemma weak_IMPLIES:
  "temp_strengthening P1 Q1 h \<Longrightarrow> temp_weakening P2 Q2 h \<Longrightarrow>
    temp_weakening (P1 \<^bold>\<longrightarrow> P2) (Q1 \<^bold>\<longrightarrow> Q2) h"
  by (simp add: temp_weakening_def2 temp_strengthening_def)


subsubsection \<open>Box\<close>

(* FIXME: should be same as nil_is_Conc2 when all nils are turned to right side! *)
lemma UU_is_Conc: "(UU = x @@ y) = (((x::'a Seq)= UU) | (x = nil \<and> y = UU))"
  by (Seq_case_simp x)

lemma ex2seqConc [rule_format]:
  "Finite s1 \<longrightarrow> (\<forall>ex. (s \<noteq> nil \<and> s \<noteq> UU \<and> ex2seq ex = s1 @@ s) \<longrightarrow> (\<exists>ex'. s = ex2seq ex'))"
  apply (rule impI)
  apply Seq_Finite_induct
  apply blast
  text \<open>main case\<close>
  apply clarify
  apply (pair ex)
  apply (Seq_case_simp x2)
  text \<open>\<open>UU\<close> case\<close>
  apply (simp add: nil_is_Conc)
  text \<open>\<open>nil\<close> case\<close>
  apply (simp add: nil_is_Conc)
  text \<open>cons case\<close>
  apply (pair aa)
  apply auto
  done

(* important property of ex2seq: can be shiftet, as defined "pointwise" *)
lemma ex2seq_tsuffix: "tsuffix s (ex2seq ex) \<Longrightarrow> \<exists>ex'. s = (ex2seq ex')"
  apply (unfold tsuffix_def suffix_def)
  apply auto
  apply (drule ex2seqConc)
  apply auto
  done


(*important property of cex_absSeq: As it is a 1to1 correspondence,
  properties carry over *)
lemma cex_absSeq_tsuffix: "tsuffix s t \<Longrightarrow> tsuffix (cex_absSeq h s) (cex_absSeq h t)"
  apply (unfold tsuffix_def suffix_def cex_absSeq_def)
  apply auto
  apply (simp add: Mapnil)
  apply (simp add: MapUU)
  apply (rule_tac x = "Map (% (s,a,t) . (h s,a, h t))\<cdot>s1" in exI)
  apply (simp add: Map2Finite MapConc)
  done


lemma strength_Box: "temp_strengthening P Q h \<Longrightarrow> temp_strengthening (\<box>P) (\<box>Q) h"
  apply (unfold temp_strengthening_def state_strengthening_def temp_sat_def satisfies_def Box_def)
  apply clarify
  apply (frule ex2seq_tsuffix)
  apply clarify
  apply (drule_tac h = "h" in cex_absSeq_tsuffix)
  apply (simp add: ex2seq_abs_cex)
  done


subsubsection \<open>Init\<close>

lemma strength_Init:
  "state_strengthening P Q h \<Longrightarrow> temp_strengthening (Init P) (Init Q) h"
  apply (unfold temp_strengthening_def state_strengthening_def
    temp_sat_def satisfies_def Init_def unlift_def)
  apply auto
  apply (pair ex)
  apply (Seq_case_simp x2)
  apply (pair a)
  done


subsubsection \<open>Next\<close>

lemma TL_ex2seq_UU: "TL \<cdot> (ex2seq (cex_abs h ex)) = UU \<longleftrightarrow> TL \<cdot> (ex2seq ex) = UU"
  apply (pair ex)
  apply (Seq_case_simp x2)
  apply (pair a)
  apply (Seq_case_simp s)
  apply (pair a)
  done

lemma TL_ex2seq_nil: "TL \<cdot> (ex2seq (cex_abs h ex)) = nil \<longleftrightarrow> TL \<cdot> (ex2seq ex) = nil"
  apply (pair ex)
  apply (Seq_case_simp x2)
  apply (pair a)
  apply (Seq_case_simp s)
  apply (pair a)
  done

(*important property of cex_absSeq: As it is a 1to1 correspondence,
  properties carry over*)
lemma cex_absSeq_TL: "cex_absSeq h (TL \<cdot> s) = TL \<cdot> (cex_absSeq h s)"
  by (simp add: MapTL cex_absSeq_def)

(* important property of ex2seq: can be shiftet, as defined "pointwise" *)
lemma TLex2seq: "snd ex \<noteq> UU \<Longrightarrow> snd ex \<noteq> nil \<Longrightarrow> \<exists>ex'. TL\<cdot>(ex2seq ex) = ex2seq ex'"
  apply (pair ex)
  apply (Seq_case_simp x2)
  apply (pair a)
  apply auto
  done

lemma ex2seqnilTL: "TL \<cdot> (ex2seq ex) \<noteq> nil \<longleftrightarrow> snd ex \<noteq> nil \<and> snd ex \<noteq> UU"
  apply (pair ex)
  apply (Seq_case_simp x2)
  apply (pair a)
  apply (Seq_case_simp s)
  apply (pair a)
  done

lemma strength_Next: "temp_strengthening P Q h \<Longrightarrow> temp_strengthening (\<circle>P) (\<circle>Q) h"
  apply (unfold temp_strengthening_def state_strengthening_def temp_sat_def satisfies_def Next_def)
  apply simp
  apply auto
  apply (simp add: TL_ex2seq_nil TL_ex2seq_UU)
  apply (simp add: TL_ex2seq_nil TL_ex2seq_UU)
  apply (simp add: TL_ex2seq_nil TL_ex2seq_UU)
  apply (simp add: TL_ex2seq_nil TL_ex2seq_UU)
  text \<open>cons case\<close>
  apply (simp add: TL_ex2seq_nil TL_ex2seq_UU ex2seq_abs_cex cex_absSeq_TL [symmetric] ex2seqnilTL)
  apply (erule conjE)
  apply (drule TLex2seq)
  apply assumption
  apply auto
  done


text \<open>Localizing Temporal Weakenings - 2\<close>

lemma weak_Init: "state_weakening P Q h \<Longrightarrow> temp_weakening (Init P) (Init Q) h"
  apply (simp add: temp_weakening_def2 state_weakening_def2
    temp_sat_def satisfies_def Init_def unlift_def)
  apply auto
  apply (pair ex)
  apply (Seq_case_simp x2)
  apply (pair a)
  done


text \<open>Localizing Temproal Strengthenings - 3\<close>

lemma strength_Diamond: "temp_strengthening P Q h \<Longrightarrow> temp_strengthening (\<diamond>P) (\<diamond>Q) h"
  apply (unfold Diamond_def)
  apply (rule strength_NOT)
  apply (rule weak_Box)
  apply (erule weak_NOT)
  done

lemma strength_Leadsto:
  "temp_weakening P1 P2 h \<Longrightarrow> temp_strengthening Q1 Q2 h \<Longrightarrow>
    temp_strengthening (P1 \<leadsto> Q1) (P2 \<leadsto> Q2) h"
  apply (unfold Leadsto_def)
  apply (rule strength_Box)
  apply (erule strength_IMPLIES)
  apply (erule strength_Diamond)
  done


text \<open>Localizing Temporal Weakenings - 3\<close>

lemma weak_Diamond: "temp_weakening P Q h \<Longrightarrow> temp_weakening (\<diamond>P) (\<diamond>Q) h"
  apply (unfold Diamond_def)
  apply (rule weak_NOT)
  apply (rule strength_Box)
  apply (erule strength_NOT)
  done

lemma weak_Leadsto:
  "temp_strengthening P1 P2 h \<Longrightarrow> temp_weakening Q1 Q2 h \<Longrightarrow>
    temp_weakening (P1 \<leadsto> Q1) (P2 \<leadsto> Q2) h"
  apply (unfold Leadsto_def)
  apply (rule weak_Box)
  apply (erule weak_IMPLIES)
  apply (erule weak_Diamond)
  done

lemma weak_WF:
  "(\<And>s. Enabled A acts (h s) \<Longrightarrow> Enabled C acts s)
    \<Longrightarrow> temp_weakening (WF A acts) (WF C acts) h"
  apply (unfold WF_def)
  apply (rule weak_IMPLIES)
  apply (rule strength_Diamond)
  apply (rule strength_Box)
  apply (rule strength_Init)
  apply (rule_tac [2] weak_Box)
  apply (rule_tac [2] weak_Diamond)
  apply (rule_tac [2] weak_Init)
  apply (auto simp add: state_weakening_def state_strengthening_def
    xt2_def plift_def option_lift_def NOT_def)
  done

lemma weak_SF:
  "(\<And>s. Enabled A acts (h s) \<Longrightarrow> Enabled C acts s)
    \<Longrightarrow> temp_weakening (SF A acts) (SF C acts) h"
  apply (unfold SF_def)
  apply (rule weak_IMPLIES)
  apply (rule strength_Box)
  apply (rule strength_Diamond)
  apply (rule strength_Init)
  apply (rule_tac [2] weak_Box)
  apply (rule_tac [2] weak_Diamond)
  apply (rule_tac [2] weak_Init)
  apply (auto simp add: state_weakening_def state_strengthening_def
    xt2_def plift_def option_lift_def NOT_def)
  done


lemmas weak_strength_lemmas =
  weak_OR weak_AND weak_NOT weak_IMPLIES weak_Box weak_Next weak_Init
  weak_Diamond weak_Leadsto strength_OR strength_AND strength_NOT
  strength_IMPLIES strength_Box strength_Next strength_Init
  strength_Diamond strength_Leadsto weak_WF weak_SF

ML \<open>
fun abstraction_tac ctxt =
  SELECT_GOAL (auto_tac
    (ctxt addSIs @{thms weak_strength_lemmas}
      addsimps [@{thm state_strengthening_def}, @{thm state_weakening_def}]))
\<close>

method_setup abstraction = \<open>Scan.succeed (SIMPLE_METHOD' o abstraction_tac)\<close>

end
