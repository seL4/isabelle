(*  Title:      HOLCF/IOA/meta_theory/Abstraction.thy
    Author:     Olaf Müller
*)

header {* Abstraction Theory -- tailored for I/O automata *}

theory Abstraction
imports LiveIOA
uses ("ioa.ML")
begin

defaultsort type

definition
  cex_abs :: "('s1 => 's2) => ('a,'s1)execution => ('a,'s2)execution" where
  "cex_abs f ex = (f (fst ex), Map (%(a,t). (a,f t))$(snd ex))"
definition
  -- {* equals cex_abs on Sequences -- after ex2seq application *}
  cex_absSeq :: "('s1 => 's2) => ('a option,'s1)transition Seq => ('a option,'s2)transition Seq" where
  "cex_absSeq f = (%s. Map (%(s,a,t). (f s,a,f t))$s)"

definition
  is_abstraction ::"[('s1=>'s2),('a,'s1)ioa,('a,'s2)ioa] => bool" where
  "is_abstraction f C A =
   ((!s:starts_of(C). f(s):starts_of(A)) &
   (!s t a. reachable C s & s -a--C-> t
            --> (f s) -a--A-> (f t)))"

definition
  weakeningIOA :: "('a,'s2)ioa => ('a,'s1)ioa => ('s1 => 's2) => bool" where
  "weakeningIOA A C h = (!ex. ex : executions C --> cex_abs h ex : executions A)"
definition
  temp_strengthening :: "('a,'s2)ioa_temp => ('a,'s1)ioa_temp => ('s1 => 's2) => bool" where
  "temp_strengthening Q P h = (!ex. (cex_abs h ex |== Q) --> (ex |== P))"
definition
  temp_weakening :: "('a,'s2)ioa_temp => ('a,'s1)ioa_temp => ('s1 => 's2) => bool" where
  "temp_weakening Q P h = temp_strengthening (.~ Q) (.~ P) h"

definition
  state_strengthening :: "('a,'s2)step_pred => ('a,'s1)step_pred => ('s1 => 's2) => bool" where
  "state_strengthening Q P h = (!s t a.  Q (h(s),a,h(t)) --> P (s,a,t))"
definition
  state_weakening :: "('a,'s2)step_pred => ('a,'s1)step_pred => ('s1 => 's2) => bool" where
  "state_weakening Q P h = state_strengthening (.~Q) (.~P) h"

definition
  is_live_abstraction :: "('s1 => 's2) => ('a,'s1)live_ioa => ('a,'s2)live_ioa => bool" where
  "is_live_abstraction h CL AM =
     (is_abstraction h (fst CL) (fst AM) &
      temp_weakening (snd AM) (snd CL) h)"


axiomatization where
(* thm about ex2seq which is not provable by induction as ex2seq is not continous *)
ex2seq_abs_cex:
  "ex2seq (cex_abs h ex) = cex_absSeq h (ex2seq ex)"

axiomatization where
(* analog to the proved thm strength_Box - proof skipped as trivial *)
weak_Box:
"temp_weakening P Q h
 ==> temp_weakening ([] P) ([] Q) h"

axiomatization where
(* analog to the proved thm strength_Next - proof skipped as trivial *)
weak_Next:
"temp_weakening P Q h
 ==> temp_weakening (Next P) (Next Q) h"


subsection "cex_abs"

lemma cex_abs_UU: "cex_abs f (s,UU) = (f s, UU)"
  by (simp add: cex_abs_def)

lemma cex_abs_nil: "cex_abs f (s,nil) = (f s, nil)"
  by (simp add: cex_abs_def)

lemma cex_abs_cons: "cex_abs f (s,(a,t)>>ex) = (f s, (a,f t) >> (snd (cex_abs f (t,ex))))"
  by (simp add: cex_abs_def)

declare cex_abs_UU [simp] cex_abs_nil [simp] cex_abs_cons [simp]


subsection "lemmas"

lemma temp_weakening_def2: "temp_weakening Q P h = (! ex. (ex |== P) --> (cex_abs h ex |== Q))"
  apply (simp add: temp_weakening_def temp_strengthening_def NOT_def temp_sat_def satisfies_def)
  apply auto
  done

lemma state_weakening_def2: "state_weakening Q P h = (! s t a. P (s,a,t) --> Q (h(s),a,h(t)))"
  apply (simp add: state_weakening_def state_strengthening_def NOT_def)
  apply auto
  done


subsection "Abstraction Rules for Properties"

lemma exec_frag_abstraction [rule_format]:
 "[| is_abstraction h C A |] ==>
  !s. reachable C s & is_exec_frag C (s,xs)
  --> is_exec_frag A (cex_abs h (s,xs))"
apply (unfold cex_abs_def)
apply simp
apply (tactic {* pair_induct_tac @{context} "xs" [@{thm is_exec_frag_def}] 1 *})
txt {* main case *}
apply (auto dest: reachable.reachable_n simp add: is_abstraction_def)
done


lemma abs_is_weakening: "is_abstraction h C A ==> weakeningIOA A C h"
apply (simp add: weakeningIOA_def)
apply auto
apply (simp add: executions_def)
txt {* start state *}
apply (rule conjI)
apply (simp add: is_abstraction_def cex_abs_def)
txt {* is-execution-fragment *}
apply (erule exec_frag_abstraction)
apply (simp add: reachable.reachable_0)
done


lemma AbsRuleT1: "[|is_abstraction h C A; validIOA A Q; temp_strengthening Q P h |]
          ==> validIOA C P"
apply (drule abs_is_weakening)
apply (simp add: weakeningIOA_def validIOA_def temp_strengthening_def)
apply (auto simp add: split_paired_all)
done


(* FIX: Nach TLS.ML *)

lemma IMPLIES_temp_sat: "(ex |== P .--> Q) = ((ex |== P) --> (ex |== Q))"
  by (simp add: IMPLIES_def temp_sat_def satisfies_def)

lemma AND_temp_sat: "(ex |== P .& Q) = ((ex |== P) & (ex |== Q))"
  by (simp add: AND_def temp_sat_def satisfies_def)

lemma OR_temp_sat: "(ex |== P .| Q) = ((ex |== P) | (ex |== Q))"
  by (simp add: OR_def temp_sat_def satisfies_def)

lemma NOT_temp_sat: "(ex |== .~ P) = (~ (ex |== P))"
  by (simp add: NOT_def temp_sat_def satisfies_def)

declare IMPLIES_temp_sat [simp] AND_temp_sat [simp] OR_temp_sat [simp] NOT_temp_sat [simp]


lemma AbsRuleT2:
   "[|is_live_abstraction h (C,L) (A,M);
          validLIOA (A,M) Q;  temp_strengthening Q P h |]
          ==> validLIOA (C,L) P"
apply (unfold is_live_abstraction_def)
apply auto
apply (drule abs_is_weakening)
apply (simp add: weakeningIOA_def temp_weakening_def2 validLIOA_def validIOA_def temp_strengthening_def)
apply (auto simp add: split_paired_all)
done


lemma AbsRuleTImprove:
   "[|is_live_abstraction h (C,L) (A,M);
          validLIOA (A,M) (H1 .--> Q);  temp_strengthening Q P h;
          temp_weakening H1 H2 h; validLIOA (C,L) H2 |]
          ==> validLIOA (C,L) P"
apply (unfold is_live_abstraction_def)
apply auto
apply (drule abs_is_weakening)
apply (simp add: weakeningIOA_def temp_weakening_def2 validLIOA_def validIOA_def temp_strengthening_def)
apply (auto simp add: split_paired_all)
done


subsection "Correctness of safe abstraction"

lemma abstraction_is_ref_map:
"is_abstraction h C A ==> is_ref_map h C A"
apply (unfold is_abstraction_def is_ref_map_def)
apply auto
apply (rule_tac x = "(a,h t) >>nil" in exI)
apply (simp add: move_def)
done


lemma abs_safety: "[| inp(C)=inp(A); out(C)=out(A);
                   is_abstraction h C A |]
                ==> C =<| A"
apply (simp add: ioa_implements_def)
apply (rule trace_inclusion)
apply (simp (no_asm) add: externals_def)
apply (auto)[1]
apply (erule abstraction_is_ref_map)
done


subsection "Correctness of life abstraction"

(* Reduces to Filter (Map fst x) = Filter (Map fst (Map (%(a,t). (a,x)) x),
   that is to special Map Lemma *)
lemma traces_coincide_abs:
  "ext C = ext A
         ==> mk_trace C$xs = mk_trace A$(snd (cex_abs f (s,xs)))"
apply (unfold cex_abs_def mk_trace_def filter_act_def)
apply simp
apply (tactic {* pair_induct_tac @{context} "xs" [] 1 *})
done


(* Does not work with abstraction_is_ref_map as proof of abs_safety, because
   is_live_abstraction includes temp_strengthening which is necessarily based
   on cex_abs and not on corresp_ex. Thus, the proof is redoone in a more specific
   way for cex_abs *)
lemma abs_liveness: "[| inp(C)=inp(A); out(C)=out(A);
                   is_live_abstraction h (C,M) (A,L) |]
                ==> live_implements (C,M) (A,L)"
apply (simp add: is_live_abstraction_def live_implements_def livetraces_def liveexecutions_def)
apply auto
apply (rule_tac x = "cex_abs h ex" in exI)
apply auto
  (* Traces coincide *)
  apply (tactic {* pair_tac @{context} "ex" 1 *})
  apply (rule traces_coincide_abs)
  apply (simp (no_asm) add: externals_def)
  apply (auto)[1]

  (* cex_abs is execution *)
  apply (tactic {* pair_tac @{context} "ex" 1 *})
  apply (simp add: executions_def)
  (* start state *)
  apply (rule conjI)
  apply (simp add: is_abstraction_def cex_abs_def)
  (* is-execution-fragment *)
  apply (erule exec_frag_abstraction)
  apply (simp add: reachable.reachable_0)

 (* Liveness *)
apply (simp add: temp_weakening_def2)
 apply (tactic {* pair_tac @{context} "ex" 1 *})
done

(* FIX: NAch Traces.ML bringen *)

lemma implements_trans:
"[| A =<| B; B =<| C|] ==> A =<| C"
by (auto simp add: ioa_implements_def)


subsection "Abstraction Rules for Automata"

lemma AbsRuleA1: "[| inp(C)=inp(A); out(C)=out(A);
                   inp(Q)=inp(P); out(Q)=out(P);
                   is_abstraction h1 C A;
                   A =<| Q ;
                   is_abstraction h2 Q P |]
                ==> C =<| P"
apply (drule abs_safety)
apply assumption+
apply (drule abs_safety)
apply assumption+
apply (erule implements_trans)
apply (erule implements_trans)
apply assumption
done


lemma AbsRuleA2: "!!LC. [| inp(C)=inp(A); out(C)=out(A);
                   inp(Q)=inp(P); out(Q)=out(P);
                   is_live_abstraction h1 (C,LC) (A,LA);
                   live_implements (A,LA) (Q,LQ) ;
                   is_live_abstraction h2 (Q,LQ) (P,LP) |]
                ==> live_implements (C,LC) (P,LP)"
apply (drule abs_liveness)
apply assumption+
apply (drule abs_liveness)
apply assumption+
apply (erule live_implements_trans)
apply (erule live_implements_trans)
apply assumption
done


declare split_paired_All [simp del]


subsection "Localizing Temporal Strengthenings and Weakenings"

lemma strength_AND:
"[| temp_strengthening P1 Q1 h;
          temp_strengthening P2 Q2 h |]
       ==> temp_strengthening (P1 .& P2) (Q1 .& Q2) h"
apply (unfold temp_strengthening_def)
apply auto
done

lemma strength_OR:
"[| temp_strengthening P1 Q1 h;
          temp_strengthening P2 Q2 h |]
       ==> temp_strengthening (P1 .| P2) (Q1 .| Q2) h"
apply (unfold temp_strengthening_def)
apply auto
done

lemma strength_NOT:
"[| temp_weakening P Q h |]
       ==> temp_strengthening (.~ P) (.~ Q) h"
apply (unfold temp_strengthening_def)
apply (simp add: temp_weakening_def2)
apply auto
done

lemma strength_IMPLIES:
"[| temp_weakening P1 Q1 h;
          temp_strengthening P2 Q2 h |]
       ==> temp_strengthening (P1 .--> P2) (Q1 .--> Q2) h"
apply (unfold temp_strengthening_def)
apply (simp add: temp_weakening_def2)
done


lemma weak_AND:
"[| temp_weakening P1 Q1 h;
          temp_weakening P2 Q2 h |]
       ==> temp_weakening (P1 .& P2) (Q1 .& Q2) h"
apply (simp add: temp_weakening_def2)
done

lemma weak_OR:
"[| temp_weakening P1 Q1 h;
          temp_weakening P2 Q2 h |]
       ==> temp_weakening (P1 .| P2) (Q1 .| Q2) h"
apply (simp add: temp_weakening_def2)
done

lemma weak_NOT:
"[| temp_strengthening P Q h |]
       ==> temp_weakening (.~ P) (.~ Q) h"
apply (unfold temp_strengthening_def)
apply (simp add: temp_weakening_def2)
apply auto
done

lemma weak_IMPLIES:
"[| temp_strengthening P1 Q1 h;
          temp_weakening P2 Q2 h |]
       ==> temp_weakening (P1 .--> P2) (Q1 .--> Q2) h"
apply (unfold temp_strengthening_def)
apply (simp add: temp_weakening_def2)
done


subsubsection {* Box *}

(* FIX: should be same as nil_is_Conc2 when all nils are turned to right side !! *)
lemma UU_is_Conc: "(UU = x @@ y) = (((x::'a Seq)= UU) | (x=nil & y=UU))"
apply (tactic {* Seq_case_simp_tac @{context} "x" 1 *})
done

lemma ex2seqConc [rule_format]:
"Finite s1 -->
  (! ex. (s~=nil & s~=UU & ex2seq ex = s1 @@ s) --> (? ex'. s = ex2seq ex'))"
apply (rule impI)
apply (tactic {* Seq_Finite_induct_tac @{context} 1 *})
apply blast
(* main case *)
apply clarify
apply (tactic {* pair_tac @{context} "ex" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "y" 1 *})
(* UU case *)
apply (simp add: nil_is_Conc)
(* nil case *)
apply (simp add: nil_is_Conc)
(* cons case *)
apply (tactic {* pair_tac @{context} "aa" 1 *})
apply auto
done

(* important property of ex2seq: can be shiftet, as defined "pointwise" *)

lemma ex2seq_tsuffix:
"tsuffix s (ex2seq ex) ==> ? ex'. s = (ex2seq ex')"
apply (unfold tsuffix_def suffix_def)
apply auto
apply (drule ex2seqConc)
apply auto
done


(* FIX: NAch Sequence.ML bringen *)

lemma Mapnil: "(Map f$s = nil) = (s=nil)"
apply (tactic {* Seq_case_simp_tac @{context} "s" 1 *})
done

lemma MapUU: "(Map f$s = UU) = (s=UU)"
apply (tactic {* Seq_case_simp_tac @{context} "s" 1 *})
done


(* important property of cex_absSeq: As it is a 1to1 correspondence,
  properties carry over *)

lemma cex_absSeq_tsuffix:
"tsuffix s t ==> tsuffix (cex_absSeq h s) (cex_absSeq h t)"
apply (unfold tsuffix_def suffix_def cex_absSeq_def)
apply auto
apply (simp add: Mapnil)
apply (simp add: MapUU)
apply (rule_tac x = "Map (% (s,a,t) . (h s,a, h t))$s1" in exI)
apply (simp add: Map2Finite MapConc)
done


lemma strength_Box:
"[| temp_strengthening P Q h |]
       ==> temp_strengthening ([] P) ([] Q) h"
apply (unfold temp_strengthening_def state_strengthening_def temp_sat_def satisfies_def Box_def)
apply clarify
apply (frule ex2seq_tsuffix)
apply clarify
apply (drule_tac h = "h" in cex_absSeq_tsuffix)
apply (simp add: ex2seq_abs_cex)
done


subsubsection {* Init *}

lemma strength_Init:
"[| state_strengthening P Q h |]
       ==> temp_strengthening (Init P) (Init Q) h"
apply (unfold temp_strengthening_def state_strengthening_def
  temp_sat_def satisfies_def Init_def unlift_def)
apply auto
apply (tactic {* pair_tac @{context} "ex" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "y" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
done


subsubsection {* Next *}

lemma TL_ex2seq_UU:
"(TL$(ex2seq (cex_abs h ex))=UU) = (TL$(ex2seq ex)=UU)"
apply (tactic {* pair_tac @{context} "ex" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "y" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "s" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
done

lemma TL_ex2seq_nil:
"(TL$(ex2seq (cex_abs h ex))=nil) = (TL$(ex2seq ex)=nil)"
apply (tactic {* pair_tac @{context} "ex" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "y" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "s" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
done

(* FIX: put to Sequence Lemmas *)
lemma MapTL: "Map f$(TL$s) = TL$(Map f$s)"
apply (tactic {* Seq_induct_tac @{context} "s" [] 1 *})
done

(* important property of cex_absSeq: As it is a 1to1 correspondence,
  properties carry over *)

lemma cex_absSeq_TL:
"cex_absSeq h (TL$s) = (TL$(cex_absSeq h s))"
apply (unfold cex_absSeq_def)
apply (simp add: MapTL)
done

(* important property of ex2seq: can be shiftet, as defined "pointwise" *)

lemma TLex2seq: "[| (snd ex)~=UU ; (snd ex)~=nil |] ==> (? ex'. TL$(ex2seq ex) = ex2seq ex')"
apply (tactic {* pair_tac @{context} "ex" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "y" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
apply auto
done


lemma ex2seqnilTL: "(TL$(ex2seq ex)~=nil) = ((snd ex)~=nil & (snd ex)~=UU)"
apply (tactic {* pair_tac @{context} "ex" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "y" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "s" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
done


lemma strength_Next:
"[| temp_strengthening P Q h |]
       ==> temp_strengthening (Next P) (Next Q) h"
apply (unfold temp_strengthening_def state_strengthening_def temp_sat_def satisfies_def Next_def)
apply simp
apply auto
apply (simp add: TL_ex2seq_nil TL_ex2seq_UU)
apply (simp add: TL_ex2seq_nil TL_ex2seq_UU)
apply (simp add: TL_ex2seq_nil TL_ex2seq_UU)
apply (simp add: TL_ex2seq_nil TL_ex2seq_UU)
(* cons case *)
apply (simp add: TL_ex2seq_nil TL_ex2seq_UU ex2seq_abs_cex cex_absSeq_TL [symmetric] ex2seqnilTL)
apply (erule conjE)
apply (drule TLex2seq)
apply assumption
apply auto
done


text {* Localizing Temporal Weakenings     - 2 *}

lemma weak_Init:
"[| state_weakening P Q h |]
       ==> temp_weakening (Init P) (Init Q) h"
apply (simp add: temp_weakening_def2 state_weakening_def2
  temp_sat_def satisfies_def Init_def unlift_def)
apply auto
apply (tactic {* pair_tac @{context} "ex" 1 *})
apply (tactic {* Seq_case_simp_tac @{context} "y" 1 *})
apply (tactic {* pair_tac @{context} "a" 1 *})
done


text {* Localizing Temproal Strengthenings - 3 *}

lemma strength_Diamond:
"[| temp_strengthening P Q h |]
       ==> temp_strengthening (<> P) (<> Q) h"
apply (unfold Diamond_def)
apply (rule strength_NOT)
apply (rule weak_Box)
apply (erule weak_NOT)
done

lemma strength_Leadsto:
"[| temp_weakening P1 P2 h;
          temp_strengthening Q1 Q2 h |]
       ==> temp_strengthening (P1 ~> Q1) (P2 ~> Q2) h"
apply (unfold Leadsto_def)
apply (rule strength_Box)
apply (erule strength_IMPLIES)
apply (erule strength_Diamond)
done


text {* Localizing Temporal Weakenings - 3 *}

lemma weak_Diamond:
"[| temp_weakening P Q h |]
       ==> temp_weakening (<> P) (<> Q) h"
apply (unfold Diamond_def)
apply (rule weak_NOT)
apply (rule strength_Box)
apply (erule strength_NOT)
done

lemma weak_Leadsto:
"[| temp_strengthening P1 P2 h;
          temp_weakening Q1 Q2 h |]
       ==> temp_weakening (P1 ~> Q1) (P2 ~> Q2) h"
apply (unfold Leadsto_def)
apply (rule weak_Box)
apply (erule weak_IMPLIES)
apply (erule weak_Diamond)
done

lemma weak_WF:
  " !!A. [| !! s. Enabled A acts (h s) ==> Enabled C acts s|]
    ==> temp_weakening (WF A acts) (WF C acts) h"
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
  " !!A. [| !! s. Enabled A acts (h s) ==> Enabled C acts s|]
    ==> temp_weakening (SF A acts) (SF C acts) h"
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

ML {*
fun abstraction_tac ctxt =
  let val (cs, ss) = local_clasimpset_of ctxt in
    SELECT_GOAL (auto_tac (cs addSIs @{thms weak_strength_lemmas},
        ss addsimps [@{thm state_strengthening_def}, @{thm state_weakening_def}]))
  end
*}

method_setup abstraction = {* Scan.succeed (SIMPLE_METHOD' o abstraction_tac) *} ""

use "ioa.ML"

end
