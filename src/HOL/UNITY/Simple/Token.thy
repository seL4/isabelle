(*  Title:      HOL/UNITY/Simple/Token.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)


header {*The Token Ring*}

theory Token
imports "../WFair"

begin

text{*From Misra, "A Logic for Concurrent Programming" (1994), sections 5.2 and 13.2.*}

subsection{*Definitions*}

datatype pstate = Hungry | Eating | Thinking
    --{*process states*}

record state =
  token :: "nat"
  proc  :: "nat => pstate"


definition HasTok :: "nat => state set" where
    "HasTok i == {s. token s = i}"

definition H :: "nat => state set" where
    "H i == {s. proc s i = Hungry}"

definition E :: "nat => state set" where
    "E i == {s. proc s i = Eating}"

definition T :: "nat => state set" where
    "T i == {s. proc s i = Thinking}"


locale Token =
  fixes N and F and nodeOrder and "next"   
  defines nodeOrder_def:
       "nodeOrder j == measure(%i. ((j+N)-i) mod N) \<inter> {..<N} \<times> {..<N}"
      and next_def:
       "next i == (Suc i) mod N"
  assumes N_positive [iff]: "0<N"
      and TR2:  "F \<in> (T i) co (T i \<union> H i)"
      and TR3:  "F \<in> (H i) co (H i \<union> E i)"
      and TR4:  "F \<in> (H i - HasTok i) co (H i)"
      and TR5:  "F \<in> (HasTok i) co (HasTok i \<union> -(E i))"
      and TR6:  "F \<in> (H i \<inter> HasTok i) leadsTo (E i)"
      and TR7:  "F \<in> (HasTok i) leadsTo (HasTok (next i))"


lemma HasToK_partition: "[| s \<in> HasTok i; s \<in> HasTok j |] ==> i=j"
by (unfold HasTok_def, auto)

lemma not_E_eq: "(s \<notin> E i) = (s \<in> H i | s \<in> T i)"
apply (simp add: H_def E_def T_def)
apply (cases "proc s i", auto)
done

lemma (in Token) token_stable: "F \<in> stable (-(E i) \<union> (HasTok i))"
apply (unfold stable_def)
apply (rule constrains_weaken)
apply (rule constrains_Un [OF constrains_Un [OF TR2 TR4] TR5])
apply (auto simp add: not_E_eq)
apply (simp_all add: H_def E_def T_def)
done


subsection{*Progress under Weak Fairness*}

lemma (in Token) wf_nodeOrder: "wf(nodeOrder j)"
apply (unfold nodeOrder_def)
apply (rule wf_measure [THEN wf_subset], blast)
done

lemma (in Token) nodeOrder_eq: 
     "[| i<N; j<N |] ==> ((next i, i) \<in> nodeOrder j) = (i \<noteq> j)"
apply (unfold nodeOrder_def next_def)
apply (auto simp add: mod_Suc mod_geq)
apply (auto split add: nat_diff_split simp add: linorder_neq_iff mod_geq)
done

text{*From "A Logic for Concurrent Programming", but not used in Chapter 4.
  Note the use of @{text cases}.  Reasoning about leadsTo takes practice!*}
lemma (in Token) TR7_nodeOrder:
     "[| i<N; j<N |] ==>    
      F \<in> (HasTok i) leadsTo ({s. (token s, i) \<in> nodeOrder j} \<union> HasTok j)"
apply (cases "i=j")
apply (blast intro: subset_imp_leadsTo)
apply (rule TR7 [THEN leadsTo_weaken_R])
apply (auto simp add: HasTok_def nodeOrder_eq)
done


text{*Chapter 4 variant, the one actually used below.*}
lemma (in Token) TR7_aux: "[| i<N; j<N; i\<noteq>j |]     
      ==> F \<in> (HasTok i) leadsTo {s. (token s, i) \<in> nodeOrder j}"
apply (rule TR7 [THEN leadsTo_weaken_R])
apply (auto simp add: HasTok_def nodeOrder_eq)
done

lemma (in Token) token_lemma:
     "({s. token s < N} \<inter> token -` {m}) = (if m<N then token -` {m} else {})"
by auto


text{*Misra's TR9: the token reaches an arbitrary node*}
lemma  (in Token) leadsTo_j: "j<N ==> F \<in> {s. token s < N} leadsTo (HasTok j)"
apply (rule leadsTo_weaken_R)
apply (rule_tac I = "-{j}" and f = token and B = "{}" 
       in wf_nodeOrder [THEN bounded_induct])
apply (simp_all (no_asm_simp) add: token_lemma vimage_Diff HasTok_def)
 prefer 2 apply blast
apply clarify
apply (rule TR7_aux [THEN leadsTo_weaken])
apply (auto simp add: HasTok_def nodeOrder_def)
done

text{*Misra's TR8: a hungry process eventually eats*}
lemma (in Token) token_progress:
     "j<N ==> F \<in> ({s. token s < N} \<inter> H j) leadsTo (E j)"
apply (rule leadsTo_cancel1 [THEN leadsTo_Un_duplicate])
apply (rule_tac [2] TR6)
apply (rule psp [OF leadsTo_j TR3, THEN leadsTo_weaken], blast+)
done


end
