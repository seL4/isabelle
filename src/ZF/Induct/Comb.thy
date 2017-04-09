(*  Title:      ZF/Induct/Comb.thy
    Author:     Lawrence C Paulson
    Copyright   1994  University of Cambridge
*)

section \<open>Combinatory Logic example: the Church-Rosser Theorem\<close>

theory Comb
imports ZF
begin

text \<open>
  Curiously, combinators do not include free variables.

  Example taken from @{cite camilleri92}.
\<close>


subsection \<open>Definitions\<close>

text \<open>Datatype definition of combinators \<open>S\<close> and \<open>K\<close>.\<close>

consts comb :: i
datatype comb =
  K
| S
| app ("p \<in> comb", "q \<in> comb")  (infixl "\<bullet>" 90)

text \<open>
  Inductive definition of contractions, \<open>\<rightarrow>\<^sup>1\<close> and
  (multi-step) reductions, \<open>\<rightarrow>\<close>.
\<close>

consts contract  :: i
abbreviation contract_syntax :: "[i,i] \<Rightarrow> o"  (infixl "\<rightarrow>\<^sup>1" 50)
  where "p \<rightarrow>\<^sup>1 q \<equiv> <p,q> \<in> contract"

abbreviation contract_multi :: "[i,i] \<Rightarrow> o"  (infixl "\<rightarrow>" 50)
  where "p \<rightarrow> q \<equiv> <p,q> \<in> contract^*"

inductive
  domains "contract" \<subseteq> "comb \<times> comb"
  intros
    K:   "[| p \<in> comb;  q \<in> comb |] ==> K\<bullet>p\<bullet>q \<rightarrow>\<^sup>1 p"
    S:   "[| p \<in> comb;  q \<in> comb;  r \<in> comb |] ==> S\<bullet>p\<bullet>q\<bullet>r \<rightarrow>\<^sup>1 (p\<bullet>r)\<bullet>(q\<bullet>r)"
    Ap1: "[| p\<rightarrow>\<^sup>1q;  r \<in> comb |] ==> p\<bullet>r \<rightarrow>\<^sup>1 q\<bullet>r"
    Ap2: "[| p\<rightarrow>\<^sup>1q;  r \<in> comb |] ==> r\<bullet>p \<rightarrow>\<^sup>1 r\<bullet>q"
  type_intros comb.intros

text \<open>
  Inductive definition of parallel contractions, \<open>\<Rrightarrow>\<^sup>1\<close> and
  (multi-step) parallel reductions, \<open>\<Rrightarrow>\<close>.
\<close>

consts parcontract :: i

abbreviation parcontract_syntax :: "[i,i] => o"  (infixl "\<Rrightarrow>\<^sup>1" 50)
  where "p \<Rrightarrow>\<^sup>1 q == <p,q> \<in> parcontract"

abbreviation parcontract_multi :: "[i,i] => o"  (infixl "\<Rrightarrow>" 50)
  where "p \<Rrightarrow> q == <p,q> \<in> parcontract^+"

inductive
  domains "parcontract" \<subseteq> "comb \<times> comb"
  intros
    refl: "[| p \<in> comb |] ==> p \<Rrightarrow>\<^sup>1 p"
    K:    "[| p \<in> comb;  q \<in> comb |] ==> K\<bullet>p\<bullet>q \<Rrightarrow>\<^sup>1 p"
    S:    "[| p \<in> comb;  q \<in> comb;  r \<in> comb |] ==> S\<bullet>p\<bullet>q\<bullet>r \<Rrightarrow>\<^sup>1 (p\<bullet>r)\<bullet>(q\<bullet>r)"
    Ap:   "[| p\<Rrightarrow>\<^sup>1q;  r\<Rrightarrow>\<^sup>1s |] ==> p\<bullet>r \<Rrightarrow>\<^sup>1 q\<bullet>s"
  type_intros comb.intros

text \<open>
  Misc definitions.
\<close>

definition I :: i
  where "I \<equiv> S\<bullet>K\<bullet>K"

definition diamond :: "i \<Rightarrow> o"
  where "diamond(r) \<equiv>
    \<forall>x y. <x,y>\<in>r \<longrightarrow> (\<forall>y'. <x,y'>\<in>r \<longrightarrow> (\<exists>z. <y,z>\<in>r & <y',z> \<in> r))"


subsection \<open>Transitive closure preserves the Church-Rosser property\<close>

lemma diamond_strip_lemmaD [rule_format]:
  "[| diamond(r);  <x,y>:r^+ |] ==>
    \<forall>y'. <x,y'>:r \<longrightarrow> (\<exists>z. <y',z>: r^+ & <y,z>: r)"
  apply (unfold diamond_def)
  apply (erule trancl_induct)
   apply (blast intro: r_into_trancl)
  apply clarify
  apply (drule spec [THEN mp], assumption)
  apply (blast intro: r_into_trancl trans_trancl [THEN transD])
  done

lemma diamond_trancl: "diamond(r) ==> diamond(r^+)"
  apply (simp (no_asm_simp) add: diamond_def)
  apply (rule impI [THEN allI, THEN allI])
  apply (erule trancl_induct)
   apply auto
   apply (best intro: r_into_trancl trans_trancl [THEN transD]
     dest: diamond_strip_lemmaD)+
  done

inductive_cases Ap_E [elim!]: "p\<bullet>q \<in> comb"


subsection \<open>Results about Contraction\<close>

text \<open>
  For type checking: replaces @{term "a \<rightarrow>\<^sup>1 b"} by \<open>a, b \<in>
  comb\<close>.
\<close>

lemmas contract_combE2 = contract.dom_subset [THEN subsetD, THEN SigmaE2]
  and contract_combD1 = contract.dom_subset [THEN subsetD, THEN SigmaD1]
  and contract_combD2 = contract.dom_subset [THEN subsetD, THEN SigmaD2]

lemma field_contract_eq: "field(contract) = comb"
  by (blast intro: contract.K elim!: contract_combE2)

lemmas reduction_refl =
  field_contract_eq [THEN equalityD2, THEN subsetD, THEN rtrancl_refl]

lemmas rtrancl_into_rtrancl2 =
  r_into_rtrancl [THEN trans_rtrancl [THEN transD]]

declare reduction_refl [intro!] contract.K [intro!] contract.S [intro!]

lemmas reduction_rls =
  contract.K [THEN rtrancl_into_rtrancl2]
  contract.S [THEN rtrancl_into_rtrancl2]
  contract.Ap1 [THEN rtrancl_into_rtrancl2]
  contract.Ap2 [THEN rtrancl_into_rtrancl2]

lemma "p \<in> comb ==> I\<bullet>p \<rightarrow> p"
  \<comment> \<open>Example only: not used\<close>
  unfolding I_def by (blast intro: reduction_rls)

lemma comb_I: "I \<in> comb"
  unfolding I_def by blast


subsection \<open>Non-contraction results\<close>

text \<open>Derive a case for each combinator constructor.\<close>

inductive_cases K_contractE [elim!]: "K \<rightarrow>\<^sup>1 r"
  and S_contractE [elim!]: "S \<rightarrow>\<^sup>1 r"
  and Ap_contractE [elim!]: "p\<bullet>q \<rightarrow>\<^sup>1 r"

lemma I_contract_E: "I \<rightarrow>\<^sup>1 r ==> P"
  by (auto simp add: I_def)

lemma K1_contractD: "K\<bullet>p \<rightarrow>\<^sup>1 r ==> (\<exists>q. r = K\<bullet>q & p \<rightarrow>\<^sup>1 q)"
  by auto

lemma Ap_reduce1: "[| p \<rightarrow> q;  r \<in> comb |] ==> p\<bullet>r \<rightarrow> q\<bullet>r"
  apply (frule rtrancl_type [THEN subsetD, THEN SigmaD1])
  apply (drule field_contract_eq [THEN equalityD1, THEN subsetD])
  apply (erule rtrancl_induct)
   apply (blast intro: reduction_rls)
  apply (erule trans_rtrancl [THEN transD])
  apply (blast intro: contract_combD2 reduction_rls)
  done

lemma Ap_reduce2: "[| p \<rightarrow> q;  r \<in> comb |] ==> r\<bullet>p \<rightarrow> r\<bullet>q"
  apply (frule rtrancl_type [THEN subsetD, THEN SigmaD1])
  apply (drule field_contract_eq [THEN equalityD1, THEN subsetD])
  apply (erule rtrancl_induct)
   apply (blast intro: reduction_rls)
  apply (blast intro: trans_rtrancl [THEN transD] 
                      contract_combD2 reduction_rls)
  done

text \<open>Counterexample to the diamond property for \<open>\<rightarrow>\<^sup>1\<close>.\<close>

lemma KIII_contract1: "K\<bullet>I\<bullet>(I\<bullet>I) \<rightarrow>\<^sup>1 I"
  by (blast intro: comb_I)

lemma KIII_contract2: "K\<bullet>I\<bullet>(I\<bullet>I) \<rightarrow>\<^sup>1 K\<bullet>I\<bullet>((K\<bullet>I)\<bullet>(K\<bullet>I))"
  by (unfold I_def) (blast intro: contract.intros)

lemma KIII_contract3: "K\<bullet>I\<bullet>((K\<bullet>I)\<bullet>(K\<bullet>I)) \<rightarrow>\<^sup>1 I"
  by (blast intro: comb_I)

lemma not_diamond_contract: "\<not> diamond(contract)"
  apply (unfold diamond_def)
  apply (blast intro: KIII_contract1 KIII_contract2 KIII_contract3
    elim!: I_contract_E)
  done


subsection \<open>Results about Parallel Contraction\<close>

text \<open>For type checking: replaces \<open>a \<Rrightarrow>\<^sup>1 b\<close> by \<open>a, b
  \<in> comb\<close>\<close>
lemmas parcontract_combE2 = parcontract.dom_subset [THEN subsetD, THEN SigmaE2]
  and parcontract_combD1 = parcontract.dom_subset [THEN subsetD, THEN SigmaD1]
  and parcontract_combD2 = parcontract.dom_subset [THEN subsetD, THEN SigmaD2]

lemma field_parcontract_eq: "field(parcontract) = comb"
  by (blast intro: parcontract.K elim!: parcontract_combE2)

text \<open>Derive a case for each combinator constructor.\<close>
inductive_cases
      K_parcontractE [elim!]: "K \<Rrightarrow>\<^sup>1 r"
  and S_parcontractE [elim!]: "S \<Rrightarrow>\<^sup>1 r"
  and Ap_parcontractE [elim!]: "p\<bullet>q \<Rrightarrow>\<^sup>1 r"

declare parcontract.intros [intro]


subsection \<open>Basic properties of parallel contraction\<close>

lemma K1_parcontractD [dest!]:
    "K\<bullet>p \<Rrightarrow>\<^sup>1 r ==> (\<exists>p'. r = K\<bullet>p' & p \<Rrightarrow>\<^sup>1 p')"
  by auto

lemma S1_parcontractD [dest!]:
    "S\<bullet>p \<Rrightarrow>\<^sup>1 r ==> (\<exists>p'. r = S\<bullet>p' & p \<Rrightarrow>\<^sup>1 p')"
  by auto

lemma S2_parcontractD [dest!]:
    "S\<bullet>p\<bullet>q \<Rrightarrow>\<^sup>1 r ==> (\<exists>p' q'. r = S\<bullet>p'\<bullet>q' & p \<Rrightarrow>\<^sup>1 p' & q \<Rrightarrow>\<^sup>1 q')"
  by auto

lemma diamond_parcontract: "diamond(parcontract)"
  \<comment> \<open>Church-Rosser property for parallel contraction\<close>
  apply (unfold diamond_def)
  apply (rule impI [THEN allI, THEN allI])
  apply (erule parcontract.induct)
     apply (blast elim!: comb.free_elims  intro: parcontract_combD2)+
  done

text \<open>
  \medskip Equivalence of @{prop "p \<rightarrow> q"} and @{prop "p \<Rrightarrow> q"}.
\<close>

lemma contract_imp_parcontract: "p\<rightarrow>\<^sup>1q ==> p\<Rrightarrow>\<^sup>1q"
  by (induct set: contract) auto

lemma reduce_imp_parreduce: "p\<rightarrow>q ==> p\<Rrightarrow>q"
  apply (frule rtrancl_type [THEN subsetD, THEN SigmaD1])
  apply (drule field_contract_eq [THEN equalityD1, THEN subsetD])
  apply (erule rtrancl_induct)
   apply (blast intro: r_into_trancl)
  apply (blast intro: contract_imp_parcontract r_into_trancl
    trans_trancl [THEN transD])
  done

lemma parcontract_imp_reduce: "p\<Rrightarrow>\<^sup>1q ==> p\<rightarrow>q"
  apply (induct set: parcontract)
     apply (blast intro: reduction_rls)
    apply (blast intro: reduction_rls)
   apply (blast intro: reduction_rls)
  apply (blast intro: trans_rtrancl [THEN transD]
    Ap_reduce1 Ap_reduce2 parcontract_combD1 parcontract_combD2)
  done

lemma parreduce_imp_reduce: "p\<Rrightarrow>q ==> p\<rightarrow>q"
  apply (frule trancl_type [THEN subsetD, THEN SigmaD1])
  apply (drule field_parcontract_eq [THEN equalityD1, THEN subsetD])
  apply (erule trancl_induct, erule parcontract_imp_reduce)
  apply (erule trans_rtrancl [THEN transD])
  apply (erule parcontract_imp_reduce)
  done

lemma parreduce_iff_reduce: "p\<Rrightarrow>q \<longleftrightarrow> p\<rightarrow>q"
  by (blast intro: parreduce_imp_reduce reduce_imp_parreduce)

end
