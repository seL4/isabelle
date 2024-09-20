(*  Title:      HOL/Induct/Comb.thy
    Author:     Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

section \<open>Combinatory Logic example: the Church-Rosser Theorem\<close>

theory Comb
imports Main
begin

text \<open>
  Combinator terms do not have free variables.
  Example taken from \<^cite>\<open>camilleri92\<close>.
\<close>

subsection \<open>Definitions\<close>

text \<open>Datatype definition of combinators \<open>S\<close> and \<open>K\<close>.\<close>

datatype comb = K
              | S
              | Ap comb comb (infixl \<open>\<bullet>\<close> 90)

text \<open>
  Inductive definition of contractions, \<open>\<rightarrow>\<^sup>1\<close> and
  (multi-step) reductions, \<open>\<rightarrow>\<close>.
\<close>

inductive contract1 :: "[comb,comb] \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sup>1\<close> 50)
  where
    K:     "K\<bullet>x\<bullet>y \<rightarrow>\<^sup>1 x"
  | S:     "S\<bullet>x\<bullet>y\<bullet>z \<rightarrow>\<^sup>1 (x\<bullet>z)\<bullet>(y\<bullet>z)"
  | Ap1:   "x \<rightarrow>\<^sup>1 y \<Longrightarrow> x\<bullet>z \<rightarrow>\<^sup>1 y\<bullet>z"
  | Ap2:   "x \<rightarrow>\<^sup>1 y \<Longrightarrow> z\<bullet>x \<rightarrow>\<^sup>1 z\<bullet>y"

abbreviation
  contract :: "[comb,comb] \<Rightarrow> bool"   (infixl \<open>\<rightarrow>\<close> 50) where
  "contract \<equiv> contract1\<^sup>*\<^sup>*"

text \<open>
  Inductive definition of parallel contractions, \<open>\<Rrightarrow>\<^sup>1\<close> and
  (multi-step) parallel reductions, \<open>\<Rrightarrow>\<close>.
\<close>

inductive parcontract1 :: "[comb,comb] \<Rightarrow> bool"  (infixl \<open>\<Rrightarrow>\<^sup>1\<close> 50)
  where
    refl:  "x \<Rrightarrow>\<^sup>1 x"
  | K:     "K\<bullet>x\<bullet>y \<Rrightarrow>\<^sup>1 x"
  | S:     "S\<bullet>x\<bullet>y\<bullet>z \<Rrightarrow>\<^sup>1 (x\<bullet>z)\<bullet>(y\<bullet>z)"
  | Ap:    "\<lbrakk>x \<Rrightarrow>\<^sup>1 y; z \<Rrightarrow>\<^sup>1 w\<rbrakk> \<Longrightarrow> x\<bullet>z \<Rrightarrow>\<^sup>1 y\<bullet>w"

abbreviation
  parcontract :: "[comb,comb] \<Rightarrow> bool"   (infixl \<open>\<Rrightarrow>\<close> 50) where
  "parcontract \<equiv> parcontract1\<^sup>*\<^sup>*"

text \<open>
  Misc definitions.
\<close>

definition
  I :: comb where
  "I \<equiv> S\<bullet>K\<bullet>K"

definition
  diamond   :: "([comb,comb] \<Rightarrow> bool) \<Rightarrow> bool" where
    \<comment> \<open>confluence; Lambda/Commutation treats this more abstractly\<close>
  "diamond r \<equiv> \<forall>x y. r x y \<longrightarrow>
                  (\<forall>y'. r x y' \<longrightarrow> 
                    (\<exists>z. r y z \<and> r y' z))"


subsection \<open>Reflexive/Transitive closure preserves Church-Rosser property\<close>

text\<open>Remark: So does the Transitive closure, with a similar proof\<close>

text\<open>Strip lemma.  
   The induction hypothesis covers all but the last diamond of the strip.\<close>
lemma strip_lemma [rule_format]: 
  assumes "diamond r" and r: "r\<^sup>*\<^sup>* x y" "r x y'"
  shows "\<exists>z. r\<^sup>*\<^sup>* y' z \<and> r y z"
  using r
proof (induction rule: rtranclp_induct)
  case base
  then show ?case
    by blast
next
  case (step y z)
  then show ?case
    using \<open>diamond r\<close> unfolding diamond_def
    by (metis rtranclp.rtrancl_into_rtrancl)
qed

proposition diamond_rtrancl:
  assumes "diamond r" 
  shows "diamond(r\<^sup>*\<^sup>*)"
  unfolding diamond_def
proof (intro strip)
  fix x y y'
  assume "r\<^sup>*\<^sup>* x y" "r\<^sup>*\<^sup>* x y'"
  then show "\<exists>z. r\<^sup>*\<^sup>* y z \<and> r\<^sup>*\<^sup>* y' z"
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case
      by blast
  next
    case (step y z)
    then show ?case
      by (meson assms strip_lemma rtranclp.rtrancl_into_rtrancl)
  qed
qed


subsection \<open>Non-contraction results\<close>

text \<open>Derive a case for each combinator constructor.\<close>

inductive_cases
  K_contractE [elim!]: "K \<rightarrow>\<^sup>1 r"
  and S_contractE [elim!]: "S \<rightarrow>\<^sup>1 r"
  and Ap_contractE [elim!]: "p\<bullet>q \<rightarrow>\<^sup>1 r"

declare contract1.K [intro!] contract1.S [intro!]
declare contract1.Ap1 [intro] contract1.Ap2 [intro]

lemma I_contract_E [iff]: "\<not> I \<rightarrow>\<^sup>1 z"
  unfolding I_def by blast

lemma K1_contractD [elim!]: "K\<bullet>x \<rightarrow>\<^sup>1 z \<Longrightarrow> (\<exists>x'. z = K\<bullet>x' \<and> x \<rightarrow>\<^sup>1 x')"
  by blast

lemma Ap_reduce1 [intro]: "x \<rightarrow> y \<Longrightarrow> x\<bullet>z \<rightarrow> y\<bullet>z"
  by (induction rule: rtranclp_induct; blast intro: rtranclp_trans)

lemma Ap_reduce2 [intro]: "x \<rightarrow> y \<Longrightarrow> z\<bullet>x \<rightarrow> z\<bullet>y"
  by (induction rule: rtranclp_induct; blast intro: rtranclp_trans)

text \<open>Counterexample to the diamond property for \<^term>\<open>x \<rightarrow>\<^sup>1 y\<close>\<close>

lemma not_diamond_contract: "\<not> diamond(contract1)"
  unfolding diamond_def by (metis S_contractE contract1.K) 


subsection \<open>Results about Parallel Contraction\<close>

text \<open>Derive a case for each combinator constructor.\<close>

inductive_cases
      K_parcontractE [elim!]: "K \<Rrightarrow>\<^sup>1 r"
  and S_parcontractE [elim!]: "S \<Rrightarrow>\<^sup>1 r"
  and Ap_parcontractE [elim!]: "p\<bullet>q \<Rrightarrow>\<^sup>1 r"

declare parcontract1.intros [intro]

subsection \<open>Basic properties of parallel contraction\<close>
text\<open>The rules below are not essential but make proofs much faster\<close>

lemma K1_parcontractD [dest!]: "K\<bullet>x \<Rrightarrow>\<^sup>1 z \<Longrightarrow> (\<exists>x'. z = K\<bullet>x' \<and> x \<Rrightarrow>\<^sup>1 x')"
  by blast

lemma S1_parcontractD [dest!]: "S\<bullet>x \<Rrightarrow>\<^sup>1 z \<Longrightarrow> (\<exists>x'. z = S\<bullet>x' \<and> x \<Rrightarrow>\<^sup>1 x')"
  by blast

lemma S2_parcontractD [dest!]: "S\<bullet>x\<bullet>y \<Rrightarrow>\<^sup>1 z \<Longrightarrow> (\<exists>x' y'. z = S\<bullet>x'\<bullet>y' \<and> x \<Rrightarrow>\<^sup>1 x' \<and> y \<Rrightarrow>\<^sup>1 y')"
  by blast

text\<open>Church-Rosser property for parallel contraction\<close>
proposition diamond_parcontract: "diamond parcontract1"
proof -
  have "(\<exists>z. w \<Rrightarrow>\<^sup>1 z \<and> y' \<Rrightarrow>\<^sup>1 z)" if "y \<Rrightarrow>\<^sup>1 w" "y \<Rrightarrow>\<^sup>1 y'" for w y y'
    using that by (induction arbitrary: y' rule: parcontract1.induct) fast+
  then show ?thesis
    by (auto simp: diamond_def)
qed

subsection \<open>Equivalence of \<^prop>\<open>p \<rightarrow> q\<close> and \<^prop>\<open>p \<Rrightarrow> q\<close>.\<close>

lemma contract_imp_parcontract: "x \<rightarrow>\<^sup>1 y \<Longrightarrow> x \<Rrightarrow>\<^sup>1 y"
  by (induction rule: contract1.induct; blast)

text\<open>Reductions: simply throw together reflexivity, transitivity and
  the one-step reductions\<close>

proposition reduce_I: "I\<bullet>x \<rightarrow> x"
  unfolding I_def
  by (meson contract1.K contract1.S r_into_rtranclp rtranclp.rtrancl_into_rtrancl)

lemma parcontract_imp_reduce: "x \<Rrightarrow>\<^sup>1 y \<Longrightarrow> x \<rightarrow> y"
proof (induction rule: parcontract1.induct)
  case (Ap x y z w)
  then show ?case
    by (meson Ap_reduce1 Ap_reduce2 rtranclp_trans)
qed auto

lemma reduce_eq_parreduce: "x \<rightarrow> y  \<longleftrightarrow>  x \<Rrightarrow> y"
  by (metis contract_imp_parcontract parcontract_imp_reduce predicate2I rtranclp_subset)

theorem diamond_reduce: "diamond(contract)"
  using diamond_parcontract diamond_rtrancl reduce_eq_parreduce by presburger

end
