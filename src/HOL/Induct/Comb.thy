(*  Title:      HOL/Induct/Comb.thy
    Author:     Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

section \<open>Combinatory Logic example: the Church-Rosser Theorem\<close>

theory Comb
imports Main
begin

text \<open>
  Curiously, combinators do not include free variables.

  Example taken from @{cite camilleri92}.
\<close>


subsection \<open>Definitions\<close>

text \<open>Datatype definition of combinators \<open>S\<close> and \<open>K\<close>.\<close>

datatype comb = K
              | S
              | Ap comb comb (infixl "\<bullet>" 90)

text \<open>
  Inductive definition of contractions, \<open>\<rightarrow>\<^sup>1\<close> and
  (multi-step) reductions, \<open>\<rightarrow>\<close>.
\<close>

inductive_set contract :: "(comb*comb) set"
  and contract_rel1 :: "[comb,comb] \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sup>1" 50)
where
  "x \<rightarrow>\<^sup>1 y == (x,y) \<in> contract"
| K:     "K\<bullet>x\<bullet>y \<rightarrow>\<^sup>1 x"
| S:     "S\<bullet>x\<bullet>y\<bullet>z \<rightarrow>\<^sup>1 (x\<bullet>z)\<bullet>(y\<bullet>z)"
| Ap1:   "x\<rightarrow>\<^sup>1y \<Longrightarrow> x\<bullet>z \<rightarrow>\<^sup>1 y\<bullet>z"
| Ap2:   "x\<rightarrow>\<^sup>1y \<Longrightarrow> z\<bullet>x \<rightarrow>\<^sup>1 z\<bullet>y"

abbreviation
  contract_rel :: "[comb,comb] \<Rightarrow> bool"   (infixl "\<rightarrow>" 50) where
  "x \<rightarrow> y == (x,y) \<in> contract\<^sup>*"

text \<open>
  Inductive definition of parallel contractions, \<open>\<Rrightarrow>\<^sup>1\<close> and
  (multi-step) parallel reductions, \<open>\<Rrightarrow>\<close>.
\<close>

inductive_set parcontract :: "(comb*comb) set"
  and parcontract_rel1 :: "[comb,comb] \<Rightarrow> bool"  (infixl "\<Rrightarrow>\<^sup>1" 50)
where
  "x \<Rrightarrow>\<^sup>1 y == (x,y) \<in> parcontract"
| refl:  "x \<Rrightarrow>\<^sup>1 x"
| K:     "K\<bullet>x\<bullet>y \<Rrightarrow>\<^sup>1 x"
| S:     "S\<bullet>x\<bullet>y\<bullet>z \<Rrightarrow>\<^sup>1 (x\<bullet>z)\<bullet>(y\<bullet>z)"
| Ap:    "[| x\<Rrightarrow>\<^sup>1y;  z\<Rrightarrow>\<^sup>1w |] ==> x\<bullet>z \<Rrightarrow>\<^sup>1 y\<bullet>w"

abbreviation
  parcontract_rel :: "[comb,comb] \<Rightarrow> bool"   (infixl "\<Rrightarrow>" 50) where
  "x \<Rrightarrow> y == (x,y) \<in> parcontract\<^sup>*"

text \<open>
  Misc definitions.
\<close>

definition
  I :: comb where
  "I = S\<bullet>K\<bullet>K"

definition
  diamond   :: "('a * 'a)set \<Rightarrow> bool" where
    \<comment> \<open>confluence; Lambda/Commutation treats this more abstractly\<close>
  "diamond(r) = (\<forall>x y. (x,y) \<in> r --> 
                  (\<forall>y'. (x,y') \<in> r --> 
                    (\<exists>z. (y,z) \<in> r & (y',z) \<in> r)))"


subsection \<open>Reflexive/Transitive closure preserves Church-Rosser property\<close>

text\<open>So does the Transitive closure, with a similar proof\<close>

text\<open>Strip lemma.  
   The induction hypothesis covers all but the last diamond of the strip.\<close>
lemma diamond_strip_lemmaE [rule_format]: 
    "[| diamond(r);  (x,y) \<in> r\<^sup>* |] ==>   
          \<forall>y'. (x,y') \<in> r --> (\<exists>z. (y',z) \<in> r\<^sup>* & (y,z) \<in> r)"
apply (unfold diamond_def)
apply (erule rtrancl_induct)
apply (meson rtrancl_refl)
apply (meson rtrancl_trans r_into_rtrancl)
done

lemma diamond_rtrancl: "diamond(r) \<Longrightarrow> diamond(r\<^sup>*)"
apply (simp (no_asm_simp) add: diamond_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule rtrancl_induct, blast)
apply (meson rtrancl_trans r_into_rtrancl diamond_strip_lemmaE)
done


subsection \<open>Non-contraction results\<close>

text \<open>Derive a case for each combinator constructor.\<close>

inductive_cases
      K_contractE [elim!]: "K \<rightarrow>\<^sup>1 r"
  and S_contractE [elim!]: "S \<rightarrow>\<^sup>1 r"
  and Ap_contractE [elim!]: "p\<bullet>q \<rightarrow>\<^sup>1 r"

declare contract.K [intro!] contract.S [intro!]
declare contract.Ap1 [intro] contract.Ap2 [intro]

lemma I_contract_E [elim!]: "I \<rightarrow>\<^sup>1 z \<Longrightarrow> P"
by (unfold I_def, blast)

lemma K1_contractD [elim!]: "K\<bullet>x \<rightarrow>\<^sup>1 z \<Longrightarrow> (\<exists>x'. z = K\<bullet>x' & x \<rightarrow>\<^sup>1 x')"
by blast

lemma Ap_reduce1 [intro]: "x \<rightarrow> y \<Longrightarrow> x\<bullet>z \<rightarrow> y\<bullet>z"
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_trans)+
done

lemma Ap_reduce2 [intro]: "x \<rightarrow> y \<Longrightarrow> z\<bullet>x \<rightarrow> z\<bullet>y"
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_trans)+
done

text \<open>Counterexample to the diamond property for \<^term>\<open>x \<rightarrow>\<^sup>1 y\<close>\<close>

lemma not_diamond_contract: "~ diamond(contract)"
by (unfold diamond_def, metis S_contractE contract.K) 


subsection \<open>Results about Parallel Contraction\<close>

text \<open>Derive a case for each combinator constructor.\<close>

inductive_cases
      K_parcontractE [elim!]: "K \<Rrightarrow>\<^sup>1 r"
  and S_parcontractE [elim!]: "S \<Rrightarrow>\<^sup>1 r"
  and Ap_parcontractE [elim!]: "p\<bullet>q \<Rrightarrow>\<^sup>1 r"

declare parcontract.intros [intro]

(*** Basic properties of parallel contraction ***)

subsection \<open>Basic properties of parallel contraction\<close>

lemma K1_parcontractD [dest!]: "K\<bullet>x \<Rrightarrow>\<^sup>1 z \<Longrightarrow> (\<exists>x'. z = K\<bullet>x' & x \<Rrightarrow>\<^sup>1 x')"
by blast

lemma S1_parcontractD [dest!]: "S\<bullet>x \<Rrightarrow>\<^sup>1 z \<Longrightarrow> (\<exists>x'. z = S\<bullet>x' & x \<Rrightarrow>\<^sup>1 x')"
by blast

lemma S2_parcontractD [dest!]:
     "S\<bullet>x\<bullet>y \<Rrightarrow>\<^sup>1 z \<Longrightarrow> (\<exists>x' y'. z = S\<bullet>x'\<bullet>y' & x \<Rrightarrow>\<^sup>1 x' & y \<Rrightarrow>\<^sup>1 y')"
by blast

text\<open>The rules above are not essential but make proofs much faster\<close>

text\<open>Church-Rosser property for parallel contraction\<close>
lemma diamond_parcontract: "diamond parcontract"
apply (unfold diamond_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule parcontract.induct, fast+)
done

text \<open>
  \<^medskip>
  Equivalence of \<^prop>\<open>p \<rightarrow> q\<close> and \<^prop>\<open>p \<Rrightarrow> q\<close>.
\<close>

lemma contract_subset_parcontract: "contract \<subseteq> parcontract"
by (auto, erule contract.induct, blast+)

text\<open>Reductions: simply throw together reflexivity, transitivity and
  the one-step reductions\<close>

declare r_into_rtrancl [intro]  rtrancl_trans [intro]

(*Example only: not used*)
lemma reduce_I: "I\<bullet>x \<rightarrow> x"
by (unfold I_def, blast)

lemma parcontract_subset_reduce: "parcontract \<subseteq> contract\<^sup>*"
by (auto, erule parcontract.induct, blast+)

lemma reduce_eq_parreduce: "contract\<^sup>* = parcontract\<^sup>*"
by (metis contract_subset_parcontract parcontract_subset_reduce rtrancl_subset)

theorem diamond_reduce: "diamond(contract\<^sup>*)"
by (simp add: reduce_eq_parreduce diamond_rtrancl diamond_parcontract)

end
