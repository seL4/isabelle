(*  Title:      HOL/Induct/Comb.thy
    Author:     Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

section \<open>Combinatory Logic example: the Church-Rosser Theorem\<close>

theory Comb imports Main begin

text \<open>
  Curiously, combinators do not include free variables.

  Example taken from @{cite camilleri92}.

HOL system proofs may be found in the HOL distribution at
   .../contrib/rule-induction/cl.ml
\<close>

subsection \<open>Definitions\<close>

text \<open>Datatype definition of combinators @{text S} and @{text K}.\<close>

datatype comb = K
              | S
              | Ap comb comb (infixl "##" 90)

notation (xsymbols)
  Ap  (infixl "\<bullet>" 90)


text \<open>
  Inductive definition of contractions, @{text "-1->"} and
  (multi-step) reductions, @{text "--->"}.
\<close>

inductive_set
  contract :: "(comb*comb) set"
  and contract_rel1 :: "[comb,comb] => bool"  (infixl "-1->" 50)
  where
    "x -1-> y == (x,y) \<in> contract"
   | K:     "K##x##y -1-> x"
   | S:     "S##x##y##z -1-> (x##z)##(y##z)"
   | Ap1:   "x-1->y ==> x##z -1-> y##z"
   | Ap2:   "x-1->y ==> z##x -1-> z##y"

abbreviation
  contract_rel :: "[comb,comb] => bool"   (infixl "--->" 50) where
  "x ---> y == (x,y) \<in> contract^*"

text \<open>
  Inductive definition of parallel contractions, @{text "=1=>"} and
  (multi-step) parallel reductions, @{text "===>"}.
\<close>

inductive_set
  parcontract :: "(comb*comb) set"
  and parcontract_rel1 :: "[comb,comb] => bool"  (infixl "=1=>" 50)
  where
    "x =1=> y == (x,y) \<in> parcontract"
  | refl:  "x =1=> x"
  | K:     "K##x##y =1=> x"
  | S:     "S##x##y##z =1=> (x##z)##(y##z)"
  | Ap:    "[| x=1=>y;  z=1=>w |] ==> x##z =1=> y##w"

abbreviation
  parcontract_rel :: "[comb,comb] => bool"   (infixl "===>" 50) where
  "x ===> y == (x,y) \<in> parcontract^*"

text \<open>
  Misc definitions.
\<close>

definition
  I :: comb where
  "I = S##K##K"

definition
  diamond   :: "('a * 'a)set => bool" where
    --\<open>confluence; Lambda/Commutation treats this more abstractly\<close>
  "diamond(r) = (\<forall>x y. (x,y) \<in> r --> 
                  (\<forall>y'. (x,y') \<in> r --> 
                    (\<exists>z. (y,z) \<in> r & (y',z) \<in> r)))"


subsection \<open>Reflexive/Transitive closure preserves Church-Rosser property\<close>

text\<open>So does the Transitive closure, with a similar proof\<close>

text\<open>Strip lemma.  
   The induction hypothesis covers all but the last diamond of the strip.\<close>
lemma diamond_strip_lemmaE [rule_format]: 
    "[| diamond(r);  (x,y) \<in> r^* |] ==>   
          \<forall>y'. (x,y') \<in> r --> (\<exists>z. (y',z) \<in> r^* & (y,z) \<in> r)"
apply (unfold diamond_def)
apply (erule rtrancl_induct)
apply (meson rtrancl_refl)
apply (meson rtrancl_trans r_into_rtrancl)
done

lemma diamond_rtrancl: "diamond(r) ==> diamond(r^*)"
apply (simp (no_asm_simp) add: diamond_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule rtrancl_induct, blast)
apply (meson rtrancl_trans r_into_rtrancl diamond_strip_lemmaE)
done


subsection \<open>Non-contraction results\<close>

text \<open>Derive a case for each combinator constructor.\<close>

inductive_cases
      K_contractE [elim!]: "K -1-> r"
  and S_contractE [elim!]: "S -1-> r"
  and Ap_contractE [elim!]: "p##q -1-> r"

declare contract.K [intro!] contract.S [intro!]
declare contract.Ap1 [intro] contract.Ap2 [intro]

lemma I_contract_E [elim!]: "I -1-> z ==> P"
by (unfold I_def, blast)

lemma K1_contractD [elim!]: "K##x -1-> z ==> (\<exists>x'. z = K##x' & x -1-> x')"
by blast

lemma Ap_reduce1 [intro]: "x ---> y ==> x##z ---> y##z"
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_trans)+
done

lemma Ap_reduce2 [intro]: "x ---> y ==> z##x ---> z##y"
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_trans)+
done

text \<open>Counterexample to the diamond property for @{term "x -1-> y"}\<close>

lemma not_diamond_contract: "~ diamond(contract)"
by (unfold diamond_def, metis S_contractE contract.K) 


subsection \<open>Results about Parallel Contraction\<close>

text \<open>Derive a case for each combinator constructor.\<close>

inductive_cases
      K_parcontractE [elim!]: "K =1=> r"
  and S_parcontractE [elim!]: "S =1=> r"
  and Ap_parcontractE [elim!]: "p##q =1=> r"

declare parcontract.intros [intro]

(*** Basic properties of parallel contraction ***)

subsection \<open>Basic properties of parallel contraction\<close>

lemma K1_parcontractD [dest!]: "K##x =1=> z ==> (\<exists>x'. z = K##x' & x =1=> x')"
by blast

lemma S1_parcontractD [dest!]: "S##x =1=> z ==> (\<exists>x'. z = S##x' & x =1=> x')"
by blast

lemma S2_parcontractD [dest!]:
     "S##x##y =1=> z ==> (\<exists>x' y'. z = S##x'##y' & x =1=> x' & y =1=> y')"
by blast

text\<open>The rules above are not essential but make proofs much faster\<close>

text\<open>Church-Rosser property for parallel contraction\<close>
lemma diamond_parcontract: "diamond parcontract"
apply (unfold diamond_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule parcontract.induct, fast+)
done

text \<open>
  \medskip Equivalence of @{prop "p ---> q"} and @{prop "p ===> q"}.
\<close>

lemma contract_subset_parcontract: "contract <= parcontract"
by (auto, erule contract.induct, blast+)

text\<open>Reductions: simply throw together reflexivity, transitivity and
  the one-step reductions\<close>

declare r_into_rtrancl [intro]  rtrancl_trans [intro]

(*Example only: not used*)
lemma reduce_I: "I##x ---> x"
by (unfold I_def, blast)

lemma parcontract_subset_reduce: "parcontract <= contract^*"
by (auto, erule parcontract.induct, blast+)

lemma reduce_eq_parreduce: "contract^* = parcontract^*"
by (metis contract_subset_parcontract parcontract_subset_reduce rtrancl_subset)

theorem diamond_reduce: "diamond(contract^*)"
by (simp add: reduce_eq_parreduce diamond_rtrancl diamond_parcontract)

end
