(*  Title:      HOL/Induct/Comb.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

header {* Combinatory Logic example: the Church-Rosser Theorem *}

theory Comb = Main:

text {*
  Curiously, combinators do not include free variables.

  Example taken from \cite{camilleri-melham}.

HOL system proofs may be found in the HOL distribution at
   .../contrib/rule-induction/cl.ml
*}

subsection {* Definitions *}

text {* Datatype definition of combinators @{text S} and @{text K}. *}

datatype comb = K
              | S
              | "##" comb comb (infixl 90)

text {*
  Inductive definition of contractions, @{text "-1->"} and
  (multi-step) reductions, @{text "--->"}.
*}

consts
  contract  :: "(comb*comb) set"
  "-1->"    :: "[comb,comb] => bool"   (infixl 50)
  "--->"    :: "[comb,comb] => bool"   (infixl 50)

translations
  "x -1-> y" == "(x,y) \<in> contract"
  "x ---> y" == "(x,y) \<in> contract^*"

inductive contract
  intros
    K:     "K##x##y -1-> x"
    S:     "S##x##y##z -1-> (x##z)##(y##z)"
    Ap1:   "x-1->y ==> x##z -1-> y##z"
    Ap2:   "x-1->y ==> z##x -1-> z##y"

text {*
  Inductive definition of parallel contractions, @{text "=1=>"} and
  (multi-step) parallel reductions, @{text "===>"}.
*}

consts
  parcontract :: "(comb*comb) set"
  "=1=>"      :: "[comb,comb] => bool"   (infixl 50)
  "===>"      :: "[comb,comb] => bool"   (infixl 50)

translations
  "x =1=> y" == "(x,y) \<in> parcontract"
  "x ===> y" == "(x,y) \<in> parcontract^*"

inductive parcontract
  intros
    refl:  "x =1=> x"
    K:     "K##x##y =1=> x"
    S:     "S##x##y##z =1=> (x##z)##(y##z)"
    Ap:    "[| x=1=>y;  z=1=>w |] ==> x##z =1=> y##w"

text {*
  Misc definitions.
*}

constdefs
  I :: comb
  "I == S##K##K"

  diamond   :: "('a * 'a)set => bool"	
    --{*confluence; Lambda/Commutation treats this more abstractly*}
  "diamond(r) == \<forall>x y. (x,y) \<in> r --> 
                  (\<forall>y'. (x,y') \<in> r --> 
                    (\<exists>z. (y,z) \<in> r & (y',z) \<in> r))"


subsection {*Reflexive/Transitive closure preserves Church-Rosser property*}

text{*So does the Transitive closure, with a similar proof*}

text{*Strip lemma.  
   The induction hypothesis covers all but the last diamond of the strip.*}
lemma diamond_strip_lemmaE [rule_format]: 
    "[| diamond(r);  (x,y) \<in> r^* |] ==>   
          \<forall>y'. (x,y') \<in> r --> (\<exists>z. (y',z) \<in> r^* & (y,z) \<in> r)"
apply (unfold diamond_def)
apply (erule rtrancl_induct, blast, clarify)
apply (drule spec, drule mp, assumption)
apply (blast intro: rtrancl_trans [OF _ r_into_rtrancl])
done

lemma diamond_rtrancl: "diamond(r) ==> diamond(r^*)"
apply (simp (no_asm_simp) add: diamond_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule rtrancl_induct, blast)
apply (best intro: rtrancl_trans [OF _ r_into_rtrancl] 
            elim: diamond_strip_lemmaE [THEN exE])
done


subsection {* Non-contraction results *}

text {* Derive a case for each combinator constructor. *}

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

(** Counterexample to the diamond property for -1-> **)

lemma KIII_contract1: "K##I##(I##I) -1-> I"
by (rule contract.K)

lemma KIII_contract2: "K##I##(I##I) -1-> K##I##((K##I)##(K##I))"
by (unfold I_def, blast)

lemma KIII_contract3: "K##I##((K##I)##(K##I)) -1-> I"
by blast

lemma not_diamond_contract: "~ diamond(contract)"
apply (unfold diamond_def) 
apply (best intro: KIII_contract1 KIII_contract2 KIII_contract3)
done


subsection {* Results about Parallel Contraction *}

text {* Derive a case for each combinator constructor. *}

inductive_cases
      K_parcontractE [elim!]: "K =1=> r"
  and S_parcontractE [elim!]: "S =1=> r"
  and Ap_parcontractE [elim!]: "p##q =1=> r"

declare parcontract.intros [intro]

(*** Basic properties of parallel contraction ***)

subsection {* Basic properties of parallel contraction *}

lemma K1_parcontractD [dest!]: "K##x =1=> z ==> (\<exists>x'. z = K##x' & x =1=> x')"
by blast

lemma S1_parcontractD [dest!]: "S##x =1=> z ==> (\<exists>x'. z = S##x' & x =1=> x')"
by blast

lemma S2_parcontractD [dest!]:
     "S##x##y =1=> z ==> (\<exists>x' y'. z = S##x'##y' & x =1=> x' & y =1=> y')"
by blast

text{*The rules above are not essential but make proofs much faster*}

text{*Church-Rosser property for parallel contraction*}
lemma diamond_parcontract: "diamond parcontract"
apply (unfold diamond_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule parcontract.induct, fast+)
done

text {*
  \medskip Equivalence of @{prop "p ---> q"} and @{prop "p ===> q"}.
*}

lemma contract_subset_parcontract: "contract <= parcontract"
apply (rule subsetI)
apply (simp only: split_tupled_all)
apply (erule contract.induct, blast+)
done

text{*Reductions: simply throw together reflexivity, transitivity and
  the one-step reductions*}

declare r_into_rtrancl [intro]  rtrancl_trans [intro]

(*Example only: not used*)
lemma reduce_I: "I##x ---> x"
by (unfold I_def, blast)

lemma parcontract_subset_reduce: "parcontract <= contract^*"
apply (rule subsetI)
apply (simp only: split_tupled_all)
apply (erule parcontract.induct , blast+)
done

lemma reduce_eq_parreduce: "contract^* = parcontract^*"
by (rule equalityI contract_subset_parcontract [THEN rtrancl_mono] 
         parcontract_subset_reduce [THEN rtrancl_subset_rtrancl])+

lemma diamond_reduce: "diamond(contract^*)"
by (simp add: reduce_eq_parreduce diamond_rtrancl diamond_parcontract)

end
