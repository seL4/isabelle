(*  Title:      ZF/Induct/Comb.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1994  University of Cambridge

Combinatory Logic example: the Church-Rosser Theorem
Curiously, combinators do not include free variables.

Example taken from
    J. Camilleri and T. F. Melham.
    Reasoning with Inductively Defined Relations in the HOL Theorem Prover.
    Report 265, University of Cambridge Computer Laboratory, 1992.

HOL system proofs may be found in
/usr/groups/theory/hvg-aftp/contrib/rule-induction/cl.ml
*)


theory Comb = Main:

(** Datatype definition of combinators S and K, with infixed application **)
consts comb :: i
datatype
  "comb" = K
         | S
         | "#" ("p \<in> comb", "q \<in> comb")   (infixl 90)

(** Inductive definition of contractions, -1->
             and (multi-step) reductions, --->
**)
consts
  contract  :: "i"
  "-1->"    :: "[i,i] => o"                       (infixl 50)
  "--->"    :: "[i,i] => o"                       (infixl 50)

translations
  "p -1-> q" == "<p,q> \<in> contract"
  "p ---> q" == "<p,q> \<in> contract^*"

inductive
  domains   "contract" <= "comb*comb"
  intros
    K:     "[| p \<in> comb;  q \<in> comb |] ==> K#p#q -1-> p"
    S:     "[| p \<in> comb;  q \<in> comb;  r \<in> comb |] ==> S#p#q#r -1-> (p#r)#(q#r)"
    Ap1:   "[| p-1->q;  r \<in> comb |] ==> p#r -1-> q#r"
    Ap2:   "[| p-1->q;  r \<in> comb |] ==> r#p -1-> r#q"
  type_intros "comb.intros"


(** Inductive definition of parallel contractions, =1=>
             and (multi-step) parallel reductions, ===>
**)
consts
  parcontract :: "i"
  "=1=>"      :: "[i,i] => o"                       (infixl 50)
  "===>"      :: "[i,i] => o"                       (infixl 50)

translations
  "p =1=> q" == "<p,q> \<in> parcontract"
  "p ===> q" == "<p,q> \<in> parcontract^+"

inductive
  domains   "parcontract" <= "comb*comb"
  intros
    refl:  "[| p \<in> comb |] ==> p =1=> p"
    K:     "[| p \<in> comb;  q \<in> comb |] ==> K#p#q =1=> p"
    S:     "[| p \<in> comb;  q \<in> comb;  r \<in> comb |] ==> S#p#q#r =1=> (p#r)#(q#r)"
    Ap:    "[| p=1=>q;  r=1=>s |] ==> p#r =1=> q#s"
  type_intros "comb.intros"


(*Misc definitions*)
constdefs
  I :: i
  "I == S#K#K"

  diamond :: "i => o"
  "diamond(r) == \<forall>x y. <x,y>\<in>r --> 
                          (\<forall>y'. <x,y'>\<in>r --> 
                                   (\<exists>z. <y,z>\<in>r & <y',z> \<in> r))"



(*** Transitive closure preserves the Church-Rosser property ***)

lemma diamond_strip_lemmaD [rule_format]:
    "[| diamond(r);  <x,y>:r^+ |] ==>  
     \<forall>y'. <x,y'>:r --> (\<exists>z. <y',z>: r^+ & <y,z>: r)"
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
apply (auto ); 
apply (best intro: r_into_trancl trans_trancl [THEN transD]
             dest: diamond_strip_lemmaD)+
done


inductive_cases Ap_E [elim!]: "p#q \<in> comb"

declare comb.intros [intro!]


(*** Results about Contraction ***)

(*For type checking: replaces a-1->b by a,b \<in> comb *)
lemmas contract_combE2 = contract.dom_subset [THEN subsetD, THEN SigmaE2]
lemmas contract_combD1 = contract.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas contract_combD2 = contract.dom_subset [THEN subsetD, THEN SigmaD2]

lemma field_contract_eq: "field(contract) = comb"
by (blast intro: contract.K elim!: contract_combE2)

lemmas reduction_refl = 
    field_contract_eq [THEN equalityD2, THEN subsetD, THEN rtrancl_refl]

lemmas rtrancl_into_rtrancl2 =  
    r_into_rtrancl [THEN trans_rtrancl [THEN transD]]

declare reduction_refl [intro!] contract.K [intro!] contract.S [intro!]

lemmas reduction_rls = contract.K [THEN rtrancl_into_rtrancl2]
                     contract.S [THEN rtrancl_into_rtrancl2]
                     contract.Ap1 [THEN rtrancl_into_rtrancl2]
                     contract.Ap2 [THEN rtrancl_into_rtrancl2]

(*Example only: not used*)
lemma reduce_I: "p \<in> comb ==> I#p ---> p"
by (unfold I_def, blast intro: reduction_rls)

lemma comb_I: "I \<in> comb"
by (unfold I_def, blast)

(** Non-contraction results **)

(*Derive a case for each combinator constructor*)
inductive_cases K_contractE [elim!]: "K -1-> r"
inductive_cases S_contractE [elim!]: "S -1-> r"
inductive_cases Ap_contractE [elim!]: "p#q -1-> r"

declare contract.Ap1 [intro] contract.Ap2 [intro]

lemma I_contract_E: "I -1-> r ==> P"
by (auto simp add: I_def) 

lemma K1_contractD: "K#p -1-> r ==> (\<exists>q. r = K#q & p -1-> q)"
by auto

lemma Ap_reduce1: "[| p ---> q;  r \<in> comb |] ==> p#r ---> q#r"
apply (frule rtrancl_type [THEN subsetD, THEN SigmaD1])
apply (drule field_contract_eq [THEN equalityD1, THEN subsetD])
apply (erule rtrancl_induct)
apply (blast intro: reduction_rls)
apply (erule trans_rtrancl [THEN transD])
apply (blast intro: contract_combD2 reduction_rls)
done

lemma Ap_reduce2: "[| p ---> q;  r \<in> comb |] ==> r#p ---> r#q"
apply (frule rtrancl_type [THEN subsetD, THEN SigmaD1])
apply (drule field_contract_eq [THEN equalityD1, THEN subsetD])
apply (erule rtrancl_induct)
apply (blast intro: reduction_rls)
apply (erule trans_rtrancl [THEN transD])
apply (blast intro: contract_combD2 reduction_rls)
done

(** Counterexample to the diamond property for -1-> **)

lemma KIII_contract1: "K#I#(I#I) -1-> I"
by (blast intro: comb.intros contract.K comb_I)

lemma KIII_contract2: "K#I#(I#I) -1-> K#I#((K#I)#(K#I))"
by (unfold I_def, blast intro: comb.intros contract.intros)


lemma KIII_contract3: "K#I#((K#I)#(K#I)) -1-> I"
by (blast intro: comb.intros contract.K comb_I)

lemma not_diamond_contract: "~ diamond(contract)"
apply (unfold diamond_def)
apply (blast intro: KIII_contract1 KIII_contract2 KIII_contract3 
             elim!: I_contract_E)
done



(*** Results about Parallel Contraction ***)

(*For type checking: replaces a=1=>b by a,b \<in> comb *)
lemmas parcontract_combE2 = parcontract.dom_subset [THEN subsetD, THEN SigmaE2]
lemmas parcontract_combD1 = parcontract.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas parcontract_combD2 = parcontract.dom_subset [THEN subsetD, THEN SigmaD2]

lemma field_parcontract_eq: "field(parcontract) = comb"
by (blast intro: parcontract.K elim!: parcontract_combE2)

(*Derive a case for each combinator constructor*)
inductive_cases K_parcontractE [elim!]: "K =1=> r"
inductive_cases S_parcontractE [elim!]: "S =1=> r"
inductive_cases Ap_parcontractE [elim!]: "p#q =1=> r"

declare parcontract.intros [intro]


(*** Basic properties of parallel contraction ***)

lemma K1_parcontractD [dest!]: "K#p =1=> r ==> (\<exists>p'. r = K#p' & p =1=> p')"
by auto

lemma S1_parcontractD [dest!]: "S#p =1=> r ==> (\<exists>p'. r = S#p' & p =1=> p')"
by auto

lemma S2_parcontractD [dest!]:
     "S#p#q =1=> r ==> (\<exists>p' q'. r = S#p'#q' & p =1=> p' & q =1=> q')"
by auto


(*Church-Rosser property for parallel contraction*)
lemma diamond_parcontract: "diamond(parcontract)"
apply (unfold diamond_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule parcontract.induct)
apply (blast elim!: comb.free_elims  intro: parcontract_combD2)+
done

(*** Equivalence of p--->q and p===>q ***)

lemma contract_imp_parcontract: "p-1->q ==> p=1=>q"
by (erule contract.induct, auto)

lemma reduce_imp_parreduce: "p--->q ==> p===>q"
apply (frule rtrancl_type [THEN subsetD, THEN SigmaD1])
apply (drule field_contract_eq [THEN equalityD1, THEN subsetD])
apply (erule rtrancl_induct)
 apply (blast intro: r_into_trancl)
apply (blast intro: contract_imp_parcontract r_into_trancl 
                    trans_trancl [THEN transD])
done


lemma parcontract_imp_reduce: "p=1=>q ==> p--->q"
apply (erule parcontract.induct)
   apply (blast intro: reduction_rls)
  apply (blast intro: reduction_rls)
 apply (blast intro: reduction_rls)
apply (blast intro: trans_rtrancl [THEN transD] 
                Ap_reduce1 Ap_reduce2 parcontract_combD1 parcontract_combD2)
done

lemma parreduce_imp_reduce: "p===>q ==> p--->q"
apply (frule trancl_type [THEN subsetD, THEN SigmaD1])
apply (drule field_parcontract_eq [THEN equalityD1, THEN subsetD])
apply (erule trancl_induct, erule parcontract_imp_reduce)
apply (erule trans_rtrancl [THEN transD])
apply (erule parcontract_imp_reduce)
done

lemma parreduce_iff_reduce: "p===>q <-> p--->q"
by (blast intro: parreduce_imp_reduce reduce_imp_parreduce)

end
