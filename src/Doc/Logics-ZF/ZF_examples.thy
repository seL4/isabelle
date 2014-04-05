header{*Examples of Reasoning in ZF Set Theory*}

theory ZF_examples imports Main_ZFC begin

subsection {* Binary Trees *}

consts
  bt :: "i => i"

datatype "bt(A)" =
  Lf | Br ("a \<in> A", "t1 \<in> bt(A)", "t2 \<in> bt(A)")

declare bt.intros [simp]

text{*Induction via tactic emulation*}
lemma Br_neq_left [rule_format]: "l \<in> bt(A) ==> \<forall>x r. Br(x, l, r) \<noteq> l"
  --{* @{subgoals[display,indent=0,margin=65]} *}
  apply (induct_tac l)
  --{* @{subgoals[display,indent=0,margin=65]} *}
  apply auto
  done

(*
  apply (Inductive.case_tac l)
  apply (tactic {*exhaust_tac "l" 1*})
*)

text{*The new induction method, which I don't understand*}
lemma Br_neq_left': "l \<in> bt(A) ==> (!!x r. Br(x, l, r) \<noteq> l)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
  apply (induct set: bt)
  --{* @{subgoals[display,indent=0,margin=65]} *}
  apply auto
  done

lemma Br_iff: "Br(a,l,r) = Br(a',l',r') <-> a=a' & l=l' & r=r'"
  -- "Proving a freeness theorem."
  by (blast elim!: bt.free_elims)

inductive_cases Br_in_bt: "Br(a,l,r) \<in> bt(A)"
  -- "An elimination rule, for type-checking."

text {*
@{thm[display] Br_in_bt[no_vars]}
*};

subsection{*Primitive recursion*}

consts  n_nodes :: "i => i"
primrec
  "n_nodes(Lf) = 0"
  "n_nodes(Br(a,l,r)) = succ(n_nodes(l) #+ n_nodes(r))"

lemma n_nodes_type [simp]: "t \<in> bt(A) ==> n_nodes(t) \<in> nat"
  by (induct_tac t, auto) 

consts  n_nodes_aux :: "i => i"
primrec
  "n_nodes_aux(Lf) = (\<lambda>k \<in> nat. k)"
  "n_nodes_aux(Br(a,l,r)) = 
      (\<lambda>k \<in> nat. n_nodes_aux(r) `  (n_nodes_aux(l) ` succ(k)))"

lemma n_nodes_aux_eq [rule_format]:
     "t \<in> bt(A) ==> \<forall>k \<in> nat. n_nodes_aux(t)`k = n_nodes(t) #+ k"
  by (induct_tac t, simp_all) 

definition n_nodes_tail :: "i => i" where
   "n_nodes_tail(t) == n_nodes_aux(t) ` 0"

lemma "t \<in> bt(A) ==> n_nodes_tail(t) = n_nodes(t)"
 by (simp add: n_nodes_tail_def n_nodes_aux_eq) 


subsection {*Inductive definitions*}

consts  Fin       :: "i=>i"
inductive
  domains   "Fin(A)" \<subseteq> "Pow(A)"
  intros
    emptyI:  "0 \<in> Fin(A)"
    consI:   "[| a \<in> A;  b \<in> Fin(A) |] ==> cons(a,b) \<in> Fin(A)"
  type_intros  empty_subsetI cons_subsetI PowI
  type_elims   PowD [elim_format]


consts  acc :: "i => i"
inductive
  domains "acc(r)" \<subseteq> "field(r)"
  intros
    vimage:  "[| r-``{a}: Pow(acc(r)); a \<in> field(r) |] ==> a \<in> acc(r)"
  monos      Pow_mono


consts
  llist  :: "i=>i";

codatatype
  "llist(A)" = LNil | LCons ("a \<in> A", "l \<in> llist(A)")


(*Coinductive definition of equality*)
consts
  lleq :: "i=>i"

(*Previously used <*> in the domain and variant pairs as elements.  But
  standard pairs work just as well.  To use variant pairs, must change prefix
  a q/Q to the Sigma, Pair and converse rules.*)
coinductive
  domains "lleq(A)" \<subseteq> "llist(A) * llist(A)"
  intros
    LNil:  "<LNil, LNil> \<in> lleq(A)"
    LCons: "[| a \<in> A; <l,l'> \<in> lleq(A) |] 
            ==> <LCons(a,l), LCons(a,l')> \<in> lleq(A)"
  type_intros  llist.intros


subsection{*Powerset example*}

lemma Pow_mono: "A\<subseteq>B  ==>  Pow(A) \<subseteq> Pow(B)"
apply (rule subsetI)
apply (rule PowI)
apply (drule PowD)
apply (erule subset_trans, assumption)
done

lemma "Pow(A Int B) = Pow(A) Int Pow(B)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule equalityI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule Int_greatest)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule Int_lower1 [THEN Pow_mono])
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule Int_lower2 [THEN Pow_mono])
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule subsetI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule IntE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule PowI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (drule PowD)+
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule Int_greatest)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (assumption+)
done

text{*Trying again from the beginning in order to use @{text blast}*}
lemma "Pow(A Int B) = Pow(A) Int Pow(B)"
by blast


lemma "C\<subseteq>D ==> Union(C) \<subseteq> Union(D)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule subsetI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule UnionE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule UnionI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule subsetD)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption 
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption 
done

text{*A more abstract version of the same proof*}

lemma "C\<subseteq>D ==> Union(C) \<subseteq> Union(D)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule Union_least)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule Union_upper)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule subsetD, assumption)
done


lemma "[| a \<in> A;  f \<in> A->B;  g \<in> C->D;  A \<inter> C = 0 |] ==> (f \<union> g)`a = f`a"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule apply_equality)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule UnI1)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule apply_Pair)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption 
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption 
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule fun_disjoint_Un)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption 
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption 
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply assumption 
done

end
