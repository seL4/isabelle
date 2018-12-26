section\<open>Examples of Reasoning in ZF Set Theory\<close>

theory ZF_examples imports ZFC begin

subsection \<open>Binary Trees\<close>

consts
  bt :: "i => i"

datatype "bt(A)" =
  Lf | Br ("a \<in> A", "t1 \<in> bt(A)", "t2 \<in> bt(A)")

declare bt.intros [simp]

text\<open>Induction via tactic emulation\<close>
lemma Br_neq_left [rule_format]: "l \<in> bt(A) ==> \<forall>x r. Br(x, l, r) \<noteq> l"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
  apply (induct_tac l)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
  apply auto
  done

(*
  apply (Inductive.case_tac l)
  apply (tactic {*exhaust_tac "l" 1*})
*)

text\<open>The new induction method, which I don't understand\<close>
lemma Br_neq_left': "l \<in> bt(A) ==> (!!x r. Br(x, l, r) \<noteq> l)"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
  apply (induct set: bt)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
  apply auto
  done

lemma Br_iff: "Br(a,l,r) = Br(a',l',r') <-> a=a' & l=l' & r=r'"
  \<comment> \<open>Proving a freeness theorem.\<close>
  by (blast elim!: bt.free_elims)

inductive_cases Br_in_bt: "Br(a,l,r) \<in> bt(A)"
  \<comment> \<open>An elimination rule, for type-checking.\<close>

text \<open>
@{thm[display] Br_in_bt[no_vars]}
\<close>

subsection\<open>Primitive recursion\<close>

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


subsection \<open>Inductive definitions\<close>

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
  llist  :: "i=>i"

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


subsection\<open>Powerset example\<close>

lemma Pow_mono: "A\<subseteq>B  ==>  Pow(A) \<subseteq> Pow(B)"
apply (rule subsetI)
apply (rule PowI)
apply (drule PowD)
apply (erule subset_trans, assumption)
done

lemma "Pow(A Int B) = Pow(A) Int Pow(B)"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule equalityI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule Int_greatest)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule Int_lower1 [THEN Pow_mono])
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule Int_lower2 [THEN Pow_mono])
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule subsetI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule IntE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule PowI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (drule PowD)+
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule Int_greatest)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (assumption+)
done

text\<open>Trying again from the beginning in order to use \<open>blast\<close>\<close>
lemma "Pow(A Int B) = Pow(A) Int Pow(B)"
by blast


lemma "C\<subseteq>D ==> Union(C) \<subseteq> Union(D)"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule subsetI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule UnionE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule UnionI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule subsetD)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption 
done

text\<open>A more abstract version of the same proof\<close>

lemma "C\<subseteq>D ==> Union(C) \<subseteq> Union(D)"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule Union_least)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule Union_upper)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule subsetD, assumption)
done


lemma "[| a \<in> A;  f \<in> A->B;  g \<in> C->D;  A \<inter> C = 0 |] ==> (f \<union> g)`a = f`a"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule apply_equality)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule UnI1)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule apply_Pair)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule fun_disjoint_Un)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption 
done

end
