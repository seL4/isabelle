header{*Examples of Reasoning in ZF Set Theory*}

theory ZF_examples = Main_ZFC:

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

lemma Br_iff: "Br(a, l, r) = Br(a', l', r') <-> a = a' & l = l' & r = r'"
  -- "Proving a freeness theorem."
  by (blast elim!: bt.free_elims)

inductive_cases BrE: "Br(a, l, r) \<in> bt(A)"
  -- "An elimination rule, for type-checking."

text {*
@{thm[display] BrE[no_vars]}
\rulename{BrE}
*};

subsection{*Powerset example*}

lemma Pow_mono: "A<=B  ==>  Pow(A) <= Pow(B)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule subsetI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule PowI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (drule PowD)
  --{* @{subgoals[display,indent=0,margin=65]} *}
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
apply (rule Int_greatest, assumption+)
done

text{*Trying again from the beginning in order to use @{text blast}*}
lemma "Pow(A Int B) = Pow(A) Int Pow(B)"
by blast


lemma "C<=D ==> Union(C) <= Union(D)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule subsetI)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule UnionE)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule UnionI)
apply (erule subsetD, assumption, assumption)
  --{* @{subgoals[display,indent=0,margin=65]} *}
done

text{*Trying again from the beginning in order to prove from the definitions*}

lemma "C<=D ==> Union(C) <= Union(D)"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule Union_least)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule Union_upper)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (erule subsetD, assumption)
done


lemma "[| a:A;  f: A->B;  g: C->D;  A Int C = 0 |] ==> (f Un g)`a = f`a"
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule apply_equality)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule UnI1)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule apply_Pair, assumption+)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (rule fun_disjoint_Un, assumption+)
done

end
