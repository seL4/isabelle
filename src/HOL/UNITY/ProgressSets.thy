(*  Title:      HOL/UNITY/ProgressSets
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

Progress Sets.  From 

    David Meier and Beverly Sanders,
    Composing Leads-to Properties
    Theoretical Computer Science 243:1-2 (2000), 339-361.
*)

header{*Progress Sets*}

theory ProgressSets = Transformers:

constdefs
  closure_set :: "'a set set => bool"
   "closure_set C ==
	 (\<forall>D. D \<subseteq> C --> \<Inter>D \<in> C) & (\<forall>D. D \<subseteq> C --> \<Union>D \<in> C)"

  cl :: "['a set set, 'a set] => 'a set"
   --{*short for ``closure''*}
   "cl C r == \<Inter>{x. x\<in>C & r \<subseteq> x}"

lemma UNIV_in_closure_set: "closure_set C ==> UNIV \<in> C"
by (force simp add: closure_set_def)

lemma empty_in_closure_set: "closure_set C ==> {} \<in> C"
by (force simp add: closure_set_def)

lemma Union_in_closure_set: "[|D \<subseteq> C; closure_set C|] ==> \<Union>D \<in> C"
by (simp add: closure_set_def)

lemma Inter_in_closure_set: "[|D \<subseteq> C; closure_set C|] ==> \<Inter>D \<in> C"
by (simp add: closure_set_def)

lemma UN_in_closure_set:
     "[|closure_set C; !!i. i\<in>I ==> r i \<in> C|] ==> (\<Union>i\<in>I. r i) \<in> C"
apply (simp add: Set.UN_eq) 
apply (blast intro: Union_in_closure_set) 
done

lemma IN_in_closure_set:
     "[|closure_set C; !!i. i\<in>I ==> r i \<in> C|] ==> (\<Inter>i\<in>I. r i)  \<in> C"
apply (simp add: INT_eq) 
apply (blast intro: Inter_in_closure_set) 
done

lemma Un_in_closure_set: "[|x\<in>C; y\<in>C; closure_set C|] ==> x\<union>y \<in> C"
apply (simp only: Un_eq_Union) 
apply (blast intro: Union_in_closure_set) 
done

lemma Int_in_closure_set: "[|x\<in>C; y\<in>C; closure_set C|] ==> x\<inter>y \<in> C"
apply (simp only: Int_eq_Inter) 
apply (blast intro: Inter_in_closure_set) 
done

lemma closure_set_stable: "closure_set {X. F \<in> stable X}"
by (simp add: closure_set_def stable_def constrains_def, blast)

text{*The next three results state that @{term "cl C r"} is the minimal
 element of @{term C} that includes @{term r}.*}
lemma cl_in_closure_set: "closure_set C ==> cl C r \<in> C"
apply (simp add: closure_set_def cl_def)
apply (erule conjE)  
apply (drule spec, erule mp, blast) 
done

lemma cl_least: "[|c\<in>C; r\<subseteq>c|] ==> cl C r \<subseteq> c" 
by (force simp add: cl_def)

text{*The next three lemmas constitute assertion (4.61)*}
lemma cl_mono: "r \<subseteq> r' ==> cl C r \<subseteq> cl C r'"
by (simp add: cl_def, blast)

lemma subset_cl: "r \<subseteq> cl C r"
by (simp add: cl_def, blast)

lemma cl_UN_subset: "(\<Union>i\<in>I. cl C (r i)) \<subseteq> cl C (\<Union>i\<in>I. r i)"
by (simp add: cl_def, blast)

lemma cl_Un: "closure_set C ==> cl C (r\<union>s) = cl C r \<union> cl C s"
apply (rule equalityI) 
 prefer 2 
  apply (simp add: cl_def, blast)
apply (rule cl_least)
 apply (blast intro: Un_in_closure_set cl_in_closure_set)
apply (blast intro: subset_cl [THEN subsetD])  
done

lemma cl_UN: "closure_set C ==> cl C (\<Union>i\<in>I. r i) = (\<Union>i\<in>I. cl C (r i))"
apply (rule equalityI) 
 prefer 2 
  apply (simp add: cl_def, blast)
apply (rule cl_least)
 apply (blast intro: UN_in_closure_set cl_in_closure_set)
apply (blast intro: subset_cl [THEN subsetD])  
done

lemma cl_idem [simp]: "cl C (cl C r) = cl C r"
by (simp add: cl_def, blast)

lemma cl_ident: "r\<in>C ==> cl C r = r" 
by (force simp add: cl_def)

text{*Assertion (4.62)*}
lemma cl_ident_iff: "closure_set C ==> (cl C r = r) = (r\<in>C)" 
apply (rule iffI) 
 apply (erule subst)
 apply (erule cl_in_closure_set)  
apply (erule cl_ident) 
done

end
