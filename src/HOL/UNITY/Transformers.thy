(*  Title:      HOL/UNITY/Transformers
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

Predicate Transformers from 

    David Meier and Beverly Sanders,
    Composing Leads-to Properties
    Theoretical Computer Science 243:1-2 (2000), 339-361.
*)

header{*Predicate Transformers*}

theory Transformers = Comp:

subsection{*Defining the Predicate Transformers @{term wp},
   @{term awp} and  @{term wens}*}

constdefs
  wp :: "[('a*'a) set, 'a set] => 'a set"  
    --{*Dijkstra's weakest-precondition operator*}
    "wp act B == - (act^-1 `` (-B))"

  awp :: "[ 'a program, 'a set] => 'a set"  
    "awp F B == (\<Inter>act \<in> Acts F. wp act B)"

  wens :: "[ 'a program, ('a*'a) set, 'a set] => 'a set"  
    "wens F act B == gfp(\<lambda>X. (wp act B \<inter> awp F (B \<union> X)) \<union> B)"

text{*The fundamental theorem for wp*}
theorem wp_iff: "(A <= wp act B) = (act `` A <= B)"
by (force simp add: wp_def) 

lemma Compl_Domain_subset_wp: "- (Domain act) \<subseteq> wp act B"
by (force simp add: wp_def) 

lemma awp_Int_eq: "awp F (A\<inter>B) = awp F A \<inter> awp F B"
by (simp add: awp_def wp_def, blast) 

text{*The fundamental theorem for awp*}
theorem awp_iff: "(A <= awp F B) = (F \<in> A co B)"
by (simp add: awp_def constrains_def wp_iff INT_subset_iff) 

theorem stable_iff_awp: "(A \<subseteq> awp F A) = (F \<in> stable A)"
by (simp add: awp_iff stable_def) 

lemma awp_mono: "(A \<subseteq> B) ==> awp F A \<subseteq> awp F B"
by (simp add: awp_def wp_def, blast)

lemma wens_unfold:
     "wens F act B = (wp act B \<inter> awp F (B \<union> wens F act B)) \<union> B"
apply (simp add: wens_def) 
apply (rule gfp_unfold) 
apply (simp add: mono_def wp_def awp_def, blast) 
done

text{*These two theorems justify the claim that @{term wens} returns the
weakest assertion satisfying the ensures property*}
lemma ensures_imp_wens: "F \<in> A ensures B ==> \<exists>act \<in> Acts F. A \<subseteq> wens F act B"
apply (simp add: wens_def ensures_def transient_def, clarify) 
apply (rule rev_bexI, assumption) 
apply (rule gfp_upperbound)
apply (simp add: constrains_def awp_def wp_def, blast)
done

lemma wens_ensures: "act \<in> Acts F ==> F \<in> (wens F act B) ensures B"
by (simp add: wens_def gfp_def constrains_def awp_def wp_def
              ensures_def transient_def, blast) 

text{*These two results constitute assertion (4.13) of the thesis*}
lemma wens_mono: "(A \<subseteq> B) ==> wens F act A \<subseteq> wens F act B"
apply (simp add: wens_def wp_def awp_def) 
apply (rule gfp_mono, blast) 
done

lemma wens_weakening: "B \<subseteq> wens F act B"
by (simp add: wens_def gfp_def, blast)

text{*Assertion (6), or 4.16 in the thesis*}
lemma subset_wens: "A-B \<subseteq> wp act B \<inter> awp F (B \<union> A) ==> A \<subseteq> wens F act B" 
apply (simp add: wens_def wp_def awp_def) 
apply (rule gfp_upperbound, blast) 
done

text{*Assertion 4.17 in the thesis*}
lemma Diff_wens_constrains: "F \<in> (wens F act A - A) co wens F act A" 
by (simp add: wens_def gfp_def wp_def awp_def constrains_def, blast)

text{*Assertion (7): 4.18 in the thesis.  NOTE that many of these results
hold for an arbitrary action.  We often do not require @{term "act \<in> Acts F"}*}
lemma stable_wens: "F \<in> stable A ==> F \<in> stable (wens F act A)"
apply (simp add: stable_def)
apply (drule constrains_Un [OF Diff_wens_constrains [of F act A]]) 
apply (simp add: Un_Int_distrib2 Compl_partition2) 
apply (erule constrains_weaken) 
 apply blast 
apply (simp add: Un_subset_iff wens_weakening) 
done

text{*Assertion 4.20 in the thesis.*}
lemma wens_Int_eq_lemma:
      "[|T-B \<subseteq> awp F T; act \<in> Acts F|]
       ==> T \<inter> wens F act B \<subseteq> wens F act (T\<inter>B)"
apply (rule subset_wens) 
apply (rule_tac P="\<lambda>x. ?f x \<subseteq> ?b" in ssubst [OF wens_unfold])
apply (simp add: wp_def awp_def, blast)
done

text{*Assertion (8): 4.21 in the thesis. Here we indeed require
      @{term "act \<in> Acts F"}*}
lemma wens_Int_eq:
      "[|T-B \<subseteq> awp F T; act \<in> Acts F|]
       ==> T \<inter> wens F act B = T \<inter> wens F act (T\<inter>B)"
apply (rule equalityI)
 apply (simp_all add: Int_lower1 Int_subset_iff) 
 apply (rule wens_Int_eq_lemma, assumption+) 
apply (rule subset_trans [OF _ wens_mono [of "T\<inter>B" B]], auto) 
done

subsection{*Defining the Weakest Ensures Set*}

consts
  wens_set :: "['a program, 'a set] => 'a set set"

inductive "wens_set F B"
 intros 

  Basis: "B \<in> wens_set F B"

  Wens:  "[|X \<in> wens_set F B; act \<in> Acts F|] ==> wens F act X \<in> wens_set F B"

  Union: "W \<noteq> {} ==> \<forall>U \<in> W. U \<in> wens_set F B ==> \<Union>W \<in> wens_set F B"

lemma wens_set_imp_co: "A \<in> wens_set F B ==> F \<in> (A-B) co A"
apply (erule wens_set.induct) 
  apply (simp add: constrains_def)
 apply (drule_tac act1=act and A1=X 
        in constrains_Un [OF Diff_wens_constrains]) 
 apply (erule constrains_weaken, blast) 
 apply (simp add: Un_subset_iff wens_weakening) 
apply (rule constrains_weaken) 
apply (rule_tac I=W and A="\<lambda>v. v-B" and A'="\<lambda>v. v" in constrains_UN, blast+)
done

lemma wens_set_imp_leadsTo: "A \<in> wens_set F B ==> F \<in> A leadsTo B"
apply (erule wens_set.induct)
  apply (rule leadsTo_refl)  
 apply (blast intro: wens_ensures leadsTo_Basis leadsTo_Trans ) 
apply (blast intro: leadsTo_Union) 
done

(*????????????????Set.thy Set.all_not_in_conv*)
lemma ex_in_conv: "(\<exists>x. x \<in> A) = (A \<noteq> {})"
by blast


lemma leadsTo_imp_wens_set: "F \<in> A leadsTo B ==> \<exists>C \<in> wens_set F B. A \<subseteq> C"
apply (erule leadsTo_induct_pre)
  apply (blast dest!: ensures_imp_wens intro: wens_set.Basis wens_set.Wens)
 apply clarify 
 apply (drule ensures_weaken_R, assumption)  
 apply (blast dest!: ensures_imp_wens intro: wens_set.Wens)
apply (case_tac "S={}") 
 apply (simp, blast intro: wens_set.Basis)
apply (clarsimp dest!: bchoice simp: ball_conj_distrib Bex_def) 
apply (rule_tac x = "\<Union>{Z. \<exists>U\<in>S. Z = f U}" in exI)
apply (blast intro: wens_set.Union) 
done

text{*Assertion (9): 4.27 in the thesis.*}

lemma leadsTo_iff_wens_set: "(F \<in> A leadsTo B) = (\<exists>C \<in> wens_set F B. A \<subseteq> C)"
by (blast intro: leadsTo_imp_wens_set leadsTo_weaken_L wens_set_imp_leadsTo) 

text{*This is the result that requires the definition of @{term wens_set} to
require @{term W} to be non-empty in the Unio case, for otherwise we should
always have @{term "{} \<in> wens_set F B"}.*}
lemma wens_set_imp_subset: "A \<in> wens_set F B ==> B \<subseteq> A"
apply (erule wens_set.induct) 
  apply (blast intro: wens_weakening [THEN subsetD])+
done


subsection{*Properties Involving Program Union*}

text{*Assertion (4.30) of thesis, reoriented*}
lemma awp_Join_eq: "awp (F\<squnion>G) B = awp F B \<inter> awp G B"
by (simp add: awp_def wp_def, blast)

lemma wens_subset: 
     "wens F act B - B \<subseteq> wp act B \<inter> awp F (B \<union> wens F act B)"
by (subst wens_unfold, fast) 

text{*Assertion (4.31)*}
lemma subset_wens_Join:
      "[|A = T \<inter> wens F act B;  T-B \<subseteq> awp F T; A-B \<subseteq> awp G (A \<union> B)|] 
       ==> A \<subseteq> wens (F\<squnion>G) act B"
apply (subgoal_tac "(T \<inter> wens F act B) - B \<subseteq> 
                    wp act B \<inter> awp F (B \<union> wens F act B) \<inter> awp F T") 
 apply (rule subset_wens) 
 apply (simp add: awp_Join_eq awp_Int_eq Int_subset_iff Un_commute)
 apply (simp add: awp_def wp_def, blast) 
apply (insert wens_subset [of F act B], blast) 
done

text{*Assertion (4.32)*}
lemma wens_Join_subset: "wens (F\<squnion>G) act B \<subseteq> wens F act B"
apply (simp add: wens_def) 
apply (rule gfp_mono)
apply (auto simp add: awp_Join_eq)  
done

text{*Lemma, because the inductive step is just too messy.*}
lemma wens_Union_inductive_step:
  assumes awpF: "T-B \<subseteq> awp F T"
      and awpG: "!!X. X \<in> wens_set F B ==> (T\<inter>X) - B \<subseteq> awp G (T\<inter>X)"
  shows "[|X \<in> wens_set F B; act \<in> Acts F; Y \<subseteq> X; T\<inter>X = T\<inter>Y|]
         ==> wens (F\<squnion>G) act Y \<subseteq> wens F act X \<and>
             T \<inter> wens F act X = T \<inter> wens (F\<squnion>G) act Y"
apply (subgoal_tac "wens (F\<squnion>G) act Y \<subseteq> wens F act X")  
 prefer 2
 apply (blast dest: wens_mono intro: wens_Join_subset [THEN subsetD], simp)
apply (rule equalityI) 
 prefer 2 apply blast
apply (simp add: Int_lower1 Int_subset_iff) 
apply (frule wens_set_imp_subset) 
apply (subgoal_tac "T-X \<subseteq> awp F T")  
 prefer 2 apply (blast intro: awpF [THEN subsetD]) 
apply (rule_tac B = "wens (F\<squnion>G) act (T\<inter>X)" in subset_trans) 
 prefer 2 apply (blast intro!: wens_mono)
apply (subst wens_Int_eq, assumption+) 
apply (rule subset_wens_Join [of _ T])
  apply simp 
 apply blast
apply (subgoal_tac "T \<inter> wens F act (T\<inter>X) \<union> T\<inter>X = T \<inter> wens F act X")
 prefer 2
 apply (subst wens_Int_eq [symmetric], assumption+) 
 apply (blast intro: wens_weakening [THEN subsetD], simp) 
apply (blast intro: awpG [THEN subsetD] wens_set.Wens)
done

lemma wens_Union:
  assumes awpF: "T-B \<subseteq> awp F T"
      and awpG: "!!X. X \<in> wens_set F B ==> (T\<inter>X) - B \<subseteq> awp G (T\<inter>X)"
      and major: "X \<in> wens_set F B"
  shows "\<exists>Y \<in> wens_set (F\<squnion>G) B. Y \<subseteq> X & T\<inter>X = T\<inter>Y"
apply (rule wens_set.induct [OF major])
  txt{*Basis: trivial*}
  apply (blast intro: wens_set.Basis)
 txt{*Inductive step*}
 apply clarify 
 apply (rule_tac x = "wens (F\<squnion>G) act Y" in rev_bexI)
  apply (force intro: wens_set.Wens)
 apply (simp add: wens_Union_inductive_step [OF awpF awpG]) 
txt{*Union: by Axiom of Choice*}
apply (simp add: ball_conj_distrib Bex_def) 
apply (clarify dest!: bchoice) 
apply (rule_tac x = "\<Union>{Z. \<exists>U\<in>W. Z = f U}" in exI)
apply (blast intro: wens_set.Union) 
done

end
