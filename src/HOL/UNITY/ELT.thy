(*  Title:      HOL/UNITY/ELT.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

leadsTo strengthened with a specification of the allowable sets transient parts

TRY INSTEAD (to get rid of the {} and to gain strong induction)

  elt :: "['a set set, 'a program, 'a set] => ('a set) set"

inductive "elt CC F B"
  intros 

    Weaken:  "A <= B ==> A : elt CC F B"

    ETrans:  "[| F : A ensures A';  A-A' : CC;  A' : elt CC F B |]
              ==> A : elt CC F B"

    Union:  "{A. A: S} : Pow (elt CC F B) ==> (Union S) : elt CC F B"

  monos Pow_mono
*)

section\<open>Progress Under Allowable Sets\<close>

theory ELT imports Project begin

inductive_set
  (*LEADS-TO constant for the inductive definition*)
  elt :: "['a set set, 'a program] => ('a set * 'a set) set"
  for CC :: "'a set set" and F :: "'a program"
 where

   Basis:  "[| F \<in> A ensures B;  A-B \<in> (insert {} CC) |] ==> (A,B) \<in> elt CC F"

 | Trans:  "[| (A,B) \<in> elt CC F;  (B,C) \<in> elt CC F |] ==> (A,C) \<in> elt CC F"

 | Union:  "\<forall>A\<in>S. (A,B) \<in> elt CC F ==> (Union S, B) \<in> elt CC F"


definition  
  (*the set of all sets determined by f alone*)
  givenBy :: "['a => 'b] => 'a set set"
  where "givenBy f = range (%B. f-` B)"

definition
  (*visible version of the LEADS-TO relation*)
  leadsETo :: "['a set, 'a set set, 'a set] => 'a program set"
                                        (\<open>(3_/ leadsTo[_]/ _)\<close> [80,0,80] 80)
  where "leadsETo A CC B = {F. (A,B) \<in> elt CC F}"

definition
  LeadsETo :: "['a set, 'a set set, 'a set] => 'a program set"
                                        (\<open>(3_/ LeadsTo[_]/ _)\<close> [80,0,80] 80)
  where "LeadsETo A CC B =
      {F. F \<in> (reachable F Int A) leadsTo[(%C. reachable F Int C) ` CC] B}"


(*** givenBy ***)

lemma givenBy_id [simp]: "givenBy id = UNIV"
by (unfold givenBy_def, auto)

lemma givenBy_eq_all: "(givenBy v) = {A. \<forall>x\<in>A. \<forall>y. v x = v y \<longrightarrow> y \<in> A}"
apply (unfold givenBy_def, safe)
apply (rule_tac [2] x = "v ` _" in image_eqI, auto)
done

lemma givenByI: "(\<And>x y. [| x \<in> A;  v x = v y |] ==> y \<in> A) ==> A \<in> givenBy v"
by (subst givenBy_eq_all, blast)

lemma givenByD: "[| A \<in> givenBy v;  x \<in> A;  v x = v y |] ==> y \<in> A"
by (unfold givenBy_def, auto)

lemma empty_mem_givenBy [iff]: "{} \<in> givenBy v"
by (blast intro!: givenByI)

lemma givenBy_imp_eq_Collect: "A \<in> givenBy v ==> \<exists>P. A = {s. P(v s)}"
apply (rule_tac x = "\<lambda>n. \<exists>s. v s = n \<and> s \<in> A" in exI)
apply (simp (no_asm_use) add: givenBy_eq_all)
apply blast
done

lemma Collect_mem_givenBy: "{s. P(v s)} \<in> givenBy v"
by (unfold givenBy_def, best)

lemma givenBy_eq_Collect: "givenBy v = {A. \<exists>P. A = {s. P(v s)}}"
by (blast intro: Collect_mem_givenBy givenBy_imp_eq_Collect)

(*preserving v preserves properties given by v*)
lemma preserves_givenBy_imp_stable:
     "[| F \<in> preserves v;  D \<in> givenBy v |] ==> F \<in> stable D"
by (force simp add: preserves_subset_stable [THEN subsetD] givenBy_eq_Collect)

lemma givenBy_o_subset: "givenBy (w o v) <= givenBy v"
apply (simp (no_asm) add: givenBy_eq_Collect)
apply best 
done

lemma givenBy_DiffI:
     "[| A \<in> givenBy v;  B \<in> givenBy v |] ==> A-B \<in> givenBy v"
apply (simp (no_asm_use) add: givenBy_eq_Collect)
apply safe
apply (rule_tac x = "%z. R z & ~ Q z" for R Q in exI)
unfolding set_diff_eq
apply auto
done


(** Standard leadsTo rules **)

lemma leadsETo_Basis [intro]: 
     "[| F \<in> A ensures B;  A-B \<in> insert {} CC |] ==> F \<in> A leadsTo[CC] B"
apply (unfold leadsETo_def)
apply (blast intro: elt.Basis)
done

lemma leadsETo_Trans: 
     "[| F \<in> A leadsTo[CC] B;  F \<in> B leadsTo[CC] C |] ==> F \<in> A leadsTo[CC] C"
apply (unfold leadsETo_def)
apply (blast intro: elt.Trans)
done


(*Useful with cancellation, disjunction*)
lemma leadsETo_Un_duplicate:
     "F \<in> A leadsTo[CC] (A' \<union> A') \<Longrightarrow> F \<in> A leadsTo[CC] A'"
by (simp add: Un_ac)

lemma leadsETo_Un_duplicate2:
     "F \<in> A leadsTo[CC] (A' \<union> C \<union> C) ==> F \<in> A leadsTo[CC] (A' Un C)"
by (simp add: Un_ac)

(*The Union introduction rule as we should have liked to state it*)
lemma leadsETo_Union:
    "(\<And>A. A \<in> S \<Longrightarrow> F \<in> A leadsTo[CC] B) \<Longrightarrow> F \<in> (\<Union>S) leadsTo[CC] B"
apply (unfold leadsETo_def)
apply (blast intro: elt.Union)
done

lemma leadsETo_UN:
    "(\<And>i. i \<in> I \<Longrightarrow> F \<in> (A i) leadsTo[CC] B)  
     ==> F \<in> (UN i:I. A i) leadsTo[CC] B"
apply (blast intro: leadsETo_Union)
done

(*The INDUCTION rule as we should have liked to state it*)
lemma leadsETo_induct:
  "[| F \<in> za leadsTo[CC] zb;   
      !!A B. [| F \<in> A ensures B;  A-B \<in> insert {} CC |] ==> P A B;  
      !!A B C. [| F \<in> A leadsTo[CC] B; P A B; F \<in> B leadsTo[CC] C; P B C |]  
               ==> P A C;  
      !!B S. \<forall>A\<in>S. F \<in> A leadsTo[CC] B & P A B ==> P (\<Union>S) B  
   |] ==> P za zb"
apply (unfold leadsETo_def)
apply (drule CollectD) 
apply (erule elt.induct, blast+)
done


(** New facts involving leadsETo **)

lemma leadsETo_mono: "CC' <= CC ==> (A leadsTo[CC'] B) <= (A leadsTo[CC] B)"
apply safe
apply (erule leadsETo_induct)
prefer 3 apply (blast intro: leadsETo_Union)
prefer 2 apply (blast intro: leadsETo_Trans)
apply blast
done

lemma leadsETo_Trans_Un:
     "[| F \<in> A leadsTo[CC] B;  F \<in> B leadsTo[DD] C |]  
      ==> F \<in> A leadsTo[CC Un DD] C"
by (blast intro: leadsETo_mono [THEN subsetD] leadsETo_Trans)

lemma leadsETo_Union_Int:
 "(!!A. A \<in> S ==> F \<in> (A Int C) leadsTo[CC] B) 
  ==> F \<in> (\<Union>S Int C) leadsTo[CC] B"
apply (unfold leadsETo_def)
apply (simp only: Int_Union_Union)
apply (blast intro: elt.Union)
done

(*Binary union introduction rule*)
lemma leadsETo_Un:
     "[| F \<in> A leadsTo[CC] C; F \<in> B leadsTo[CC] C |] 
      ==> F \<in> (A Un B) leadsTo[CC] C"
  using leadsETo_Union [of "{A, B}" F CC C] by auto

lemma single_leadsETo_I:
     "(\<And>x. x \<in> A ==> F \<in> {x} leadsTo[CC] B) \<Longrightarrow> F \<in> A leadsTo[CC] B"
by (subst UN_singleton [symmetric], rule leadsETo_UN, blast)


lemma subset_imp_leadsETo: "A<=B \<Longrightarrow> F \<in> A leadsTo[CC] B"
by (simp add: subset_imp_ensures [THEN leadsETo_Basis] 
              Diff_eq_empty_iff [THEN iffD2])

lemmas empty_leadsETo = empty_subsetI [THEN subset_imp_leadsETo, simp]



(** Weakening laws **)

lemma leadsETo_weaken_R:
     "[| F \<in> A leadsTo[CC] A';  A'<=B' |] ==> F \<in> A leadsTo[CC] B'"
by (blast intro: subset_imp_leadsETo leadsETo_Trans)

lemma leadsETo_weaken_L:
     "[| F \<in> A leadsTo[CC] A'; B<=A |] ==> F \<in> B leadsTo[CC] A'"
by (blast intro: leadsETo_Trans subset_imp_leadsETo)

(*Distributes over binary unions*)
lemma leadsETo_Un_distrib:
     "F \<in> (A Un B) leadsTo[CC] C  =   
      (F \<in> A leadsTo[CC] C \<and> F \<in> B leadsTo[CC] C)"
by (blast intro: leadsETo_Un leadsETo_weaken_L)

lemma leadsETo_UN_distrib:
     "F \<in> (UN i:I. A i) leadsTo[CC] B  =   
      (\<forall>i\<in>I. F \<in> (A i) leadsTo[CC] B)"
by (blast intro: leadsETo_UN leadsETo_weaken_L)

lemma leadsETo_Union_distrib:
     "F \<in> (\<Union>S) leadsTo[CC] B  =  (\<forall>A\<in>S. F \<in> A leadsTo[CC] B)"
by (blast intro: leadsETo_Union leadsETo_weaken_L)

lemma leadsETo_weaken:
     "[| F \<in> A leadsTo[CC'] A'; B<=A; A'<=B';  CC' <= CC |]  
      ==> F \<in> B leadsTo[CC] B'"
apply (drule leadsETo_mono [THEN subsetD], assumption)
apply (blast del: subsetCE 
             intro: leadsETo_weaken_R leadsETo_weaken_L leadsETo_Trans)
done

lemma leadsETo_givenBy:
     "[| F \<in> A leadsTo[CC] A';  CC <= givenBy v |]  
      ==> F \<in> A leadsTo[givenBy v] A'"
by (blast intro: leadsETo_weaken)


(*Set difference*)
lemma leadsETo_Diff:
     "[| F \<in> (A-B) leadsTo[CC] C; F \<in> B leadsTo[CC] C |]  
      ==> F \<in> A leadsTo[CC] C"
by (blast intro: leadsETo_Un leadsETo_weaken)


(*Binary union version*)
lemma leadsETo_Un_Un:
     "[| F \<in> A leadsTo[CC] A';  F \<in> B leadsTo[CC] B' |]  
      ==> F \<in> (A Un B) leadsTo[CC] (A' Un B')"
by (blast intro: leadsETo_Un leadsETo_weaken_R)


(** The cancellation law **)

lemma leadsETo_cancel2:
     "[| F \<in> A leadsTo[CC] (A' Un B); F \<in> B leadsTo[CC] B' |]  
      ==> F \<in> A leadsTo[CC] (A' Un B')"
by (blast intro: leadsETo_Un_Un subset_imp_leadsETo leadsETo_Trans)

lemma leadsETo_cancel1:
     "[| F \<in> A leadsTo[CC] (B Un A'); F \<in> B leadsTo[CC] B' |]  
    ==> F \<in> A leadsTo[CC] (B' Un A')"
apply (simp add: Un_commute)
apply (blast intro!: leadsETo_cancel2)
done

lemma leadsETo_cancel_Diff1:
     "[| F \<in> A leadsTo[CC] (B Un A'); F \<in> (B-A') leadsTo[CC] B' |]  
    ==> F \<in> A leadsTo[CC] (B' Un A')"
apply (rule leadsETo_cancel1)
 prefer 2 apply assumption
apply simp_all
done


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
lemma e_psp_stable: 
   "[| F \<in> A leadsTo[CC] A';  F \<in> stable B;  \<forall>C\<in>CC. C Int B \<in> CC |]  
    ==> F \<in> (A Int B) leadsTo[CC] (A' Int B)"
apply (unfold stable_def)
apply (erule leadsETo_induct)
prefer 3 apply (blast intro: leadsETo_Union_Int)
prefer 2 apply (blast intro: leadsETo_Trans)
apply (rule leadsETo_Basis)
prefer 2 apply (force simp add: Diff_Int_distrib2 [symmetric])
apply (simp add: ensures_def Diff_Int_distrib2 [symmetric] 
                 Int_Un_distrib2 [symmetric])
apply (blast intro: transient_strengthen constrains_Int)
done

lemma e_psp_stable2:
     "[| F \<in> A leadsTo[CC] A'; F \<in> stable B;  \<forall>C\<in>CC. C Int B \<in> CC |]  
      ==> F \<in> (B Int A) leadsTo[CC] (B Int A')"
by (simp (no_asm_simp) add: e_psp_stable Int_ac)

lemma e_psp:
     "[| F \<in> A leadsTo[CC] A'; F \<in> B co B';   
         \<forall>C\<in>CC. C Int B Int B' \<in> CC |]  
      ==> F \<in> (A Int B') leadsTo[CC] ((A' Int B) Un (B' - B))"
apply (erule leadsETo_induct)
prefer 3 apply (blast intro: leadsETo_Union_Int)
(*Transitivity case has a delicate argument involving "cancellation"*)
apply (rule_tac [2] leadsETo_Un_duplicate2)
apply (erule_tac [2] leadsETo_cancel_Diff1)
prefer 2
 apply (simp add: Int_Diff Diff_triv)
 apply (blast intro: leadsETo_weaken_L dest: constrains_imp_subset)
(*Basis case*)
apply (rule leadsETo_Basis)
apply (blast intro: psp_ensures)
apply (subgoal_tac "A Int B' - (Ba Int B Un (B' - B)) = (A - Ba) Int B Int B'")
apply auto
done

lemma e_psp2:
     "[| F \<in> A leadsTo[CC] A'; F \<in> B co B';   
         \<forall>C\<in>CC. C Int B Int B' \<in> CC |]  
      ==> F \<in> (B' Int A) leadsTo[CC] ((B Int A') Un (B' - B))"
by (simp add: e_psp Int_ac)


(*** Special properties involving the parameter [CC] ***)

(*??IS THIS NEEDED?? or is it just an example of what's provable??*)
lemma gen_leadsETo_imp_Join_leadsETo:
     "[| F \<in> (A leadsTo[givenBy v] B);  G \<in> preserves v;   
         F\<squnion>G \<in> stable C |]  
      ==> F\<squnion>G \<in> ((C Int A) leadsTo[(%D. C Int D) ` givenBy v] B)"
apply (erule leadsETo_induct)
  prefer 3
  apply (subst Int_Union) 
  apply (blast intro: leadsETo_UN)
prefer 2
 apply (blast intro: e_psp_stable2 [THEN leadsETo_weaken_L] leadsETo_Trans)
apply (rule leadsETo_Basis)
apply (auto simp add: Diff_eq_empty_iff [THEN iffD2] 
                      Int_Diff ensures_def givenBy_eq_Collect)
prefer 3 apply (blast intro: transient_strengthen)
apply (drule_tac [2] P1 = P in preserves_subset_stable [THEN subsetD])
apply (drule_tac P1 = P in preserves_subset_stable [THEN subsetD])
apply (unfold stable_def)
apply (blast intro: constrains_Int [THEN constrains_weaken])+
done

(**** Relationship with traditional "leadsTo", strong & weak ****)

(** strong **)

lemma leadsETo_subset_leadsTo: "(A leadsTo[CC] B) <= (A leadsTo B)"
apply safe
apply (erule leadsETo_induct)
  prefer 3 apply (blast intro: leadsTo_Union)
 prefer 2 apply (blast intro: leadsTo_Trans, blast)
done

lemma leadsETo_UNIV_eq_leadsTo: "(A leadsTo[UNIV] B) = (A leadsTo B)"
apply safe
apply (erule leadsETo_subset_leadsTo [THEN subsetD])
(*right-to-left case*)
apply (erule leadsTo_induct)
  prefer 3 apply (blast intro: leadsETo_Union)
 prefer 2 apply (blast intro: leadsETo_Trans, blast)
done

(**** weak ****)

lemma LeadsETo_eq_leadsETo: 
     "A LeadsTo[CC] B =  
        {F. F \<in> (reachable F Int A) leadsTo[(%C. reachable F Int C) ` CC]  
        (reachable F Int B)}"
apply (unfold LeadsETo_def)
apply (blast dest: e_psp_stable2 intro: leadsETo_weaken)
done

(*** Introduction rules: Basis, Trans, Union ***)

lemma LeadsETo_Trans:
     "[| F \<in> A LeadsTo[CC] B;  F \<in> B LeadsTo[CC] C |]  
      ==> F \<in> A LeadsTo[CC] C"
apply (simp add: LeadsETo_eq_leadsETo)
apply (blast intro: leadsETo_Trans)
done

lemma LeadsETo_Union:
     "(\<And>A. A \<in> S \<Longrightarrow> F \<in> A LeadsTo[CC] B) \<Longrightarrow> F \<in> (\<Union>S) LeadsTo[CC] B"
apply (simp add: LeadsETo_def)
apply (subst Int_Union)
apply (blast intro: leadsETo_UN)
done

lemma LeadsETo_UN:
     "(\<And>i. i \<in> I \<Longrightarrow> F \<in> (A i) LeadsTo[CC] B)  
      \<Longrightarrow> F \<in> (UN i:I. A i) LeadsTo[CC] B"
apply (blast intro: LeadsETo_Union)
done

(*Binary union introduction rule*)
lemma LeadsETo_Un:
     "[| F \<in> A LeadsTo[CC] C; F \<in> B LeadsTo[CC] C |]  
      ==> F \<in> (A Un B) LeadsTo[CC] C"
  using LeadsETo_Union [of "{A, B}" F CC C] by auto

(*Lets us look at the starting state*)
lemma single_LeadsETo_I:
     "(\<And>s. s \<in> A ==> F \<in> {s} LeadsTo[CC] B) \<Longrightarrow> F \<in> A LeadsTo[CC] B"
by (subst UN_singleton [symmetric], rule LeadsETo_UN, blast)

lemma subset_imp_LeadsETo:
     "A <= B \<Longrightarrow> F \<in> A LeadsTo[CC] B"
apply (simp (no_asm) add: LeadsETo_def)
apply (blast intro: subset_imp_leadsETo)
done

lemmas empty_LeadsETo = empty_subsetI [THEN subset_imp_LeadsETo]

lemma LeadsETo_weaken_R:
     "[| F \<in> A LeadsTo[CC] A';  A' <= B' |] ==> F \<in> A LeadsTo[CC] B'"
apply (simp add: LeadsETo_def)
apply (blast intro: leadsETo_weaken_R)
done

lemma LeadsETo_weaken_L:
     "[| F \<in> A LeadsTo[CC] A';  B <= A |] ==> F \<in> B LeadsTo[CC] A'"
apply (simp add: LeadsETo_def)
apply (blast intro: leadsETo_weaken_L)
done

lemma LeadsETo_weaken:
     "[| F \<in> A LeadsTo[CC'] A';    
         B <= A;  A' <= B';  CC' <= CC |]  
      ==> F \<in> B LeadsTo[CC] B'"
apply (simp (no_asm_use) add: LeadsETo_def)
apply (blast intro: leadsETo_weaken)
done

lemma LeadsETo_subset_LeadsTo: "(A LeadsTo[CC] B) <= (A LeadsTo B)"
apply (unfold LeadsETo_def LeadsTo_def)
apply (blast intro: leadsETo_subset_leadsTo [THEN subsetD])
done

(*Postcondition can be strengthened to (reachable F Int B) *)
lemma reachable_ensures:
     "F \<in> A ensures B \<Longrightarrow> F \<in> (reachable F Int A) ensures B"
apply (rule stable_ensures_Int [THEN ensures_weaken_R], auto)
done

lemma lel_lemma:
     "F \<in> A leadsTo B \<Longrightarrow> F \<in> (reachable F Int A) leadsTo[Pow(reachable F)] B"
apply (erule leadsTo_induct)
  apply (blast intro: reachable_ensures)
 apply (blast dest: e_psp_stable2 intro: leadsETo_Trans leadsETo_weaken_L)
apply (subst Int_Union)
apply (blast intro: leadsETo_UN)
done

lemma LeadsETo_UNIV_eq_LeadsTo: "(A LeadsTo[UNIV] B) = (A LeadsTo B)"
apply safe
apply (erule LeadsETo_subset_LeadsTo [THEN subsetD])
(*right-to-left case*)
apply (unfold LeadsETo_def LeadsTo_def)
apply (blast intro: lel_lemma [THEN leadsETo_weaken])
done


(**** EXTEND/PROJECT PROPERTIES ****)

context Extend
begin

lemma givenBy_o_eq_extend_set:
     "givenBy (v o f) = extend_set h ` (givenBy v)"
apply (simp add: givenBy_eq_Collect)
apply (rule equalityI, best)
apply blast 
done

lemma givenBy_eq_extend_set: "givenBy f = range (extend_set h)"
by (simp add: givenBy_eq_Collect, best)

lemma extend_set_givenBy_I:
     "D \<in> givenBy v ==> extend_set h D \<in> givenBy (v o f)"
apply (simp (no_asm_use) add: givenBy_eq_all, blast)
done

lemma leadsETo_imp_extend_leadsETo:
     "F \<in> A leadsTo[CC] B  
      ==> extend h F \<in> (extend_set h A) leadsTo[extend_set h ` CC]  
                       (extend_set h B)"
apply (erule leadsETo_induct)
  apply (force intro: subset_imp_ensures 
               simp add: extend_ensures extend_set_Diff_distrib [symmetric])
 apply (blast intro: leadsETo_Trans)
apply (simp add: leadsETo_UN extend_set_Union)
done


(*This version's stronger in the "ensures" precondition
  BUT there's no ensures_weaken_L*)
lemma Join_project_ensures_strong:
     "[| project h C G \<notin> transient (project_set h C Int (A-B)) |  
           project_set h C Int (A - B) = {};   
         extend h F\<squnion>G \<in> stable C;   
         F\<squnion>project h C G \<in> (project_set h C Int A) ensures B |]  
      ==> extend h F\<squnion>G \<in> (C Int extend_set h A) ensures (extend_set h B)"
apply (subst Int_extend_set_lemma [symmetric])
apply (rule Join_project_ensures)
apply (auto simp add: Int_Diff)
done

(*NOT WORKING.  MODIFY AS IN Project.thy
lemma pld_lemma:
     "[| extend h F\<squnion>G : stable C;   
         F\<squnion>project h C G : (project_set h C Int A) leadsTo[(%D. project_set h C Int D)`givenBy v] B;   
         G : preserves (v o f) |]  
      ==> extend h F\<squnion>G :  
            (C Int extend_set h (project_set h C Int A))  
            leadsTo[(%D. C Int extend_set h D)`givenBy v]  (extend_set h B)"
apply (erule leadsETo_induct)
  prefer 3
  apply (simp del: UN_simps add: Int_UN_distrib leadsETo_UN extend_set_Union)
 prefer 2
 apply (blast intro: e_psp_stable2 [THEN leadsETo_weaken_L] leadsETo_Trans)
txt{*Base case is hard*}
apply auto
apply (force intro: leadsETo_Basis subset_imp_ensures)
apply (rule leadsETo_Basis)
 prefer 2
 apply (simp add: Int_Diff Int_extend_set_lemma extend_set_Diff_distrib [symmetric])
apply (rule Join_project_ensures_strong)
apply (auto intro: project_stable_project_set simp add: Int_left_absorb)
apply (simp (no_asm_simp) add: stable_ensures_Int [THEN ensures_weaken_R] Int_lower2 project_stable_project_set extend_stable_project_set)
done

lemma project_leadsETo_D_lemma:
     "[| extend h F\<squnion>G : stable C;   
         F\<squnion>project h C G :  
             (project_set h C Int A)  
             leadsTo[(%D. project_set h C Int D)`givenBy v] B;   
         G : preserves (v o f) |]  
      ==> extend h F\<squnion>G : (C Int extend_set h A)  
            leadsTo[(%D. C Int extend_set h D)`givenBy v] (extend_set h B)"
apply (rule pld_lemma [THEN leadsETo_weaken])
apply (auto simp add: split_extended_all)
done

lemma project_leadsETo_D:
     "[| F\<squnion>project h UNIV G : A leadsTo[givenBy v] B;   
         G : preserves (v o f) |]   
      ==> extend h F\<squnion>G : (extend_set h A)  
            leadsTo[givenBy (v o f)] (extend_set h B)"
apply (cut_tac project_leadsETo_D_lemma [of _ _ UNIV], auto) 
apply (erule leadsETo_givenBy)
apply (rule givenBy_o_eq_extend_set [THEN equalityD2])
done

lemma project_LeadsETo_D:
     "[| F\<squnion>project h (reachable (extend h F\<squnion>G)) G  
             : A LeadsTo[givenBy v] B;   
         G : preserves (v o f) |]  
      ==> extend h F\<squnion>G :  
            (extend_set h A) LeadsTo[givenBy (v o f)] (extend_set h B)"
apply (cut_tac subset_refl [THEN stable_reachable, THEN project_leadsETo_D_lemma])
apply (auto simp add: LeadsETo_def)
 apply (erule leadsETo_mono [THEN [2] rev_subsetD])
 apply (blast intro: extend_set_givenBy_I)
apply (simp add: project_set_reachable_extend_eq [symmetric])
done

lemma extending_leadsETo: 
     "(ALL G. extend h F ok G --> G : preserves (v o f))  
      ==> extending (%G. UNIV) h F  
                (extend_set h A leadsTo[givenBy (v o f)] extend_set h B)  
                (A leadsTo[givenBy v] B)"
apply (unfold extending_def)
apply (auto simp add: project_leadsETo_D)
done

lemma extending_LeadsETo: 
     "(ALL G. extend h F ok G --> G : preserves (v o f))  
      ==> extending (%G. reachable (extend h F\<squnion>G)) h F  
                (extend_set h A LeadsTo[givenBy (v o f)] extend_set h B)  
                (A LeadsTo[givenBy v]  B)"
apply (unfold extending_def)
apply (blast intro: project_LeadsETo_D)
done
*)


(*** leadsETo in the precondition ***)

(*Lemma for the Trans case*)
lemma pli_lemma:
     "[| extend h F\<squnion>G \<in> stable C;     
         F\<squnion>project h C G     
           \<in> project_set h C Int project_set h A leadsTo project_set h B |]  
      ==> F\<squnion>project h C G     
            \<in> project_set h C Int project_set h A leadsTo     
              project_set h C Int project_set h B"
apply (rule psp_stable2 [THEN leadsTo_weaken_L])
apply (auto simp add: project_stable_project_set extend_stable_project_set)
done

lemma project_leadsETo_I_lemma:
     "[| extend h F\<squnion>G \<in> stable C;   
         extend h F\<squnion>G \<in>  
           (C Int A) leadsTo[(%D. C Int D)`givenBy f]  B |]   
  ==> F\<squnion>project h C G   
    \<in> (project_set h C Int project_set h (C Int A)) leadsTo (project_set h B)"
apply (erule leadsETo_induct)
  prefer 3
  apply (simp only: Int_UN_distrib project_set_Union)
  apply (blast intro: leadsTo_UN)
 prefer 2 apply (blast intro: leadsTo_Trans pli_lemma)
apply (simp add: givenBy_eq_extend_set)
apply (rule leadsTo_Basis)
apply (blast intro: ensures_extend_set_imp_project_ensures)
done

lemma project_leadsETo_I:
     "extend h F\<squnion>G \<in> (extend_set h A) leadsTo[givenBy f] (extend_set h B)
      \<Longrightarrow> F\<squnion>project h UNIV G \<in> A leadsTo B"
apply (rule project_leadsETo_I_lemma [THEN leadsTo_weaken], auto)
done

lemma project_LeadsETo_I:
     "extend h F\<squnion>G \<in> (extend_set h A) LeadsTo[givenBy f] (extend_set h B) 
      \<Longrightarrow> F\<squnion>project h (reachable (extend h F\<squnion>G)) G   
           \<in> A LeadsTo B"
apply (simp (no_asm_use) add: LeadsTo_def LeadsETo_def)
apply (rule project_leadsETo_I_lemma [THEN leadsTo_weaken])
apply (auto simp add: project_set_reachable_extend_eq [symmetric])
done

lemma projecting_leadsTo: 
     "projecting (\<lambda>G. UNIV) h F  
                 (extend_set h A leadsTo[givenBy f] extend_set h B)  
                 (A leadsTo B)"
apply (unfold projecting_def)
apply (force dest: project_leadsETo_I)
done

lemma projecting_LeadsTo: 
     "projecting (\<lambda>G. reachable (extend h F\<squnion>G)) h F  
                 (extend_set h A LeadsTo[givenBy f] extend_set h B)  
                 (A LeadsTo B)"
apply (unfold projecting_def)
apply (force dest: project_LeadsETo_I)
done

end

end
