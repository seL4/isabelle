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

header{*Progress Under Allowable Sets*}

theory ELT imports Project begin

inductive_set
  (*LEADS-TO constant for the inductive definition*)
  elt :: "['a set set, 'a program] => ('a set * 'a set) set"
  for CC :: "'a set set" and F :: "'a program"
 where

   Basis:  "[| F : A ensures B;  A-B : (insert {} CC) |] ==> (A,B) : elt CC F"

 | Trans:  "[| (A,B) : elt CC F;  (B,C) : elt CC F |] ==> (A,C) : elt CC F"

 | Union:  "ALL A: S. (A,B) : elt CC F ==> (Union S, B) : elt CC F"


definition  
  (*the set of all sets determined by f alone*)
  givenBy :: "['a => 'b] => 'a set set"
  where "givenBy f = range (%B. f-` B)"

definition
  (*visible version of the LEADS-TO relation*)
  leadsETo :: "['a set, 'a set set, 'a set] => 'a program set"
                                        ("(3_/ leadsTo[_]/ _)" [80,0,80] 80)
  where "leadsETo A CC B = {F. (A,B) : elt CC F}"

definition
  LeadsETo :: "['a set, 'a set set, 'a set] => 'a program set"
                                        ("(3_/ LeadsTo[_]/ _)" [80,0,80] 80)
  where "LeadsETo A CC B =
      {F. F : (reachable F Int A) leadsTo[(%C. reachable F Int C) ` CC] B}"


(*** givenBy ***)

lemma givenBy_id [simp]: "givenBy id = UNIV"
by (unfold givenBy_def, auto)

lemma givenBy_eq_all: "(givenBy v) = {A. ALL x:A. ALL y. v x = v y --> y: A}"
apply (unfold givenBy_def, safe)
apply (rule_tac [2] x = "v ` ?u" in image_eqI, auto)
done

lemma givenByI: "(!!x y. [| x:A;  v x = v y |] ==> y: A) ==> A: givenBy v"
by (subst givenBy_eq_all, blast)

lemma givenByD: "[| A: givenBy v;  x:A;  v x = v y |] ==> y: A"
by (unfold givenBy_def, auto)

lemma empty_mem_givenBy [iff]: "{} : givenBy v"
by (blast intro!: givenByI)

lemma givenBy_imp_eq_Collect: "A: givenBy v ==> EX P. A = {s. P(v s)}"
apply (rule_tac x = "%n. EX s. v s = n & s : A" in exI)
apply (simp (no_asm_use) add: givenBy_eq_all)
apply blast
done

lemma Collect_mem_givenBy: "{s. P(v s)} : givenBy v"
by (unfold givenBy_def, best)

lemma givenBy_eq_Collect: "givenBy v = {A. EX P. A = {s. P(v s)}}"
by (blast intro: Collect_mem_givenBy givenBy_imp_eq_Collect)

(*preserving v preserves properties given by v*)
lemma preserves_givenBy_imp_stable:
     "[| F : preserves v;  D : givenBy v |] ==> F : stable D"
by (force simp add: preserves_subset_stable [THEN subsetD] givenBy_eq_Collect)

lemma givenBy_o_subset: "givenBy (w o v) <= givenBy v"
apply (simp (no_asm) add: givenBy_eq_Collect)
apply best 
done

lemma givenBy_DiffI:
     "[| A : givenBy v;  B : givenBy v |] ==> A-B : givenBy v"
apply (simp (no_asm_use) add: givenBy_eq_Collect)
apply safe
apply (rule_tac x = "%z. ?R z & ~ ?Q z" in exI)
unfolding set_diff_eq
apply auto
done


(** Standard leadsTo rules **)

lemma leadsETo_Basis [intro]: 
     "[| F: A ensures B;  A-B: insert {} CC |] ==> F : A leadsTo[CC] B"
apply (unfold leadsETo_def)
apply (blast intro: elt.Basis)
done

lemma leadsETo_Trans: 
     "[| F : A leadsTo[CC] B;  F : B leadsTo[CC] C |] ==> F : A leadsTo[CC] C"
apply (unfold leadsETo_def)
apply (blast intro: elt.Trans)
done


(*Useful with cancellation, disjunction*)
lemma leadsETo_Un_duplicate:
     "F : A leadsTo[CC] (A' Un A') ==> F : A leadsTo[CC] A'"
by (simp add: Un_ac)

lemma leadsETo_Un_duplicate2:
     "F : A leadsTo[CC] (A' Un C Un C) ==> F : A leadsTo[CC] (A' Un C)"
by (simp add: Un_ac)

(*The Union introduction rule as we should have liked to state it*)
lemma leadsETo_Union:
    "(!!A. A : S ==> F : A leadsTo[CC] B) ==> F : (Union S) leadsTo[CC] B"
apply (unfold leadsETo_def)
apply (blast intro: elt.Union)
done

lemma leadsETo_UN:
    "(!!i. i : I ==> F : (A i) leadsTo[CC] B)  
     ==> F : (UN i:I. A i) leadsTo[CC] B"
apply (subst Union_image_eq [symmetric])
apply (blast intro: leadsETo_Union)
done

(*The INDUCTION rule as we should have liked to state it*)
lemma leadsETo_induct:
  "[| F : za leadsTo[CC] zb;   
      !!A B. [| F : A ensures B;  A-B : insert {} CC |] ==> P A B;  
      !!A B C. [| F : A leadsTo[CC] B; P A B; F : B leadsTo[CC] C; P B C |]  
               ==> P A C;  
      !!B S. ALL A:S. F : A leadsTo[CC] B & P A B ==> P (Union S) B  
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
     "[| F : A leadsTo[CC] B;  F : B leadsTo[DD] C |]  
      ==> F : A leadsTo[CC Un DD] C"
by (blast intro: leadsETo_mono [THEN subsetD] leadsETo_Trans)

lemma leadsETo_Union_Int:
 "(!!A. A : S ==> F : (A Int C) leadsTo[CC] B) 
  ==> F : (Union S Int C) leadsTo[CC] B"
apply (unfold leadsETo_def)
apply (simp only: Int_Union_Union)
apply (blast intro: elt.Union)
done

(*Binary union introduction rule*)
lemma leadsETo_Un:
     "[| F : A leadsTo[CC] C; F : B leadsTo[CC] C |] 
      ==> F : (A Un B) leadsTo[CC] C"
  using leadsETo_Union [of "{A, B}" F CC C] by auto

lemma single_leadsETo_I:
     "(!!x. x : A ==> F : {x} leadsTo[CC] B) ==> F : A leadsTo[CC] B"
by (subst UN_singleton [symmetric], rule leadsETo_UN, blast)


lemma subset_imp_leadsETo: "A<=B ==> F : A leadsTo[CC] B"
by (simp add: subset_imp_ensures [THEN leadsETo_Basis] 
              Diff_eq_empty_iff [THEN iffD2])

lemmas empty_leadsETo = empty_subsetI [THEN subset_imp_leadsETo, simp]



(** Weakening laws **)

lemma leadsETo_weaken_R:
     "[| F : A leadsTo[CC] A';  A'<=B' |] ==> F : A leadsTo[CC] B'"
by (blast intro: subset_imp_leadsETo leadsETo_Trans)

lemma leadsETo_weaken_L [rule_format]:
     "[| F : A leadsTo[CC] A'; B<=A |] ==> F : B leadsTo[CC] A'"
by (blast intro: leadsETo_Trans subset_imp_leadsETo)

(*Distributes over binary unions*)
lemma leadsETo_Un_distrib:
     "F : (A Un B) leadsTo[CC] C  =   
      (F : A leadsTo[CC] C & F : B leadsTo[CC] C)"
by (blast intro: leadsETo_Un leadsETo_weaken_L)

lemma leadsETo_UN_distrib:
     "F : (UN i:I. A i) leadsTo[CC] B  =   
      (ALL i : I. F : (A i) leadsTo[CC] B)"
by (blast intro: leadsETo_UN leadsETo_weaken_L)

lemma leadsETo_Union_distrib:
     "F : (Union S) leadsTo[CC] B  =  (ALL A : S. F : A leadsTo[CC] B)"
by (blast intro: leadsETo_Union leadsETo_weaken_L)

lemma leadsETo_weaken:
     "[| F : A leadsTo[CC'] A'; B<=A; A'<=B';  CC' <= CC |]  
      ==> F : B leadsTo[CC] B'"
apply (drule leadsETo_mono [THEN subsetD], assumption)
apply (blast del: subsetCE 
             intro: leadsETo_weaken_R leadsETo_weaken_L leadsETo_Trans)
done

lemma leadsETo_givenBy:
     "[| F : A leadsTo[CC] A';  CC <= givenBy v |]  
      ==> F : A leadsTo[givenBy v] A'"
by (blast intro: leadsETo_weaken)


(*Set difference*)
lemma leadsETo_Diff:
     "[| F : (A-B) leadsTo[CC] C; F : B leadsTo[CC] C |]  
      ==> F : A leadsTo[CC] C"
by (blast intro: leadsETo_Un leadsETo_weaken)


(*Binary union version*)
lemma leadsETo_Un_Un:
     "[| F : A leadsTo[CC] A';  F : B leadsTo[CC] B' |]  
      ==> F : (A Un B) leadsTo[CC] (A' Un B')"
by (blast intro: leadsETo_Un leadsETo_weaken_R)


(** The cancellation law **)

lemma leadsETo_cancel2:
     "[| F : A leadsTo[CC] (A' Un B); F : B leadsTo[CC] B' |]  
      ==> F : A leadsTo[CC] (A' Un B')"
by (blast intro: leadsETo_Un_Un subset_imp_leadsETo leadsETo_Trans)

lemma leadsETo_cancel1:
     "[| F : A leadsTo[CC] (B Un A'); F : B leadsTo[CC] B' |]  
    ==> F : A leadsTo[CC] (B' Un A')"
apply (simp add: Un_commute)
apply (blast intro!: leadsETo_cancel2)
done

lemma leadsETo_cancel_Diff1:
     "[| F : A leadsTo[CC] (B Un A'); F : (B-A') leadsTo[CC] B' |]  
    ==> F : A leadsTo[CC] (B' Un A')"
apply (rule leadsETo_cancel1)
 prefer 2 apply assumption
apply simp_all
done


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
lemma e_psp_stable: 
   "[| F : A leadsTo[CC] A';  F : stable B;  ALL C:CC. C Int B : CC |]  
    ==> F : (A Int B) leadsTo[CC] (A' Int B)"
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
     "[| F : A leadsTo[CC] A'; F : stable B;  ALL C:CC. C Int B : CC |]  
      ==> F : (B Int A) leadsTo[CC] (B Int A')"
by (simp (no_asm_simp) add: e_psp_stable Int_ac)

lemma e_psp:
     "[| F : A leadsTo[CC] A'; F : B co B';   
         ALL C:CC. C Int B Int B' : CC |]  
      ==> F : (A Int B') leadsTo[CC] ((A' Int B) Un (B' - B))"
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
     "[| F : A leadsTo[CC] A'; F : B co B';   
         ALL C:CC. C Int B Int B' : CC |]  
      ==> F : (B' Int A) leadsTo[CC] ((B Int A') Un (B' - B))"
by (simp add: e_psp Int_ac)


(*** Special properties involving the parameter [CC] ***)

(*??IS THIS NEEDED?? or is it just an example of what's provable??*)
lemma gen_leadsETo_imp_Join_leadsETo:
     "[| F: (A leadsTo[givenBy v] B);  G : preserves v;   
         F\<squnion>G : stable C |]  
      ==> F\<squnion>G : ((C Int A) leadsTo[(%D. C Int D) ` givenBy v] B)"
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
        {F. F : (reachable F Int A) leadsTo[(%C. reachable F Int C) ` CC]  
        (reachable F Int B)}"
apply (unfold LeadsETo_def)
apply (blast dest: e_psp_stable2 intro: leadsETo_weaken)
done

(*** Introduction rules: Basis, Trans, Union ***)

lemma LeadsETo_Trans:
     "[| F : A LeadsTo[CC] B;  F : B LeadsTo[CC] C |]  
      ==> F : A LeadsTo[CC] C"
apply (simp add: LeadsETo_eq_leadsETo)
apply (blast intro: leadsETo_Trans)
done

lemma LeadsETo_Union:
     "(!!A. A : S ==> F : A LeadsTo[CC] B) ==> F : (Union S) LeadsTo[CC] B"
apply (simp add: LeadsETo_def)
apply (subst Int_Union)
apply (blast intro: leadsETo_UN)
done

lemma LeadsETo_UN:
     "(!!i. i : I ==> F : (A i) LeadsTo[CC] B)  
      ==> F : (UN i:I. A i) LeadsTo[CC] B"
apply (simp only: Union_image_eq [symmetric])
apply (blast intro: LeadsETo_Union)
done

(*Binary union introduction rule*)
lemma LeadsETo_Un:
     "[| F : A LeadsTo[CC] C; F : B LeadsTo[CC] C |]  
      ==> F : (A Un B) LeadsTo[CC] C"
  using LeadsETo_Union [of "{A, B}" F CC C] by auto

(*Lets us look at the starting state*)
lemma single_LeadsETo_I:
     "(!!s. s : A ==> F : {s} LeadsTo[CC] B) ==> F : A LeadsTo[CC] B"
by (subst UN_singleton [symmetric], rule LeadsETo_UN, blast)

lemma subset_imp_LeadsETo:
     "A <= B ==> F : A LeadsTo[CC] B"
apply (simp (no_asm) add: LeadsETo_def)
apply (blast intro: subset_imp_leadsETo)
done

lemmas empty_LeadsETo = empty_subsetI [THEN subset_imp_LeadsETo]

lemma LeadsETo_weaken_R [rule_format]:
     "[| F : A LeadsTo[CC] A';  A' <= B' |] ==> F : A LeadsTo[CC] B'"
apply (simp (no_asm_use) add: LeadsETo_def)
apply (blast intro: leadsETo_weaken_R)
done

lemma LeadsETo_weaken_L [rule_format]:
     "[| F : A LeadsTo[CC] A';  B <= A |] ==> F : B LeadsTo[CC] A'"
apply (simp (no_asm_use) add: LeadsETo_def)
apply (blast intro: leadsETo_weaken_L)
done

lemma LeadsETo_weaken:
     "[| F : A LeadsTo[CC'] A';    
         B <= A;  A' <= B';  CC' <= CC |]  
      ==> F : B LeadsTo[CC] B'"
apply (simp (no_asm_use) add: LeadsETo_def)
apply (blast intro: leadsETo_weaken)
done

lemma LeadsETo_subset_LeadsTo: "(A LeadsTo[CC] B) <= (A LeadsTo B)"
apply (unfold LeadsETo_def LeadsTo_def)
apply (blast intro: leadsETo_subset_leadsTo [THEN subsetD])
done

(*Postcondition can be strengthened to (reachable F Int B) *)
lemma reachable_ensures:
     "F : A ensures B ==> F : (reachable F Int A) ensures B"
apply (rule stable_ensures_Int [THEN ensures_weaken_R], auto)
done

lemma lel_lemma:
     "F : A leadsTo B ==> F : (reachable F Int A) leadsTo[Pow(reachable F)] B"
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

lemma (in Extend) givenBy_o_eq_extend_set:
     "givenBy (v o f) = extend_set h ` (givenBy v)"
apply (simp add: givenBy_eq_Collect)
apply (rule equalityI, best)
apply blast 
done

lemma (in Extend) givenBy_eq_extend_set: "givenBy f = range (extend_set h)"
by (simp add: givenBy_eq_Collect, best)

lemma (in Extend) extend_set_givenBy_I:
     "D : givenBy v ==> extend_set h D : givenBy (v o f)"
apply (simp (no_asm_use) add: givenBy_eq_all, blast)
done

lemma (in Extend) leadsETo_imp_extend_leadsETo:
     "F : A leadsTo[CC] B  
      ==> extend h F : (extend_set h A) leadsTo[extend_set h ` CC]  
                       (extend_set h B)"
apply (erule leadsETo_induct)
  apply (force intro: subset_imp_ensures 
               simp add: extend_ensures extend_set_Diff_distrib [symmetric])
 apply (blast intro: leadsETo_Trans)
apply (simp add: leadsETo_UN extend_set_Union)
done


(*This version's stronger in the "ensures" precondition
  BUT there's no ensures_weaken_L*)
lemma (in Extend) Join_project_ensures_strong:
     "[| project h C G ~: transient (project_set h C Int (A-B)) |  
           project_set h C Int (A - B) = {};   
         extend h F\<squnion>G : stable C;   
         F\<squnion>project h C G : (project_set h C Int A) ensures B |]  
      ==> extend h F\<squnion>G : (C Int extend_set h A) ensures (extend_set h B)"
apply (subst Int_extend_set_lemma [symmetric])
apply (rule Join_project_ensures)
apply (auto simp add: Int_Diff)
done

(*NOT WORKING.  MODIFY AS IN Project.thy
lemma (in Extend) pld_lemma:
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

lemma (in Extend) project_leadsETo_D_lemma:
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

lemma (in Extend) project_leadsETo_D:
     "[| F\<squnion>project h UNIV G : A leadsTo[givenBy v] B;   
         G : preserves (v o f) |]   
      ==> extend h F\<squnion>G : (extend_set h A)  
            leadsTo[givenBy (v o f)] (extend_set h B)"
apply (cut_tac project_leadsETo_D_lemma [of _ _ UNIV], auto) 
apply (erule leadsETo_givenBy)
apply (rule givenBy_o_eq_extend_set [THEN equalityD2])
done

lemma (in Extend) project_LeadsETo_D:
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

lemma (in Extend) extending_leadsETo: 
     "(ALL G. extend h F ok G --> G : preserves (v o f))  
      ==> extending (%G. UNIV) h F  
                (extend_set h A leadsTo[givenBy (v o f)] extend_set h B)  
                (A leadsTo[givenBy v] B)"
apply (unfold extending_def)
apply (auto simp add: project_leadsETo_D)
done

lemma (in Extend) extending_LeadsETo: 
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
lemma (in Extend) pli_lemma:
     "[| extend h F\<squnion>G : stable C;     
         F\<squnion>project h C G     
           : project_set h C Int project_set h A leadsTo project_set h B |]  
      ==> F\<squnion>project h C G     
            : project_set h C Int project_set h A leadsTo     
              project_set h C Int project_set h B"
apply (rule psp_stable2 [THEN leadsTo_weaken_L])
apply (auto simp add: project_stable_project_set extend_stable_project_set)
done

lemma (in Extend) project_leadsETo_I_lemma:
     "[| extend h F\<squnion>G : stable C;   
         extend h F\<squnion>G :  
           (C Int A) leadsTo[(%D. C Int D)`givenBy f]  B |]   
  ==> F\<squnion>project h C G   
    : (project_set h C Int project_set h (C Int A)) leadsTo (project_set h B)"
apply (erule leadsETo_induct)
  prefer 3
  apply (simp only: Int_UN_distrib project_set_Union)
  apply (blast intro: leadsTo_UN)
 prefer 2 apply (blast intro: leadsTo_Trans pli_lemma)
apply (simp add: givenBy_eq_extend_set)
apply (rule leadsTo_Basis)
apply (blast intro: ensures_extend_set_imp_project_ensures)
done

lemma (in Extend) project_leadsETo_I:
     "extend h F\<squnion>G : (extend_set h A) leadsTo[givenBy f] (extend_set h B)
      ==> F\<squnion>project h UNIV G : A leadsTo B"
apply (rule project_leadsETo_I_lemma [THEN leadsTo_weaken], auto)
done

lemma (in Extend) project_LeadsETo_I:
     "extend h F\<squnion>G : (extend_set h A) LeadsTo[givenBy f] (extend_set h B) 
      ==> F\<squnion>project h (reachable (extend h F\<squnion>G)) G   
           : A LeadsTo B"
apply (simp (no_asm_use) add: LeadsTo_def LeadsETo_def)
apply (rule project_leadsETo_I_lemma [THEN leadsTo_weaken])
apply (auto simp add: project_set_reachable_extend_eq [symmetric])
done

lemma (in Extend) projecting_leadsTo: 
     "projecting (%G. UNIV) h F  
                 (extend_set h A leadsTo[givenBy f] extend_set h B)  
                 (A leadsTo B)"
apply (unfold projecting_def)
apply (force dest: project_leadsETo_I)
done

lemma (in Extend) projecting_LeadsTo: 
     "projecting (%G. reachable (extend h F\<squnion>G)) h F  
                 (extend_set h A LeadsTo[givenBy f] extend_set h B)  
                 (A LeadsTo B)"
apply (unfold projecting_def)
apply (force dest: project_LeadsETo_I)
done

end
