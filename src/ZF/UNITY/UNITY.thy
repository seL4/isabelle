(*  Title:      ZF/UNITY/UNITY.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge
*)

section \<open>The Basic UNITY Theory\<close>

theory UNITY imports State begin

text\<open>The basic UNITY theory (revised version, based upon the "co" operator)
From Misra, "A Logic for Concurrent Programming", 1994.

This ZF theory was ported from its HOL equivalent.\<close>

definition
  program  :: i  where
  "program == {<init, acts, allowed>:
               Pow(state) * Pow(Pow(state*state)) * Pow(Pow(state*state)).
               id(state) \<in> acts & id(state) \<in> allowed}"

definition
  mk_program :: "[i,i,i]=>i"  where
  \<comment> \<open>The definition yields a program thanks to the coercions
       init \<inter> state, acts \<inter> Pow(state*state), etc.\<close>
  "mk_program(init, acts, allowed) ==
    <init \<inter> state, cons(id(state), acts \<inter> Pow(state*state)),
              cons(id(state), allowed \<inter> Pow(state*state))>"

definition
  SKIP :: i  (\<open>\<bottom>\<close>) where
  "SKIP == mk_program(state, 0, Pow(state*state))"

  (* Coercion from anything to program *)
definition
  programify :: "i=>i"  where
  "programify(F) == if F \<in> program then F else SKIP"

definition
  RawInit :: "i=>i"  where
  "RawInit(F) == fst(F)"

definition
  Init :: "i=>i"  where
  "Init(F) == RawInit(programify(F))"

definition
  RawActs :: "i=>i"  where
  "RawActs(F) == cons(id(state), fst(snd(F)))"

definition
  Acts :: "i=>i"  where
  "Acts(F) == RawActs(programify(F))"

definition
  RawAllowedActs :: "i=>i"  where
  "RawAllowedActs(F) == cons(id(state), snd(snd(F)))"

definition
  AllowedActs :: "i=>i"  where
  "AllowedActs(F) == RawAllowedActs(programify(F))"


definition
  Allowed :: "i =>i"  where
  "Allowed(F) == {G \<in> program. Acts(G) \<subseteq> AllowedActs(F)}"

definition
  initially :: "i=>i"  where
  "initially(A) == {F \<in> program. Init(F)\<subseteq>A}"

definition "constrains" :: "[i, i] => i"  (infixl \<open>co\<close> 60)  where
  "A co B == {F \<in> program. (\<forall>act \<in> Acts(F). act``A\<subseteq>B) & st_set(A)}"
    \<comment> \<open>the condition \<^term>\<open>st_set(A)\<close> makes the definition slightly
         stronger than the HOL one\<close>

definition unless :: "[i, i] => i"  (infixl \<open>unless\<close> 60)  where
  "A unless B == (A - B) co (A \<union> B)"

definition
  stable     :: "i=>i"  where
   "stable(A) == A co A"

definition
  strongest_rhs :: "[i, i] => i"  where
  "strongest_rhs(F, A) == \<Inter>({B \<in> Pow(state). F \<in> A co B})"

definition
  invariant :: "i => i"  where
  "invariant(A) == initially(A) \<inter> stable(A)"

  (* meta-function composition *)
definition
  metacomp :: "[i=>i, i=>i] => (i=>i)" (infixl \<open>comp\<close> 65)  where
  "f comp g == %x. f(g(x))"

definition
  pg_compl :: "i=>i"  where
  "pg_compl(X)== program - X"

text\<open>SKIP\<close>
lemma SKIP_in_program [iff,TC]: "SKIP \<in> program"
by (force simp add: SKIP_def program_def mk_program_def)


subsection\<open>The function \<^term>\<open>programify\<close>, the coercion from anything to
 program\<close>

lemma programify_program [simp]: "F \<in> program ==> programify(F)=F"
by (force simp add: programify_def) 

lemma programify_in_program [iff,TC]: "programify(F) \<in> program"
by (force simp add: programify_def) 

text\<open>Collapsing rules: to remove programify from expressions\<close>
lemma programify_idem [simp]: "programify(programify(F))=programify(F)"
by (force simp add: programify_def) 

lemma Init_programify [simp]: "Init(programify(F)) = Init(F)"
by (simp add: Init_def)

lemma Acts_programify [simp]: "Acts(programify(F)) = Acts(F)"
by (simp add: Acts_def)

lemma AllowedActs_programify [simp]:
     "AllowedActs(programify(F)) = AllowedActs(F)"
by (simp add: AllowedActs_def)

subsection\<open>The Inspectors for Programs\<close>

lemma id_in_RawActs: "F \<in> program ==>id(state) \<in> RawActs(F)"
by (auto simp add: program_def RawActs_def)

lemma id_in_Acts [iff,TC]: "id(state) \<in> Acts(F)"
by (simp add: id_in_RawActs Acts_def)

lemma id_in_RawAllowedActs: "F \<in> program ==>id(state) \<in> RawAllowedActs(F)"
by (auto simp add: program_def RawAllowedActs_def)

lemma id_in_AllowedActs [iff,TC]: "id(state) \<in> AllowedActs(F)"
by (simp add: id_in_RawAllowedActs AllowedActs_def)

lemma cons_id_Acts [simp]: "cons(id(state), Acts(F)) = Acts(F)"
by (simp add: cons_absorb)

lemma cons_id_AllowedActs [simp]:
     "cons(id(state), AllowedActs(F)) = AllowedActs(F)"
by (simp add: cons_absorb)


subsection\<open>Types of the Inspectors\<close>

lemma RawInit_type: "F \<in> program ==> RawInit(F)\<subseteq>state"
by (auto simp add: program_def RawInit_def)

lemma RawActs_type: "F \<in> program ==> RawActs(F)\<subseteq>Pow(state*state)"
by (auto simp add: program_def RawActs_def)

lemma RawAllowedActs_type:
     "F \<in> program ==> RawAllowedActs(F)\<subseteq>Pow(state*state)"
by (auto simp add: program_def RawAllowedActs_def)

lemma Init_type: "Init(F)\<subseteq>state"
by (simp add: RawInit_type Init_def)

lemmas InitD = Init_type [THEN subsetD]

lemma st_set_Init [iff]: "st_set(Init(F))"
apply (unfold st_set_def)
apply (rule Init_type)
done

lemma Acts_type: "Acts(F)\<subseteq>Pow(state*state)"
by (simp add: RawActs_type Acts_def)

lemma AllowedActs_type: "AllowedActs(F) \<subseteq> Pow(state*state)"
by (simp add: RawAllowedActs_type AllowedActs_def)

text\<open>Needed in Behaviors\<close>
lemma ActsD: "[| act \<in> Acts(F); <s,s'> \<in> act |] ==> s \<in> state & s' \<in> state"
by (blast dest: Acts_type [THEN subsetD])

lemma AllowedActsD:
     "[| act \<in> AllowedActs(F); <s,s'> \<in> act |] ==> s \<in> state & s' \<in> state"
by (blast dest: AllowedActs_type [THEN subsetD])

subsection\<open>Simplification rules involving \<^term>\<open>state\<close>, \<^term>\<open>Init\<close>, 
  \<^term>\<open>Acts\<close>, and \<^term>\<open>AllowedActs\<close>\<close>

text\<open>But are they really needed?\<close>

lemma state_subset_is_Init_iff [iff]: "state \<subseteq> Init(F) \<longleftrightarrow> Init(F)=state"
by (cut_tac F = F in Init_type, auto)

lemma Pow_state_times_state_is_subset_Acts_iff [iff]:
     "Pow(state*state) \<subseteq> Acts(F) \<longleftrightarrow> Acts(F)=Pow(state*state)"
by (cut_tac F = F in Acts_type, auto)

lemma Pow_state_times_state_is_subset_AllowedActs_iff [iff]:
     "Pow(state*state) \<subseteq> AllowedActs(F) \<longleftrightarrow> AllowedActs(F)=Pow(state*state)"
by (cut_tac F = F in AllowedActs_type, auto)

subsubsection\<open>Eliminating \<open>\<inter> state\<close> from expressions\<close>

lemma Init_Int_state [simp]: "Init(F) \<inter> state = Init(F)"
by (cut_tac F = F in Init_type, blast)

lemma state_Int_Init [simp]: "state \<inter> Init(F) = Init(F)"
by (cut_tac F = F in Init_type, blast)

lemma Acts_Int_Pow_state_times_state [simp]:
     "Acts(F) \<inter> Pow(state*state) = Acts(F)"
by (cut_tac F = F in Acts_type, blast)

lemma state_times_state_Int_Acts [simp]:
     "Pow(state*state) \<inter> Acts(F) = Acts(F)"
by (cut_tac F = F in Acts_type, blast)

lemma AllowedActs_Int_Pow_state_times_state [simp]:
     "AllowedActs(F) \<inter> Pow(state*state) = AllowedActs(F)"
by (cut_tac F = F in AllowedActs_type, blast)

lemma state_times_state_Int_AllowedActs [simp]:
     "Pow(state*state) \<inter> AllowedActs(F) = AllowedActs(F)"
by (cut_tac F = F in AllowedActs_type, blast)


subsubsection\<open>The Operator \<^term>\<open>mk_program\<close>\<close>

lemma mk_program_in_program [iff,TC]:
     "mk_program(init, acts, allowed) \<in> program"
by (auto simp add: mk_program_def program_def)

lemma RawInit_eq [simp]:
     "RawInit(mk_program(init, acts, allowed)) = init \<inter> state"
by (auto simp add: mk_program_def RawInit_def)

lemma RawActs_eq [simp]:
     "RawActs(mk_program(init, acts, allowed)) = 
      cons(id(state), acts \<inter> Pow(state*state))"
by (auto simp add: mk_program_def RawActs_def)

lemma RawAllowedActs_eq [simp]:
     "RawAllowedActs(mk_program(init, acts, allowed)) =
      cons(id(state), allowed \<inter> Pow(state*state))"
by (auto simp add: mk_program_def RawAllowedActs_def)

lemma Init_eq [simp]: "Init(mk_program(init, acts, allowed)) = init \<inter> state"
by (simp add: Init_def)

lemma Acts_eq [simp]:
     "Acts(mk_program(init, acts, allowed)) = 
      cons(id(state), acts  \<inter> Pow(state*state))"
by (simp add: Acts_def)

lemma AllowedActs_eq [simp]:
     "AllowedActs(mk_program(init, acts, allowed))=
      cons(id(state), allowed \<inter> Pow(state*state))"
by (simp add: AllowedActs_def)

text\<open>Init, Acts, and AlowedActs  of SKIP\<close>

lemma RawInit_SKIP [simp]: "RawInit(SKIP) = state"
by (simp add: SKIP_def)

lemma RawAllowedActs_SKIP [simp]: "RawAllowedActs(SKIP) = Pow(state*state)"
by (force simp add: SKIP_def)

lemma RawActs_SKIP [simp]: "RawActs(SKIP) = {id(state)}"
by (force simp add: SKIP_def)

lemma Init_SKIP [simp]: "Init(SKIP) = state"
by (force simp add: SKIP_def)

lemma Acts_SKIP [simp]: "Acts(SKIP) = {id(state)}"
by (force simp add: SKIP_def)

lemma AllowedActs_SKIP [simp]: "AllowedActs(SKIP) = Pow(state*state)"
by (force simp add: SKIP_def)

text\<open>Equality of UNITY programs\<close>

lemma raw_surjective_mk_program:
     "F \<in> program ==> mk_program(RawInit(F), RawActs(F), RawAllowedActs(F))=F"
apply (auto simp add: program_def mk_program_def RawInit_def RawActs_def
            RawAllowedActs_def, blast+)
done

lemma surjective_mk_program [simp]:
  "mk_program(Init(F), Acts(F), AllowedActs(F)) = programify(F)"
by (auto simp add: raw_surjective_mk_program Init_def Acts_def AllowedActs_def)

lemma program_equalityI:                             
    "[|Init(F) = Init(G); Acts(F) = Acts(G);
       AllowedActs(F) = AllowedActs(G); F \<in> program; G \<in> program |] ==> F = G"
apply (subgoal_tac "programify(F) = programify(G)") 
apply simp 
apply (simp only: surjective_mk_program [symmetric]) 
done

lemma program_equalityE:                             
 "[|F = G;
    [|Init(F) = Init(G); Acts(F) = Acts(G); AllowedActs(F) = AllowedActs(G) |]
    ==> P |] 
  ==> P"
by force


lemma program_equality_iff:
    "[| F \<in> program; G \<in> program |] ==>(F=G)  \<longleftrightarrow>
     (Init(F) = Init(G) & Acts(F) = Acts(G) & AllowedActs(F) = AllowedActs(G))"
by (blast intro: program_equalityI program_equalityE)

subsection\<open>These rules allow "lazy" definition expansion\<close>

lemma def_prg_Init:
     "F == mk_program (init,acts,allowed) ==> Init(F) = init \<inter> state"
by auto

lemma def_prg_Acts:
     "F == mk_program (init,acts,allowed)
      ==> Acts(F) = cons(id(state), acts \<inter> Pow(state*state))"
by auto

lemma def_prg_AllowedActs:
     "F == mk_program (init,acts,allowed)
      ==> AllowedActs(F) = cons(id(state), allowed \<inter> Pow(state*state))"
by auto

lemma def_prg_simps:
    "[| F == mk_program (init,acts,allowed) |]
     ==> Init(F) = init \<inter> state & 
         Acts(F) = cons(id(state), acts \<inter> Pow(state*state)) &
         AllowedActs(F) = cons(id(state), allowed \<inter> Pow(state*state))"
by auto


text\<open>An action is expanded only if a pair of states is being tested against it\<close>
lemma def_act_simp:
     "[| act == {<s,s'> \<in> A*B. P(s, s')} |]
      ==> (<s,s'> \<in> act) \<longleftrightarrow> (<s,s'> \<in> A*B & P(s, s'))"
by auto

text\<open>A set is expanded only if an element is being tested against it\<close>
lemma def_set_simp: "A == B ==> (x \<in> A) \<longleftrightarrow> (x \<in> B)"
by auto


subsection\<open>The Constrains Operator\<close>

lemma constrains_type: "A co B \<subseteq> program"
by (force simp add: constrains_def)

lemma constrainsI:
    "[|(!!act s s'. [| act: Acts(F);  <s,s'> \<in> act; s \<in> A|] ==> s' \<in> A');
        F \<in> program; st_set(A) |]  ==> F \<in> A co A'"
by (force simp add: constrains_def)

lemma constrainsD:
   "F \<in> A co B ==> \<forall>act \<in> Acts(F). act``A\<subseteq>B"
by (force simp add: constrains_def)

lemma constrainsD2: "F \<in> A co B ==> F \<in> program & st_set(A)"
by (force simp add: constrains_def)

lemma constrains_empty [iff]: "F \<in> 0 co B \<longleftrightarrow> F \<in> program"
by (force simp add: constrains_def st_set_def)

lemma constrains_empty2 [iff]: "(F \<in> A co 0) \<longleftrightarrow> (A=0 & F \<in> program)"
by (force simp add: constrains_def st_set_def)

lemma constrains_state [iff]: "(F \<in> state co B) \<longleftrightarrow> (state\<subseteq>B & F \<in> program)"
apply (cut_tac F = F in Acts_type)
apply (force simp add: constrains_def st_set_def)
done

lemma constrains_state2 [iff]: "F \<in> A co state \<longleftrightarrow> (F \<in> program & st_set(A))"
apply (cut_tac F = F in Acts_type)
apply (force simp add: constrains_def st_set_def)
done

text\<open>monotonic in 2nd argument\<close>
lemma constrains_weaken_R:
    "[| F \<in> A co A'; A'\<subseteq>B' |] ==> F \<in> A co B'"
apply (unfold constrains_def, blast)
done

text\<open>anti-monotonic in 1st argument\<close>
lemma constrains_weaken_L:
    "[| F \<in> A co A'; B\<subseteq>A |] ==> F \<in> B co A'"
apply (unfold constrains_def st_set_def, blast)
done

lemma constrains_weaken:
   "[| F \<in> A co A'; B\<subseteq>A; A'\<subseteq>B' |] ==> F \<in> B co B'"
apply (drule constrains_weaken_R)
apply (drule_tac [2] constrains_weaken_L, blast+)
done


subsection\<open>Constrains and Union\<close>

lemma constrains_Un:
    "[| F \<in> A co A'; F \<in> B co B' |] ==> F \<in> (A \<union> B) co (A' \<union> B')"
by (auto simp add: constrains_def st_set_def, force)

lemma constrains_UN:
     "[|!!i. i \<in> I ==> F \<in> A(i) co A'(i); F \<in> program |]
      ==> F \<in> (\<Union>i \<in> I. A(i)) co (\<Union>i \<in> I. A'(i))"
by (force simp add: constrains_def st_set_def) 

lemma constrains_Un_distrib:
     "(A \<union> B) co C = (A co C) \<inter> (B co C)"
by (force simp add: constrains_def st_set_def)

lemma constrains_UN_distrib:
   "i \<in> I ==> (\<Union>i \<in> I. A(i)) co B = (\<Inter>i \<in> I. A(i) co B)"
by (force simp add: constrains_def st_set_def)


subsection\<open>Constrains and Intersection\<close>

lemma constrains_Int_distrib: "C co (A \<inter> B) = (C co A) \<inter> (C co B)"
by (force simp add: constrains_def st_set_def)

lemma constrains_INT_distrib:
     "x \<in> I ==> A co (\<Inter>i \<in> I. B(i)) = (\<Inter>i \<in> I. A co B(i))"
by (force simp add: constrains_def st_set_def)

lemma constrains_Int:
    "[| F \<in> A co A'; F \<in> B co B' |] ==> F \<in> (A \<inter> B) co (A' \<inter> B')"
by (force simp add: constrains_def st_set_def)

lemma constrains_INT [rule_format]:
     "[| \<forall>i \<in> I. F \<in> A(i) co A'(i); F \<in> program|]
      ==> F \<in> (\<Inter>i \<in> I. A(i)) co (\<Inter>i \<in> I. A'(i))"
apply (case_tac "I=0")
 apply (simp add: Inter_def)
apply (erule not_emptyE)
apply (auto simp add: constrains_def st_set_def, blast) 
apply (drule bspec, assumption, force) 
done

(* The rule below simulates the HOL's one for (\<Inter>z. A i) co (\<Inter>z. B i) *)
lemma constrains_All:
"[| \<forall>z. F:{s \<in> state. P(s, z)} co {s \<in> state. Q(s, z)}; F \<in> program |]==>
    F:{s \<in> state. \<forall>z. P(s, z)} co {s \<in> state. \<forall>z. Q(s, z)}"
by (unfold constrains_def, blast)

lemma constrains_imp_subset:
  "[| F \<in> A co A' |] ==> A \<subseteq> A'"
by (unfold constrains_def st_set_def, force)

text\<open>The reasoning is by subsets since "co" refers to single actions
  only.  So this rule isn't that useful.\<close>

lemma constrains_trans: "[| F \<in> A co B; F \<in> B co C |] ==> F \<in> A co C"
by (unfold constrains_def st_set_def, auto, blast)

lemma constrains_cancel:
"[| F \<in> A co (A' \<union> B); F \<in> B co B' |] ==> F \<in> A co (A' \<union> B')"
apply (drule_tac A = B in constrains_imp_subset)
apply (blast intro: constrains_weaken_R)
done


subsection\<open>The Unless Operator\<close>

lemma unless_type: "A unless B \<subseteq> program"
by (force simp add: unless_def constrains_def) 

lemma unlessI: "[| F \<in> (A-B) co (A \<union> B) |] ==> F \<in> A unless B"
apply (unfold unless_def)
apply (blast dest: constrainsD2)
done

lemma unlessD: "F :A unless B ==> F \<in> (A-B) co (A \<union> B)"
by (unfold unless_def, auto)


subsection\<open>The Operator \<^term>\<open>initially\<close>\<close>

lemma initially_type: "initially(A) \<subseteq> program"
by (unfold initially_def, blast)

lemma initiallyI: "[| F \<in> program; Init(F)\<subseteq>A |] ==> F \<in> initially(A)"
by (unfold initially_def, blast)

lemma initiallyD: "F \<in> initially(A) ==> Init(F)\<subseteq>A"
by (unfold initially_def, blast)


subsection\<open>The Operator \<^term>\<open>stable\<close>\<close>

lemma stable_type: "stable(A)\<subseteq>program"
by (unfold stable_def constrains_def, blast)

lemma stableI: "F \<in> A co A ==> F \<in> stable(A)"
by (unfold stable_def, assumption)

lemma stableD: "F \<in> stable(A) ==> F \<in> A co A"
by (unfold stable_def, assumption)

lemma stableD2: "F \<in> stable(A) ==> F \<in> program & st_set(A)"
by (unfold stable_def constrains_def, auto)

lemma stable_state [simp]: "stable(state) = program"
by (auto simp add: stable_def constrains_def dest: Acts_type [THEN subsetD])


lemma stable_unless: "stable(A)= A unless 0"
by (auto simp add: unless_def stable_def)


subsection\<open>Union and Intersection with \<^term>\<open>stable\<close>\<close>

lemma stable_Un:
    "[| F \<in> stable(A); F \<in> stable(A') |] ==> F \<in> stable(A \<union> A')"
apply (unfold stable_def)
apply (blast intro: constrains_Un)
done

lemma stable_UN:
     "[|!!i. i\<in>I ==> F \<in> stable(A(i)); F \<in> program |] 
      ==> F \<in> stable (\<Union>i \<in> I. A(i))"
apply (unfold stable_def)
apply (blast intro: constrains_UN)
done

lemma stable_Int:
    "[| F \<in> stable(A);  F \<in> stable(A') |] ==> F \<in> stable (A \<inter> A')"
apply (unfold stable_def)
apply (blast intro: constrains_Int)
done

lemma stable_INT:
     "[| !!i. i \<in> I ==> F \<in> stable(A(i)); F \<in> program |]
      ==> F \<in> stable (\<Inter>i \<in> I. A(i))"
apply (unfold stable_def)
apply (blast intro: constrains_INT)
done

lemma stable_All:
    "[|\<forall>z. F \<in> stable({s \<in> state. P(s, z)}); F \<in> program|]
     ==> F \<in> stable({s \<in> state. \<forall>z. P(s, z)})"
apply (unfold stable_def)
apply (rule constrains_All, auto)
done

lemma stable_constrains_Un:
     "[| F \<in> stable(C); F \<in> A co (C \<union> A') |] ==> F \<in> (C \<union> A) co (C \<union> A')"
apply (unfold stable_def constrains_def st_set_def, auto)
apply (blast dest!: bspec)
done

lemma stable_constrains_Int:
     "[| F \<in> stable(C); F \<in>  (C \<inter> A) co A' |] ==> F \<in> (C \<inter> A) co (C \<inter> A')"
by (unfold stable_def constrains_def st_set_def, blast)

(* [| F \<in> stable(C); F  \<in> (C \<inter> A) co A |] ==> F \<in> stable(C \<inter> A) *)
lemmas stable_constrains_stable = stable_constrains_Int [THEN stableI]

subsection\<open>The Operator \<^term>\<open>invariant\<close>\<close>

lemma invariant_type: "invariant(A) \<subseteq> program"
apply (unfold invariant_def)
apply (blast dest: stable_type [THEN subsetD])
done

lemma invariantI: "[| Init(F)\<subseteq>A;  F \<in> stable(A) |] ==> F \<in> invariant(A)"
apply (unfold invariant_def initially_def)
apply (frule stable_type [THEN subsetD], auto)
done

lemma invariantD: "F \<in> invariant(A) ==> Init(F)\<subseteq>A & F \<in> stable(A)"
by (unfold invariant_def initially_def, auto)

lemma invariantD2: "F \<in> invariant(A) ==> F \<in> program & st_set(A)"
apply (unfold invariant_def)
apply (blast dest: stableD2)
done

text\<open>Could also say
      \<^term>\<open>invariant(A) \<inter> invariant(B) \<subseteq> invariant (A \<inter> B)\<close>\<close>
lemma invariant_Int:
  "[| F \<in> invariant(A);  F \<in> invariant(B) |] ==> F \<in> invariant(A \<inter> B)"
apply (unfold invariant_def initially_def)
apply (simp add: stable_Int, blast)
done


subsection\<open>The Elimination Theorem\<close>

(** The "free" m has become universally quantified!
 Should the premise be !!m instead of \<forall>m ? Would make it harder
 to use in forward proof. **)

text\<open>The general case is easier to prove than the special case!\<close>
lemma "elimination":
    "[| \<forall>m \<in> M. F \<in> {s \<in> A. x(s) = m} co B(m); F \<in> program  |]
     ==> F \<in> {s \<in> A. x(s) \<in> M} co (\<Union>m \<in> M. B(m))"
by (auto simp add: constrains_def st_set_def, blast)

text\<open>As above, but for the special case of A=state\<close>
lemma elimination2:
     "[| \<forall>m \<in> M. F \<in> {s \<in> state. x(s) = m} co B(m); F \<in> program  |]
     ==> F:{s \<in> state. x(s) \<in> M} co (\<Union>m \<in> M. B(m))"
by (rule UNITY.elimination, auto)

subsection\<open>The Operator \<^term>\<open>strongest_rhs\<close>\<close>

lemma constrains_strongest_rhs:
    "[| F \<in> program; st_set(A) |] ==> F \<in> A co (strongest_rhs(F,A))"
by (auto simp add: constrains_def strongest_rhs_def st_set_def
              dest: Acts_type [THEN subsetD])

lemma strongest_rhs_is_strongest:
     "[| F \<in> A co B; st_set(B) |] ==> strongest_rhs(F,A) \<subseteq> B"
by (auto simp add: constrains_def strongest_rhs_def st_set_def)

ML \<open>
fun simp_of_act def = def RS @{thm def_act_simp};
fun simp_of_set def = def RS @{thm def_set_simp};
\<close>

end
