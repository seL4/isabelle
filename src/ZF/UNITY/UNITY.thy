(*  Title:      ZF/UNITY/UNITY.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)
From Misra, "A Logic for Concurrent Programming", 1994

Theory ported from HOL.
*)

header {*The Basic UNITY Theory*}

theory UNITY = State:
consts
  constrains :: "[i, i] => i"  (infixl "co"     60)
  op_unless  :: "[i, i] => i"  (infixl "unless" 60)

constdefs
   program  :: i
  "program == {<init, acts, allowed>:
	       Pow(state) * Pow(Pow(state*state)) * Pow(Pow(state*state)).
	       id(state) \<in> acts & id(state) \<in> allowed}"

  mk_program :: "[i,i,i]=>i"
  --{* The definition yields a program thanks to the coercions
       init \<inter> state, acts \<inter> Pow(state*state), etc. *}
  "mk_program(init, acts, allowed) ==
    <init \<inter> state, cons(id(state), acts \<inter> Pow(state*state)),
              cons(id(state), allowed \<inter> Pow(state*state))>"

  SKIP :: i
  "SKIP == mk_program(state, 0, Pow(state*state))"

  (* Coercion from anything to program *)
  programify :: "i=>i"
  "programify(F) == if F \<in> program then F else SKIP"

  RawInit :: "i=>i"
  "RawInit(F) == fst(F)"

  Init :: "i=>i"
  "Init(F) == RawInit(programify(F))"

  RawActs :: "i=>i"
  "RawActs(F) == cons(id(state), fst(snd(F)))"

  Acts :: "i=>i"
  "Acts(F) == RawActs(programify(F))"

  RawAllowedActs :: "i=>i"
  "RawAllowedActs(F) == cons(id(state), snd(snd(F)))"

  AllowedActs :: "i=>i"
  "AllowedActs(F) == RawAllowedActs(programify(F))"


  Allowed :: "i =>i"
  "Allowed(F) == {G \<in> program. Acts(G) \<subseteq> AllowedActs(F)}"

  initially :: "i=>i"
  "initially(A) == {F \<in> program. Init(F)\<subseteq>A}"

  stable     :: "i=>i"
   "stable(A) == A co A"

  strongest_rhs :: "[i, i] => i"
  "strongest_rhs(F, A) == Inter({B \<in> Pow(state). F \<in> A co B})"

  invariant :: "i => i"
  "invariant(A) == initially(A) \<inter> stable(A)"

  (* meta-function composition *)
  metacomp :: "[i=>i, i=>i] => (i=>i)" (infixl "comp" 65)
  "f comp g == %x. f(g(x))"

  pg_compl :: "i=>i"
  "pg_compl(X)== program - X"

defs
  constrains_def:
     "A co B == {F \<in> program. (\<forall>act \<in> Acts(F). act``A\<subseteq>B) & st_set(A)}"
    --{* the condition @{term "st_set(A)"} makes the definition slightly
         stronger than the HOL one *}

  unless_def:    "A unless B == (A - B) co (A Un B)"


(** SKIP **)
lemma SKIP_in_program [iff,TC]: "SKIP \<in> program"
by (force simp add: SKIP_def program_def mk_program_def)


subsection{*The function @{term programify}, the coercion from anything to
 program*}

lemma programify_program [simp]: "F \<in> program ==> programify(F)=F"
by (force simp add: programify_def) 

lemma programify_in_program [iff,TC]: "programify(F) \<in> program"
by (force simp add: programify_def) 

(** Collapsing rules: to remove programify from expressions **)
lemma programify_idem [simp]: "programify(programify(F))=programify(F)"
by (force simp add: programify_def) 

lemma Init_programify [simp]: "Init(programify(F)) = Init(F)"
by (simp add: Init_def)

lemma Acts_programify [simp]: "Acts(programify(F)) = Acts(F)"
by (simp add: Acts_def)

lemma AllowedActs_programify [simp]:
     "AllowedActs(programify(F)) = AllowedActs(F)"
by (simp add: AllowedActs_def)

subsection{*The Inspectors for Programs*}

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


subsection{*Types of the Inspectors*}

lemma RawInit_type: "F \<in> program ==> RawInit(F)\<subseteq>state"
by (auto simp add: program_def RawInit_def)

lemma RawActs_type: "F \<in> program ==> RawActs(F)\<subseteq>Pow(state*state)"
by (auto simp add: program_def RawActs_def)

lemma RawAllowedActs_type:
     "F \<in> program ==> RawAllowedActs(F)\<subseteq>Pow(state*state)"
by (auto simp add: program_def RawAllowedActs_def)

lemma Init_type: "Init(F)\<subseteq>state"
by (simp add: RawInit_type Init_def)

lemmas InitD = Init_type [THEN subsetD, standard]

lemma st_set_Init [iff]: "st_set(Init(F))"
apply (unfold st_set_def)
apply (rule Init_type)
done

lemma Acts_type: "Acts(F)\<subseteq>Pow(state*state)"
by (simp add: RawActs_type Acts_def)

lemma AllowedActs_type: "AllowedActs(F) \<subseteq> Pow(state*state)"
by (simp add: RawAllowedActs_type AllowedActs_def)

(* Needed in Behaviors *)
lemma ActsD: "[| act \<in> Acts(F); <s,s'> \<in> act |] ==> s \<in> state & s' \<in> state"
by (blast dest: Acts_type [THEN subsetD])

lemma AllowedActsD:
     "[| act \<in> AllowedActs(F); <s,s'> \<in> act |] ==> s \<in> state & s' \<in> state"
by (blast dest: AllowedActs_type [THEN subsetD])

subsection{*Simplification rules involving @{term state}, @{term Init}, 
  @{term Acts}, and @{term AllowedActs}*}

text{*But are they really needed?*}

lemma state_subset_is_Init_iff [iff]: "state \<subseteq> Init(F) <-> Init(F)=state"
by (cut_tac F = F in Init_type, auto)

lemma Pow_state_times_state_is_subset_Acts_iff [iff]:
     "Pow(state*state) \<subseteq> Acts(F) <-> Acts(F)=Pow(state*state)"
by (cut_tac F = F in Acts_type, auto)

lemma Pow_state_times_state_is_subset_AllowedActs_iff [iff]:
     "Pow(state*state) \<subseteq> AllowedActs(F) <-> AllowedActs(F)=Pow(state*state)"
by (cut_tac F = F in AllowedActs_type, auto)

subsubsection{*Eliminating @{text "\<inter> state"} from expressions*}

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


subsubsection{*The Opoerator @{term mk_program}*}

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

(**Init, Acts, and AlowedActs  of SKIP **)

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

(** Equality of UNITY programs **)

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
    "[| F \<in> program; G \<in> program |] ==>(F=G)  <->
     (Init(F) = Init(G) & Acts(F) = Acts(G) & AllowedActs(F) = AllowedActs(G))"
by (blast intro: program_equalityI program_equalityE)

subsection{*These rules allow "lazy" definition expansion*}

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


(*An action is expanded only if a pair of states is being tested against it*)
lemma def_act_simp:
     "[| act == {<s,s'> \<in> A*B. P(s, s')} |]
      ==> (<s,s'> \<in> act) <-> (<s,s'> \<in> A*B & P(s, s'))"
by auto

(*A set is expanded only if an element is being tested against it*)
lemma def_set_simp: "A == B ==> (x \<in> A) <-> (x \<in> B)"
by auto


subsection{*The Constrains Operator*}

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

lemma constrains_empty [iff]: "F \<in> 0 co B <-> F \<in> program"
by (force simp add: constrains_def st_set_def)

lemma constrains_empty2 [iff]: "(F \<in> A co 0) <-> (A=0 & F \<in> program)"
by (force simp add: constrains_def st_set_def)

lemma constrains_state [iff]: "(F \<in> state co B) <-> (state\<subseteq>B & F \<in> program)"
apply (cut_tac F = F in Acts_type)
apply (force simp add: constrains_def st_set_def)
done

lemma constrains_state2 [iff]: "F \<in> A co state <-> (F \<in> program & st_set(A))"
apply (cut_tac F = F in Acts_type)
apply (force simp add: constrains_def st_set_def)
done

(*monotonic in 2nd argument*)
lemma constrains_weaken_R:
    "[| F \<in> A co A'; A'\<subseteq>B' |] ==> F \<in> A co B'"
apply (unfold constrains_def, blast)
done

(*anti-monotonic in 1st argument*)
lemma constrains_weaken_L:
    "[| F \<in> A co A'; B\<subseteq>A |] ==> F \<in> B co A'"
apply (unfold constrains_def st_set_def, blast)
done

lemma constrains_weaken:
   "[| F \<in> A co A'; B\<subseteq>A; A'\<subseteq>B' |] ==> F \<in> B co B'"
apply (drule constrains_weaken_R)
apply (drule_tac [2] constrains_weaken_L, blast+)
done


subsection{*Constrains and Union*}

lemma constrains_Un:
    "[| F \<in> A co A'; F \<in> B co B' |] ==> F \<in> (A Un B) co (A' Un B')"
by (auto simp add: constrains_def st_set_def, force)

lemma constrains_UN:
     "[|!!i. i \<in> I ==> F \<in> A(i) co A'(i); F \<in> program |]
      ==> F \<in> (\<Union>i \<in> I. A(i)) co (\<Union>i \<in> I. A'(i))"
by (force simp add: constrains_def st_set_def) 

lemma constrains_Un_distrib:
     "(A Un B) co C = (A co C) \<inter> (B co C)"
by (force simp add: constrains_def st_set_def)

lemma constrains_UN_distrib:
   "i \<in> I ==> (\<Union>i \<in> I. A(i)) co B = (\<Inter>i \<in> I. A(i) co B)"
by (force simp add: constrains_def st_set_def)


subsection{*Constrains and Intersection*}

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

(*The reasoning is by subsets since "co" refers to single actions
  only.  So this rule isn't that useful.*)

lemma constrains_trans: "[| F \<in> A co B; F \<in> B co C |] ==> F \<in> A co C"
by (unfold constrains_def st_set_def, auto, blast)

lemma constrains_cancel:
"[| F \<in> A co (A' Un B); F \<in> B co B' |] ==> F \<in> A co (A' Un B')"
apply (drule_tac A = B in constrains_imp_subset)
apply (blast intro: constrains_weaken_R)
done


subsection{*The Unless Operator*}

lemma unless_type: "A unless B \<subseteq> program"
by (force simp add: unless_def constrains_def) 

lemma unlessI: "[| F \<in> (A-B) co (A Un B) |] ==> F \<in> A unless B"
apply (unfold unless_def)
apply (blast dest: constrainsD2)
done

lemma unlessD: "F :A unless B ==> F \<in> (A-B) co (A Un B)"
by (unfold unless_def, auto)


subsection{*The Operator @{term initially}*}

lemma initially_type: "initially(A) \<subseteq> program"
by (unfold initially_def, blast)

lemma initiallyI: "[| F \<in> program; Init(F)\<subseteq>A |] ==> F \<in> initially(A)"
by (unfold initially_def, blast)

lemma initiallyD: "F \<in> initially(A) ==> Init(F)\<subseteq>A"
by (unfold initially_def, blast)


subsection{*The Operator @{term stable}*}

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


subsection{*Union and Intersection with @{term stable}*}

lemma stable_Un:
    "[| F \<in> stable(A); F \<in> stable(A') |] ==> F \<in> stable(A Un A')"
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
     "[| F \<in> stable(C); F \<in> A co (C Un A') |] ==> F \<in> (C Un A) co (C Un A')"
apply (unfold stable_def constrains_def st_set_def, auto)
apply (blast dest!: bspec)
done

lemma stable_constrains_Int:
     "[| F \<in> stable(C); F \<in>  (C \<inter> A) co A' |] ==> F \<in> (C \<inter> A) co (C \<inter> A')"
by (unfold stable_def constrains_def st_set_def, blast)

(* [| F \<in> stable(C); F  \<in> (C \<inter> A) co A |] ==> F \<in> stable(C \<inter> A) *)
lemmas stable_constrains_stable = stable_constrains_Int [THEN stableI, standard]

subsection{*The Operator @{term invariant}*}

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

text{*Could also say
      @{term "invariant(A) \<inter> invariant(B) \<subseteq> invariant (A \<inter> B)"}*}
lemma invariant_Int:
  "[| F \<in> invariant(A);  F \<in> invariant(B) |] ==> F \<in> invariant(A \<inter> B)"
apply (unfold invariant_def initially_def)
apply (simp add: stable_Int, blast)
done


subsection{*The Elimination Theorem*}

(** The "free" m has become universally quantified!
 Should the premise be !!m instead of \<forall>m ? Would make it harder
 to use in forward proof. **)

(* The general case easier to prove that le special case! *)
lemma "elimination":
    "[| \<forall>m \<in> M. F \<in> {s \<in> A. x(s) = m} co B(m); F \<in> program  |]
     ==> F \<in> {s \<in> A. x(s) \<in> M} co (\<Union>m \<in> M. B(m))"
by (auto simp add: constrains_def st_set_def, blast)

(* As above, but for the special case of A=state *)
lemma elimination2:
     "[| \<forall>m \<in> M. F \<in> {s \<in> state. x(s) = m} co B(m); F \<in> program  |]
     ==> F:{s \<in> state. x(s) \<in> M} co (\<Union>m \<in> M. B(m))"
by (rule UNITY.elimination, auto)

subsection{*The Operator @{term strongest_rhs}*}

lemma constrains_strongest_rhs:
    "[| F \<in> program; st_set(A) |] ==> F \<in> A co (strongest_rhs(F,A))"
by (auto simp add: constrains_def strongest_rhs_def st_set_def
              dest: Acts_type [THEN subsetD])

lemma strongest_rhs_is_strongest:
     "[| F \<in> A co B; st_set(B) |] ==> strongest_rhs(F,A) \<subseteq> B"
by (auto simp add: constrains_def strongest_rhs_def st_set_def)

ML
{*
val constrains_def = thm "constrains_def";
val stable_def = thm "stable_def";
val invariant_def = thm "invariant_def";
val unless_def = thm "unless_def";
val initially_def = thm "initially_def";
val SKIP_def = thm "SKIP_def";
val Allowed_def = thm "Allowed_def";
val programify_def = thm "programify_def";
val metacomp_def = thm "metacomp_def";

val id_in_Acts = thm "id_in_Acts";
val id_in_RawAllowedActs = thm "id_in_RawAllowedActs";
val id_in_AllowedActs = thm "id_in_AllowedActs";
val cons_id_Acts = thm "cons_id_Acts";
val cons_id_AllowedActs = thm "cons_id_AllowedActs";
val Init_type = thm "Init_type";
val st_set_Init = thm "st_set_Init";
val Acts_type = thm "Acts_type";
val AllowedActs_type = thm "AllowedActs_type";
val ActsD = thm "ActsD";
val AllowedActsD = thm "AllowedActsD";
val mk_program_in_program = thm "mk_program_in_program";
val Init_eq = thm "Init_eq";
val Acts_eq = thm "Acts_eq";
val AllowedActs_eq = thm "AllowedActs_eq";
val Init_SKIP = thm "Init_SKIP";
val Acts_SKIP = thm "Acts_SKIP";
val AllowedActs_SKIP = thm "AllowedActs_SKIP";
val raw_surjective_mk_program = thm "raw_surjective_mk_program";
val surjective_mk_program = thm "surjective_mk_program";
val program_equalityI = thm "program_equalityI";
val program_equalityE = thm "program_equalityE";
val program_equality_iff = thm "program_equality_iff";
val def_prg_Init = thm "def_prg_Init";
val def_prg_Acts = thm "def_prg_Acts";
val def_prg_AllowedActs = thm "def_prg_AllowedActs";
val def_prg_simps = thm "def_prg_simps";
val def_act_simp = thm "def_act_simp";
val def_set_simp = thm "def_set_simp";
val constrains_type = thm "constrains_type";
val constrainsI = thm "constrainsI";
val constrainsD = thm "constrainsD";
val constrainsD2 = thm "constrainsD2";
val constrains_empty = thm "constrains_empty";
val constrains_empty2 = thm "constrains_empty2";
val constrains_state = thm "constrains_state";
val constrains_state2 = thm "constrains_state2";
val constrains_weaken_R = thm "constrains_weaken_R";
val constrains_weaken_L = thm "constrains_weaken_L";
val constrains_weaken = thm "constrains_weaken";
val constrains_Un = thm "constrains_Un";
val constrains_UN = thm "constrains_UN";
val constrains_Un_distrib = thm "constrains_Un_distrib";
val constrains_UN_distrib = thm "constrains_UN_distrib";
val constrains_Int_distrib = thm "constrains_Int_distrib";
val constrains_INT_distrib = thm "constrains_INT_distrib";
val constrains_Int = thm "constrains_Int";
val constrains_INT = thm "constrains_INT";
val constrains_All = thm "constrains_All";
val constrains_imp_subset = thm "constrains_imp_subset";
val constrains_trans = thm "constrains_trans";
val constrains_cancel = thm "constrains_cancel";
val unless_type = thm "unless_type";
val unlessI = thm "unlessI";
val unlessD = thm "unlessD";
val initially_type = thm "initially_type";
val initiallyI = thm "initiallyI";
val initiallyD = thm "initiallyD";
val stable_type = thm "stable_type";
val stableI = thm "stableI";
val stableD = thm "stableD";
val stableD2 = thm "stableD2";
val stable_state = thm "stable_state";
val stable_unless = thm "stable_unless";
val stable_Un = thm "stable_Un";
val stable_UN = thm "stable_UN";
val stable_Int = thm "stable_Int";
val stable_INT = thm "stable_INT";
val stable_All = thm "stable_All";
val stable_constrains_Un = thm "stable_constrains_Un";
val stable_constrains_Int = thm "stable_constrains_Int";
val invariant_type = thm "invariant_type";
val invariantI = thm "invariantI";
val invariantD = thm "invariantD";
val invariantD2 = thm "invariantD2";
val invariant_Int = thm "invariant_Int";
val elimination = thm "elimination";
val elimination2 = thm "elimination2";
val constrains_strongest_rhs = thm "constrains_strongest_rhs";
val strongest_rhs_is_strongest = thm "strongest_rhs_is_strongest";

fun simp_of_act def = def RS def_act_simp;
fun simp_of_set def = def RS def_set_simp;
*}

end
