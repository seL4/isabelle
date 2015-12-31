(*  Title:      HOL/HOLCF/IOA/Automata.thy
    Author:     Olaf Müller, Konrad Slind, Tobias Nipkow
*)

section \<open>The I/O automata of Lynch and Tuttle in HOLCF\<close>

theory Automata
imports Asig
begin

default_sort type

type_synonym ('a, 's) transition = "'s * 'a * 's"
type_synonym ('a, 's) ioa =
  "'a signature * 's set * ('a,'s)transition set * ('a set set) * ('a set set)"


(* --------------------------------- IOA ---------------------------------*)

(* IO automata *)

definition asig_of :: "('a, 's)ioa \<Rightarrow> 'a signature"
  where "asig_of = fst"

definition starts_of :: "('a, 's) ioa \<Rightarrow> 's set"
  where "starts_of = (fst \<circ> snd)"

definition trans_of :: "('a, 's) ioa \<Rightarrow> ('a, 's) transition set"
  where "trans_of = (fst \<circ> snd \<circ> snd)"

abbreviation trans_of_syn  ("_ \<midarrow>_\<midarrow>_\<rightarrow> _" [81, 81, 81, 81] 100)
  where "s \<midarrow>a\<midarrow>A\<rightarrow> t \<equiv> (s, a, t) \<in> trans_of A"

definition wfair_of :: "('a, 's) ioa \<Rightarrow> 'a set set"
  where "wfair_of = (fst \<circ> snd \<circ> snd \<circ> snd)"

definition sfair_of :: "('a, 's) ioa \<Rightarrow> 'a set set"
  where "sfair_of = (snd \<circ> snd \<circ> snd \<circ> snd)"

definition is_asig_of :: "('a, 's) ioa \<Rightarrow> bool"
  where "is_asig_of A = is_asig (asig_of A)"

definition is_starts_of :: "('a, 's) ioa \<Rightarrow> bool"
  where "is_starts_of A \<longleftrightarrow> starts_of A \<noteq> {}"

definition is_trans_of :: "('a, 's) ioa \<Rightarrow> bool"
  where "is_trans_of A \<longleftrightarrow>
    (\<forall>triple. triple \<in> trans_of A \<longrightarrow> fst (snd triple) \<in> actions (asig_of A))"

definition input_enabled :: "('a, 's) ioa \<Rightarrow> bool"
  where "input_enabled A \<longleftrightarrow>
    (\<forall>a. a \<in> inputs (asig_of A) \<longrightarrow> (\<forall>s1. \<exists>s2. (s1, a, s2) \<in> trans_of A))"

definition IOA :: "('a, 's) ioa \<Rightarrow> bool"
  where "IOA A \<longleftrightarrow>
    is_asig_of A \<and>
    is_starts_of A \<and>
    is_trans_of A \<and>
    input_enabled A"

abbreviation "act A == actions (asig_of A)"
abbreviation "ext A == externals (asig_of A)"
abbreviation int where "int A == internals (asig_of A)"
abbreviation "inp A == inputs (asig_of A)"
abbreviation "out A == outputs (asig_of A)"
abbreviation "local A == locals (asig_of A)"

(* invariants *)
inductive reachable :: "('a, 's) ioa \<Rightarrow> 's \<Rightarrow> bool"
  for C :: "('a, 's) ioa"
where
  reachable_0:  "s \<in> starts_of C \<Longrightarrow> reachable C s"
| reachable_n:  "\<lbrakk>reachable C s; (s, a, t) \<in> trans_of C\<rbrakk> \<Longrightarrow> reachable C t"

definition invariant :: "[('a, 's) ioa, 's \<Rightarrow> bool] \<Rightarrow> bool"
  where "invariant A P \<longleftrightarrow> (\<forall>s. reachable A s \<longrightarrow> P s)"


(* ------------------------- parallel composition --------------------------*)

(* binary composition of action signatures and automata *)

definition compatible :: "[('a, 's) ioa, ('a, 't) ioa] \<Rightarrow> bool"
where
  "compatible A B \<longleftrightarrow>
  (((out A \<inter> out B) = {}) \<and>
   ((int A \<inter> act B) = {}) \<and>
   ((int B \<inter> act A) = {}))"

definition asig_comp :: "['a signature, 'a signature] \<Rightarrow> 'a signature"
where
  "asig_comp a1 a2 =
     (((inputs(a1) \<union> inputs(a2)) - (outputs(a1) \<union> outputs(a2)),
       (outputs(a1) \<union> outputs(a2)),
       (internals(a1) \<union> internals(a2))))"

definition par :: "[('a, 's) ioa, ('a, 't) ioa] \<Rightarrow> ('a, 's * 't) ioa"  (infixr "\<parallel>" 10)
where
  "(A \<parallel> B) =
      (asig_comp (asig_of A) (asig_of B),
       {pr. fst(pr) \<in> starts_of(A) \<and> snd(pr) \<in> starts_of(B)},
       {tr. let s = fst(tr); a = fst(snd(tr)); t = snd(snd(tr))
            in (a \<in> act A | a:act B) \<and>
               (if a \<in> act A then
                  (fst(s), a, fst(t)) \<in> trans_of(A)
                else fst(t) = fst(s))
               &
               (if a \<in> act B then
                  (snd(s), a, snd(t)) \<in> trans_of(B)
                else snd(t) = snd(s))},
        wfair_of A \<union> wfair_of B,
        sfair_of A \<union> sfair_of B)"


(* ------------------------ hiding -------------------------------------------- *)

(* hiding and restricting *)

definition restrict_asig :: "['a signature, 'a set] \<Rightarrow> 'a signature"
where
  "restrict_asig asig actns =
    (inputs(asig) Int actns,
     outputs(asig) Int actns,
     internals(asig) Un (externals(asig) - actns))"

(* Notice that for wfair_of and sfair_of nothing has to be changed, as
   changes from the outputs to the internals does not touch the locals as
   a whole, which is of importance for fairness only *)
definition restrict :: "[('a, 's) ioa, 'a set] \<Rightarrow> ('a, 's) ioa"
where
  "restrict A actns =
    (restrict_asig (asig_of A) actns,
     starts_of A,
     trans_of A,
     wfair_of A,
     sfair_of A)"

definition hide_asig :: "['a signature, 'a set] \<Rightarrow> 'a signature"
where
  "hide_asig asig actns =
    (inputs(asig) - actns,
     outputs(asig) - actns,
     internals(asig) \<union> actns)"

definition hide :: "[('a, 's) ioa, 'a set] \<Rightarrow> ('a, 's) ioa"
where
  "hide A actns =
    (hide_asig (asig_of A) actns,
     starts_of A,
     trans_of A,
     wfair_of A,
     sfair_of A)"

(* ------------------------- renaming ------------------------------------------- *)

definition rename_set :: "'a set \<Rightarrow> ('c \<Rightarrow> 'a option) \<Rightarrow> 'c set"
  where "rename_set A ren = {b. \<exists>x. Some x = ren b \<and> x \<in> A}"

definition rename :: "('a, 'b) ioa \<Rightarrow> ('c \<Rightarrow> 'a option) \<Rightarrow> ('c, 'b) ioa"
where
  "rename ioa ren =
    ((rename_set (inp ioa) ren,
      rename_set (out ioa) ren,
      rename_set (int ioa) ren),
     starts_of ioa,
     {tr. let s = fst(tr); a = fst(snd(tr));  t = snd(snd(tr))
          in
          \<exists>x. Some(x) = ren(a) \<and> (s,x,t):trans_of ioa},
     {rename_set s ren | s. s \<in> wfair_of ioa},
     {rename_set s ren | s. s \<in> sfair_of ioa})"


(* ------------------------- fairness ----------------------------- *)

(* enabledness of actions and action sets *)

definition enabled :: "('a, 's) ioa \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
  where "enabled A a s \<longleftrightarrow> (\<exists>t. s \<midarrow>a\<midarrow>A\<rightarrow> t)"

definition Enabled :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool"
  where "Enabled A W s \<longleftrightarrow> (\<exists>w \<in> W. enabled A w s)"


(* action set keeps enabled until probably disabled by itself *)

definition en_persistent :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "en_persistent A W \<longleftrightarrow>
    (\<forall>s a t. Enabled A W s \<and> a \<notin> W \<and> s \<midarrow>a\<midarrow>A\<rightarrow> t \<longrightarrow> Enabled A W t)"


(* post_conditions for actions and action sets *)

definition was_enabled :: "('a, 's) ioa \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
  where "was_enabled A a t \<longleftrightarrow> (\<exists>s. s \<midarrow>a\<midarrow>A\<rightarrow> t)"

definition set_was_enabled :: "('a, 's) ioa \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool"
  where "set_was_enabled A W t \<longleftrightarrow> (\<exists>w \<in> W. was_enabled A w t)"


(* constraints for fair IOA *)

definition fairIOA :: "('a, 's) ioa \<Rightarrow> bool"
  where "fairIOA A \<longleftrightarrow> (\<forall>S \<in> wfair_of A. S \<subseteq> local A) \<and> (\<forall>S \<in> sfair_of A. S \<subseteq> local A)"

definition input_resistant :: "('a, 's) ioa \<Rightarrow> bool"
where
  "input_resistant A \<longleftrightarrow>
    (\<forall>W \<in> sfair_of A. \<forall>s a t.
      reachable A s \<and> reachable A t \<and> a \<in> inp A \<and>
      Enabled A W s \<and> s \<midarrow>a\<midarrow>A\<rightarrow> t \<longrightarrow> Enabled A W t)"


declare split_paired_Ex [simp del]

lemmas ioa_projections = asig_of_def starts_of_def trans_of_def wfair_of_def sfair_of_def


subsection "asig_of, starts_of, trans_of"

lemma ioa_triple_proj:
 "((asig_of (x,y,z,w,s)) = x)   &
  ((starts_of (x,y,z,w,s)) = y) &
  ((trans_of (x,y,z,w,s)) = z)  &
  ((wfair_of (x,y,z,w,s)) = w) &
  ((sfair_of (x,y,z,w,s)) = s)"
  apply (simp add: ioa_projections)
  done

lemma trans_in_actions:
  "[| is_trans_of A; (s1,a,s2):trans_of(A) |] ==> a:act A"
  apply (unfold is_trans_of_def actions_def is_asig_def)
    apply (erule allE, erule impE, assumption)
    apply simp
  done

lemma starts_of_par: "starts_of(A \<parallel> B) = {p. fst(p):starts_of(A) & snd(p):starts_of(B)}"
  by (simp add: par_def ioa_projections)

lemma trans_of_par:
"trans_of(A \<parallel> B) = {tr. let s = fst(tr); a = fst(snd(tr)); t = snd(snd(tr))
             in (a:act A | a:act B) &
                (if a:act A then
                   (fst(s),a,fst(t)):trans_of(A)
                 else fst(t) = fst(s))
                &
                (if a:act B then
                   (snd(s),a,snd(t)):trans_of(B)
                 else snd(t) = snd(s))}"
  by (simp add: par_def ioa_projections)


subsection "actions and par"

lemma actions_asig_comp: "actions(asig_comp a b) = actions(a) Un actions(b)"
  by (auto simp add: actions_def asig_comp_def asig_projections)

lemma asig_of_par: "asig_of(A \<parallel> B) = asig_comp (asig_of A) (asig_of B)"
  by (simp add: par_def ioa_projections)


lemma externals_of_par: "ext (A1\<parallel>A2) = (ext A1) Un (ext A2)"
  apply (simp add: externals_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def Un_def set_diff_eq)
  apply blast
  done

lemma actions_of_par: "act (A1\<parallel>A2) = (act A1) Un (act A2)"
  apply (simp add: actions_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def asig_internals_def Un_def set_diff_eq)
  apply blast
  done

lemma inputs_of_par: "inp (A1\<parallel>A2) = ((inp A1) Un (inp A2)) - ((out A1) Un (out A2))"
  by (simp add: actions_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def Un_def set_diff_eq)

lemma outputs_of_par: "out (A1\<parallel>A2) = (out A1) Un (out A2)"
  by (simp add: actions_def asig_of_par asig_comp_def
    asig_outputs_def Un_def set_diff_eq)

lemma internals_of_par: "int (A1\<parallel>A2) = (int A1) Un (int A2)"
  by (simp add: actions_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def asig_internals_def Un_def set_diff_eq)


subsection "actions and compatibility"

lemma compat_commute: "compatible A B = compatible B A"
  by (auto simp add: compatible_def Int_commute)

lemma ext1_is_not_int2: "[| compatible A1 A2; a:ext A1|] ==> a~:int A2"
  apply (unfold externals_def actions_def compatible_def)
  apply simp
  apply blast
  done

(* just commuting the previous one: better commute compatible *)
lemma ext2_is_not_int1: "[| compatible A2 A1 ; a:ext A1|] ==> a~:int A2"
  apply (unfold externals_def actions_def compatible_def)
  apply simp
  apply blast
  done

lemmas ext1_ext2_is_not_act2 = ext1_is_not_int2 [THEN int_and_ext_is_act]
lemmas ext1_ext2_is_not_act1 = ext2_is_not_int1 [THEN int_and_ext_is_act]

lemma intA_is_not_extB: "[| compatible A B; x:int A |] ==> x~:ext B"
  apply (unfold externals_def actions_def compatible_def)
  apply simp
  apply blast
  done

lemma intA_is_not_actB: "[| compatible A B; a:int A |] ==> a ~: act B"
  apply (unfold externals_def actions_def compatible_def is_asig_def asig_of_def)
  apply simp
  apply blast
  done

(* the only one that needs disjointness of outputs and of internals and _all_ acts *)
lemma outAactB_is_inpB: "[| compatible A B; a:out A ;a:act B|] ==> a : inp B"
  apply (unfold asig_outputs_def asig_internals_def actions_def asig_inputs_def
      compatible_def is_asig_def asig_of_def)
  apply simp
  apply blast
  done

(* needed for propagation of input_enabledness from A,B to A\<parallel>B *)
lemma inpAAactB_is_inpBoroutB:
  "[| compatible A B; a:inp A ;a:act B|] ==> a : inp B | a: out B"
  apply (unfold asig_outputs_def asig_internals_def actions_def asig_inputs_def
      compatible_def is_asig_def asig_of_def)
  apply simp
  apply blast
  done


subsection "input_enabledness and par"

(* ugly case distinctions. Heart of proof:
     1. inpAAactB_is_inpBoroutB ie. internals are really hidden.
     2. inputs_of_par: outputs are no longer inputs of par. This is important here *)
lemma input_enabled_par:
  "[| compatible A B; input_enabled A; input_enabled B|]
        ==> input_enabled (A\<parallel>B)"
  apply (unfold input_enabled_def)
  apply (simp add: Let_def inputs_of_par trans_of_par)
  apply (tactic "safe_tac (Context.raw_transfer @{theory} @{theory_context Fun})")
  apply (simp add: inp_is_act)
  prefer 2
  apply (simp add: inp_is_act)
  (* a: inp A *)
  apply (case_tac "a:act B")
  (* a:act B *)
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (drule inpAAactB_is_inpBoroutB)
  apply assumption
  apply assumption
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (erule_tac x = "aa" in allE)
  apply (erule_tac x = "b" in allE)
  apply (erule exE)
  apply (erule exE)
  apply (rule_tac x = " (s2,s2a) " in exI)
  apply (simp add: inp_is_act)
  (* a~: act B*)
  apply (simp add: inp_is_act)
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (erule_tac x = "aa" in allE)
  apply (erule exE)
  apply (rule_tac x = " (s2,b) " in exI)
  apply simp
  
  (* a:inp B *)
  apply (case_tac "a:act A")
  (* a:act A *)
  apply (erule_tac x = "a" in allE)
  apply (erule_tac x = "a" in allE)
  apply (simp add: inp_is_act)
  apply (frule_tac A1 = "A" in compat_commute [THEN iffD1])
  apply (drule inpAAactB_is_inpBoroutB)
  back
  apply assumption
  apply assumption
  apply simp
  apply (erule_tac x = "aa" in allE)
  apply (erule_tac x = "b" in allE)
  apply (erule exE)
  apply (erule exE)
  apply (rule_tac x = " (s2,s2a) " in exI)
  apply (simp add: inp_is_act)
  (* a~: act B*)
  apply (simp add: inp_is_act)
  apply (erule_tac x = "a" in allE)
  apply (erule_tac x = "a" in allE)
  apply simp
  apply (erule_tac x = "b" in allE)
  apply (erule exE)
  apply (rule_tac x = " (aa,s2) " in exI)
  apply simp
  done


subsection "invariants"

lemma invariantI:
  "[| !!s. s:starts_of(A) ==> P(s);
      !!s t a. [|reachable A s; P(s)|] ==> (s,a,t): trans_of(A) --> P(t) |]
   ==> invariant A P"
  apply (unfold invariant_def)
  apply (rule allI)
  apply (rule impI)
  apply (rule_tac x = "s" in reachable.induct)
  apply assumption
  apply blast
  apply blast
  done

lemma invariantI1:
 "[| !!s. s : starts_of(A) ==> P(s);
     !!s t a. reachable A s ==> P(s) --> (s,a,t):trans_of(A) --> P(t)
  |] ==> invariant A P"
  apply (blast intro: invariantI)
  done

lemma invariantE: "[| invariant A P; reachable A s |] ==> P(s)"
  apply (unfold invariant_def)
  apply blast
  done


subsection "restrict"


lemmas reachable_0 = reachable.reachable_0
  and reachable_n = reachable.reachable_n

lemma cancel_restrict_a: "starts_of(restrict ioa acts) = starts_of(ioa) &
          trans_of(restrict ioa acts) = trans_of(ioa)"
  by (simp add: restrict_def ioa_projections)

lemma cancel_restrict_b: "reachable (restrict ioa acts) s = reachable ioa s"
  apply (rule iffI)
  apply (erule reachable.induct)
  apply (simp add: cancel_restrict_a reachable_0)
  apply (erule reachable_n)
  apply (simp add: cancel_restrict_a)
  (* <--  *)
  apply (erule reachable.induct)
  apply (rule reachable_0)
  apply (simp add: cancel_restrict_a)
  apply (erule reachable_n)
  apply (simp add: cancel_restrict_a)
  done

lemma acts_restrict: "act (restrict A acts) = act A"
  apply (simp (no_asm) add: actions_def asig_internals_def
    asig_outputs_def asig_inputs_def externals_def asig_of_def restrict_def restrict_asig_def)
  apply auto
  done

lemma cancel_restrict: "starts_of(restrict ioa acts) = starts_of(ioa) &
          trans_of(restrict ioa acts) = trans_of(ioa) &
          reachable (restrict ioa acts) s = reachable ioa s &
          act (restrict A acts) = act A"
  by (simp add: cancel_restrict_a cancel_restrict_b acts_restrict)


subsection "rename"

lemma trans_rename: "s \<midarrow>a\<midarrow>(rename C f)\<rightarrow> t ==> (? x. Some(x) = f(a) & s \<midarrow>x\<midarrow>C\<rightarrow> t)"
  by (simp add: Let_def rename_def trans_of_def)


lemma reachable_rename: "[| reachable (rename C g) s |] ==> reachable C s"
  apply (erule reachable.induct)
  apply (rule reachable_0)
  apply (simp add: rename_def ioa_projections)
  apply (drule trans_rename)
  apply (erule exE)
  apply (erule conjE)
  apply (erule reachable_n)
  apply assumption
  done


subsection "trans_of(A\<parallel>B)"

lemma trans_A_proj: "[|(s,a,t):trans_of (A\<parallel>B); a:act A|]
              ==> (fst s,a,fst t):trans_of A"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_B_proj: "[|(s,a,t):trans_of (A\<parallel>B); a:act B|]
              ==> (snd s,a,snd t):trans_of B"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_A_proj2: "[|(s,a,t):trans_of (A\<parallel>B); a~:act A|]
              ==> fst s = fst t"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_B_proj2: "[|(s,a,t):trans_of (A\<parallel>B); a~:act B|]
              ==> snd s = snd t"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_AB_proj: "(s,a,t):trans_of (A\<parallel>B)
               ==> a :act A | a :act B"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_AB: "[|a:act A;a:act B;
       (fst s,a,fst t):trans_of A;(snd s,a,snd t):trans_of B|]
   ==> (s,a,t):trans_of (A\<parallel>B)"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_A_notB: "[|a:act A;a~:act B;
       (fst s,a,fst t):trans_of A;snd s=snd t|]
   ==> (s,a,t):trans_of (A\<parallel>B)"
  by (simp add: Let_def par_def trans_of_def)

lemma trans_notA_B: "[|a~:act A;a:act B;
       (snd s,a,snd t):trans_of B;fst s=fst t|]
   ==> (s,a,t):trans_of (A\<parallel>B)"
  by (simp add: Let_def par_def trans_of_def)

lemmas trans_of_defs1 = trans_AB trans_A_notB trans_notA_B
  and trans_of_defs2 = trans_A_proj trans_B_proj trans_A_proj2 trans_B_proj2 trans_AB_proj


lemma trans_of_par4:
"((s,a,t) : trans_of(A \<parallel> B \<parallel> C \<parallel> D)) =
  ((a:actions(asig_of(A)) | a:actions(asig_of(B)) | a:actions(asig_of(C)) |
    a:actions(asig_of(D))) &
   (if a:actions(asig_of(A)) then (fst(s),a,fst(t)):trans_of(A)
    else fst t=fst s) &
   (if a:actions(asig_of(B)) then (fst(snd(s)),a,fst(snd(t))):trans_of(B)
    else fst(snd(t))=fst(snd(s))) &
   (if a:actions(asig_of(C)) then
      (fst(snd(snd(s))),a,fst(snd(snd(t)))):trans_of(C)
    else fst(snd(snd(t)))=fst(snd(snd(s)))) &
   (if a:actions(asig_of(D)) then
      (snd(snd(snd(s))),a,snd(snd(snd(t)))):trans_of(D)
    else snd(snd(snd(t)))=snd(snd(snd(s)))))"
  by (simp add: par_def actions_asig_comp prod_eq_iff Let_def ioa_projections)


subsection "proof obligation generator for IOA requirements"

(* without assumptions on A and B because is_trans_of is also incorporated in \<parallel>def *)
lemma is_trans_of_par: "is_trans_of (A\<parallel>B)"
  by (simp add: is_trans_of_def Let_def actions_of_par trans_of_par)

lemma is_trans_of_restrict: "is_trans_of A ==> is_trans_of (restrict A acts)"
  by (simp add: is_trans_of_def cancel_restrict acts_restrict)

lemma is_trans_of_rename: "is_trans_of A ==> is_trans_of (rename A f)"
  apply (unfold is_trans_of_def restrict_def restrict_asig_def)
  apply (simp add: Let_def actions_def trans_of_def asig_internals_def
    asig_outputs_def asig_inputs_def externals_def asig_of_def rename_def rename_set_def)
  apply blast
  done

lemma is_asig_of_par: "[| is_asig_of A; is_asig_of B; compatible A B|]
          ==> is_asig_of (A\<parallel>B)"
  apply (simp add: is_asig_of_def asig_of_par asig_comp_def compatible_def
    asig_internals_def asig_outputs_def asig_inputs_def actions_def is_asig_def)
  apply (simp add: asig_of_def)
  apply auto
  done

lemma is_asig_of_restrict: "is_asig_of A ==> is_asig_of (restrict A f)"
  apply (unfold is_asig_of_def is_asig_def asig_of_def restrict_def restrict_asig_def
             asig_internals_def asig_outputs_def asig_inputs_def externals_def o_def)
  apply simp
  apply auto
  done

lemma is_asig_of_rename: "is_asig_of A ==> is_asig_of (rename A f)"
  apply (simp add: is_asig_of_def rename_def rename_set_def asig_internals_def
    asig_outputs_def asig_inputs_def actions_def is_asig_def asig_of_def)
  apply auto
  apply (drule_tac [!] s = "Some _" in sym)
  apply auto
  done

lemmas [simp] = is_asig_of_par is_asig_of_restrict
  is_asig_of_rename is_trans_of_par is_trans_of_restrict is_trans_of_rename


lemma compatible_par: "[|compatible A B; compatible A C |]==> compatible A (B\<parallel>C)"
  apply (unfold compatible_def)
  apply (simp add: internals_of_par outputs_of_par actions_of_par)
  apply auto
  done

(*  better derive by previous one and compat_commute *)
lemma compatible_par2: "[|compatible A C; compatible B C |]==> compatible (A\<parallel>B) C"
  apply (unfold compatible_def)
  apply (simp add: internals_of_par outputs_of_par actions_of_par)
  apply auto
  done

lemma compatible_restrict:
  "[| compatible A B; (ext B - S) Int ext A = {}|]
        ==> compatible A (restrict B S)"
  apply (unfold compatible_def)
  apply (simp add: ioa_triple_proj asig_triple_proj externals_def
    restrict_def restrict_asig_def actions_def)
  apply auto
  done

declare split_paired_Ex [simp]

end
