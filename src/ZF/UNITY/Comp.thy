(*  Title:      ZF/UNITY/Comp.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   1998  University of Cambridge

From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January  2001 

Added: a strong form of the order relation over component and localize 

Theory ported from HOL.
  
*)

header{*Composition*}

theory Comp = Union + Increasing:

constdefs

  component :: "[i,i]=>o"  (infixl "component" 65) 
  "F component H == (EX G. F Join G = H)"

  strict_component :: "[i,i]=>o" (infixl "strict'_component" 65)
  "F strict_component H == F component H & F~=H"

  (* A stronger form of the component relation *)
  component_of :: "[i,i]=>o"   (infixl "component'_of" 65)
  "F component_of H  == (EX G. F ok G & F Join G = H)"
  
  strict_component_of :: "[i,i]=>o" (infixl "strict'_component'_of" 65)
  "F strict_component_of H  == F component_of H  & F~=H"

  (* Preserves a state function f, in particular a variable *)
  preserves :: "(i=>i)=>i"
  "preserves(f) == {F:program. ALL z. F: stable({s:state. f(s) = z})}"

  fun_pair :: "[i=>i, i =>i] =>(i=>i)"
  "fun_pair(f, g) == %x. <f(x), g(x)>"

  localize  :: "[i=>i, i] => i"
  "localize(f,F) == mk_program(Init(F), Acts(F),
		       AllowedActs(F) Int (UN G:preserves(f). Acts(G)))"

  
(*** component and strict_component relations ***)

lemma componentI: 
     "H component F | H component G ==> H component (F Join G)"
apply (unfold component_def, auto)
apply (rule_tac x = "Ga Join G" in exI)
apply (rule_tac [2] x = "G Join F" in exI)
apply (auto simp add: Join_ac)
done

lemma component_eq_subset: 
     "G \<in> program ==> (F component G) <->  
   (Init(G) <= Init(F) & Acts(F) <= Acts(G) & AllowedActs(G) <= AllowedActs(F))"
apply (unfold component_def, auto)
apply (rule exI)
apply (rule program_equalityI, auto)
done

lemma component_SKIP [simp]: "F \<in> program ==> SKIP component F"
apply (unfold component_def)
apply (rule_tac x = F in exI)
apply (force intro: Join_SKIP_left)
done

lemma component_refl [simp]: "F \<in> program ==> F component F"
apply (unfold component_def)
apply (rule_tac x = F in exI)
apply (force intro: Join_SKIP_right)
done

lemma SKIP_minimal: "F component SKIP ==> programify(F) = SKIP"
apply (rule program_equalityI)
apply (simp_all add: component_eq_subset, blast)
done

lemma component_Join1: "F component (F Join G)"
by (unfold component_def, blast)

lemma component_Join2: "G component (F Join G)"
apply (unfold component_def)
apply (simp (no_asm) add: Join_commute)
apply blast
done

lemma Join_absorb1: "F component G ==> F Join G = G"
by (auto simp add: component_def Join_left_absorb)

lemma Join_absorb2: "G component F ==> F Join G = F"
by (auto simp add: Join_ac component_def)

lemma JN_component_iff:
     "H \<in> program==>(JOIN(I,F) component H) <-> (\<forall>i \<in> I. F(i) component H)"
apply (case_tac "I=0", force)
apply (simp (no_asm_simp) add: component_eq_subset)
apply auto
apply blast
apply (rename_tac "y")
apply (drule_tac c = y and A = "AllowedActs (H)" in subsetD)
apply (blast elim!: not_emptyE)+
done

lemma component_JN: "i \<in> I ==> F(i) component (\<Squnion>i \<in> I. (F(i)))"
apply (unfold component_def)
apply (blast intro: JN_absorb)
done

lemma component_trans: "[| F component G; G component H |] ==> F component H"
apply (unfold component_def)
apply (blast intro: Join_assoc [symmetric])
done

lemma component_antisym:
     "[| F \<in> program; G \<in> program |] ==>(F component G & G  component F) --> F = G"
apply (simp (no_asm_simp) add: component_eq_subset)
apply clarify
apply (rule program_equalityI, auto)
done

lemma Join_component_iff:
     "H \<in> program ==> 
      ((F Join G) component H) <-> (F component H & G component H)"
apply (simp (no_asm_simp) add: component_eq_subset)
apply blast
done

lemma component_constrains:
     "[| F component G; G \<in> A co B; F \<in> program |] ==> F \<in> A co B"
apply (frule constrainsD2)
apply (auto simp add: constrains_def component_eq_subset)
done

(* Used in Guar.thy to show that programs are partially ordered*)
(* bind_thm ("program_less_le", strict_component_def RS meta_eq_to_obj_eq);*)

(*** preserves ***)

lemma preserves_is_safety_prop [simp]: "safety_prop(preserves(f))"
apply (unfold preserves_def safety_prop_def)
apply (auto dest: ActsD simp add: stable_def constrains_def)
apply (drule_tac c = act in subsetD, auto)
done

lemma preservesI [rule_format]: 
     "\<forall>z. F \<in> stable({s \<in> state. f(s) = z})  ==> F \<in> preserves(f)"
apply (auto simp add: preserves_def)
apply (blast dest: stableD2)
done

lemma preserves_imp_eq: 
     "[| F \<in> preserves(f);  act \<in> Acts(F);  <s,t> \<in> act |] ==> f(s) = f(t)"
apply (unfold preserves_def stable_def constrains_def)
apply (subgoal_tac "s \<in> state & t \<in> state")
 prefer 2 apply (blast dest!: Acts_type [THEN subsetD], force) 
done

lemma Join_preserves [iff]: 
"(F Join G \<in> preserves(v)) <->   
      (programify(F) \<in> preserves(v) & programify(G) \<in> preserves(v))"
by (auto simp add: preserves_def INT_iff)
 
lemma JN_preserves [iff]:
     "(JOIN(I,F): preserves(v)) <-> (\<forall>i \<in> I. programify(F(i)):preserves(v))"
by (auto simp add: JN_stable preserves_def INT_iff)

lemma SKIP_preserves [iff]: "SKIP \<in> preserves(v)"
by (auto simp add: preserves_def INT_iff)

lemma fun_pair_apply [simp]: "fun_pair(f,g,x) = <f(x), g(x)>"
apply (unfold fun_pair_def)
apply (simp (no_asm))
done

lemma preserves_fun_pair:
     "preserves(fun_pair(v,w)) = preserves(v) Int preserves(w)"
apply (rule equalityI)
apply (auto simp add: preserves_def stable_def constrains_def, blast+)
done

lemma preserves_fun_pair_iff [iff]:
     "F \<in> preserves(fun_pair(v, w))  <-> F \<in> preserves(v) Int preserves(w)"
by (simp add: preserves_fun_pair)

lemma fun_pair_comp_distrib:
     "(fun_pair(f, g) comp h)(x) = fun_pair(f comp h, g comp h, x)"
by (simp add: fun_pair_def metacomp_def)

lemma comp_apply [simp]: "(f comp g)(x) = f(g(x))"
by (simp add: metacomp_def)

lemma preserves_type: "preserves(v)<=program"
by (unfold preserves_def, auto)

lemma preserves_into_program [TC]: "F \<in> preserves(f) ==> F \<in> program"
by (blast intro: preserves_type [THEN subsetD])

lemma subset_preserves_comp: "preserves(f) <= preserves(g comp f)"
apply (auto simp add: preserves_def stable_def constrains_def)
apply (drule_tac x = "f (xb)" in spec)
apply (drule_tac x = act in bspec, auto)
done

lemma imp_preserves_comp: "F \<in> preserves(f) ==> F \<in> preserves(g comp f)"
by (blast intro: subset_preserves_comp [THEN subsetD])

lemma preserves_subset_stable: "preserves(f) <= stable({s \<in> state. P(f(s))})"
apply (auto simp add: preserves_def stable_def constrains_def)
apply (rename_tac s' s)
apply (subgoal_tac "f (s) = f (s') ")
apply (force+)
done

lemma preserves_imp_stable:
     "F \<in> preserves(f) ==> F \<in> stable({s \<in> state. P(f(s))})"
by (blast intro: preserves_subset_stable [THEN subsetD])

lemma preserves_imp_increasing: 
 "[| F \<in> preserves(f); \<forall>x \<in> state. f(x):A |] ==> F \<in> Increasing.increasing(A, r, f)"
apply (unfold Increasing.increasing_def)
apply (auto intro: preserves_into_program)
apply (rule_tac P = "%x. <k, x>:r" in preserves_imp_stable, auto)
done

lemma preserves_id_subset_stable: 
 "st_set(A) ==> preserves(%x. x) <= stable(A)"
apply (unfold preserves_def stable_def constrains_def, auto)
apply (drule_tac x = xb in spec)
apply (drule_tac x = act in bspec)
apply (auto dest: ActsD)
done

lemma preserves_id_imp_stable:
     "[| F \<in> preserves(%x. x); st_set(A) |] ==> F \<in> stable(A)"
by (blast intro: preserves_id_subset_stable [THEN subsetD])

(** Added by Sidi **)
(** component_of **)

(*  component_of is stronger than component *)
lemma component_of_imp_component: 
"F component_of H ==> F component H"
apply (unfold component_def component_of_def, blast)
done

(* component_of satisfies many of component's properties *)
lemma component_of_refl [simp]: "F \<in> program ==> F component_of F"
apply (unfold component_of_def)
apply (rule_tac x = SKIP in exI, auto)
done

lemma component_of_SKIP [simp]: "F \<in> program ==>SKIP component_of F"
apply (unfold component_of_def, auto)
apply (rule_tac x = F in exI, auto)
done

lemma component_of_trans: 
     "[| F component_of G; G component_of H |] ==> F component_of H"
apply (unfold component_of_def)
apply (blast intro: Join_assoc [symmetric])
done

(** localize **)
lemma localize_Init_eq [simp]: "Init(localize(v,F)) = Init(F)"
by (unfold localize_def, simp)

lemma localize_Acts_eq [simp]: "Acts(localize(v,F)) = Acts(F)"
by (unfold localize_def, simp)

lemma localize_AllowedActs_eq [simp]: 
 "AllowedActs(localize(v,F)) = AllowedActs(F) Int (\<Union>G \<in> preserves(v). Acts(G))"
apply (unfold localize_def)
apply (rule equalityI)
apply (auto dest: Acts_type [THEN subsetD])
done


(** Theorems used in ClientImpl **)

lemma stable_localTo_stable2: 
 "[| F \<in> stable({s \<in> state. P(f(s), g(s))});  G \<in> preserves(f);  G \<in> preserves(g) |]  
      ==> F Join G \<in> stable({s \<in> state. P(f(s), g(s))})"
apply (auto dest: ActsD preserves_into_program simp add: stable_def constrains_def)
apply (case_tac "act \<in> Acts (F) ")
apply auto
apply (drule preserves_imp_eq)
apply (drule_tac [3] preserves_imp_eq, auto)
done

lemma Increasing_preserves_Stable:
     "[| F \<in> stable({s \<in> state. <f(s), g(s)>:r});  G \<in> preserves(f);    
         F Join G \<in> Increasing(A, r, g);  
         \<forall>x \<in> state. f(x):A & g(x):A |]      
      ==> F Join G \<in> Stable({s \<in> state. <f(s), g(s)>:r})"
apply (auto simp add: stable_def Stable_def Increasing_def Constrains_def all_conj_distrib)
apply (simp_all add: constrains_type [THEN subsetD] preserves_type [THEN subsetD])
apply (blast intro: constrains_weaken)
(*The G case remains*)
apply (auto dest: ActsD simp add: preserves_def stable_def constrains_def ball_conj_distrib all_conj_distrib)
(*We have a G-action, so delete assumptions about F-actions*)
apply (erule_tac V = "\<forall>act \<in> Acts (F) . ?P (act)" in thin_rl)
apply (erule_tac V = "\<forall>k\<in>A. \<forall>act \<in> Acts (F) . ?P (k,act)" in thin_rl)
apply (subgoal_tac "f (x) = f (xa) ")
apply (auto dest!: bspec)
done


(** Lemma used in AllocImpl **)

lemma Constrains_UN_left: 
     "[| \<forall>x \<in> I. F \<in> A(x) Co B; F \<in> program |] ==> F:(\<Union>x \<in> I. A(x)) Co B"
by (unfold Constrains_def constrains_def, auto)


lemma stable_Join_Stable: 
 "[| F \<in> stable({s \<in> state. P(f(s), g(s))});  
     \<forall>k \<in> A. F Join G \<in> Stable({s \<in> state. P(k, g(s))});  
     G \<in> preserves(f); \<forall>s \<in> state. f(s):A|]
  ==> F Join G \<in> Stable({s \<in> state. P(f(s), g(s))})"
apply (unfold stable_def Stable_def preserves_def)
apply (rule_tac A = "(\<Union>k \<in> A. {s \<in> state. f(s)=k} Int {s \<in> state. P (f (s), g (s))})" in Constrains_weaken_L)
prefer 2 apply blast
apply (rule Constrains_UN_left, auto)
apply (rule_tac A = "{s \<in> state. f(s)=k} Int {s \<in> state. P (f (s), g (s))} Int {s \<in> state. P (k, g (s))}" and A' = "({s \<in> state. f(s)=k} Un {s \<in> state. P (f (s), g (s))}) Int {s \<in> state. P (k, g (s))}" in Constrains_weaken)
 prefer 2 apply blast 
 prefer 2 apply blast 
apply (rule Constrains_Int)
apply (rule constrains_imp_Constrains)
apply (auto simp add: constrains_type [THEN subsetD])
apply (blast intro: constrains_weaken) 
apply (drule_tac x = k in spec)
apply (blast intro: constrains_weaken) 
done

ML
{*
val component_of_def = thm "component_of_def";
val component_def = thm "component_def";

val componentI = thm "componentI";
val component_eq_subset = thm "component_eq_subset";
val component_SKIP = thm "component_SKIP";
val component_refl = thm "component_refl";
val SKIP_minimal = thm "SKIP_minimal";
val component_Join1 = thm "component_Join1";
val component_Join2 = thm "component_Join2";
val Join_absorb1 = thm "Join_absorb1";
val Join_absorb2 = thm "Join_absorb2";
val JN_component_iff = thm "JN_component_iff";
val component_JN = thm "component_JN";
val component_trans = thm "component_trans";
val component_antisym = thm "component_antisym";
val Join_component_iff = thm "Join_component_iff";
val component_constrains = thm "component_constrains";
val preserves_is_safety_prop = thm "preserves_is_safety_prop";
val preservesI = thm "preservesI";
val preserves_imp_eq = thm "preserves_imp_eq";
val Join_preserves = thm "Join_preserves";
val JN_preserves = thm "JN_preserves";
val SKIP_preserves = thm "SKIP_preserves";
val fun_pair_apply = thm "fun_pair_apply";
val preserves_fun_pair = thm "preserves_fun_pair";
val preserves_fun_pair_iff = thm "preserves_fun_pair_iff";
val fun_pair_comp_distrib = thm "fun_pair_comp_distrib";
val comp_apply = thm "comp_apply";
val preserves_type = thm "preserves_type";
val preserves_into_program = thm "preserves_into_program";
val subset_preserves_comp = thm "subset_preserves_comp";
val imp_preserves_comp = thm "imp_preserves_comp";
val preserves_subset_stable = thm "preserves_subset_stable";
val preserves_imp_stable = thm "preserves_imp_stable";
val preserves_imp_increasing = thm "preserves_imp_increasing";
val preserves_id_subset_stable = thm "preserves_id_subset_stable";
val preserves_id_imp_stable = thm "preserves_id_imp_stable";
val component_of_imp_component = thm "component_of_imp_component";
val component_of_refl = thm "component_of_refl";
val component_of_SKIP = thm "component_of_SKIP";
val component_of_trans = thm "component_of_trans";
val localize_Init_eq = thm "localize_Init_eq";
val localize_Acts_eq = thm "localize_Acts_eq";
val localize_AllowedActs_eq = thm "localize_AllowedActs_eq";
val stable_localTo_stable2 = thm "stable_localTo_stable2";
val Increasing_preserves_Stable = thm "Increasing_preserves_Stable";
val Constrains_UN_left = thm "Constrains_UN_left";
val stable_Join_Stable = thm "stable_Join_Stable";
*}

end
