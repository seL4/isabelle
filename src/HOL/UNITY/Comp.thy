(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition
From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January  2001

Added: a strong form of the \<subseteq> relation (component_of) and localize

*)

header{*Composition: Basic Primitives*}

theory Comp = Union:

instance program :: (type) ord ..

defs
  component_def:          "F \<le> H == \<exists>G. F\<squnion>G = H"
  strict_component_def:   "(F < (H::'a program)) == (F \<le> H & F \<noteq> H)"


constdefs
  component_of :: "'a program =>'a program=> bool"
                                    (infixl "component'_of" 50)
  "F component_of H == \<exists>G. F ok G & F\<squnion>G = H"

  strict_component_of :: "'a program\<Rightarrow>'a program=> bool"
                                    (infixl "strict'_component'_of" 50)
  "F strict_component_of H == F component_of H & F\<noteq>H"

  preserves :: "('a=>'b) => 'a program set"
    "preserves v == \<Inter>z. stable {s. v s = z}"

  localize  :: "('a=>'b) => 'a program => 'a program"
  "localize v F == mk_program(Init F, Acts F,
			      AllowedActs F \<inter> (\<Union>G \<in> preserves v. Acts G))"

  funPair      :: "['a => 'b, 'a => 'c, 'a] => 'b * 'c"
  "funPair f g == %x. (f x, g x)"


subsection{*The component relation*}
lemma componentI: "H \<le> F | H \<le> G ==> H \<le> (F\<squnion>G)"
apply (unfold component_def, auto)
apply (rule_tac x = "G\<squnion>Ga" in exI)
apply (rule_tac [2] x = "G\<squnion>F" in exI)
apply (auto simp add: Join_ac)
done

lemma component_eq_subset:
     "(F \<le> G) =
      (Init G \<subseteq> Init F & Acts F \<subseteq> Acts G & AllowedActs G \<subseteq> AllowedActs F)"
apply (unfold component_def)
apply (force intro!: exI program_equalityI)
done

lemma component_SKIP [iff]: "SKIP \<le> F"
apply (unfold component_def)
apply (force intro: Join_SKIP_left)
done

lemma component_refl [iff]: "F \<le> (F :: 'a program)"
apply (unfold component_def)
apply (blast intro: Join_SKIP_right)
done

lemma SKIP_minimal: "F \<le> SKIP ==> F = SKIP"
by (auto intro!: program_equalityI simp add: component_eq_subset)

lemma component_Join1: "F \<le> (F\<squnion>G)"
by (unfold component_def, blast)

lemma component_Join2: "G \<le> (F\<squnion>G)"
apply (unfold component_def)
apply (simp add: Join_commute, blast)
done

lemma Join_absorb1: "F \<le> G ==> F\<squnion>G = G"
by (auto simp add: component_def Join_left_absorb)

lemma Join_absorb2: "G \<le> F ==> F\<squnion>G = F"
by (auto simp add: Join_ac component_def)

lemma JN_component_iff: "((JOIN I F) \<le> H) = (\<forall>i \<in> I. F i \<le> H)"
by (simp add: component_eq_subset, blast)

lemma component_JN: "i \<in> I ==> (F i) \<le> (\<Squnion>i \<in> I. (F i))"
apply (unfold component_def)
apply (blast intro: JN_absorb)
done

lemma component_trans: "[| F \<le> G; G \<le> H |] ==> F \<le> (H :: 'a program)"
apply (unfold component_def)
apply (blast intro: Join_assoc [symmetric])
done

lemma component_antisym: "[| F \<le> G; G \<le> F |] ==> F = (G :: 'a program)"
apply (simp (no_asm_use) add: component_eq_subset)
apply (blast intro!: program_equalityI)
done

lemma Join_component_iff: "((F\<squnion>G) \<le> H) = (F \<le> H & G \<le> H)"
by (simp add: component_eq_subset, blast)

lemma component_constrains: "[| F \<le> G; G \<in> A co B |] ==> F \<in> A co B"
by (auto simp add: constrains_def component_eq_subset)

(*Used in Guar.thy to show that programs are partially ordered*)
lemmas program_less_le = strict_component_def [THEN meta_eq_to_obj_eq]


subsection{*The preserves property*}

lemma preservesI: "(!!z. F \<in> stable {s. v s = z}) ==> F \<in> preserves v"
by (unfold preserves_def, blast)

lemma preserves_imp_eq:
     "[| F \<in> preserves v;  act \<in> Acts F;  (s,s') \<in> act |] ==> v s = v s'"
by (unfold preserves_def stable_def constrains_def, force)

lemma Join_preserves [iff]:
     "(F\<squnion>G \<in> preserves v) = (F \<in> preserves v & G \<in> preserves v)"
by (unfold preserves_def, auto)

lemma JN_preserves [iff]:
     "(JOIN I F \<in> preserves v) = (\<forall>i \<in> I. F i \<in> preserves v)"
by (simp add: JN_stable preserves_def, blast)

lemma SKIP_preserves [iff]: "SKIP \<in> preserves v"
by (auto simp add: preserves_def)

lemma funPair_apply [simp]: "(funPair f g) x = (f x, g x)"
by (simp add:  funPair_def)

lemma preserves_funPair: "preserves (funPair v w) = preserves v \<inter> preserves w"
by (auto simp add: preserves_def stable_def constrains_def, blast)

(* (F \<in> preserves (funPair v w)) = (F \<in> preserves v \<inter> preserves w) *)
declare preserves_funPair [THEN eqset_imp_iff, iff]


lemma funPair_o_distrib: "(funPair f g) o h = funPair (f o h) (g o h)"
by (simp add: funPair_def o_def)

lemma fst_o_funPair [simp]: "fst o (funPair f g) = f"
by (simp add: funPair_def o_def)

lemma snd_o_funPair [simp]: "snd o (funPair f g) = g"
by (simp add: funPair_def o_def)

lemma subset_preserves_o: "preserves v \<subseteq> preserves (w o v)"
by (force simp add: preserves_def stable_def constrains_def)

lemma preserves_subset_stable: "preserves v \<subseteq> stable {s. P (v s)}"
apply (auto simp add: preserves_def stable_def constrains_def)
apply (rename_tac s' s)
apply (subgoal_tac "v s = v s'")
apply (force+)
done

lemma preserves_subset_increasing: "preserves v \<subseteq> increasing v"
by (auto simp add: preserves_subset_stable [THEN subsetD] increasing_def)

lemma preserves_id_subset_stable: "preserves id \<subseteq> stable A"
by (force simp add: preserves_def stable_def constrains_def)


(** For use with def_UNION_ok_iff **)

lemma safety_prop_preserves [iff]: "safety_prop (preserves v)"
by (auto intro: safety_prop_INTER1 simp add: preserves_def)


(** Some lemmas used only in Client.ML **)

lemma stable_localTo_stable2:
     "[| F \<in> stable {s. P (v s) (w s)};
         G \<in> preserves v;  G \<in> preserves w |]
      ==> F\<squnion>G \<in> stable {s. P (v s) (w s)}"
apply simp
apply (subgoal_tac "G \<in> preserves (funPair v w) ")
 prefer 2 apply simp
apply (drule_tac P1 = "split ?Q" in preserves_subset_stable [THEN subsetD], 
       auto)
done

lemma Increasing_preserves_Stable:
     "[| F \<in> stable {s. v s \<le> w s};  G \<in> preserves v; F\<squnion>G \<in> Increasing w |]
      ==> F\<squnion>G \<in> Stable {s. v s \<le> w s}"
apply (auto simp add: stable_def Stable_def Increasing_def Constrains_def all_conj_distrib)
apply (blast intro: constrains_weaken)
(*The G case remains*)
apply (auto simp add: preserves_def stable_def constrains_def)
apply (case_tac "act: Acts F", blast)
(*We have a G-action, so delete assumptions about F-actions*)
apply (erule_tac V = "\<forall>act \<in> Acts F. ?P act" in thin_rl)
apply (erule_tac V = "\<forall>z. \<forall>act \<in> Acts F. ?P z act" in thin_rl)
apply (subgoal_tac "v x = v xa")
 apply auto
apply (erule order_trans, blast)
done

(** component_of **)

(*  component_of is stronger than \<le> *)
lemma component_of_imp_component: "F component_of H ==> F \<le> H"
by (unfold component_def component_of_def, blast)


(* component_of satisfies many of the same properties as \<le> *)
lemma component_of_refl [simp]: "F component_of F"
apply (unfold component_of_def)
apply (rule_tac x = SKIP in exI, auto)
done

lemma component_of_SKIP [simp]: "SKIP component_of F"
by (unfold component_of_def, auto)

lemma component_of_trans:
     "[| F component_of G; G component_of H |] ==> F component_of H"
apply (unfold component_of_def)
apply (blast intro: Join_assoc [symmetric])
done

lemmas strict_component_of_eq =
    strict_component_of_def [THEN meta_eq_to_obj_eq, standard]

(** localize **)
lemma localize_Init_eq [simp]: "Init (localize v F) = Init F"
by (simp add: localize_def)

lemma localize_Acts_eq [simp]: "Acts (localize v F) = Acts F"
by (simp add: localize_def)

lemma localize_AllowedActs_eq [simp]:
   "AllowedActs (localize v F) = AllowedActs F \<inter> (\<Union>G \<in> preserves v. Acts G)"
by (unfold localize_def, auto)

end
