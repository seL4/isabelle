(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition
From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January  2001 

Added: a strong form of the <= relation (component_of) and localize 

*)

theory Comp = Union:

instance program :: (type) ord ..

defs
  component_def:          "F <= H == EX G. F Join G = H"
  strict_component_def:   "(F < (H::'a program)) == (F <= H & F ~= H)"


constdefs
  component_of :: "'a program=>'a program=> bool"
                                    (infixl "component'_of" 50)
  "F component_of H == EX G. F ok G & F Join G = H"

  strict_component_of :: "'a program\<Rightarrow>'a program=> bool"
                                    (infixl "strict'_component'_of" 50)
  "F strict_component_of H == F component_of H & F~=H"
  
  preserves :: "('a=>'b) => 'a program set"
    "preserves v == INT z. stable {s. v s = z}"

  localize  :: "('a=>'b) => 'a program => 'a program"
  "localize v F == mk_program(Init F, Acts F,
			      AllowedActs F Int (UN G:preserves v. Acts G))"

  funPair      :: "['a => 'b, 'a => 'c, 'a] => 'b * 'c"
  "funPair f g == %x. (f x, g x)"


(*** component <= ***)
lemma componentI: 
     "H <= F | H <= G ==> H <= (F Join G)"
apply (unfold component_def, auto)
apply (rule_tac x = "G Join Ga" in exI)
apply (rule_tac [2] x = "G Join F" in exI)
apply (auto simp add: Join_ac)
done

lemma component_eq_subset: 
     "(F <= G) =  
      (Init G <= Init F & Acts F <= Acts G & AllowedActs G <= AllowedActs F)"
apply (unfold component_def)
apply (force intro!: exI program_equalityI)
done

lemma component_SKIP [iff]: "SKIP <= F"
apply (unfold component_def)
apply (force intro: Join_SKIP_left)
done

lemma component_refl [iff]: "F <= (F :: 'a program)"
apply (unfold component_def)
apply (blast intro: Join_SKIP_right)
done

lemma SKIP_minimal: "F <= SKIP ==> F = SKIP"
by (auto intro!: program_equalityI simp add: component_eq_subset)

lemma component_Join1: "F <= (F Join G)"
by (unfold component_def, blast)

lemma component_Join2: "G <= (F Join G)"
apply (unfold component_def)
apply (simp (no_asm) add: Join_commute)
apply blast
done

lemma Join_absorb1: "F<=G ==> F Join G = G"
by (auto simp add: component_def Join_left_absorb)

lemma Join_absorb2: "G<=F ==> F Join G = F"
by (auto simp add: Join_ac component_def)

lemma JN_component_iff: "((JOIN I F) <= H) = (ALL i: I. F i <= H)"
apply (simp (no_asm) add: component_eq_subset)
apply blast
done

lemma component_JN: "i : I ==> (F i) <= (JN i:I. (F i))"
apply (unfold component_def)
apply (blast intro: JN_absorb)
done

lemma component_trans: "[| F <= G; G <= H |] ==> F <= (H :: 'a program)"
apply (unfold component_def)
apply (blast intro: Join_assoc [symmetric])
done

lemma component_antisym: "[| F <= G; G <= F |] ==> F = (G :: 'a program)"
apply (simp (no_asm_use) add: component_eq_subset)
apply (blast intro!: program_equalityI)
done

lemma Join_component_iff: "((F Join G) <= H) = (F <= H & G <= H)"
apply (simp (no_asm) add: component_eq_subset)
apply blast
done

lemma component_constrains: "[| F <= G; G : A co B |] ==> F : A co B"
by (auto simp add: constrains_def component_eq_subset)

(*Used in Guar.thy to show that programs are partially ordered*)
lemmas program_less_le = strict_component_def [THEN meta_eq_to_obj_eq]


(*** preserves ***)

lemma preservesI: "(!!z. F : stable {s. v s = z}) ==> F : preserves v"
by (unfold preserves_def, blast)

lemma preserves_imp_eq: 
     "[| F : preserves v;  act : Acts F;  (s,s') : act |] ==> v s = v s'"
apply (unfold preserves_def stable_def constrains_def, force)
done

lemma Join_preserves [iff]: 
     "(F Join G : preserves v) = (F : preserves v & G : preserves v)"
apply (unfold preserves_def, auto)
done

lemma JN_preserves [iff]:
     "(JOIN I F : preserves v) = (ALL i:I. F i : preserves v)"
apply (simp (no_asm) add: JN_stable preserves_def)
apply blast
done

lemma SKIP_preserves [iff]: "SKIP : preserves v"
by (auto simp add: preserves_def)

lemma funPair_apply [simp]: "(funPair f g) x = (f x, g x)"
by (simp add:  funPair_def)

lemma preserves_funPair: "preserves (funPair v w) = preserves v Int preserves w"
by (auto simp add: preserves_def stable_def constrains_def, blast)

(* (F : preserves (funPair v w)) = (F : preserves v Int preserves w) *)
declare preserves_funPair [THEN eqset_imp_iff, iff]


lemma funPair_o_distrib: "(funPair f g) o h = funPair (f o h) (g o h)"
apply (simp (no_asm) add: funPair_def o_def)
done

lemma fst_o_funPair [simp]: "fst o (funPair f g) = f"
apply (simp (no_asm) add: funPair_def o_def)
done

lemma snd_o_funPair [simp]: "snd o (funPair f g) = g"
apply (simp (no_asm) add: funPair_def o_def)
done

lemma subset_preserves_o: "preserves v <= preserves (w o v)"
by (force simp add: preserves_def stable_def constrains_def)

lemma preserves_subset_stable: "preserves v <= stable {s. P (v s)}"
apply (auto simp add: preserves_def stable_def constrains_def)
apply (rename_tac s' s)
apply (subgoal_tac "v s = v s'")
apply (force+)
done

lemma preserves_subset_increasing: "preserves v <= increasing v"
by (auto simp add: preserves_subset_stable [THEN subsetD] increasing_def)

lemma preserves_id_subset_stable: "preserves id <= stable A"
by (force simp add: preserves_def stable_def constrains_def)


(** For use with def_UNION_ok_iff **)

lemma safety_prop_preserves [iff]: "safety_prop (preserves v)"
by (auto intro: safety_prop_INTER1 simp add: preserves_def)


(** Some lemmas used only in Client.ML **)

lemma stable_localTo_stable2:
     "[| F : stable {s. P (v s) (w s)};    
         G : preserves v;  G : preserves w |]                
      ==> F Join G : stable {s. P (v s) (w s)}"
apply (simp (no_asm_simp))
apply (subgoal_tac "G: preserves (funPair v w) ")
 prefer 2 apply simp 
apply (drule_tac P1 = "split ?Q" in  preserves_subset_stable [THEN subsetD], auto)
done

lemma Increasing_preserves_Stable:
     "[| F : stable {s. v s <= w s};  G : preserves v;        
         F Join G : Increasing w |]                
      ==> F Join G : Stable {s. v s <= w s}"
apply (auto simp add: stable_def Stable_def Increasing_def Constrains_def all_conj_distrib)
apply (blast intro: constrains_weaken)
(*The G case remains*)
apply (auto simp add: preserves_def stable_def constrains_def)
apply (case_tac "act: Acts F", blast)
(*We have a G-action, so delete assumptions about F-actions*)
apply (erule_tac V = "ALL act:Acts F. ?P act" in thin_rl)
apply (erule_tac V = "ALL z. ALL act:Acts F. ?P z act" in thin_rl)
apply (subgoal_tac "v x = v xa")
prefer 2 apply blast
apply auto
apply (erule order_trans, blast)
done

(** component_of **)

(*  component_of is stronger than <= *)
lemma component_of_imp_component: "F component_of H ==> F <= H"
by (unfold component_def component_of_def, blast)


(* component_of satisfies many of the <='s properties *)
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
apply (unfold localize_def)
apply (simp (no_asm))
done

lemma localize_Acts_eq [simp]: "Acts (localize v F) = Acts F"
apply (unfold localize_def)
apply (simp (no_asm))
done

lemma localize_AllowedActs_eq [simp]: 
 "AllowedActs (localize v F) = AllowedActs F Int (UN G:(preserves v). Acts G)"
apply (unfold localize_def, auto)
done

end
