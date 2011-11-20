(*  Title:      HOL/UNITY/Rename.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge
*)

header{*Renaming of State Sets*}

theory Rename imports Extend begin

definition rename :: "['a => 'b, 'a program] => 'b program" where
    "rename h == extend (%(x,u::unit). h x)"

declare image_inv_f_f [simp] image_surj_f_inv_f [simp]

declare Extend.intro [simp,intro]

lemma good_map_bij [simp,intro]: "bij h ==> good_map (%(x,u). h x)"
apply (rule good_mapI)
apply (unfold bij_def inj_on_def surj_def, auto)
done

lemma fst_o_inv_eq_inv: "bij h ==> fst (inv (%(x,u). h x) s) = inv h s"
apply (unfold bij_def split_def, clarify)
apply (subgoal_tac "surj (%p. h (fst p))")
 prefer 2 apply (simp add: surj_def)
apply (erule injD)
apply (simp (no_asm_simp) add: surj_f_inv_f)
apply (erule surj_f_inv_f)
done

lemma mem_rename_set_iff: "bij h ==> z \<in> h`A = (inv h z \<in> A)"
by (force simp add: bij_is_inj bij_is_surj [THEN surj_f_inv_f])


lemma extend_set_eq_image [simp]: "extend_set (%(x,u). h x) A = h`A"
by (force simp add: extend_set_def)

lemma Init_rename [simp]: "Init (rename h F) = h`(Init F)"
by (simp add: rename_def)


subsection{*inverse properties*}

lemma extend_set_inv: 
     "bij h  
      ==> extend_set (%(x,u::'c). inv h x) = project_set (%(x,u::'c). h x)"
apply (unfold bij_def)
apply (rule ext)
apply (force simp add: extend_set_def project_set_def surj_f_inv_f)
done

(** for "rename" (programs) **)

lemma bij_extend_act_eq_project_act: "bij h  
      ==> extend_act (%(x,u::'c). h x) = project_act (%(x,u::'c). inv h x)"
apply (rule ext)
apply (force simp add: extend_act_def project_act_def bij_def surj_f_inv_f)
done

lemma bij_extend_act: "bij h ==> bij (extend_act (%(x,u::'c). h x))"
apply (rule bijI)
apply (rule Extend.inj_extend_act)
apply simp
apply (simp add: bij_extend_act_eq_project_act)
apply (rule surjI)
apply (rule Extend.extend_act_inverse)
apply (blast intro: bij_imp_bij_inv good_map_bij)
done

lemma bij_project_act: "bij h ==> bij (project_act (%(x,u::'c). h x))"
apply (frule bij_imp_bij_inv [THEN bij_extend_act])
apply (simp add: bij_extend_act_eq_project_act bij_imp_bij_inv inv_inv_eq)
done

lemma bij_inv_project_act_eq: "bij h ==> inv (project_act (%(x,u::'c). inv h x)) =  
                project_act (%(x,u::'c). h x)"
apply (simp (no_asm_simp) add: bij_extend_act_eq_project_act [symmetric])
apply (rule surj_imp_inv_eq)
apply (blast intro!: bij_extend_act bij_is_surj)
apply (simp (no_asm_simp) add: Extend.extend_act_inverse)
done

lemma extend_inv: "bij h   
      ==> extend (%(x,u::'c). inv h x) = project (%(x,u::'c). h x) UNIV"
apply (frule bij_imp_bij_inv)
apply (rule ext)
apply (rule program_equalityI)
  apply (simp (no_asm_simp) add: extend_set_inv)
 apply (simp add: Extend.project_act_Id Extend.Acts_extend 
          insert_Id_image_Acts bij_extend_act_eq_project_act inv_inv_eq) 
apply (simp add: Extend.AllowedActs_extend Extend.AllowedActs_project 
             bij_project_act bij_vimage_eq_inv_image bij_inv_project_act_eq)
done

lemma rename_inv_rename [simp]: "bij h ==> rename (inv h) (rename h F) = F"
by (simp add: rename_def extend_inv Extend.extend_inverse)

lemma rename_rename_inv [simp]: "bij h ==> rename h (rename (inv h) F) = F"
apply (frule bij_imp_bij_inv)
apply (erule inv_inv_eq [THEN subst], erule rename_inv_rename)
done

lemma rename_inv_eq: "bij h ==> rename (inv h) = inv (rename h)"
by (rule inv_equality [symmetric], auto)

(** (rename h) is bijective <=> h is bijective **)

lemma bij_extend: "bij h ==> bij (extend (%(x,u::'c). h x))"
apply (rule bijI)
apply (blast intro: Extend.inj_extend)
apply (rule_tac f = "extend (% (x,u) . inv h x)" in surjI) 
apply (subst (1 2) inv_inv_eq [of h, symmetric], assumption+)
apply (simp add: bij_imp_bij_inv extend_inv [of "inv h"]) 
apply (simp add: inv_inv_eq)
apply (rule Extend.extend_inverse) 
apply (simp add: bij_imp_bij_inv) 
done

lemma bij_project: "bij h ==> bij (project (%(x,u::'c). h x) UNIV)"
apply (subst extend_inv [symmetric])
apply (auto simp add: bij_imp_bij_inv bij_extend)
done

lemma inv_project_eq:
     "bij h   
      ==> inv (project (%(x,u::'c). h x) UNIV) = extend (%(x,u::'c). h x)"
apply (rule inj_imp_inv_eq)
apply (erule bij_project [THEN bij_is_inj])
apply (simp (no_asm_simp) add: Extend.extend_inverse)
done

lemma Allowed_rename [simp]:
     "bij h ==> Allowed (rename h F) = rename h ` Allowed F"
apply (simp (no_asm_simp) add: rename_def Extend.Allowed_extend)
apply (subst bij_vimage_eq_inv_image)
apply (rule bij_project, blast)
apply (simp (no_asm_simp) add: inv_project_eq)
done

lemma bij_rename: "bij h ==> bij (rename h)"
apply (simp (no_asm_simp) add: rename_def bij_extend)
done
lemmas surj_rename = bij_rename [THEN bij_is_surj]

lemma inj_rename_imp_inj: "inj (rename h) ==> inj h"
apply (unfold inj_on_def, auto)
apply (drule_tac x = "mk_program ({x}, {}, {})" in spec)
apply (drule_tac x = "mk_program ({y}, {}, {})" in spec)
apply (auto simp add: program_equality_iff rename_def extend_def)
done

lemma surj_rename_imp_surj: "surj (rename h) ==> surj h"
apply (unfold surj_def, auto)
apply (drule_tac x = "mk_program ({y}, {}, {})" in spec)
apply (auto simp add: program_equality_iff rename_def extend_def)
done

lemma bij_rename_imp_bij: "bij (rename h) ==> bij h"
apply (unfold bij_def)
apply (simp (no_asm_simp) add: inj_rename_imp_inj surj_rename_imp_surj)
done

lemma bij_rename_iff [simp]: "bij (rename h) = bij h"
by (blast intro: bij_rename bij_rename_imp_bij)


subsection{*the lattice operations*}

lemma rename_SKIP [simp]: "bij h ==> rename h SKIP = SKIP"
by (simp add: rename_def Extend.extend_SKIP)

lemma rename_Join [simp]: 
     "bij h ==> rename h (F Join G) = rename h F Join rename h G"
by (simp add: rename_def Extend.extend_Join)

lemma rename_JN [simp]:
     "bij h ==> rename h (JOIN I F) = (\<Squnion>i \<in> I. rename h (F i))"
by (simp add: rename_def Extend.extend_JN)


subsection{*Strong Safety: co, stable*}

lemma rename_constrains: 
     "bij h ==> (rename h F \<in> (h`A) co (h`B)) = (F \<in> A co B)"
apply (unfold rename_def)
apply (subst extend_set_eq_image [symmetric])+
apply (erule good_map_bij [THEN Extend.intro, THEN Extend.extend_constrains])
done

lemma rename_stable: 
     "bij h ==> (rename h F \<in> stable (h`A)) = (F \<in> stable A)"
apply (simp add: stable_def rename_constrains)
done

lemma rename_invariant:
     "bij h ==> (rename h F \<in> invariant (h`A)) = (F \<in> invariant A)"
apply (simp add: invariant_def rename_stable bij_is_inj [THEN inj_image_subset_iff])
done

lemma rename_increasing:
     "bij h ==> (rename h F \<in> increasing func) = (F \<in> increasing (func o h))"
apply (simp add: increasing_def rename_stable [symmetric] bij_image_Collect_eq bij_is_surj [THEN surj_f_inv_f])
done


subsection{*Weak Safety: Co, Stable*}

lemma reachable_rename_eq: 
     "bij h ==> reachable (rename h F) = h ` (reachable F)"
apply (simp add: rename_def Extend.reachable_extend_eq)
done

lemma rename_Constrains:
     "bij h ==> (rename h F \<in> (h`A) Co (h`B)) = (F \<in> A Co B)"
by (simp add: Constrains_def reachable_rename_eq rename_constrains
               bij_is_inj image_Int [symmetric])

lemma rename_Stable: 
     "bij h ==> (rename h F \<in> Stable (h`A)) = (F \<in> Stable A)"
by (simp add: Stable_def rename_Constrains)

lemma rename_Always: "bij h ==> (rename h F \<in> Always (h`A)) = (F \<in> Always A)"
by (simp add: Always_def rename_Stable bij_is_inj [THEN inj_image_subset_iff])

lemma rename_Increasing:
     "bij h ==> (rename h F \<in> Increasing func) = (F \<in> Increasing (func o h))"
by (simp add: Increasing_def rename_Stable [symmetric] bij_image_Collect_eq 
              bij_is_surj [THEN surj_f_inv_f])


subsection{*Progress: transient, ensures*}

lemma rename_transient: 
     "bij h ==> (rename h F \<in> transient (h`A)) = (F \<in> transient A)"
apply (unfold rename_def)
apply (subst extend_set_eq_image [symmetric])
apply (erule good_map_bij [THEN Extend.intro, THEN Extend.extend_transient])
done

lemma rename_ensures: 
     "bij h ==> (rename h F \<in> (h`A) ensures (h`B)) = (F \<in> A ensures B)"
apply (unfold rename_def)
apply (subst extend_set_eq_image [symmetric])+
apply (erule good_map_bij [THEN Extend.intro, THEN Extend.extend_ensures])
done

lemma rename_leadsTo: 
     "bij h ==> (rename h F \<in> (h`A) leadsTo (h`B)) = (F \<in> A leadsTo B)"
apply (unfold rename_def)
apply (subst extend_set_eq_image [symmetric])+
apply (erule good_map_bij [THEN Extend.intro, THEN Extend.extend_leadsTo])
done

lemma rename_LeadsTo: 
     "bij h ==> (rename h F \<in> (h`A) LeadsTo (h`B)) = (F \<in> A LeadsTo B)"
apply (unfold rename_def)
apply (subst extend_set_eq_image [symmetric])+
apply (erule good_map_bij [THEN Extend.intro, THEN Extend.extend_LeadsTo])
done

lemma rename_rename_guarantees_eq: 
     "bij h ==> (rename h F \<in> (rename h ` X) guarantees  
                              (rename h ` Y)) =  
                (F \<in> X guarantees Y)"
apply (unfold rename_def)
apply (subst good_map_bij [THEN Extend.intro, THEN Extend.extend_guarantees_eq [symmetric]], assumption)
apply (simp (no_asm_simp) add: fst_o_inv_eq_inv o_def)
done

lemma rename_guarantees_eq_rename_inv:
     "bij h ==> (rename h F \<in> X guarantees Y) =  
                (F \<in> (rename (inv h) ` X) guarantees  
                     (rename (inv h) ` Y))"
apply (subst rename_rename_guarantees_eq [symmetric], assumption)
apply (simp add: image_eq_UN o_def bij_is_surj [THEN surj_f_inv_f])
done

lemma rename_preserves:
     "bij h ==> (rename h G \<in> preserves v) = (G \<in> preserves (v o h))"
apply (subst good_map_bij [THEN Extend.intro, THEN Extend.extend_preserves [symmetric]], assumption)
apply (simp add: o_def fst_o_inv_eq_inv rename_def bij_is_surj [THEN surj_f_inv_f])
done

lemma ok_rename_iff [simp]: "bij h ==> (rename h F ok rename h G) = (F ok G)"
by (simp add: Extend.ok_extend_iff rename_def)

lemma OK_rename_iff [simp]: "bij h ==> OK I (%i. rename h (F i)) = (OK I F)"
by (simp add: Extend.OK_extend_iff rename_def)


subsection{*"image" versions of the rules, for lifting "guarantees" properties*}

(*All the proofs are similar.  Better would have been to prove one 
  meta-theorem, but how can we handle the polymorphism?  E.g. in 
  rename_constrains the two appearances of "co" have different types!*)
lemmas bij_eq_rename = surj_rename [THEN surj_f_inv_f, symmetric]

lemma rename_image_constrains:
     "bij h ==> rename h ` (A co B) = (h ` A) co (h`B)" 
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_constrains) 
done

lemma rename_image_stable: "bij h ==> rename h ` stable A = stable (h ` A)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_stable)
done

lemma rename_image_increasing:
     "bij h ==> rename h ` increasing func = increasing (func o inv h)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_increasing o_def bij_is_inj) 
done

lemma rename_image_invariant:
     "bij h ==> rename h ` invariant A = invariant (h ` A)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_invariant) 
done

lemma rename_image_Constrains:
     "bij h ==> rename h ` (A Co B) = (h ` A) Co (h`B)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_Constrains)
done

lemma rename_image_preserves:
     "bij h ==> rename h ` preserves v = preserves (v o inv h)"
by (simp add: o_def rename_image_stable preserves_def bij_image_INT 
              bij_image_Collect_eq)

lemma rename_image_Stable:
     "bij h ==> rename h ` Stable A = Stable (h ` A)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_Stable) 
done

lemma rename_image_Increasing:
     "bij h ==> rename h ` Increasing func = Increasing (func o inv h)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_Increasing o_def bij_is_inj)
done

lemma rename_image_Always: "bij h ==> rename h ` Always A = Always (h ` A)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_Always)
done

lemma rename_image_leadsTo:
     "bij h ==> rename h ` (A leadsTo B) = (h ` A) leadsTo (h`B)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_leadsTo) 
done

lemma rename_image_LeadsTo:
     "bij h ==> rename h ` (A LeadsTo B) = (h ` A) LeadsTo (h`B)"
apply auto 
 defer 1
 apply (rename_tac F) 
 apply (subgoal_tac "\<exists>G. F = rename h G") 
 apply (auto intro!: bij_eq_rename simp add: rename_LeadsTo) 
done

end
