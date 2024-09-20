(*  Title:      ZF/UNITY/Guar.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January 2001

Added \<in> Compatibility, weakest guarantees, etc.

and Weakest existential property,
from Charpentier and Chandy "Theorems about Composition",
Fifth International Conference on Mathematics of Program, 2000.

Theory ported from HOL.
*)


section\<open>The Chandy-Sanders Guarantees Operator\<close>

theory Guar imports Comp begin 


(* To be moved to theory WFair???? *)
lemma leadsTo_Basis': "\<lbrakk>F \<in> A co A \<union> B; F \<in> transient(A); st_set(B)\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto> B"
apply (frule constrainsD2)
apply (drule_tac B = "A-B" in constrains_weaken_L, blast) 
apply (drule_tac B = "A-B" in transient_strengthen, blast) 
apply (blast intro: ensuresI [THEN leadsTo_Basis])
done


  (*Existential and Universal properties.  We formalize the two-program
    case, proving equivalence with Chandy and Sanders's n-ary definitions*)

definition
   ex_prop :: "i \<Rightarrow> o"  where
   "ex_prop(X) \<equiv> X<=program \<and>
    (\<forall>F \<in> program. \<forall>G \<in> program. F ok G \<longrightarrow> F \<in> X | G \<in> X \<longrightarrow> (F \<squnion> G) \<in> X)"

definition
  strict_ex_prop  :: "i \<Rightarrow> o"  where
  "strict_ex_prop(X) \<equiv> X<=program \<and>
   (\<forall>F \<in> program. \<forall>G \<in> program. F ok G \<longrightarrow> (F \<in> X | G \<in> X) \<longleftrightarrow> (F \<squnion> G \<in> X))"

definition
  uv_prop  :: "i \<Rightarrow> o"  where
   "uv_prop(X) \<equiv> X<=program \<and>
    (SKIP \<in> X \<and> (\<forall>F \<in> program. \<forall>G \<in> program. F ok G \<longrightarrow> F \<in> X \<and> G \<in> X \<longrightarrow> (F \<squnion> G) \<in> X))"
  
definition
 strict_uv_prop  :: "i \<Rightarrow> o"  where
   "strict_uv_prop(X) \<equiv> X<=program \<and>
    (SKIP \<in> X \<and> (\<forall>F \<in> program. \<forall>G \<in> program. F ok G \<longrightarrow>(F \<in> X \<and> G \<in> X) \<longleftrightarrow> (F \<squnion> G \<in> X)))"

definition
  guar :: "[i, i] \<Rightarrow> i" (infixl \<open>guarantees\<close> 55)  where
              (*higher than membership, lower than Co*)
  "X guarantees Y \<equiv> {F \<in> program. \<forall>G \<in> program. F ok G \<longrightarrow> F \<squnion> G \<in> X \<longrightarrow> F \<squnion> G \<in> Y}"
  
definition
  (* Weakest guarantees *)
   wg :: "[i,i] \<Rightarrow> i"  where
  "wg(F,Y) \<equiv> \<Union>({X \<in> Pow(program). F:(X guarantees Y)})"

definition
  (* Weakest existential property stronger than X *)
   wx :: "i \<Rightarrow>i"  where
   "wx(X) \<equiv> \<Union>({Y \<in> Pow(program). Y<=X \<and> ex_prop(Y)})"

definition
  (*Ill-defined programs can arise through "\<squnion>"*)
  welldef :: i  where
  "welldef \<equiv> {F \<in> program. Init(F) \<noteq> 0}"
  
definition
  refines :: "[i, i, i] \<Rightarrow> o" (\<open>(\<open>indent=3 notation=\<open>mixfix refines wrt\<close>\<close>_ refines _ wrt _)\<close> [10,10,10] 10)  where
  "G refines F wrt X \<equiv>
   \<forall>H \<in> program. (F ok H  \<and> G ok H \<and> F \<squnion> H \<in> welldef \<inter> X)
    \<longrightarrow> (G \<squnion> H \<in> welldef \<inter> X)"

definition
  iso_refines :: "[i,i, i] \<Rightarrow> o"  (\<open>(\<open>indent=3 notation=\<open>mixfix iso_refines wrt\<close>\<close>_ iso'_refines _ wrt _)\<close> [10,10,10] 10)  where
  "G iso_refines F wrt X \<equiv>  F \<in> welldef \<inter> X \<longrightarrow> G \<in> welldef \<inter> X"


(*** existential properties ***)

lemma ex_imp_subset_program: "ex_prop(X) \<Longrightarrow> X\<subseteq>program"
by (simp add: ex_prop_def)

lemma ex1 [rule_format]: 
 "GG \<in> Fin(program) 
  \<Longrightarrow> ex_prop(X) \<longrightarrow> GG \<inter> X\<noteq>0 \<longrightarrow> OK(GG, (\<lambda>G. G)) \<longrightarrow>(\<Squnion>G \<in> GG. G) \<in> X"
  unfolding ex_prop_def
apply (erule Fin_induct)
apply (simp_all add: OK_cons_iff)
apply (safe elim!: not_emptyE, auto) 
done

lemma ex2 [rule_format]: 
"X \<subseteq> program \<Longrightarrow>  
 (\<forall>GG \<in> Fin(program). GG \<inter> X \<noteq> 0 \<longrightarrow> OK(GG,(\<lambda>G. G))\<longrightarrow>(\<Squnion>G \<in> GG. G) \<in> X) 
   \<longrightarrow> ex_prop(X)"
apply (unfold ex_prop_def, clarify)
apply (drule_tac x = "{F,G}" in bspec)
apply (simp_all add: OK_iff_ok)
apply (auto intro: ok_sym)
done

(*Chandy \<and> Sanders take this as a definition*)

lemma ex_prop_finite:
     "ex_prop(X) \<longleftrightarrow> (X\<subseteq>program \<and>  
  (\<forall>GG \<in> Fin(program). GG \<inter> X \<noteq> 0 \<and> OK(GG,(\<lambda>G. G))\<longrightarrow>(\<Squnion>G \<in> GG. G) \<in> X))"
apply auto
apply (blast intro: ex1 ex2 dest: ex_imp_subset_program)+
done

(* Equivalent definition of ex_prop given at the end of section 3*)
lemma ex_prop_equiv: 
"ex_prop(X) \<longleftrightarrow>  
  X\<subseteq>program \<and> (\<forall>G \<in> program. (G \<in> X \<longleftrightarrow> (\<forall>H \<in> program. (G component_of H) \<longrightarrow> H \<in> X)))"
apply (unfold ex_prop_def component_of_def, safe, force, force, blast) 
apply (subst Join_commute)
apply (blast intro: ok_sym) 
done

(*** universal properties ***)

lemma uv_imp_subset_program: "uv_prop(X)\<Longrightarrow> X\<subseteq>program"
  unfolding uv_prop_def
apply (simp (no_asm_simp))
done

lemma uv1 [rule_format]: 
     "GG \<in> Fin(program) \<Longrightarrow>  
      (uv_prop(X)\<longrightarrow> GG \<subseteq> X \<and> OK(GG, (\<lambda>G. G)) \<longrightarrow> (\<Squnion>G \<in> GG. G) \<in> X)"
  unfolding uv_prop_def
apply (erule Fin_induct)
apply (auto simp add: OK_cons_iff)
done

lemma uv2 [rule_format]: 
     "X\<subseteq>program  \<Longrightarrow> 
      (\<forall>GG \<in> Fin(program). GG \<subseteq> X \<and> OK(GG,(\<lambda>G. G)) \<longrightarrow> (\<Squnion>G \<in> GG. G) \<in> X)
      \<longrightarrow> uv_prop(X)"
apply (unfold uv_prop_def, auto)
apply (drule_tac x = 0 in bspec, simp+) 
apply (drule_tac x = "{F,G}" in bspec, simp) 
apply (force dest: ok_sym simp add: OK_iff_ok) 
done

(*Chandy \<and> Sanders take this as a definition*)
lemma uv_prop_finite: 
"uv_prop(X) \<longleftrightarrow> X\<subseteq>program \<and>  
  (\<forall>GG \<in> Fin(program). GG \<subseteq> X \<and> OK(GG, \<lambda>G. G) \<longrightarrow> (\<Squnion>G \<in> GG. G) \<in>  X)"
apply auto
apply (blast dest: uv_imp_subset_program)
apply (blast intro: uv1)
apply (blast intro!: uv2 dest:)
done

(*** guarantees ***)
lemma guaranteesI: 
     "\<lbrakk>(\<And>G. \<lbrakk>F ok G; F \<squnion> G \<in> X; G \<in> program\<rbrakk> \<Longrightarrow> F \<squnion> G \<in> Y); 
         F \<in> program\<rbrakk>   
    \<Longrightarrow> F \<in> X guarantees Y"
by (simp add: guar_def component_def)

lemma guaranteesD: 
     "\<lbrakk>F \<in> X guarantees Y;  F ok G;  F \<squnion> G \<in> X; G \<in> program\<rbrakk>  
      \<Longrightarrow> F \<squnion> G \<in> Y"
by (simp add: guar_def component_def)


(*This version of guaranteesD matches more easily in the conclusion
  The major premise can no longer be  F\<subseteq>H since we need to reason about G*)

lemma component_guaranteesD: 
     "\<lbrakk>F \<in> X guarantees Y;  F \<squnion> G = H;  H \<in> X;  F ok G; G \<in> program\<rbrakk>  
      \<Longrightarrow> H \<in> Y"
by (simp add: guar_def, blast)

lemma guarantees_weaken: 
     "\<lbrakk>F \<in> X guarantees X'; Y \<subseteq> X; X' \<subseteq> Y'\<rbrakk> \<Longrightarrow> F \<in> Y guarantees Y'"
by (simp add: guar_def, auto)

lemma subset_imp_guarantees_program:
     "X \<subseteq> Y \<Longrightarrow> X guarantees Y = program"
by (unfold guar_def, blast)

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
lemma subset_imp_guarantees:
     "\<lbrakk>X \<subseteq> Y; F \<in> program\<rbrakk> \<Longrightarrow> F \<in> X guarantees Y"
by (unfold guar_def, blast)

lemma component_of_Join1: "F ok G \<Longrightarrow> F component_of (F \<squnion> G)"
by (unfold component_of_def, blast)

lemma component_of_Join2: "F ok G \<Longrightarrow> G component_of (F \<squnion> G)"
apply (subst Join_commute)
apply (blast intro: ok_sym component_of_Join1)
done

(*Remark at end of section 4.1 *)
lemma ex_prop_imp: 
     "ex_prop(Y) \<Longrightarrow> (Y = (program guarantees Y))"
apply (simp (no_asm_use) add: ex_prop_equiv guar_def component_of_def)
apply clarify
apply (rule equalityI, blast, safe)
apply (drule_tac x = x in bspec, assumption, force) 
done

lemma guarantees_imp: "(Y = program guarantees Y) \<Longrightarrow> ex_prop(Y)"
  unfolding guar_def
apply (simp (no_asm_simp) add: ex_prop_equiv)
apply safe
apply (blast intro: elim: equalityE) 
apply (simp_all (no_asm_use) add: component_of_def)
apply (force elim: equalityE)+
done

lemma ex_prop_equiv2: "(ex_prop(Y)) \<longleftrightarrow> (Y = program guarantees Y)"
by (blast intro: ex_prop_imp guarantees_imp)

(** Distributive laws.  Re-orient to perform miniscoping **)

lemma guarantees_UN_left: 
     "i \<in> I \<Longrightarrow>(\<Union>i \<in> I. X(i)) guarantees Y = (\<Inter>i \<in> I. X(i) guarantees Y)"
  unfolding guar_def
apply (rule equalityI, safe)
 prefer 2 apply force
apply blast+
done

lemma guarantees_Un_left: 
     "(X \<union> Y) guarantees Z = (X guarantees Z) \<inter> (Y guarantees Z)"
  unfolding guar_def
apply (rule equalityI, safe, blast+)
done

lemma guarantees_INT_right: 
     "i \<in> I \<Longrightarrow> X guarantees (\<Inter>i \<in> I. Y(i)) = (\<Inter>i \<in> I. X guarantees Y(i))"
  unfolding guar_def
apply (rule equalityI, safe, blast+)
done

lemma guarantees_Int_right: 
     "Z guarantees (X \<inter> Y) = (Z guarantees X) \<inter> (Z guarantees Y)"
by (unfold guar_def, blast)

lemma guarantees_Int_right_I:
     "\<lbrakk>F \<in> Z guarantees X;  F \<in> Z guarantees Y\<rbrakk>  
     \<Longrightarrow> F \<in> Z guarantees (X \<inter> Y)"
by (simp (no_asm_simp) add: guarantees_Int_right)

lemma guarantees_INT_right_iff:
     "i \<in> I\<Longrightarrow> (F \<in> X guarantees (\<Inter>i \<in> I. Y(i))) \<longleftrightarrow>  
      (\<forall>i \<in> I. F \<in> X guarantees Y(i))"
by (simp add: guarantees_INT_right INT_iff, blast)


lemma shunting: "(X guarantees Y) = (program guarantees ((program-X) \<union> Y))"
by (unfold guar_def, auto)

lemma contrapositive:
     "(X guarantees Y) = (program - Y) guarantees (program -X)"
by (unfold guar_def, blast)

(** The following two can be expressed using intersection and subset, which
    is more faithful to the text but looks cryptic.
**)

lemma combining1: 
    "\<lbrakk>F \<in> V guarantees X;  F \<in> (X \<inter> Y) guarantees Z\<rbrakk> 
     \<Longrightarrow> F \<in> (V \<inter> Y) guarantees Z"
by (unfold guar_def, blast)

lemma combining2: 
    "\<lbrakk>F \<in> V guarantees (X \<union> Y);  F \<in> Y guarantees Z\<rbrakk> 
     \<Longrightarrow> F \<in> V guarantees (X \<union> Z)"
by (unfold guar_def, blast)


(** The following two follow Chandy-Sanders, but the use of object-quantifiers
    does not suit Isabelle... **)

(*Premise should be (\<And>i. i \<in> I \<Longrightarrow> F \<in> X guarantees Y i) *)
lemma all_guarantees: 
     "\<lbrakk>\<forall>i \<in> I. F \<in> X guarantees Y(i); i \<in> I\<rbrakk>  
    \<Longrightarrow> F \<in> X guarantees (\<Inter>i \<in> I. Y(i))"
by (unfold guar_def, blast)

(*Premises should be \<lbrakk>F \<in> X guarantees Y i; i \<in> I\<rbrakk> *)
lemma ex_guarantees: 
     "\<exists>i \<in> I. F \<in> X guarantees Y(i) \<Longrightarrow> F \<in> X guarantees (\<Union>i \<in> I. Y(i))"
by (unfold guar_def, blast)


(*** Additional guarantees laws, by lcp ***)

lemma guarantees_Join_Int: 
    "\<lbrakk>F \<in> U guarantees V;  G \<in> X guarantees Y; F ok G\<rbrakk>  
     \<Longrightarrow> F \<squnion> G: (U \<inter> X) guarantees (V \<inter> Y)"

  unfolding guar_def
apply (simp (no_asm))
apply safe
apply (simp add: Join_assoc)
apply (subgoal_tac "F \<squnion> G \<squnion> Ga = G \<squnion> (F \<squnion> Ga) ")
apply (simp add: ok_commute)
apply (simp (no_asm_simp) add: Join_ac)
done

lemma guarantees_Join_Un: 
    "\<lbrakk>F \<in> U guarantees V;  G \<in> X guarantees Y; F ok G\<rbrakk>   
     \<Longrightarrow> F \<squnion> G: (U \<union> X) guarantees (V \<union> Y)"
  unfolding guar_def
apply (simp (no_asm))
apply safe
apply (simp add: Join_assoc)
apply (subgoal_tac "F \<squnion> G \<squnion> Ga = G \<squnion> (F \<squnion> Ga) ")
apply (rotate_tac 4)
apply (drule_tac x = "F \<squnion> Ga" in bspec)
apply (simp (no_asm))
apply (force simp add: ok_commute)
apply (simp (no_asm_simp) add: Join_ac)
done

lemma guarantees_JOIN_INT: 
     "\<lbrakk>\<forall>i \<in> I. F(i) \<in> X(i) guarantees Y(i);  OK(I,F); i \<in> I\<rbrakk>  
      \<Longrightarrow> (\<Squnion>i \<in> I. F(i)) \<in> (\<Inter>i \<in> I. X(i)) guarantees (\<Inter>i \<in> I. Y(i))"
apply (unfold guar_def, safe)
 prefer 2 apply blast
apply (drule_tac x = xa in bspec)
apply (simp_all add: INT_iff, safe)
apply (drule_tac x = "(\<Squnion>x \<in> (I-{xa}) . F (x)) \<squnion> G" and A=program in bspec)
apply (auto intro: OK_imp_ok simp add: Join_assoc [symmetric] JOIN_Join_diff JOIN_absorb)
done

lemma guarantees_JOIN_UN: 
    "\<lbrakk>\<forall>i \<in> I. F(i) \<in> X(i) guarantees Y(i);  OK(I,F)\<rbrakk>  
     \<Longrightarrow> JOIN(I,F) \<in> (\<Union>i \<in> I. X(i)) guarantees (\<Union>i \<in> I. Y(i))"
apply (unfold guar_def, auto)
apply (drule_tac x = y in bspec, simp_all, safe)
apply (rename_tac G y)
apply (drule_tac x = "JOIN (I-{y}, F) \<squnion> G" and A=program in bspec)
apply (auto intro: OK_imp_ok simp add: Join_assoc [symmetric] JOIN_Join_diff JOIN_absorb)
done

(*** guarantees laws for breaking down the program, by lcp ***)

lemma guarantees_Join_I1: 
     "\<lbrakk>F \<in> X guarantees Y;  F ok G\<rbrakk> \<Longrightarrow> F \<squnion> G \<in> X guarantees Y"
apply (simp add: guar_def, safe)
apply (simp add: Join_assoc)
done

lemma guarantees_Join_I2:
     "\<lbrakk>G \<in> X guarantees Y;  F ok G\<rbrakk> \<Longrightarrow> F \<squnion> G \<in> X guarantees Y"
apply (simp add: Join_commute [of _ G] ok_commute [of _ G])
apply (blast intro: guarantees_Join_I1)
done

lemma guarantees_JOIN_I: 
     "\<lbrakk>i \<in> I; F(i) \<in>  X guarantees Y;  OK(I,F)\<rbrakk>  
      \<Longrightarrow> (\<Squnion>i \<in> I. F(i)) \<in> X guarantees Y"
apply (unfold guar_def, safe)
apply (drule_tac x = "JOIN (I-{i},F) \<squnion> G" in bspec)
apply (simp (no_asm))
apply (auto intro: OK_imp_ok simp add: JOIN_Join_diff Join_assoc [symmetric])
done

(*** well-definedness ***)

lemma Join_welldef_D1: "F \<squnion> G \<in> welldef \<Longrightarrow> programify(F) \<in>  welldef"
by (unfold welldef_def, auto)

lemma Join_welldef_D2: "F \<squnion> G \<in> welldef \<Longrightarrow> programify(G) \<in>  welldef"
by (unfold welldef_def, auto)

(*** refinement ***)

lemma refines_refl: "F refines F wrt X"
by (unfold refines_def, blast)

(* More results on guarantees, added by Sidi Ehmety from Chandy \<and> Sander, section 6 *)

lemma wg_type: "wg(F, X) \<subseteq> program"
by (unfold wg_def, auto)

lemma guarantees_type: "X guarantees Y \<subseteq> program"
by (unfold guar_def, auto)

lemma wgD2: "G \<in> wg(F, X) \<Longrightarrow> G \<in> program \<and> F \<in> program"
apply (unfold wg_def, auto)
apply (blast dest: guarantees_type [THEN subsetD])
done

lemma guarantees_equiv: 
"(F \<in> X guarantees Y) \<longleftrightarrow>  
   F \<in> program \<and> (\<forall>H \<in> program. H \<in> X \<longrightarrow> (F component_of H \<longrightarrow> H \<in> Y))"
by (unfold guar_def component_of_def, force) 

lemma wg_weakest:
     "\<And>X. \<lbrakk>F \<in> (X guarantees Y); X \<subseteq> program\<rbrakk> \<Longrightarrow> X \<subseteq> wg(F,Y)"
by (unfold wg_def, auto)

lemma wg_guarantees: "F \<in> program \<Longrightarrow> F \<in> wg(F,Y) guarantees Y"
by (unfold wg_def guar_def, blast)

lemma wg_equiv:
     "H \<in> wg(F,X) \<longleftrightarrow> 
      ((F component_of H \<longrightarrow> H \<in> X) \<and> F \<in> program \<and> H \<in> program)"
apply (simp add: wg_def guarantees_equiv)
apply (rule iffI, safe)
apply (rule_tac [4] x = "{H}" in bexI)
apply (rule_tac [3] x = "{H}" in bexI, blast+)
done

lemma component_of_wg: 
    "F component_of H \<Longrightarrow> H \<in> wg(F,X) \<longleftrightarrow> (H \<in> X \<and> F \<in> program \<and> H \<in> program)"
by (simp (no_asm_simp) add: wg_equiv)

lemma wg_finite [rule_format]: 
"\<forall>FF \<in> Fin(program). FF \<inter> X \<noteq> 0 \<longrightarrow> OK(FF, \<lambda>F. F)  
   \<longrightarrow> (\<forall>F \<in> FF. ((\<Squnion>F \<in> FF. F) \<in>  wg(F,X)) \<longleftrightarrow> ((\<Squnion>F \<in> FF. F) \<in> X))"
apply clarify
apply (subgoal_tac "F component_of (\<Squnion>F \<in> FF. F) ")
apply (drule_tac X = X in component_of_wg)
apply (force dest!: Fin.dom_subset [THEN subsetD, THEN PowD])
apply (simp_all add: component_of_def)
apply (rule_tac x = "\<Squnion>F \<in> (FF-{F}) . F" in exI)
apply (auto intro: JOIN_Join_diff dest: ok_sym simp add: OK_iff_ok)
done

lemma wg_ex_prop:
     "ex_prop(X) \<Longrightarrow> (F \<in> X) \<longleftrightarrow> (\<forall>H \<in> program. H \<in> wg(F,X) \<and> F \<in> program)"
apply (simp (no_asm_use) add: ex_prop_equiv wg_equiv)
apply blast
done

(** From Charpentier and Chandy "Theorems About Composition" **)
(* Proposition 2 *)
lemma wx_subset: "wx(X)\<subseteq>X"
by (unfold wx_def, auto)

lemma wx_ex_prop: "ex_prop(wx(X))"
apply (simp (no_asm_use) add: ex_prop_def wx_def)
apply safe
apply blast
apply (rule_tac x=x in bexI, force, simp)+
done

lemma wx_weakest: "\<forall>Z. Z\<subseteq>program \<longrightarrow> Z\<subseteq> X \<longrightarrow> ex_prop(Z) \<longrightarrow> Z \<subseteq> wx(X)"
by (unfold wx_def, auto)

(* Proposition 6 *)
lemma wx'_ex_prop: 
 "ex_prop({F \<in> program. \<forall>G \<in> program. F ok G \<longrightarrow> F \<squnion> G \<in> X})"
apply (unfold ex_prop_def, safe)
 apply (drule_tac x = "G \<squnion> Ga" in bspec)
  apply (simp (no_asm))
 apply (force simp add: Join_assoc)
apply (drule_tac x = "F \<squnion> Ga" in bspec)
 apply (simp (no_asm))
apply (simp (no_asm_use))
apply safe
 apply (simp (no_asm_simp) add: ok_commute)
apply (subgoal_tac "F \<squnion> G = G \<squnion> F")
 apply (simp (no_asm_simp) add: Join_assoc)
apply (simp (no_asm) add: Join_commute)
done

(* Equivalence with the other definition of wx *)

lemma wx_equiv: 
     "wx(X) = {F \<in> program. \<forall>G \<in> program. F ok G \<longrightarrow> (F \<squnion> G) \<in> X}"
  unfolding wx_def
apply (rule equalityI, safe, blast)
 apply (simp (no_asm_use) add: ex_prop_def)
apply blast 
apply (rule_tac B = "{F \<in> program. \<forall>G \<in> program. F ok G \<longrightarrow> F \<squnion> G \<in> X}" 
         in UnionI, 
       safe)
apply (rule_tac [2] wx'_ex_prop)
apply (drule_tac x=SKIP in bspec, simp)+
apply auto 
done

(* Propositions 7 to 11 are all about this second definition of wx. And
   by equivalence between the two definition, they are the same as the ones proved *)


(* Proposition 12 *)
(* Main result of the paper *)
lemma guarantees_wx_eq: "(X guarantees Y) = wx((program-X) \<union> Y)"
by (auto simp add: guar_def wx_equiv)

(* 
{* Corollary, but this result has already been proved elsewhere *}
 "ex_prop(X guarantees Y)"
*)

(* Rules given in section 7 of Chandy and Sander's
    Reasoning About Program composition paper *)

lemma stable_guarantees_Always:
     "\<lbrakk>Init(F) \<subseteq> A; F \<in> program\<rbrakk> \<Longrightarrow> F \<in> stable(A) guarantees Always(A)"
apply (rule guaranteesI)
 prefer 2 apply assumption
apply (simp (no_asm) add: Join_commute)
apply (rule stable_Join_Always1)
apply (simp_all add: invariant_def)
apply (auto simp add: programify_def initially_def)
done

lemma constrains_guarantees_leadsTo:
     "\<lbrakk>F \<in> transient(A); st_set(B)\<rbrakk> 
      \<Longrightarrow> F: (A co A \<union> B) guarantees (A \<longmapsto> (B-A))"
apply (rule guaranteesI)
 prefer 2 apply (blast dest: transient_type [THEN subsetD])
apply (rule leadsTo_Basis')
  apply (blast intro: constrains_weaken_R) 
 apply (blast intro!: Join_transient_I1, blast)
done

end
