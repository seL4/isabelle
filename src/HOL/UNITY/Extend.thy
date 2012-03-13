(*  Title:      HOL/UNITY/Extend.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Extending of state setsExtending of state sets
  function f (forget)    maps the extended state to the original state
  function g (forgotten) maps the extended state to the "extending part"
*)

header{*Extending State Sets*}

theory Extend imports Guar begin

definition
  (*MOVE to Relation.thy?*)
  Restrict :: "[ 'a set, ('a*'b) set] => ('a*'b) set"
  where "Restrict A r = r \<inter> (A <*> UNIV)"

definition
  good_map :: "['a*'b => 'c] => bool"
  where "good_map h <-> surj h & (\<forall>x y. fst (inv h (h (x,y))) = x)"
     (*Using the locale constant "f", this is  f (h (x,y))) = x*)
  
definition
  extend_set :: "['a*'b => 'c, 'a set] => 'c set"
  where "extend_set h A = h ` (A <*> UNIV)"

definition
  project_set :: "['a*'b => 'c, 'c set] => 'a set"
  where "project_set h C = {x. \<exists>y. h(x,y) \<in> C}"

definition
  extend_act :: "['a*'b => 'c, ('a*'a) set] => ('c*'c) set"
  where "extend_act h = (%act. \<Union>(s,s') \<in> act. \<Union>y. {(h(s,y), h(s',y))})"

definition
  project_act :: "['a*'b => 'c, ('c*'c) set] => ('a*'a) set"
  where "project_act h act = {(x,x'). \<exists>y y'. (h(x,y), h(x',y')) \<in> act}"

definition
  extend :: "['a*'b => 'c, 'a program] => 'c program"
  where "extend h F = mk_program (extend_set h (Init F),
                               extend_act h ` Acts F,
                               project_act h -` AllowedActs F)"

definition
  (*Argument C allows weak safety laws to be projected*)
  project :: "['a*'b => 'c, 'c set, 'c program] => 'a program"
  where "project h C F =
       mk_program (project_set h (Init F),
                   project_act h ` Restrict C ` Acts F,
                   {act. Restrict (project_set h C) act :
                         project_act h ` Restrict C ` AllowedActs F})"

locale Extend =
  fixes f     :: "'c => 'a"
    and g     :: "'c => 'b"
    and h     :: "'a*'b => 'c"    (*isomorphism between 'a * 'b and 'c *)
    and slice :: "['c set, 'b] => 'a set"
  assumes
    good_h:  "good_map h"
  defines f_def: "f z == fst (inv h z)"
      and g_def: "g z == snd (inv h z)"
      and slice_def: "slice Z y == {x. h(x,y) \<in> Z}"


(** These we prove OUTSIDE the locale. **)


subsection{*Restrict*}
(*MOVE to Relation.thy?*)

lemma Restrict_iff [iff]: "((x,y): Restrict A r) = ((x,y): r & x \<in> A)"
by (unfold Restrict_def, blast)

lemma Restrict_UNIV [simp]: "Restrict UNIV = id"
apply (rule ext)
apply (auto simp add: Restrict_def)
done

lemma Restrict_empty [simp]: "Restrict {} r = {}"
by (auto simp add: Restrict_def)

lemma Restrict_Int [simp]: "Restrict A (Restrict B r) = Restrict (A \<inter> B) r"
by (unfold Restrict_def, blast)

lemma Restrict_triv: "Domain r \<subseteq> A ==> Restrict A r = r"
by (unfold Restrict_def, auto)

lemma Restrict_subset: "Restrict A r \<subseteq> r"
by (unfold Restrict_def, auto)

lemma Restrict_eq_mono: 
     "[| A \<subseteq> B;  Restrict B r = Restrict B s |]  
      ==> Restrict A r = Restrict A s"
by (unfold Restrict_def, blast)

lemma Restrict_imageI: 
     "[| s \<in> RR;  Restrict A r = Restrict A s |]  
      ==> Restrict A r \<in> Restrict A ` RR"
by (unfold Restrict_def image_def, auto)

lemma Domain_Restrict [simp]: "Domain (Restrict A r) = A \<inter> Domain r"
by blast

lemma Image_Restrict [simp]: "(Restrict A r) `` B = r `` (A \<inter> B)"
by blast

(*Possibly easier than reasoning about "inv h"*)
lemma good_mapI: 
     assumes surj_h: "surj h"
         and prem:   "!! x x' y y'. h(x,y) = h(x',y') ==> x=x'"
     shows "good_map h"
apply (simp add: good_map_def) 
apply (safe intro!: surj_h)
apply (rule prem)
apply (subst surjective_pairing [symmetric])
apply (subst surj_h [THEN surj_f_inv_f])
apply (rule refl)
done

lemma good_map_is_surj: "good_map h ==> surj h"
by (unfold good_map_def, auto)

(*A convenient way of finding a closed form for inv h*)
lemma fst_inv_equalityI: 
     assumes surj_h: "surj h"
         and prem:   "!! x y. g (h(x,y)) = x"
     shows "fst (inv h z) = g z"
by (metis UNIV_I f_inv_into_f pair_collapse prem surj_h)


subsection{*Trivial properties of f, g, h*}

context Extend
begin

lemma f_h_eq [simp]: "f(h(x,y)) = x" 
by (simp add: f_def good_h [unfolded good_map_def, THEN conjunct2])

lemma h_inject1 [dest]: "h(x,y) = h(x',y') ==> x=x'"
apply (drule_tac f = f in arg_cong)
apply (simp add: f_def good_h [unfolded good_map_def, THEN conjunct2])
done

lemma h_f_g_equiv: "h(f z, g z) == z"
by (simp add: f_def g_def 
            good_h [unfolded good_map_def, THEN conjunct1, THEN surj_f_inv_f])

lemma h_f_g_eq: "h(f z, g z) = z"
by (simp add: h_f_g_equiv)


lemma split_extended_all:
     "(!!z. PROP P z) == (!!u y. PROP P (h (u, y)))"
proof 
   assume allP: "\<And>z. PROP P z"
   fix u y
   show "PROP P (h (u, y))" by (rule allP)
 next
   assume allPh: "\<And>u y. PROP P (h(u,y))"
   fix z
   have Phfgz: "PROP P (h (f z, g z))" by (rule allPh)
   show "PROP P z" by (rule Phfgz [unfolded h_f_g_equiv])
qed 

end


subsection{*@{term extend_set}: basic properties*}

lemma project_set_iff [iff]:
     "(x \<in> project_set h C) = (\<exists>y. h(x,y) \<in> C)"
by (simp add: project_set_def)

lemma extend_set_mono: "A \<subseteq> B ==> extend_set h A \<subseteq> extend_set h B"
by (unfold extend_set_def, blast)

context Extend
begin

lemma mem_extend_set_iff [iff]: "z \<in> extend_set h A = (f z \<in> A)"
apply (unfold extend_set_def)
apply (force intro: h_f_g_eq [symmetric])
done

lemma extend_set_strict_mono [iff]:
     "(extend_set h A \<subseteq> extend_set h B) = (A \<subseteq> B)"
by (unfold extend_set_def, force)

lemma (in -) extend_set_empty [simp]: "extend_set h {} = {}"
by (unfold extend_set_def, auto)

lemma extend_set_eq_Collect: "extend_set h {s. P s} = {s. P(f s)}"
by auto

lemma extend_set_sing: "extend_set h {x} = {s. f s = x}"
by auto

lemma extend_set_inverse [simp]: "project_set h (extend_set h C) = C"
by (unfold extend_set_def, auto)

lemma extend_set_project_set: "C \<subseteq> extend_set h (project_set h C)"
apply (unfold extend_set_def)
apply (auto simp add: split_extended_all, blast)
done

lemma inj_extend_set: "inj (extend_set h)"
apply (rule inj_on_inverseI)
apply (rule extend_set_inverse)
done

lemma extend_set_UNIV_eq [simp]: "extend_set h UNIV = UNIV"
apply (unfold extend_set_def)
apply (auto simp add: split_extended_all)
done

subsection{*@{term project_set}: basic properties*}

(*project_set is simply image!*)
lemma project_set_eq: "project_set h C = f ` C"
by (auto intro: f_h_eq [symmetric] simp add: split_extended_all)

(*Converse appears to fail*)
lemma project_set_I: "!!z. z \<in> C ==> f z \<in> project_set h C"
by (auto simp add: split_extended_all)


subsection{*More laws*}

(*Because A and B could differ on the "other" part of the state, 
   cannot generalize to 
      project_set h (A \<inter> B) = project_set h A \<inter> project_set h B
*)
lemma project_set_extend_set_Int: "project_set h ((extend_set h A) \<inter> B) = A \<inter> (project_set h B)"
  by auto

(*Unused, but interesting?*)
lemma project_set_extend_set_Un: "project_set h ((extend_set h A) \<union> B) = A \<union> (project_set h B)"
  by auto

lemma (in -) project_set_Int_subset:
    "project_set h (A \<inter> B) \<subseteq> (project_set h A) \<inter> (project_set h B)"
  by auto

lemma extend_set_Un_distrib: "extend_set h (A \<union> B) = extend_set h A \<union> extend_set h B"
  by auto

lemma extend_set_Int_distrib: "extend_set h (A \<inter> B) = extend_set h A \<inter> extend_set h B"
  by auto

lemma extend_set_INT_distrib: "extend_set h (INTER A B) = (\<Inter>x \<in> A. extend_set h (B x))"
  by auto

lemma extend_set_Diff_distrib: "extend_set h (A - B) = extend_set h A - extend_set h B"
  by auto

lemma extend_set_Union: "extend_set h (Union A) = (\<Union>X \<in> A. extend_set h X)"
  by blast

lemma extend_set_subset_Compl_eq: "(extend_set h A \<subseteq> - extend_set h B) = (A \<subseteq> - B)"
  by (auto simp: extend_set_def)


subsection{*@{term extend_act}*}

(*Can't strengthen it to
  ((h(s,y), h(s',y')) \<in> extend_act h act) = ((s, s') \<in> act & y=y')
  because h doesn't have to be injective in the 2nd argument*)
lemma mem_extend_act_iff [iff]: "((h(s,y), h(s',y)) \<in> extend_act h act) = ((s, s') \<in> act)"
  by (auto simp: extend_act_def)

(*Converse fails: (z,z') would include actions that changed the g-part*)
lemma extend_act_D: "(z, z') \<in> extend_act h act ==> (f z, f z') \<in> act"
  by (auto simp: extend_act_def)

lemma extend_act_inverse [simp]: "project_act h (extend_act h act) = act"
  unfolding extend_act_def project_act_def by blast

lemma project_act_extend_act_restrict [simp]:
     "project_act h (Restrict C (extend_act h act)) =  
      Restrict (project_set h C) act"
  unfolding extend_act_def project_act_def by blast

lemma subset_extend_act_D: "act' \<subseteq> extend_act h act ==> project_act h act' \<subseteq> act"
  unfolding extend_act_def project_act_def by force

lemma inj_extend_act: "inj (extend_act h)"
apply (rule inj_on_inverseI)
apply (rule extend_act_inverse)
done

lemma extend_act_Image [simp]:
     "extend_act h act `` (extend_set h A) = extend_set h (act `` A)"
  unfolding extend_set_def extend_act_def by force

lemma extend_act_strict_mono [iff]:
     "(extend_act h act' \<subseteq> extend_act h act) = (act'<=act)"
  by (auto simp: extend_act_def)

lemma [iff]: "(extend_act h act = extend_act h act') = (act = act')"
  by (rule inj_extend_act [THEN inj_eq])

lemma (in -) Domain_extend_act:
    "Domain (extend_act h act) = extend_set h (Domain act)"
  unfolding extend_set_def extend_act_def by force

lemma extend_act_Id [simp]: "extend_act h Id = Id"
  unfolding extend_act_def by (force intro: h_f_g_eq [symmetric])

lemma project_act_I:  "!!z z'. (z, z') \<in> act ==> (f z, f z') \<in> project_act h act"
  unfolding project_act_def by (force simp add: split_extended_all)

lemma project_act_Id [simp]: "project_act h Id = Id"
  unfolding project_act_def by force

lemma Domain_project_act: "Domain (project_act h act) = project_set h (Domain act)"
  unfolding project_act_def by (force simp add: split_extended_all)


subsection{*extend*}

text{*Basic properties*}

lemma (in -) Init_extend [simp]:
     "Init (extend h F) = extend_set h (Init F)"
  by (auto simp: extend_def)

lemma (in -) Init_project [simp]:
     "Init (project h C F) = project_set h (Init F)"
  by (auto simp: project_def)

lemma Acts_extend [simp]: "Acts (extend h F) = (extend_act h ` Acts F)"
  by (simp add: extend_def insert_Id_image_Acts)

lemma AllowedActs_extend [simp]:
     "AllowedActs (extend h F) = project_act h -` AllowedActs F"
  by (simp add: extend_def insert_absorb)

lemma (in -) Acts_project [simp]:
     "Acts(project h C F) = insert Id (project_act h ` Restrict C ` Acts F)"
  by (auto simp add: project_def image_iff)

lemma AllowedActs_project [simp]:
     "AllowedActs(project h C F) =  
        {act. Restrict (project_set h C) act  
               \<in> project_act h ` Restrict C ` AllowedActs F}"
apply (simp (no_asm) add: project_def image_iff)
apply (subst insert_absorb)
apply (auto intro!: bexI [of _ Id] simp add: project_act_def)
done

lemma Allowed_extend: "Allowed (extend h F) = project h UNIV -` Allowed F"
  by (auto simp add: Allowed_def)

lemma extend_SKIP [simp]: "extend h SKIP = SKIP"
apply (unfold SKIP_def)
apply (rule program_equalityI, auto)
done

lemma (in -) project_set_UNIV [simp]: "project_set h UNIV = UNIV"
  by auto

lemma (in -) project_set_Union: "project_set h (Union A) = (\<Union>X \<in> A. project_set h X)"
  by blast


(*Converse FAILS: the extended state contributing to project_set h C
  may not coincide with the one contributing to project_act h act*)
lemma (in -) project_act_Restrict_subset:
     "project_act h (Restrict C act) \<subseteq> Restrict (project_set h C) (project_act h act)"
  by (auto simp add: project_act_def)

lemma project_act_Restrict_Id_eq: "project_act h (Restrict C Id) = Restrict (project_set h C) Id"
  by (auto simp add: project_act_def)

lemma project_extend_eq:
     "project h C (extend h F) =  
      mk_program (Init F, Restrict (project_set h C) ` Acts F,  
                  {act. Restrict (project_set h C) act 
                          \<in> project_act h ` Restrict C ` 
                                     (project_act h -` AllowedActs F)})"
apply (rule program_equalityI)
  apply simp
 apply (simp add: image_eq_UN)
apply (simp add: project_def)
done

lemma extend_inverse [simp]:
     "project h UNIV (extend h F) = F"
apply (simp (no_asm_simp) add: project_extend_eq image_eq_UN
          subset_UNIV [THEN subset_trans, THEN Restrict_triv])
apply (rule program_equalityI)
apply (simp_all (no_asm))
apply (subst insert_absorb)
apply (simp (no_asm) add: bexI [of _ Id])
apply auto
apply (rename_tac "act")
apply (rule_tac x = "extend_act h act" in bexI, auto)
done

lemma inj_extend: "inj (extend h)"
apply (rule inj_on_inverseI)
apply (rule extend_inverse)
done

lemma extend_Join [simp]: "extend h (F\<squnion>G) = extend h F\<squnion>extend h G"
apply (rule program_equalityI)
apply (simp (no_asm) add: extend_set_Int_distrib)
apply (simp add: image_Un, auto)
done

lemma extend_JN [simp]: "extend h (JOIN I F) = (\<Squnion>i \<in> I. extend h (F i))"
apply (rule program_equalityI)
  apply (simp (no_asm) add: extend_set_INT_distrib)
 apply (simp add: image_UN, auto)
done

(** These monotonicity results look natural but are UNUSED **)

lemma extend_mono: "F \<le> G ==> extend h F \<le> extend h G"
  by (force simp add: component_eq_subset)

lemma project_mono: "F \<le> G ==> project h C F \<le> project h C G"
  by (simp add: component_eq_subset, blast)

lemma all_total_extend: "all_total F ==> all_total (extend h F)"
  by (simp add: all_total_def Domain_extend_act)

subsection{*Safety: co, stable*}

lemma extend_constrains:
     "(extend h F \<in> (extend_set h A) co (extend_set h B)) =  
      (F \<in> A co B)"
  by (simp add: constrains_def)

lemma extend_stable:
     "(extend h F \<in> stable (extend_set h A)) = (F \<in> stable A)"
  by (simp add: stable_def extend_constrains)

lemma extend_invariant:
     "(extend h F \<in> invariant (extend_set h A)) = (F \<in> invariant A)"
  by (simp add: invariant_def extend_stable)

(*Projects the state predicates in the property satisfied by  extend h F.
  Converse fails: A and B may differ in their extra variables*)
lemma extend_constrains_project_set:
     "extend h F \<in> A co B ==> F \<in> (project_set h A) co (project_set h B)"
  by (auto simp add: constrains_def, force)

lemma extend_stable_project_set:
     "extend h F \<in> stable A ==> F \<in> stable (project_set h A)"
  by (simp add: stable_def extend_constrains_project_set)


subsection{*Weak safety primitives: Co, Stable*}

lemma reachable_extend_f: "p \<in> reachable (extend h F) ==> f p \<in> reachable F"
  by (induct set: reachable) (auto intro: reachable.intros simp add: extend_act_def image_iff)

lemma h_reachable_extend: "h(s,y) \<in> reachable (extend h F) ==> s \<in> reachable F"
  by (force dest!: reachable_extend_f)

lemma reachable_extend_eq: "reachable (extend h F) = extend_set h (reachable F)"
apply (unfold extend_set_def)
apply (rule equalityI)
apply (force intro: h_f_g_eq [symmetric] dest!: reachable_extend_f, clarify)
apply (erule reachable.induct)
apply (force intro: reachable.intros)+
done

lemma extend_Constrains:
     "(extend h F \<in> (extend_set h A) Co (extend_set h B)) =   
      (F \<in> A Co B)"
  by (simp add: Constrains_def reachable_extend_eq extend_constrains 
              extend_set_Int_distrib [symmetric])

lemma extend_Stable: "(extend h F \<in> Stable (extend_set h A)) = (F \<in> Stable A)"
  by (simp add: Stable_def extend_Constrains)

lemma extend_Always: "(extend h F \<in> Always (extend_set h A)) = (F \<in> Always A)"
  by (simp add: Always_def extend_Stable)


(** Safety and "project" **)

(** projection: monotonicity for safety **)

lemma (in -) project_act_mono:
     "D \<subseteq> C ==>  
      project_act h (Restrict D act) \<subseteq> project_act h (Restrict C act)"
  by (auto simp add: project_act_def)

lemma project_constrains_mono:
     "[| D \<subseteq> C; project h C F \<in> A co B |] ==> project h D F \<in> A co B"
apply (auto simp add: constrains_def)
apply (drule project_act_mono, blast)
done

lemma project_stable_mono:
     "[| D \<subseteq> C;  project h C F \<in> stable A |] ==> project h D F \<in> stable A"
  by (simp add: stable_def project_constrains_mono)

(*Key lemma used in several proofs about project and co*)
lemma project_constrains: 
     "(project h C F \<in> A co B)  =   
      (F \<in> (C \<inter> extend_set h A) co (extend_set h B) & A \<subseteq> B)"
apply (unfold constrains_def)
apply (auto intro!: project_act_I simp add: ball_Un)
apply (force intro!: project_act_I dest!: subsetD)
(*the <== direction*)
apply (unfold project_act_def)
apply (force dest!: subsetD)
done

lemma project_stable: "(project h UNIV F \<in> stable A) = (F \<in> stable (extend_set h A))"
  by (simp add: stable_def project_constrains)

lemma project_stable_I: "F \<in> stable (extend_set h A) ==> project h C F \<in> stable A"
apply (drule project_stable [THEN iffD2])
apply (blast intro: project_stable_mono)
done

lemma Int_extend_set_lemma:
     "A \<inter> extend_set h ((project_set h A) \<inter> B) = A \<inter> extend_set h B"
  by (auto simp add: split_extended_all)

(*Strange (look at occurrences of C) but used in leadsETo proofs*)
lemma project_constrains_project_set:
     "G \<in> C co B ==> project h C G \<in> project_set h C co project_set h B"
  by (simp add: constrains_def project_def project_act_def, blast)

lemma project_stable_project_set:
     "G \<in> stable C ==> project h C G \<in> stable (project_set h C)"
  by (simp add: stable_def project_constrains_project_set)


subsection{*Progress: transient, ensures*}

lemma extend_transient:
     "(extend h F \<in> transient (extend_set h A)) = (F \<in> transient A)"
  by (auto simp add: transient_def extend_set_subset_Compl_eq Domain_extend_act)

lemma extend_ensures:
     "(extend h F \<in> (extend_set h A) ensures (extend_set h B)) =  
      (F \<in> A ensures B)"
  by (simp add: ensures_def extend_constrains extend_transient 
        extend_set_Un_distrib [symmetric] extend_set_Diff_distrib [symmetric])

lemma leadsTo_imp_extend_leadsTo:
     "F \<in> A leadsTo B  
      ==> extend h F \<in> (extend_set h A) leadsTo (extend_set h B)"
apply (erule leadsTo_induct)
  apply (simp add: leadsTo_Basis extend_ensures)
 apply (blast intro: leadsTo_Trans)
apply (simp add: leadsTo_UN extend_set_Union)
done

subsection{*Proving the converse takes some doing!*}

lemma slice_iff [iff]: "(x \<in> slice C y) = (h(x,y) \<in> C)"
  by (simp add: slice_def)

lemma slice_Union: "slice (Union S) y = (\<Union>x \<in> S. slice x y)"
  by auto

lemma slice_extend_set: "slice (extend_set h A) y = A"
  by auto

lemma project_set_is_UN_slice: "project_set h A = (\<Union>y. slice A y)"
  by auto

lemma extend_transient_slice:
     "extend h F \<in> transient A ==> F \<in> transient (slice A y)"
  by (auto simp: transient_def)

(*Converse?*)
lemma extend_constrains_slice:
     "extend h F \<in> A co B ==> F \<in> (slice A y) co (slice B y)"
  by (auto simp add: constrains_def)

lemma extend_ensures_slice:
     "extend h F \<in> A ensures B ==> F \<in> (slice A y) ensures (project_set h B)"
apply (auto simp add: ensures_def extend_constrains extend_transient)
apply (erule_tac [2] extend_transient_slice [THEN transient_strengthen])
apply (erule extend_constrains_slice [THEN constrains_weaken], auto)
done

lemma leadsTo_slice_project_set:
     "\<forall>y. F \<in> (slice B y) leadsTo CU ==> F \<in> (project_set h B) leadsTo CU"
apply (simp add: project_set_is_UN_slice)
apply (blast intro: leadsTo_UN)
done

lemma extend_leadsTo_slice [rule_format]:
     "extend h F \<in> AU leadsTo BU  
      ==> \<forall>y. F \<in> (slice AU y) leadsTo (project_set h BU)"
apply (erule leadsTo_induct)
  apply (blast intro: extend_ensures_slice)
 apply (blast intro: leadsTo_slice_project_set leadsTo_Trans)
apply (simp add: leadsTo_UN slice_Union)
done

lemma extend_leadsTo:
     "(extend h F \<in> (extend_set h A) leadsTo (extend_set h B)) =  
      (F \<in> A leadsTo B)"
apply safe
apply (erule_tac [2] leadsTo_imp_extend_leadsTo)
apply (drule extend_leadsTo_slice)
apply (simp add: slice_extend_set)
done

lemma extend_LeadsTo:
     "(extend h F \<in> (extend_set h A) LeadsTo (extend_set h B)) =   
      (F \<in> A LeadsTo B)"
  by (simp add: LeadsTo_def reachable_extend_eq extend_leadsTo
              extend_set_Int_distrib [symmetric])


subsection{*preserves*}

lemma project_preserves_I:
     "G \<in> preserves (v o f) ==> project h C G \<in> preserves v"
  by (auto simp add: preserves_def project_stable_I extend_set_eq_Collect)

(*to preserve f is to preserve the whole original state*)
lemma project_preserves_id_I:
     "G \<in> preserves f ==> project h C G \<in> preserves id"
  by (simp add: project_preserves_I)

lemma extend_preserves:
     "(extend h G \<in> preserves (v o f)) = (G \<in> preserves v)"
  by (auto simp add: preserves_def extend_stable [symmetric] 
                   extend_set_eq_Collect)

lemma inj_extend_preserves: "inj h ==> (extend h G \<in> preserves g)"
  by (auto simp add: preserves_def extend_def extend_act_def stable_def 
                   constrains_def g_def)


subsection{*Guarantees*}

lemma project_extend_Join: "project h UNIV ((extend h F)\<squnion>G) = F\<squnion>(project h UNIV G)"
apply (rule program_equalityI)
  apply (simp add: project_set_extend_set_Int)
 apply (auto simp add: image_eq_UN)
done

lemma extend_Join_eq_extend_D:
     "(extend h F)\<squnion>G = extend h H ==> H = F\<squnion>(project h UNIV G)"
apply (drule_tac f = "project h UNIV" in arg_cong)
apply (simp add: project_extend_Join)
done

(** Strong precondition and postcondition; only useful when
    the old and new state sets are in bijection **)


lemma ok_extend_imp_ok_project: "extend h F ok G ==> F ok project h UNIV G"
apply (auto simp add: ok_def)
apply (drule subsetD)
apply (auto intro!: rev_image_eqI)
done

lemma ok_extend_iff: "(extend h F ok extend h G) = (F ok G)"
apply (simp add: ok_def, safe)
apply force+
done

lemma OK_extend_iff: "OK I (%i. extend h (F i)) = (OK I F)"
apply (unfold OK_def, safe)
apply (drule_tac x = i in bspec)
apply (drule_tac [2] x = j in bspec)
apply force+
done

lemma guarantees_imp_extend_guarantees:
     "F \<in> X guarantees Y ==>  
      extend h F \<in> (extend h ` X) guarantees (extend h ` Y)"
apply (rule guaranteesI, clarify)
apply (blast dest: ok_extend_imp_ok_project extend_Join_eq_extend_D 
                   guaranteesD)
done

lemma extend_guarantees_imp_guarantees:
     "extend h F \<in> (extend h ` X) guarantees (extend h ` Y)  
      ==> F \<in> X guarantees Y"
apply (auto simp add: guar_def)
apply (drule_tac x = "extend h G" in spec)
apply (simp del: extend_Join 
            add: extend_Join [symmetric] ok_extend_iff 
                 inj_extend [THEN inj_image_mem_iff])
done

lemma extend_guarantees_eq:
     "(extend h F \<in> (extend h ` X) guarantees (extend h ` Y)) =  
      (F \<in> X guarantees Y)"
  by (blast intro: guarantees_imp_extend_guarantees 
                 extend_guarantees_imp_guarantees)

end

end
