(*  Title:      HOL/UNITY/Extend.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Extending of state sets
  function f (forget)    maps the extended state to the original state
  function g (forgotten) maps the extended state to the "extending part"
*)

(** These we prove OUTSIDE the locale. **)


(*** Restrict [MOVE to Relation.thy?] ***)

Goalw [Restrict_def] "((x,y): Restrict A r) = ((x,y): r & x: A)";
by (Blast_tac 1);
qed "Restrict_iff";
AddIffs [Restrict_iff];

Goal "Restrict UNIV = id";
by (rtac ext 1);
by (auto_tac (claset(), simpset() addsimps [Restrict_def]));
qed "Restrict_UNIV";
Addsimps [Restrict_UNIV];

Goal "Restrict {} r = {}";
by (auto_tac (claset(), simpset() addsimps [Restrict_def]));
qed "Restrict_empty";
Addsimps [Restrict_empty];

Goalw [Restrict_def] "Restrict A (Restrict B r) = Restrict (A Int B) r";
by (Blast_tac 1);
qed "Restrict_Int";
Addsimps [Restrict_Int];

Goalw [Restrict_def] "Domain r <= A ==> Restrict A r = r";
by Auto_tac;
qed "Restrict_triv";

Goalw [Restrict_def] "Restrict A r <= r";
by Auto_tac;
qed "Restrict_subset";

Goalw [Restrict_def]
     "[| A <= B;  Restrict B r = Restrict B s |] \
\     ==> Restrict A r = Restrict A s";
by (Blast_tac 1);
qed "Restrict_eq_mono";

Goalw [Restrict_def, image_def]
     "[| s : RR;  Restrict A r = Restrict A s |] \
\     ==> Restrict A r : Restrict A `` RR";
by Auto_tac;
qed "Restrict_imageI";

Goal "Domain (Restrict A r) = A Int Domain r";
by (Blast_tac 1);
qed "Domain_Restrict";

Goal "(Restrict A r) ^^ B = r ^^ (A Int B)";
by (Blast_tac 1);
qed "Image_Restrict";

Addsimps [Domain_Restrict, Image_Restrict];


Goal "f Id = Id ==> insert Id (f``Acts F) = f `` Acts F";
by (blast_tac (claset() addIs [sym RS image_eqI]) 1);
qed "insert_Id_image_Acts";

(*Possibly easier than reasoning about "inv h"*)
val [surj_h,prem] = 
Goalw [good_map_def]
     "[| surj h; !! x x' y y'. h(x,y) = h(x',y') ==> x=x' |] ==> good_map h";
by (safe_tac (claset() addSIs [surj_h]));
by (rtac prem 1);
by (stac (surjective_pairing RS sym) 1);
by (stac (surj_h RS surj_f_inv_f) 1);
by (rtac refl 1);
qed "good_mapI";

Goalw [good_map_def] "good_map h ==> surj h";
by Auto_tac;
qed "good_map_is_surj";

(*A convenient way of finding a closed form for inv h*)
val [surj,prem] = Goalw [inv_def]
     "[| surj h;  !! x y. g (h(x,y)) = x |] ==> fst (inv h z) = g z";
by (res_inst_tac [("y1", "z")] (surj RS surjD RS exE) 1);
by (rtac someI2 1);
by (dres_inst_tac [("f", "g")] arg_cong 2);
by (auto_tac (claset(), simpset() addsimps [prem]));
qed "fst_inv_equalityI";


Open_locale "Extend";

val slice_def = thm "slice_def";

(*** Trivial properties of f, g, h ***)

val good_h = rewrite_rule [good_map_def] (thm "good_h");
val surj_h = good_h RS conjunct1;

val f_def = thm "f_def";
val g_def = thm "g_def";

Goal "f(h(x,y)) = x";
by (simp_tac (simpset() addsimps [f_def, good_h RS conjunct2]) 1);
qed "f_h_eq";
Addsimps [f_h_eq];

Goal "h(x,y) = h(x',y') ==> x=x'";
by (dres_inst_tac [("f", "fst o inv h")] arg_cong 1);
(*FIXME: If locales worked properly we could put just "f" above*)
by (full_simp_tac (simpset() addsimps [f_def, good_h RS conjunct2]) 1);
qed "h_inject1";
AddDs [h_inject1];

Goal "h(f z, g z) = z";
by (simp_tac (simpset() addsimps [f_def, g_def, surj_h RS surj_f_inv_f]) 1);
qed "h_f_g_eq";


(** A sequence of proof steps borrowed from Provers/split_paired_all.ML **)

val cT = TFree ("'c", ["term"]);

(* "PROP P x == PROP P (h (f x, g x))" *)
val lemma1 = Thm.combination
  (Thm.reflexive (cterm_of (sign_of thy) (Free ("P", cT --> propT))))
  (Drule.unvarify (h_f_g_eq RS sym RS eq_reflection));

val prems = Goalw [lemma1] "(!!u y. PROP P (h (u, y))) ==> PROP P x";
by (resolve_tac prems 1);
val lemma2 = result();

val prems = Goal "(!!u y. PROP P (h (u, y))) ==> (!!z. PROP P z)";
by (rtac lemma2 1);
by (resolve_tac prems 1);
val lemma3 = result();

val prems = Goal "(!!z. PROP P z) ==> (!!u y. PROP P (h (u, y)))";
(*not needed for proof, but prevents generalization over h, 'c, etc.*)
by (cut_facts_tac [surj_h] 1);
by (resolve_tac prems 1);
val lemma4 = result();

val split_extended_all = Thm.equal_intr lemma4 lemma3;


(*** extend_set: basic properties ***)

Goal "(x : project_set h C) = (EX y. h(x,y) : C)";
by (simp_tac (simpset() addsimps [project_set_def]) 1);
qed "project_set_iff";

AddIffs [project_set_iff];

Goalw [extend_set_def] "A<=B ==> extend_set h A <= extend_set h B";
by (Blast_tac 1);
qed "extend_set_mono";

Goalw [extend_set_def] "z : extend_set h A = (f z : A)";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "mem_extend_set_iff";

AddIffs [mem_extend_set_iff];

Goalw [extend_set_def] "(extend_set h A <= extend_set h B) = (A <= B)";
by (Force_tac 1);
qed "extend_set_strict_mono";
AddIffs [extend_set_strict_mono];

Goalw [extend_set_def] "extend_set h {} = {}";
by Auto_tac;
qed "extend_set_empty";
Addsimps [extend_set_empty];

Goal "extend_set h {s. P s} = {s. P (f s)}";
by Auto_tac;
qed "extend_set_eq_Collect";

Goal "extend_set h {x} = {s. f s = x}";
by Auto_tac;
qed "extend_set_sing";

Goalw [extend_set_def] "project_set h (extend_set h C) = C";
by Auto_tac;
qed "extend_set_inverse";
Addsimps [extend_set_inverse];

Goalw [extend_set_def] "C <= extend_set h (project_set h C)";
by (auto_tac (claset(), 
	      simpset() addsimps [split_extended_all]));
by (Blast_tac 1);
qed "extend_set_project_set";

Goal "inj (extend_set h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_set_inverse 1);
qed "inj_extend_set";

Goalw [extend_set_def] "extend_set h UNIV = UNIV";
by (auto_tac (claset(), 
	      simpset() addsimps [split_extended_all]));
qed "extend_set_UNIV_eq";
Addsimps [standard extend_set_UNIV_eq];

(*** project_set: basic properties ***)

(*project_set is simply image!*)
Goal "project_set h C = f `` C";
by (auto_tac (claset() addIs [f_h_eq RS sym], 
	      simpset() addsimps [split_extended_all]));
qed "project_set_eq";

(*Converse appears to fail*)
Goal "!!z. z : C ==> f z : project_set h C";
by (auto_tac (claset(), 
	      simpset() addsimps [split_extended_all]));
qed "project_set_I";


(*** More laws ***)

(*Because A and B could differ on the "other" part of the state, 
   cannot generalize to 
      project_set h (A Int B) = project_set h A Int project_set h B
*)
Goal "project_set h ((extend_set h A) Int B) = A Int (project_set h B)";
by Auto_tac;
qed "project_set_extend_set_Int";

(*Unused, but interesting?*)
Goal "project_set h ((extend_set h A) Un B) = A Un (project_set h B)";
by Auto_tac;
qed "project_set_extend_set_Un";

Goal "project_set h (A Int B) <= (project_set h A) Int (project_set h B)";
by Auto_tac;
qed "project_set_Int_subset";

Goal "extend_set h (A Un B) = extend_set h A Un extend_set h B";
by Auto_tac;
qed "extend_set_Un_distrib";

Goal "extend_set h (A Int B) = extend_set h A Int extend_set h B";
by Auto_tac;
qed "extend_set_Int_distrib";

Goal "extend_set h (INTER A B) = (INT x:A. extend_set h (B x))";
by Auto_tac;
qed "extend_set_INT_distrib";

Goal "extend_set h (A - B) = extend_set h A - extend_set h B";
by Auto_tac;
qed "extend_set_Diff_distrib";

Goal "extend_set h (Union A) = (UN X:A. extend_set h X)";
by (Blast_tac 1);
qed "extend_set_Union";

Goalw [extend_set_def] "(extend_set h A <= - extend_set h B) = (A <= - B)";
by Auto_tac;
qed "extend_set_subset_Compl_eq";


(*** extend_act ***)

(*Can't strengthen it to
  ((h(s,y), h(s',y')) : extend_act h act) = ((s, s') : act & y=y')
  because h doesn't have to be injective in the 2nd argument*)
Goalw [extend_act_def]
     "((h(s,y), h(s',y)) : extend_act h act) = ((s, s') : act)";
by Auto_tac;
qed "mem_extend_act_iff";
AddIffs [mem_extend_act_iff]; 

(*Converse fails: (z,z') would include actions that changed the g-part*)
Goalw [extend_act_def]
     "(z, z') : extend_act h act ==> (f z, f z') : act";
by Auto_tac;
qed "extend_act_D";

Goalw [extend_act_def, project_act_def]
     "project_act h (extend_act h act) = act";
by (Blast_tac 1);
qed "extend_act_inverse";

Goalw [extend_act_def, project_act_def]
     "project_act h (Restrict C (extend_act h act)) = \
\     Restrict (project_set h C) act";
by (Blast_tac 1);
qed "project_act_extend_act_restrict";
Addsimps [project_act_extend_act_restrict];

Goalw [extend_act_def, project_act_def]
     "act' <= extend_act h act ==> project_act h act' <= act";
by (Force_tac 1);
qed "subset_extend_act_D";

Goal "inj (extend_act h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_act_inverse 1);
qed "inj_extend_act";

Goalw [extend_set_def, extend_act_def]
     "extend_act h act ^^ (extend_set h A) = extend_set h (act ^^ A)";
by (Force_tac 1);
qed "extend_act_Image";
Addsimps [extend_act_Image];

Goalw [extend_act_def] "(extend_act h act' <= extend_act h act) = (act'<=act)";
by Auto_tac;
qed "extend_act_strict_mono";

AddIffs [extend_act_strict_mono, inj_extend_act RS inj_eq];
(*The latter theorem is  (extend_act h act' = extend_act h act) = (act'=act) *)

Goalw [extend_set_def, extend_act_def]
    "Domain (extend_act h act) = extend_set h (Domain act)";
by (Force_tac 1);
qed "Domain_extend_act"; 

Goalw [extend_act_def]
    "extend_act h Id = Id";
by (force_tac (claset() addIs  [h_f_g_eq RS sym], simpset()) 1);
qed "extend_act_Id";

Goalw [project_act_def]
     "!!z z'. (z, z') : act ==> (f z, f z') : project_act h act";
by (force_tac (claset(), 
              simpset() addsimps [split_extended_all]) 1);
qed "project_act_I";

Goalw [project_act_def] "project_act h Id = Id";
by (Force_tac 1);
qed "project_act_Id";

Goalw [project_act_def]
  "Domain (project_act h act) = project_set h (Domain act)";
by (force_tac (claset(), 
              simpset() addsimps [split_extended_all]) 1);
qed "Domain_project_act";

Addsimps [extend_act_Id];


(**** extend ****)

(*** Basic properties ***)

Goalw [extend_def] "Init (extend h F) = extend_set h (Init F)";
by Auto_tac;
qed "Init_extend";

Goalw [project_def] "Init (project h C F) = project_set h (Init F)";
by Auto_tac;
qed "Init_project";

Goal "Acts (extend h F) = (extend_act h `` Acts F)";
by (simp_tac (simpset() addsimps [extend_def, insert_Id_image_Acts]) 1);
qed "Acts_extend";

Goal "Acts(project h C F) = insert Id (project_act h `` Restrict C `` Acts F)";
by (auto_tac (claset(), 
	      simpset() addsimps [project_def, image_iff]));
qed "Acts_project";

Addsimps [Init_extend, Init_project, Acts_extend, Acts_project];

Goalw [SKIP_def] "extend h SKIP = SKIP";
by (rtac program_equalityI 1);
by Auto_tac;
qed "extend_SKIP";
Addsimps [export extend_SKIP];

Goal "project_set h UNIV = UNIV";
by Auto_tac;
qed "project_set_UNIV";
Addsimps [project_set_UNIV];

Goal "project_set h (Union A) = (UN X:A. project_set h X)";
by (Blast_tac 1);
qed "project_set_Union";

Goal "project h C (extend h F) = \
\     mk_program (Init F, Restrict (project_set h C) `` Acts F)";
by (rtac program_equalityI 1);
by (asm_simp_tac (simpset() addsimps [image_eq_UN]) 2);
by (Simp_tac 1);
qed "project_extend_eq";

(*ALL act: Acts F. Domain act is MUCH TOO STRONG since Domain Id = UNIV!*)
Goal "UNIV <= project_set h C \
\     ==> project h C (extend h F) = F";
by (asm_simp_tac (simpset() addsimps [project_extend_eq, image_eq_UN, 
                   subset_UNIV RS subset_trans RS Restrict_triv]) 1);
qed "extend_inverse";
Addsimps [extend_inverse];

Goal "inj (extend h)";
by (rtac inj_on_inverseI 1);
by (rtac extend_inverse 1);
by (Force_tac 1);
qed "inj_extend";

Goal "extend h (F Join G) = extend h F Join extend h G";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_Un]) 2);
by (simp_tac (simpset() addsimps [extend_set_Int_distrib]) 1);
qed "extend_Join";
Addsimps [extend_Join];

Goal "extend h (JOIN I F) = (JN i:I. extend h (F i))";
by (rtac program_equalityI 1);
by (simp_tac (simpset() addsimps [image_UN]) 2);
by (simp_tac (simpset() addsimps [extend_set_INT_distrib]) 1);
qed "extend_JN";
Addsimps [extend_JN];

(** These monotonicity results look natural but are UNUSED **)

Goal "F <= G ==> extend h F <= extend h G";
by (full_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by Auto_tac;
qed "extend_mono";

Goal "F <= G ==> project h C F <= project h C G";
by (full_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by Auto_tac;
qed "project_mono";


(*** Safety: co, stable ***)

Goal "(extend h F : (extend_set h A) co (extend_set h B)) = \
\     (F : A co B)";
by (simp_tac (simpset() addsimps [constrains_def]) 1);
qed "extend_constrains";

Goal "(extend h F : stable (extend_set h A)) = (F : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, extend_constrains]) 1);
qed "extend_stable";

Goal "(extend h F : invariant (extend_set h A)) = (F : invariant A)";
by (asm_simp_tac (simpset() addsimps [invariant_def, extend_stable]) 1);
qed "extend_invariant";

(*Projects the state predicates in the property satisfied by  extend h F.
  Converse fails: A and B may differ in their extra variables*)
Goal "extend h F : A co B ==> F : (project_set h A) co (project_set h B)";
by (auto_tac (claset(), simpset() addsimps [constrains_def]));
by (Force_tac 1);
qed "extend_constrains_project_set";

Goal "extend h F : stable A ==> F : stable (project_set h A)";
by (asm_full_simp_tac
    (simpset() addsimps [stable_def, extend_constrains_project_set]) 1);
qed "extend_stable_project_set";


(*** Weak safety primitives: Co, Stable ***)

Goal "p : reachable (extend h F) ==> f p : reachable F";
by (etac reachable.induct 1);
by (auto_tac
    (claset() addIs reachable.intrs,
     simpset() addsimps [extend_act_def, image_iff]));
qed "reachable_extend_f";

Goal "h(s,y) : reachable (extend h F) ==> s : reachable F";
by (force_tac (claset() addSDs [reachable_extend_f], simpset()) 1);
qed "h_reachable_extend";

Goalw [extend_set_def]
     "reachable (extend h F) = extend_set h (reachable F)";
by (rtac equalityI 1);
by (force_tac (claset() addIs  [h_f_g_eq RS sym]
			addSDs [reachable_extend_f], 
	       simpset()) 1);
by (Clarify_tac 1);
by (etac reachable.induct 1);
by (ALLGOALS (force_tac (claset() addIs reachable.intrs, 
			 simpset())));
qed "reachable_extend_eq";

Goal "(extend h F : (extend_set h A) Co (extend_set h B)) =  \
\     (F : A Co B)";
by (simp_tac
    (simpset() addsimps [Constrains_def, reachable_extend_eq, 
			 extend_constrains, extend_set_Int_distrib RS sym]) 1);
qed "extend_Constrains";

Goal "(extend h F : Stable (extend_set h A)) = (F : Stable A)";
by (simp_tac (simpset() addsimps [Stable_def, extend_Constrains]) 1);
qed "extend_Stable";

Goal "(extend h F : Always (extend_set h A)) = (F : Always A)";
by (asm_simp_tac (simpset() addsimps [Always_def, extend_Stable]) 1);
qed "extend_Always";


(** Safety and "project" **)

(** projection: monotonicity for safety **)

Goal "D <= C ==> \
\     project_act h (Restrict D act) <= project_act h (Restrict C act)";
by (auto_tac (claset(), simpset() addsimps [project_act_def]));
qed "project_act_mono";

Goal "[| D <= C; project h C F : A co B |] ==> project h D F : A co B";
by (auto_tac (claset(), simpset() addsimps [constrains_def]));
by (dtac project_act_mono 1);
by (Blast_tac 1);
qed "project_constrains_mono";

Goal "[| D <= C;  project h C F : stable A |] ==> project h D F : stable A";
by (asm_full_simp_tac
    (simpset() addsimps [stable_def, project_constrains_mono]) 1);
qed "project_stable_mono";

(*Key lemma used in several proofs about project and co*)
Goalw [constrains_def]
     "(project h C F : A co B)  =  \
\     (F : (C Int extend_set h A) co (extend_set h B) & A <= B)";
by (auto_tac (claset() addSIs [project_act_I], simpset() addsimps [ball_Un]));
by (force_tac (claset() addSIs [project_act_I] addSDs [subsetD], simpset()) 1);
(*the <== direction*)
by (rewtac project_act_def);
by (force_tac (claset() addSDs [subsetD], simpset()) 1);
qed "project_constrains";

Goalw [stable_def]
     "(project h UNIV F : stable A) = (F : stable (extend_set h A))";
by (simp_tac (simpset() addsimps [project_constrains]) 1);
qed "project_stable";

Goal "F : stable (extend_set h A) ==> project h C F : stable A";
by (dtac (project_stable RS iffD2) 1);
by (blast_tac (claset() addIs [project_stable_mono]) 1);
qed "project_stable_I";

Goal "A Int extend_set h ((project_set h A) Int B) = A Int extend_set h B";
by (auto_tac (claset(), simpset() addsimps [split_extended_all]));
qed "Int_extend_set_lemma";

(*Strange (look at occurrences of C) but used in leadsETo proofs*)
Goal "G : C co B ==> project h C G : project_set h C co project_set h B";
by (full_simp_tac (simpset() addsimps [constrains_def, project_def, 
				       project_act_def]) 1);
by (Blast_tac 1);
qed "project_constrains_project_set";

Goal "G : stable C ==> project h C G : stable (project_set h C)";
by (asm_full_simp_tac (simpset() addsimps [stable_def, 
					   project_constrains_project_set]) 1);
qed "project_stable_project_set";


(*** Progress: transient, ensures ***)

Goal "(extend h F : transient (extend_set h A)) = (F : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [transient_def, extend_set_subset_Compl_eq,
				  Domain_extend_act]));
qed "extend_transient";

Goal "(extend h F : (extend_set h A) ensures (extend_set h B)) = \
\     (F : A ensures B)";
by (simp_tac
    (simpset() addsimps [ensures_def, extend_constrains, extend_transient, 
			 extend_set_Un_distrib RS sym, 
			 extend_set_Diff_distrib RS sym]) 1);
qed "extend_ensures";

Goal "F : A leadsTo B \
\     ==> extend h F : (extend_set h A) leadsTo (extend_set h B)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() addsimps [leadsTo_UN, extend_set_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (asm_simp_tac (simpset() addsimps [leadsTo_Basis, extend_ensures]) 1);
qed "leadsTo_imp_extend_leadsTo";

(*** Proving the converse takes some doing! ***)

Goal "(x : slice C y) = (h(x,y) : C)";
by (simp_tac (simpset() addsimps [slice_def]) 1);
qed "slice_iff";

AddIffs [slice_iff];

Goal "slice (Union S) y = (UN x:S. slice x y)";
by Auto_tac;
qed "slice_Union";

Goal "slice (extend_set h A) y = A";
by Auto_tac;
qed "slice_extend_set";

Goal "project_set h A = (UN y. slice A y)";
by Auto_tac;
qed "project_set_is_UN_slice";

Goalw [transient_def] "extend h F : transient A ==> F : transient (slice A y)";
by Auto_tac;
by (rtac bexI 1);
by Auto_tac;
by (force_tac (claset(), simpset() addsimps [extend_act_def]) 1);
qed "extend_transient_slice";

(*Converse?*)
Goal "extend h F : A co B ==> F : (slice A y) co (slice B y)";
by (auto_tac (claset(), simpset() addsimps [constrains_def]));
qed "extend_constrains_slice";

Goal "extend h F : A ensures B ==> F : (slice A y) ensures (project_set h B)";
by (auto_tac (claset(), 
	      simpset() addsimps [ensures_def, extend_constrains, 
				  extend_transient]));
by (etac (extend_transient_slice RS transient_strengthen) 2);
by (etac (extend_constrains_slice RS constrains_weaken) 1);
by Auto_tac;
qed "extend_ensures_slice";

Goal "ALL y. F : (slice B y) leadsTo CU ==> F : (project_set h B) leadsTo CU";
by (simp_tac (simpset() addsimps [project_set_is_UN_slice]) 1);
by (blast_tac (claset() addIs [leadsTo_UN]) 1);
qed "leadsTo_slice_project_set";

Goal "extend h F : AU leadsTo BU \
\     ==> ALL y. F : (slice AU y) leadsTo (project_set h BU)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() addsimps [leadsTo_UN, slice_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_slice_project_set, leadsTo_Trans]) 2);
by (blast_tac (claset() addIs [extend_ensures_slice, leadsTo_Basis]) 1);
qed_spec_mp "extend_leadsTo_slice";

Goal "(extend h F : (extend_set h A) leadsTo (extend_set h B)) = \
\     (F : A leadsTo B)";
by Safe_tac;
by (etac leadsTo_imp_extend_leadsTo 2);
by (dtac extend_leadsTo_slice 1);
by (full_simp_tac (simpset() addsimps [slice_extend_set]) 1);
qed "extend_leadsTo";

Goal "(extend h F : (extend_set h A) LeadsTo (extend_set h B)) =  \
\     (F : A LeadsTo B)";
by (simp_tac
    (simpset() addsimps [LeadsTo_def, reachable_extend_eq, 
			 extend_leadsTo, extend_set_Int_distrib RS sym]) 1);
qed "extend_LeadsTo";


(*** preserves ***)

Goal "G : preserves (v o f) ==> project h C G : preserves v";
by (auto_tac (claset(),
	      simpset() addsimps [preserves_def, project_stable_I,
				  extend_set_eq_Collect]));
qed "project_preserves_I";

(*to preserve f is to preserve the whole original state*)
Goal "G : preserves f ==> project h C G : preserves id";
by (asm_simp_tac (simpset() addsimps [project_preserves_I]) 1);
qed "project_preserves_id_I";

Goal "(extend h G : preserves (v o f)) = (G : preserves v)";
by (auto_tac (claset(),
	      simpset() addsimps [preserves_def, extend_stable RS sym,
				  extend_set_eq_Collect]));
qed "extend_preserves";

Goal "inj h ==> (extend h G : preserves g)";
by (auto_tac (claset(),
	      simpset() addsimps [preserves_def, extend_def, extend_act_def, 
				  stable_def, constrains_def, g_def]));
qed "inj_extend_preserves";


(*** Guarantees ***)

Goal "project h UNIV ((extend h F) Join G) = F Join (project h UNIV G)";
by (rtac program_equalityI 1);
by (asm_simp_tac
    (simpset() addsimps [image_eq_UN, UN_Un, extend_act_inverse]) 2);
by (simp_tac (simpset() addsimps [project_set_extend_set_Int]) 1);
qed "project_extend_Join";

Goal "(extend h F) Join G = extend h H ==> H = F Join (project h UNIV G)";
by (dres_inst_tac [("f", "project h UNIV")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [project_extend_Join]) 1);
qed "extend_Join_eq_extend_D";

(** Strong precondition and postcondition; only useful when
    the old and new state sets are in bijection **)

Goal "F : X guarantees[v] Y ==> \
\     extend h F : (extend h `` X) guarantees[v o f] (extend h `` Y)";
by (rtac guaranteesI 1);
by Auto_tac;
by (blast_tac (claset() addIs [project_preserves_I]
			addDs [extend_Join_eq_extend_D, guaranteesD]) 1);
qed "guarantees_imp_extend_guarantees";

Goal "extend h F : (extend h `` X) guarantees[v o f] (extend h `` Y) \
\     ==> F : X guarantees[v] Y";
by (auto_tac (claset(), simpset() addsimps [guar_def]));
by (dres_inst_tac [("x", "extend h G")] bspec 1);
by (asm_full_simp_tac 
    (simpset() delsimps [extend_Join] 
           addsimps [extend_Join RS sym, inj_extend RS inj_image_mem_iff]) 2);
by (asm_simp_tac (simpset() addsimps [extend_preserves]) 1);
qed "extend_guarantees_imp_guarantees";

Goal "(extend h F : (extend h `` X) guarantees[v o f] (extend h `` Y)) = \
\    (F : X guarantees[v] Y)";
by (blast_tac (claset() addIs [guarantees_imp_extend_guarantees,
			       extend_guarantees_imp_guarantees]) 1);
qed "extend_guarantees_eq";


Close_locale "Extend";

(*Close_locale should do this!
Delsimps [f_h_eq, extend_set_inverse, f_image_extend_set, extend_act_Image];
Delrules [make_elim h_inject1];
*)
