(*  Title:      HOL/ex/Tarski
    ID:         $Id$
    Author:     Florian Kammueller, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Minimal version of lattice theory plus the full theorem of Tarski:
   The fixedpoints of a complete lattice themselves form a complete lattice.

Illustrates first-class theories, using the Sigma representation of structures
*)


(* abbreviate commonly used tactic application *)

fun afs thms = (asm_full_simp_tac (simpset() addsimps thms));

(* Partial Order *)
Open_locale "PO";

val simp_PO = simplify (simpset() addsimps [PartialOrder_def]) (thm "cl_po");
Addsimps [simp_PO, thm "cl_po"];

val PO_simp = [thm "A_def", thm "r_def"];

Goal "refl A r";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "PartialOrderE1";

Goal "antisym r";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "PartialOrderE2";

Goal "trans r";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "PartialOrderE3";

Goal "[| refl A r; x: A|] ==> (x, x): r";
by (afs [refl_def] 1);
qed "reflE";
(* Interesting: A and r don't get bound because the proof doesn't use
   locale rules 
val reflE = "[| refl ?A ?r; ?x : ?A |] ==> (?x, ?x) : ?r" *)

Goal "[| antisym r; (a, b): r; (b, a): r |] ==> a = b";
by (afs [antisym_def] 1);
qed "antisymE";

Goalw [trans_def] "[| trans r; (a, b): r; (b, c): r|] ==> (a,c): r";
by (Fast_tac 1);
qed "transE";

Goal "[| monotone f A r;  x: A; y: A; (x, y): r |] ==> (f x, f y): r";
by (afs [monotone_def] 1);
qed "monotoneE";

Goal "S <= A ==> (| pset = S, order = induced S r |): PartialOrder";
by (simp_tac (simpset() addsimps [PartialOrder_def]) 1);
by (Step_tac 1);
(* refl *)
by (afs [refl_def,induced_def] 1);
by (rtac conjI 1);
by (Fast_tac 1);
by (rtac ballI 1);
by (rtac reflE 1);
by (rtac PartialOrderE1 1);
by (Fast_tac 1);
(* antisym *)
by (afs [antisym_def,induced_def] 1);
by (Step_tac 1);
by (rtac antisymE 1);
by (assume_tac 2);
by (assume_tac 2);
by (rtac PartialOrderE2 1);
(* trans *)
by (afs [trans_def,induced_def] 1);
by (Step_tac 1);
by (rtac transE 1);
by (assume_tac 2);
by (assume_tac 2);
by (rtac PartialOrderE3 1);
qed "po_subset_po";

Goal "[| (x, y): induced S r; S <= A |] ==> (x, y): r";
by (afs [induced_def] 1);
qed "indE";

Goal "[| (x, y): r; x: S; y: S |] ==> (x, y): induced S r";
by (afs [induced_def] 1);
qed "indI";

(* with locales *)
Open_locale "CL";

Delsimps [simp_PO, thm "cl_po"];

val simp_CL = simplify (simpset() addsimps [CompleteLattice_def]) 
                       (thm "cl_co");
Addsimps [simp_CL, thm "cl_co"];

Goalw [Ex_def] "(EX L. islub S cl L) = islub S cl (lub S cl)";
by (simp_tac (simpset() addsimps [lub_def, least_def, islub_def]) 1);
qed "islub_lub";

Goalw [Ex_def] "(EX G. isglb S cl G) = isglb S cl (glb S cl)";
by (simp_tac (simpset() addsimps [glb_def, greatest_def, isglb_def]) 1);
qed "isglb_glb";

Goal "isglb S cl = islub S (dual cl)";
by (afs [islub_def,isglb_def,dual_def,converse_def] 1);
qed "isglb_dual_islub";

Goal "islub S cl = isglb S (dual cl)";
by (afs [islub_def,isglb_def,dual_def,converse_def] 1);
qed "islub_dual_isglb";

Goal "dual cl : PartialOrder";
by (simp_tac (simpset() addsimps [PartialOrder_def, dual_def]) 1);
by (afs [simp_PO,refl_converse,trans_converse,antisym_converse] 1);
qed "dualPO";

Goal "! S. (S <= A -->( ? L. islub S (| pset = A, order = r|) L)) \
\     ==> ! S. (S <= A --> (? G. isglb S (| pset = A, order = r|) G))";
by (Step_tac 1);
by (res_inst_tac
    [("x"," lub {y. y: A & (! k: S. (y, k): r)}(|pset = A, order = r|)")] 
    exI 1);
by (dres_inst_tac [("x","{y. y: A & (! k: S. (y,k): r)}")] spec 1);
by (dtac mp 1);
by (Fast_tac 1);
by (afs [islub_lub, isglb_def] 1);
by (afs [islub_def] 1);
by (Blast_tac 1);
qed "Rdual";

Goal "lub S cl = glb S (dual cl)";
by (afs [lub_def,glb_def,least_def,greatest_def,dual_def,converse_def] 1);
qed "lub_dual_glb";

Goal "glb S cl = lub S (dual cl)";
by (afs [lub_def,glb_def,least_def,greatest_def,dual_def,converse_def] 1);
qed "glb_dual_lub";

Goal "CompleteLattice <= PartialOrder";
by (simp_tac (simpset() addsimps [PartialOrder_def, CompleteLattice_def]) 1);
by (Fast_tac 1);
qed "CL_subset_PO";

val CompleteLatticeE1 = CL_subset_PO RS subsetD;

Goal "! S.  S <= A --> (? L. islub S cl L)";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "CompleteLatticeE2";

Goal "! S.  S <= A --> (? G. isglb S cl G)";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "CompleteLatticeE3";

Addsimps [CompleteLatticeE1 RS (export simp_PO)];

Goal "refl A r";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "CompleteLatticeE11";

Goal "antisym r";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "CompleteLatticeE12";

Goal "trans r";
by (afs (PO_simp) 1);
qed "CompleteLatticeE13";

Goal "[| po : PartialOrder; (! S. S <= po.<A> --> (? L. islub S po L));\
\  (! S. S <= po.<A> --> (? G. isglb S po G))|] ==> po: CompleteLattice";
by (afs [CompleteLattice_def] 1);
qed "CompleteLatticeI";

Goal "dual cl : CompleteLattice";
by (simp_tac (simpset() addsimps [CompleteLattice_def,dual_def]) 1);
by (fold_goals_tac [dual_def]);
by (simp_tac (simpset() addsimps [islub_dual_isglb RS sym,
				  isglb_dual_islub RS sym,
				  export dualPO]) 1);
qed "CL_dualCL";

Goal "(dual cl.<A>) = cl.<A>";
by (simp_tac (simpset() addsimps [dual_def]) 1);
qed "dualA_iff";

Goal "((x, y): (dual cl.<r>)) = ((y, x): cl.<r>)";
by (simp_tac (simpset() addsimps [dual_def]) 1);
qed "dualr_iff";

Goal "monotone f (cl.<A>) (cl.<r>) ==> monotone f (dual cl.<A>) (dual cl.<r>)";
by (afs [monotone_def,dualA_iff,dualr_iff] 1);
qed "monotone_dual";

Goal "[| x: A; y: A|] ==> interval r x y = interval (dual cl.<r>) y x";
by (simp_tac (simpset() addsimps [interval_def,dualr_iff]) 1);
by (fold_goals_tac [thm "r_def"]);
by (Fast_tac 1);
qed "interval_dual";

Goal "[| trans r; interval r a b ~= {} |] ==> (a, b): r";
by (afs [interval_def] 1);
by (rewtac trans_def);
by (Blast_tac 1);
qed "interval_not_empty";

Goal "x: interval r a b ==> (a, x): r";
by (afs [interval_def] 1);
qed "intervalE1";

Goal "[| a: A; b: A; interval r a b ~= {} |] ==> a: interval r a b";
by (simp_tac (simpset() addsimps [interval_def]) 1);
by (afs [PartialOrderE3,interval_not_empty] 1);
by (afs [PartialOrderE1 RS reflE] 1);
qed "left_in_interval";

Goal "[| a: A; b: A; interval r a b ~= {} |] ==> b: interval r a b";
by (simp_tac (simpset() addsimps [interval_def]) 1);
by (afs [PartialOrderE3,interval_not_empty] 1);
by (afs [PartialOrderE1 RS reflE] 1);
qed "right_in_interval";

Goal "[| (| pset = A, order = r |) : PartialOrder;\
\        ! S. S <= A --> (? L. islub S (| pset = A, order = r |)  L) |] \
\   ==> (| pset = A, order = r |) : CompleteLattice";
by (afs [CompleteLatticeI, Rdual] 1);
qed "CompleteLatticeI_simp";

(* sublattice *)
Goal "S <<= cl ==> S <= A";
by (afs [sublattice_def, CompleteLattice_def, thm "A_def"] 1);
qed "sublatticeE1";

Goal "S <<= cl  ==> (| pset = S, order = induced S r |) : CompleteLattice";
by (afs ([sublattice_def, CompleteLattice_def] @ PO_simp) 1);
qed "sublatticeE2";

Goal "[| S <= A; (| pset = S, order = induced S r |) : CompleteLattice |] ==> S <<= cl";
by (afs ([sublattice_def] @ PO_simp) 1);
qed "sublatticeI";

(* lub *)
Goal "[| S <= A; islub S cl x; islub S cl L|] ==> x = L";
by (rtac antisymE 1); 
by (rtac CompleteLatticeE12 1);
by (rewtac islub_def);
by (rotate_tac ~1 1);
by (etac conjE 1);
by (dtac conjunct2 1);
by (dtac conjunct1 1);
by (dtac conjunct2 1);
by (rotate_tac ~1 1);
by (dres_inst_tac [("x","L")] bspec 1);
by (assume_tac 1);
by (fold_goals_tac [thm "r_def"]);
by (etac mp 1);
by (assume_tac 1);
(* (L, x) : (cl .<r>) *)
by (rotate_tac ~1 1);
by (etac conjE 1);
by (rotate_tac ~1 1);
by (dtac conjunct2 1);
by (dtac bspec 1);
by (etac conjunct1 1);
by (etac mp 1);
by (etac (conjunct2 RS conjunct1) 1);
qed "lub_unique";

Goal "[| S <= A |] ==> ! x: S. (x,lub S cl): r";
by (rtac exE 1);
by (rtac (CompleteLatticeE2 RS spec RS mp) 1);
by (assume_tac 1);
by (rewrite_goals_tac [lub_def,least_def]);
by (stac select_equality 1);
by (rtac conjI 1);
by (afs [islub_def] 2);
by (etac conjunct2 2);
by (afs [islub_def] 1);
by (rtac lub_unique 1);
by (afs [thm "A_def"] 1);
by (afs [islub_def] 1);
by (assume_tac 1);
by (afs [islub_def,thm "r_def"] 1);
qed "lubE1";

Goal "[| S <= A; L: A; ! x: S. (x,L): r |] ==> (lub S cl, L): r";
by (rtac exE 1);
by (rtac (CompleteLatticeE2 RS spec RS mp) 1);
by (assume_tac 1);
by (rewrite_goals_tac [lub_def,least_def]);
by (stac select_equality 1);
by (rtac conjI 1);
by (afs [islub_def] 2);
by (etac conjunct2 2);
by (afs [islub_def] 1);
by (rtac lub_unique 1);
by (afs [thm "A_def"] 1);
by (afs [islub_def] 1);
by (assume_tac 1);
by (afs [islub_def] 1);
by (dtac conjunct2 1);
by (dtac conjunct2 1);
by (rotate_tac 3 1);
by (dtac bspec 1);
by (fold_goals_tac [thm "r_def"]);
by (etac mp 2);
by (afs [thm "A_def"] 1);
by (assume_tac 1);
qed "lubE2";

Goal "[| S <= A |] ==> lub S cl : A";  
by (rtac exE 1);
by (rtac (CompleteLatticeE2 RS spec RS mp) 1);
by (assume_tac 1);
by (rewrite_goals_tac [lub_def,least_def]);
by (stac select_equality 1);
by (afs [islub_def] 1);
by (afs [islub_def, thm "A_def"] 2);
by (rtac lub_unique 1);
by (afs [thm "A_def"] 1);
by (afs [islub_def] 1);
by (assume_tac 1);
qed "lub_in_lattice";

Goal "[| S <= A; L: A; ! x: S. (x,L): r;\
\ ! z: A. (! y: S. (y,z): r) --> (L,z): r |] ==> L = lub S cl";
by (rtac lub_unique 1);
by (assume_tac 1);
by (afs ([islub_def] @ PO_simp) 1);
by (rewtac islub_def);
by (rtac conjI 1);
by (fold_goals_tac PO_simp);
by (rtac lub_in_lattice 1);
by (assume_tac 1);
by (afs [lubE1, lubE2] 1);
qed "lubI";

Goal "[| S <= A; islub S cl L |] ==> L = lub S cl";
by (afs ([lubI, islub_def] @ PO_simp) 1);
qed "lubIa";

Goal "islub S cl L ==> L : A";
by (afs [islub_def, thm "A_def"] 1);
qed "islub_in_lattice";

Goal "islub S cl L ==> ! y: S. (y, L): r";
by (afs [islub_def, thm "r_def"] 1);
qed "islubE1";

Goal "[| islub S cl L; \
\      z: A; ! y: S. (y, z): r|] ==> (L, z): r";
by (afs ([islub_def] @ PO_simp) 1);
qed "islubE2";

Goal "[| S <= A |] ==> ? L. islub S cl L";
by (afs [thm "A_def"] 1);
qed "islubE";

Goal "[| L: A; ! y: S. (y, L): r; \
\     (!z: A. (! y: S. (y, z):r) --> (L, z): r)|] ==> islub S cl L";
by (afs ([islub_def] @ PO_simp) 1);
qed "islubI";

(* glb *)
Goal "S <= A ==> glb S cl : A";  
by (stac glb_dual_lub 1);
by (afs [thm "A_def"] 1);
by (rtac (dualA_iff RS subst) 1);
by (rtac (export lub_in_lattice) 1);
by (rtac CL_dualCL 1);
by (afs [dualA_iff] 1);
qed "glb_in_lattice";

Goal "S <= A ==> ! x: S. (glb S cl, x): r";
by (stac glb_dual_lub 1);
by (rtac ballI 1);
by (afs [thm "r_def"] 1);
by (rtac (dualr_iff RS subst) 1);
by (rtac (export lubE1 RS bspec) 1);
by (rtac CL_dualCL 1);
by (afs [dualA_iff, thm "A_def"] 1);
by (assume_tac 1);
qed "glbE1";

(* Reduce the sublattice property by using substructural properties! *)
(* abandoned see Tarski_4.ML *)

Open_locale "CLF";

val simp_CLF = simplify (simpset() addsimps [CLF_def]) (thm "f_cl");
Addsimps [simp_CLF, thm "f_cl"];

Goal "f : A funcset A";
by (simp_tac (simpset() addsimps [thm "A_def"]) 1);
qed "CLF_E1";

Goal "monotone f A r";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "CLF_E2";

Goal "f : CLF ^^ {cl} ==> f : CLF ^^ {dual cl}";
by (afs [CLF_def, CL_dualCL, monotone_dual] 1); 
by (afs [dualA_iff] 1);
qed "CLF_dual";

(* fixed points *)
Goal "P <= A";
by (simp_tac (simpset() addsimps [thm "P_def", fix_def]) 1);
by (Fast_tac 1);
qed "fixfE1";

Goal "x: P ==> f x = x";
by (afs [thm "P_def", fix_def] 1);
qed "fixfE2";

Goal "[| A <= B; x: fix (lam y: A. f y) A |] ==> x: fix f B";
by (forward_tac [export fixfE2] 1);
by (dtac ((export fixfE1) RS subsetD) 1);
by (afs [fix_def] 1);
by (rtac conjI 1);
by (Fast_tac 1);
by (res_inst_tac [("P","% y. f x = y")] subst 1);
by (assume_tac 1);
by (rtac sym 1);
by (etac restrict_apply1 1);
qed "fixf_subset";

(* lemmas for Tarski, lub *)
Goal "H = {x. (x, f x) : r & x : A} ==> (lub H cl, f (lub H cl)) : r";
by (rtac lubE2 1);
by (Fast_tac 1);
by (rtac (CLF_E1 RS funcset_mem) 1);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
(* ! x:H. (x, f (lub H r)) : r *)
by (rtac ballI 1);
by (rtac transE 1);
by (rtac CompleteLatticeE13 1);
(* instantiates (x, ???z): cl.<r> to (x, f x), because of the def of H *)
by (Fast_tac 1);
(* so it remains to show (f x, f (lub H cl)) : r *)
by (res_inst_tac [("f","f")] monotoneE 1);
by (rtac CLF_E2 1);
by (Fast_tac 1);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
by (rtac (lubE1 RS bspec) 1);
by (Fast_tac 1);
by (assume_tac 1);
qed "lubH_le_flubH";

Goal "[|  H = {x. (x, f x) : r & x : A} |] ==> (f (lub H cl), lub H cl) : r";
by (rtac (lubE1 RS bspec) 1);
by (Fast_tac 1);
by (res_inst_tac [("t","H")] ssubst 1);
by (assume_tac 1);
by (rtac CollectI 1);
by (rtac conjI 1);
by (rtac (CLF_E1 RS funcset_mem) 2);
by (rtac lub_in_lattice 2);
by (Fast_tac 2);
by (res_inst_tac [("f","f")] monotoneE 1);
by (rtac CLF_E2 1);
by (afs [lubH_le_flubH] 3);
by (rtac (CLF_E1 RS funcset_mem) 2);
by (rtac lub_in_lattice 2);
by (Fast_tac 2);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
qed "flubH_le_lubH";

Goal "H = {x. (x, f x): r & x : A} ==> lub H cl : P";
by (simp_tac (simpset() addsimps [thm "P_def", fix_def]) 1);
by (rtac conjI 1);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
by (rtac antisymE 1);
by (rtac CompleteLatticeE12 1);
by (afs [flubH_le_lubH] 1);
by (afs [lubH_le_flubH] 1);
qed "lubH_is_fixp";

Goal "[| H = {x. (x, f x) : r & x : A};  x: P |] ==> x: H";
by (etac ssubst 1);
by (Simp_tac 1);
by (rtac conjI 1);
by (ftac fixfE2 1);
by (etac ssubst 1);
by (rtac reflE 1);
by (rtac CompleteLatticeE11 1);
by (etac (fixfE1 RS subsetD) 1);
by (etac (fixfE1 RS subsetD) 1);
qed "fix_in_H";

Goal "H = {x. (x, f x) : r & x : A} ==> ! x: P. (x, lub H cl) : r";
by (rtac ballI 1);
by (rtac (lubE1 RS bspec) 1);
by (Fast_tac 1);
by (rtac fix_in_H 1);
by (REPEAT (atac 1));
qed "fixf_le_lubH";

Goal "H = {x. (x, f x) : r & x : A} ==> ! L. (! y: P. (y,L): r) --> (lub H cl, L): r";
by (rtac allI 1);
by (rtac impI 1);
by (etac bspec 1);
by (rtac lubH_is_fixp 1);
by (assume_tac 1);
qed "lubH_least_fixf";

(* Tarski fixpoint theorem 1, first part *)
Goal "lub P cl = lub {x. (x, f x) : r & x : A} cl";
by (rtac sym 1);
by (rtac lubI 1);
by (rtac fixfE1 1);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
by (afs [fixf_le_lubH] 1);
by (afs [lubH_least_fixf] 1);
qed "T_thm_1_lub";

(* Tarski for glb *)
Goal "H = {x. (f x, x): r & x : A} ==> glb H cl : P";
by (full_simp_tac 
    (simpset() addsimps [glb_dual_lub, thm "P_def"] @ PO_simp) 1);
by (rtac (dualA_iff RS subst) 1);
by (rtac (CL_dualCL RS (export lubH_is_fixp)) 1);
by (rtac (thm "f_cl" RS CLF_dual) 1);
by (afs [dualr_iff, dualA_iff] 1);
qed "glbH_is_fixp";

Goal "glb P cl = glb {x. (f x, x): r & x : A} cl";
by (simp_tac (simpset() addsimps [glb_dual_lub, thm "P_def"] @ PO_simp) 1);
by (rtac (dualA_iff RS subst) 1);
by (rtac (CL_dualCL RS (export T_thm_1_lub) RS ssubst) 1);
by (rtac (thm "f_cl" RS CLF_dual) 1);
by (afs [dualr_iff] 1);
qed "T_thm_1_glb";

(* interval *)
Goal "refl A r ==> r <= A Times A";
by (afs [refl_def] 1);
qed "reflE1";

Goal "(x, y): r ==> x: A";
by (rtac SigmaD1 1);
by (rtac (reflE1 RS subsetD) 1);
by (rtac CompleteLatticeE11 1);
by (assume_tac 1);
qed "rel_imp_elem";

Goal "[| a: A; b: A |] ==> interval r a b <= A";
by (simp_tac (simpset() addsimps [interval_def]) 1);
by (rtac subsetI 1);
by (rtac rel_imp_elem 1);
by (dtac CollectD 1);
by (etac conjunct2 1);
qed "interval_subset";

Goal "[| (a, x): r; (x, b): r |] ==> x: interval r a b";
by (afs [interval_def] 1);
qed "intervalI";

Goalw [interval_def] "[| S <= interval r a b; x: S |] ==> (a, x): r";
by (Fast_tac 1);
qed "interval_lemma1";

Goalw [interval_def] "[| S <= interval r a b; x: S |] ==> (x, b): r";
by (Fast_tac 1);
qed "interval_lemma2";

Goal "[| S <= A; S ~= {};\
\        ! x: S. (a,x): r; ! y: S. (y, L): r |] ==> (a,L): r";
by (blast_tac (claset() addIs [transE, PartialOrderE3]) 1);
qed "a_less_lub";

Goal "[| S <= A; S ~= {};\
\        ! x: S. (x,b): r; ! y: S. (G, y): r |] ==> (G,b): r";
by (blast_tac (claset() addIs [transE, PartialOrderE3]) 1);
qed "glb_less_b";

Goal "[| a : A; b : A; S <= interval r a b |]==> S <= A";
by (afs [interval_subset RSN(2, subset_trans)] 1);
qed "S_intv_cl";

Goal "[| a : A; b: A; S <= interval r a b; \
\      S ~= {}; islub S cl L; interval r a b ~= {} |] ==> L : interval r a b";
by (rtac intervalI 1);
by (rtac a_less_lub 1);
by (assume_tac 2);
by (afs [S_intv_cl] 1);
by (rtac ballI 1);
by (afs [interval_lemma1] 1);
by (afs [islubE1] 1);
(* (L, b) : r *)
by (rtac islubE2 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac ballI 1);
by (afs [interval_lemma2] 1);
qed "L_in_interval";

Goal "[| a : A; b : A; interval r a b ~= {}; S <= interval r a b; isglb S cl G; \
\      S ~= {} |]   ==> G : interval r a b";
by (afs [interval_dual] 1);
by (rtac (export L_in_interval) 1);
by (rtac dualPO 1);
by (afs [dualA_iff, thm "A_def"] 1);
by (afs [dualA_iff, thm "A_def"] 1);
by (assume_tac 1);
by (afs [isglb_dual_islub] 1);
by (afs [isglb_dual_islub] 1);
by (assume_tac 1);
qed "G_in_interval";

Goal "[| a: A; b: A; interval r a b ~= {} |]\
\  ==> (| pset = interval r a b, order = induced (interval r a b) r |) : PartialOrder";
by (rtac po_subset_po 1);
by (afs [interval_subset] 1);
qed "intervalPO";

Goal "[| a : A; b : A;\
\   interval r a b ~= {} |] ==> ! S. S <= interval r a b -->\
\         (? L. islub S (| pset = interval r a b, order = induced (interval r a b) r |)  L)";
by (strip_tac 1);
by (forward_tac [S_intv_cl RS islubE] 1);
by (assume_tac 2);
by (assume_tac 1);
by (etac exE 1);
(* define the lub for the interval as: *)
by (res_inst_tac [("x","if S = {} then a else L")] exI 1);
by (rtac (export islubI) 1);
(* (if S = {} then a else L) : interval r a b *)
by (asm_full_simp_tac
    (simpset() addsimps [CompleteLatticeE1,L_in_interval]) 1);
by (afs [left_in_interval] 1);
(* lub prop 1 *)
by (case_tac "S = {}" 1);
(* S = {}, y: S = False => everything *)
by (Fast_tac 1);
(* S ~= {} *)
by (Asm_full_simp_tac 1);
(* ! y:S. (y, L) : induced (interval r a b) r *)
by (rtac ballI 1);
by (afs [induced_def, L_in_interval] 1);
by (rtac conjI 1);
by (rtac subsetD 1);
by (afs [S_intv_cl] 1);
by (assume_tac 1);
by (afs [islubE1] 1);
(* ! z:interval r a b. (! y:S. (y, z) : induced (interval r a b) r -->
      (if S = {} then a else L, z) : induced (interval r a b) r *)
by (rtac ballI 1);
by (rtac impI 1);
by (case_tac "S = {}" 1);
(* S = {} *)
by (Asm_full_simp_tac 1);
by (afs [induced_def, interval_def] 1);
by (rtac conjI 1);
by (rtac reflE 1);
by (rtac CompleteLatticeE11 1);
by (assume_tac 1);
by (rtac interval_not_empty 1);
by (rtac CompleteLatticeE13 1);
by (afs [interval_def] 1);
(* S ~= {} *)
by (Asm_full_simp_tac 1);
by (afs [induced_def, L_in_interval] 1);
by (rtac islubE2 1);
by (assume_tac 1);
by (rtac subsetD 1);
by (assume_tac 2);
by (afs [S_intv_cl] 1);
by (Fast_tac 1);
qed "intv_CL_lub";

val intv_CL_glb = intv_CL_lub RS Rdual;

Goal "[| a: A; b: A; interval r a b ~= {} |]\
\       ==> interval r a b <<= cl";
by (rtac sublatticeI 1);
by (afs [interval_subset] 1);
by (rtac CompleteLatticeI 1);
by (afs [intervalPO] 1);
by (afs [intv_CL_lub] 1);
by (afs [intv_CL_glb] 1);
qed "interval_is_sublattice";

val interv_is_compl_latt = interval_is_sublattice RS sublatticeE2;

(* Top and Bottom *)
Goal "Top cl = Bot (dual cl)";
by (afs [Top_def,Bot_def,least_def,greatest_def,dualA_iff, dualr_iff] 1);
qed "Top_dual_Bot";

Goal "Bot cl = Top (dual cl)";
by (afs [Top_def,Bot_def,least_def,greatest_def,dualA_iff, dualr_iff] 1);
qed "Bot_dual_Top";

Goal "Bot cl: A";
by (simp_tac (simpset() addsimps [Bot_def,least_def]) 1);
by (rtac selectI2 1);
by (fold_goals_tac [thm "A_def"]);
by (etac conjunct1 2);
by (rtac conjI 1);
by (rtac glb_in_lattice 1);
by (rtac subset_refl 1);
by (fold_goals_tac [thm "r_def"]);
by (afs [glbE1] 1);
qed "Bot_in_lattice";

Goal "Top cl: A";
by (simp_tac (simpset() addsimps [Top_dual_Bot, thm "A_def"]) 1);
by (rtac (dualA_iff RS subst) 1);
by (afs [export Bot_in_lattice,CL_dualCL] 1);
qed "Top_in_lattice";

Goal "x: A ==> (x, Top cl): r";
by (simp_tac (simpset() addsimps [Top_def,greatest_def]) 1);
by (rtac selectI2 1);
by (fold_goals_tac [thm "r_def", thm "A_def"]);
by (Fast_tac 2);
by (rtac conjI 1);
by (rtac lubE1 2);
by (afs [lub_in_lattice] 1);
by (rtac subset_refl 1);
qed "Top_prop";

Goal "x: A ==> (Bot cl, x): r";
by (simp_tac (simpset() addsimps [Bot_dual_Top, thm "r_def"]) 1);
by (rtac (dualr_iff RS subst) 1);
by (rtac (export Top_prop) 1);
by (rtac CL_dualCL 1);
by (afs [dualA_iff, thm "A_def"] 1);
qed "Bot_prop";

Goal "x: A  ==> interval r x (Top cl) ~= {}";
by (rtac notI 1);
by (dres_inst_tac [("a","Top cl")] equals0D 1);
by (afs [interval_def] 1);
by (afs [refl_def,Top_in_lattice,Top_prop] 1);
qed "Top_intv_not_empty";

Goal "x: A ==> interval r (Bot cl) x ~= {}";
by (simp_tac (simpset() addsimps [Bot_dual_Top]) 1);
by (stac interval_dual 1);
by (assume_tac 2);
by (afs [thm "A_def"] 1);
by (rtac (dualA_iff RS subst) 1);
by (rtac (export Top_in_lattice) 1);
by (rtac CL_dualCL 1);
by (afs [export Top_intv_not_empty,CL_dualCL,dualA_iff, thm "A_def"] 1);
qed "Bot_intv_not_empty";

(* fixed points form a partial order *)
Goal "(| pset = P, order = induced P r|) : PartialOrder";
by (rtac po_subset_po 1);
by (rtac fixfE1 1);
qed "fixf_po";

Open_locale "Tarski";

Goal "Y <= A";
by (rtac (fixfE1 RSN(2,subset_trans)) 1);
by (rtac (thm "Y_ss") 1);
qed "Y_subset_A";

Goal "lub Y cl : A";
by (afs [Y_subset_A RS lub_in_lattice] 1);
qed "lubY_in_A";

Goal "(lub Y cl, f (lub Y cl)): r";
by (rtac lubE2 1);
by (rtac Y_subset_A 1);
by (rtac (CLF_E1 RS funcset_mem) 1);
by (rtac lubY_in_A 1);
(* Y <= P ==> f x = x *)
by (rtac ballI 1);
by (res_inst_tac [("t","x")] (fixfE2 RS subst) 1);
by (etac (thm "Y_ss" RS subsetD) 1);
(* reduce (f x, f (lub Y cl)) : r to (x, lub Y cl): r by monotonicity *)
by (res_inst_tac [("f","f")] monotoneE 1);
by (rtac CLF_E2 1);
by (afs [Y_subset_A RS subsetD] 1);
by (rtac lubY_in_A 1);
by (afs [lubE1, Y_subset_A] 1);
qed "lubY_le_flubY";

Goalw [thm "intY1_def"] "intY1 <= A";
by (rtac interval_subset 1);
by (rtac lubY_in_A 1);
by (rtac Top_in_lattice 1);
qed "intY1_subset";

val intY1_elem = intY1_subset RS subsetD;

Goal "(lam x: intY1. f x): intY1 funcset intY1";
by (rtac restrictI 1);
by (afs [thm "intY1_def", interval_def] 1);
by (rtac conjI 1);
by (rtac transE 1);
by (rtac CompleteLatticeE13 1);
by (rtac lubY_le_flubY 1);
(* (f (lub Y cl), f x) : r *)
by (res_inst_tac [("f","f")]monotoneE 1);
by (rtac CLF_E2 1);
by (rtac lubY_in_A 1);
by (afs [thm "intY1_def",interval_def, intY1_elem] 1);
by (afs [thm "intY1_def", interval_def] 1);
(* (f x, Top cl) : r *)
by (rtac Top_prop 1);
by (rtac (CLF_E1 RS funcset_mem) 1);
by (afs [thm "intY1_def",interval_def, intY1_elem] 1);
qed "intY1_func";

Goal "monotone (lam x: intY1. f x) intY1 (induced intY1 r)";
by (simp_tac (simpset() addsimps [monotone_def]) 1);
by (Clarify_tac 1);
by (simp_tac (simpset() addsimps [induced_def]) 1);
by (afs [intY1_func RS funcset_mem] 1);
by (afs [restrict_apply1] 1);
by (res_inst_tac [("f","f")] monotoneE 1);
by (rtac CLF_E2 1);
by (etac (intY1_subset RS subsetD) 2);
by (etac (intY1_subset RS subsetD) 1);
by (afs [induced_def] 1);
qed "intY1_mono";

Goalw [thm "intY1_def"]
    "(| pset = intY1, order = induced intY1 r |): CompleteLattice";
by (rtac interv_is_compl_latt 1);
by (rtac lubY_in_A 1);
by (rtac Top_in_lattice 1);
by (rtac Top_intv_not_empty 1);
by (rtac lubY_in_A 1);
qed "intY1_is_cl";

Goalw  [thm "P_def"] "v : P";
by (res_inst_tac [("A","intY1")] fixf_subset 1);
by (rtac intY1_subset 1);
by (rewrite_goals_tac [thm "v_def"]);
by (rtac (simplify (simpset()) (intY1_is_cl RS export glbH_is_fixp)) 1);
by (afs [CLF_def, intY1_is_cl, intY1_func, intY1_mono] 1);
by (Simp_tac 1);
qed "v_in_P";

Goalw [thm "intY1_def"]
     "[| z : P; ! y:Y. (y, z) : induced P r |] ==> z : intY1";
by (rtac intervalI 1);
by (etac (fixfE1 RS subsetD RS Top_prop) 2);
by (rtac lubE2 1);
by (rtac Y_subset_A 1);
by (fast_tac (claset() addSEs [fixfE1 RS subsetD]) 1);
by (rtac ballI 1);
by (dtac bspec 1);
by (assume_tac 1);
by (afs [induced_def] 1);
qed "z_in_interval";

Goal "[| z : P; ! y:Y. (y, z) : induced P r |]\
\     ==> ((lam x: intY1. f x) z, z) : induced intY1 r";
by (afs [induced_def,intY1_func RS funcset_mem, z_in_interval] 1);
by (rtac (z_in_interval RS restrict_apply1 RS ssubst) 1);
by (assume_tac 1);
by (afs [induced_def] 1);
by (afs [fixfE2] 1);
by (rtac reflE 1);
by (rtac CompleteLatticeE11 1);
by (etac (fixfE1 RS subsetD) 1);
qed "f'z_in_int_rel";

Goal "? L. islub Y (| pset = P, order = induced P r |) L";
by (res_inst_tac [("x","v")] exI 1);
by (simp_tac (simpset() addsimps [islub_def]) 1);
(* v : P *)
by (afs [v_in_P] 1);
by (rtac conjI 1);
(* v is lub *)
(*  1. ! y:Y. (y, v) : induced P r *)
by (rtac ballI 1);
by (afs [induced_def, subsetD, v_in_P] 1);
by (rtac conjI 1);
by (etac (thm "Y_ss" RS subsetD) 1);
by (res_inst_tac [("b","lub Y cl")] transE 1);
by (rtac CompleteLatticeE13 1);
by (rtac (lubE1 RS bspec) 1);
by (rtac Y_subset_A 1);
by (assume_tac 1);
by (res_inst_tac [("b","Top cl")] intervalE1 1);
by (afs [thm "v_def"] 1);
by (fold_goals_tac [thm "intY1_def"]);
by (rtac (simplify (simpset()) (intY1_is_cl RS export glb_in_lattice)) 1);
by (Simp_tac 1);
by (rtac subsetI 1);
by (dtac CollectD 1);
by (etac conjunct2 1);
(* v is LEAST ub *)
by (Clarify_tac 1);
by (rtac indI 1);
by (afs [v_in_P] 2);
by (assume_tac 2);
by (rewrite_goals_tac [thm "v_def"]);
by (rtac indE 1);
by (rtac intY1_subset 2);
by (rtac (simplify (simpset()) (intY1_is_cl RS export (glbE1 RS bspec))) 1);
by (Simp_tac 1);
by (rtac subsetI 1);
by (dtac CollectD 1);
by (etac conjunct2 1);
by (afs [f'z_in_int_rel, z_in_interval] 1);
qed "tarski_full_lemma";
val Tarski_full_lemma = Export tarski_full_lemma;

Close_locale "Tarski";

Goal "(| pset = P, order = induced P r|) : CompleteLattice";
by (rtac CompleteLatticeI_simp 1);
by (afs [fixf_po] 1);
by (Clarify_tac 1);
by (etac Tarski_full_lemma 1);
qed "Tarski_full";


Close_locale "CLF";
Close_locale "CL";
Close_locale "PO";



