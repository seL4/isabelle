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

Goal "[| refl A r; x \\<in> A|] ==> (x, x) \\<in> r";
by (afs [refl_def] 1);
qed "reflE";
(* Interesting: A and r don't get bound because the proof doesn't use
   locale rules 
val reflE = "[| refl ?A ?r; ?x \\<in> ?A |] ==> (?x, ?x) \\<in> ?r" *)

Goal "[| antisym r; (a, b) \\<in> r; (b, a) \\<in> r |] ==> a = b";
by (afs [antisym_def] 1);
qed "antisymE";

Goalw [trans_def] "[| trans r; (a, b) \\<in> r; (b, c) \\<in> r|] ==> (a,c) \\<in> r";
by (Fast_tac 1);
qed "transE";

Goal "[| monotone f A r;  x \\<in> A; y \\<in> A; (x, y) \\<in> r |] ==> (f x, f y) \\<in> r";
by (afs [monotone_def] 1);
qed "monotoneE";

Goal "S <= A ==> (| pset = S, order = induced S r |) \\<in> PartialOrder";
by (simp_tac (simpset() addsimps [PartialOrder_def]) 1);
by Auto_tac; 
(* refl *)
by (afs [refl_def,induced_def] 1);
by (blast_tac (claset() addIs [PartialOrderE1 RS reflE]) 1); 
(* antisym *)
by (afs [antisym_def,induced_def] 1);
by (blast_tac (claset() addIs [PartialOrderE2 RS antisymE]) 1); 
(* trans *)
by (afs [trans_def,induced_def] 1);
by (blast_tac (claset() addIs [PartialOrderE3 RS transE]) 1); 
qed "po_subset_po";

Goal "[| (x, y) \\<in> induced S r; S <= A |] ==> (x, y) \\<in> r";
by (afs [induced_def] 1);
qed "indE";

Goal "[| (x, y) \\<in> r; x \\<in> S; y \\<in> S |] ==> (x, y) \\<in> induced S r";
by (afs [induced_def] 1);
qed "indI";

(* with locales *)
Open_locale "CL";

Delsimps [simp_PO, thm "cl_po"];

val simp_CL = simplify (simpset() addsimps [CompleteLattice_def]) 
                       (thm "cl_co");
Addsimps [simp_CL, thm "cl_co"];

Goal "(EX L. islub S cl L) = islub S cl (lub S cl)";
by (simp_tac (simpset() addsimps [lub_def, least_def, islub_def, 
                                  some_eq_ex RS sym]) 1);
qed "islub_lub";

Goal "(EX G. isglb S cl G) = isglb S cl (glb S cl)";
by (simp_tac (simpset() addsimps [glb_def, greatest_def, isglb_def, 
                                  some_eq_ex RS sym]) 1);
qed "isglb_glb";

Goal "isglb S cl = islub S (dual cl)";
by (afs [islub_def,isglb_def,dual_def,converse_def] 1);
qed "isglb_dual_islub";

Goal "islub S cl = isglb S (dual cl)";
by (afs [islub_def,isglb_def,dual_def,converse_def] 1);
qed "islub_dual_isglb";

Goal "dual cl \\<in> PartialOrder";
by (simp_tac (simpset() addsimps [PartialOrder_def, dual_def]) 1);
by (afs [simp_PO,refl_converse,trans_converse,antisym_converse] 1);
qed "dualPO";

Goal "\\<forall>S. (S <= A -->( \\<exists>L. islub S (| pset = A, order = r|) L)) \
\     ==> \\<forall>S. (S <= A --> (\\<exists>G. isglb S (| pset = A, order = r|) G))";
by (Step_tac 1);
by (res_inst_tac
    [("x"," lub {y. y \\<in> A & (\\<forall>k \\<in> S. (y, k) \\<in> r)}(|pset = A, order = r|)")] 
    exI 1);
by (dres_inst_tac [("x","{y. y \\<in> A & (\\<forall>k \\<in> S. (y,k) \\<in> r)}")] spec 1);
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

Goal "\\<forall>S.  S <= A --> (\\<exists>L. islub S cl L)";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "CompleteLatticeE2";

Goal "\\<forall>S.  S <= A --> (\\<exists>G. isglb S cl G)";
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

Goal "[| po \\<in> PartialOrder; (\\<forall>S. S <= po.<A> --> (\\<exists>L. islub S po L));\
\  (\\<forall>S. S <= po.<A> --> (\\<exists>G. isglb S po G))|] ==> po \\<in> CompleteLattice";
by (afs [CompleteLattice_def] 1);
qed "CompleteLatticeI";

Goal "dual cl \\<in> CompleteLattice";
by (simp_tac (simpset() addsimps [CompleteLattice_def,dual_def]) 1);
by (fold_goals_tac [dual_def]);
by (simp_tac (simpset() addsimps [islub_dual_isglb RS sym,
				  isglb_dual_islub RS sym,
				  export dualPO]) 1);
qed "CL_dualCL";

Goal "(dual cl.<A>) = cl.<A>";
by (simp_tac (simpset() addsimps [dual_def]) 1);
qed "dualA_iff";

Goal "((x, y) \\<in> (dual cl.<r>)) = ((y, x) \\<in> cl.<r>)";
by (simp_tac (simpset() addsimps [dual_def]) 1);
qed "dualr_iff";

Goal "monotone f (cl.<A>) (cl.<r>) ==> monotone f (dual cl.<A>) (dual cl.<r>)";
by (afs [monotone_def,dualA_iff,dualr_iff] 1);
qed "monotone_dual";

Goal "[| x \\<in> A; y \\<in> A|] ==> interval r x y = interval (dual cl.<r>) y x";
by (simp_tac (simpset() addsimps [interval_def,dualr_iff]) 1);
by (fold_goals_tac [thm "r_def"]);
by (Fast_tac 1);
qed "interval_dual";

Goal "[| trans r; interval r a b \\<noteq> {} |] ==> (a, b) \\<in> r";
by (afs [interval_def] 1);
by (rewtac trans_def);
by (Blast_tac 1);
qed "interval_not_empty";

Goal "x \\<in> interval r a b ==> (a, x) \\<in> r";
by (afs [interval_def] 1);
qed "intervalE1";

Goal "[| a \\<in> A; b \\<in> A; interval r a b \\<noteq> {} |] ==> a \\<in> interval r a b";
by (simp_tac (simpset() addsimps [interval_def]) 1);
by (afs [PartialOrderE3,interval_not_empty] 1);
by (afs [PartialOrderE1 RS reflE] 1);
qed "left_in_interval";

Goal "[| a \\<in> A; b \\<in> A; interval r a b \\<noteq> {} |] ==> b \\<in> interval r a b";
by (simp_tac (simpset() addsimps [interval_def]) 1);
by (afs [PartialOrderE3,interval_not_empty] 1);
by (afs [PartialOrderE1 RS reflE] 1);
qed "right_in_interval";

Goal "[| (| pset = A, order = r |) \\<in> PartialOrder;\
\        \\<forall>S. S <= A --> (\\<exists>L. islub S (| pset = A, order = r |)  L) |] \
\   ==> (| pset = A, order = r |) \\<in> CompleteLattice";
by (afs [CompleteLatticeI, Rdual] 1);
qed "CompleteLatticeI_simp";

(* sublattice *)
Goal "S <<= cl ==> S <= A";
by (afs [sublattice_def, CompleteLattice_def, thm "A_def"] 1);
qed "sublatticeE1";

Goal "S <<= cl  ==> (| pset = S, order = induced S r |) \\<in> CompleteLattice";
by (afs ([sublattice_def, CompleteLattice_def] @ PO_simp) 1);
qed "sublatticeE2";

Goal "[| S <= A; (| pset = S, order = induced S r |) \\<in> CompleteLattice |] ==> S <<= cl";
by (afs ([sublattice_def] @ PO_simp) 1);
qed "sublatticeI";

(* lub *)
Goal "[| S <= A; islub S cl x; islub S cl L|] ==> x = L";
by (rtac antisymE 1); 
by (rtac CompleteLatticeE12 1);
by (auto_tac (claset(), simpset() addsimps [islub_def, thm "r_def"])); 
qed "lub_unique";

Goal "[| S <= A |] ==> \\<forall>x \\<in> S. (x,lub S cl) \\<in> r";
by (rtac exE 1);
by (rtac (CompleteLatticeE2 RS spec RS mp) 1);
by (assume_tac 1);
by (rewrite_goals_tac [lub_def,least_def]);
by (stac some_equality 1);
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

Goal "[| S <= A; L \\<in> A; \\<forall>x \\<in> S. (x,L) \\<in> r |] ==> (lub S cl, L) \\<in> r";
by (rtac exE 1);
by (rtac (CompleteLatticeE2 RS spec RS mp) 1);
by (assume_tac 1);
by (rewrite_goals_tac [lub_def,least_def]);
by (stac some_equality 1);
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

Goal "[| S <= A |] ==> lub S cl \\<in> A";  
by (rtac exE 1);
by (rtac (CompleteLatticeE2 RS spec RS mp) 1);
by (assume_tac 1);
by (rewrite_goals_tac [lub_def,least_def]);
by (stac some_equality 1);
by (afs [islub_def] 1);
by (afs [islub_def, thm "A_def"] 2);
by (rtac lub_unique 1);
by (afs [thm "A_def"] 1);
by (afs [islub_def] 1);
by (assume_tac 1);
qed "lub_in_lattice";

Goal "[| S <= A; L \\<in> A; \\<forall>x \\<in> S. (x,L) \\<in> r;\
\ \\<forall>z \\<in> A. (\\<forall>y \\<in> S. (y,z) \\<in> r) --> (L,z) \\<in> r |] ==> L = lub S cl";
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

Goal "islub S cl L ==> L \\<in> A";
by (afs [islub_def, thm "A_def"] 1);
qed "islub_in_lattice";

Goal "islub S cl L ==> \\<forall>y \\<in> S. (y, L) \\<in> r";
by (afs [islub_def, thm "r_def"] 1);
qed "islubE1";

Goal "[| islub S cl L; \
\      z \\<in> A; \\<forall>y \\<in> S. (y, z) \\<in> r|] ==> (L, z) \\<in> r";
by (afs ([islub_def] @ PO_simp) 1);
qed "islubE2";

Goal "[| S <= A |] ==> \\<exists>L. islub S cl L";
by (afs [thm "A_def"] 1);
qed "islubE";

Goal "[| L \\<in> A; \\<forall>y \\<in> S. (y, L) \\<in> r; \
\     (\\<forall>z \\<in> A. (\\<forall>y \\<in> S. (y, z):r) --> (L, z) \\<in> r)|] ==> islub S cl L";
by (afs ([islub_def] @ PO_simp) 1);
qed "islubI";

(* glb *)
Goal "S <= A ==> glb S cl \\<in> A";  
by (stac glb_dual_lub 1);
by (afs [thm "A_def"] 1);
by (rtac (dualA_iff RS subst) 1);
by (rtac (export lub_in_lattice) 1);
by (rtac CL_dualCL 1);
by (afs [dualA_iff] 1);
qed "glb_in_lattice";

Goal "S <= A ==> \\<forall>x \\<in> S. (glb S cl, x) \\<in> r";
by (stac glb_dual_lub 1);
by (rtac ballI 1);
by (afs [thm "r_def"] 1);
by (rtac (dualr_iff RS subst) 1);
by (rtac (export lubE1 RS bspec) 1);
by (rtac CL_dualCL 1);
by (afs [dualA_iff, thm "A_def"] 1);
by (assume_tac 1);
qed "glbE1";

(* Reduce the sublattice property by using substructural properties\\<forall>*)
(* abandoned see Tarski_4.ML *)

Open_locale "CLF";

val simp_CLF = simplify (simpset() addsimps [CLF_def]) (thm "f_cl");
Addsimps [simp_CLF, thm "f_cl"];

Goal "f \\<in> A funcset A";
by (simp_tac (simpset() addsimps [thm "A_def"]) 1);
qed "CLF_E1";

Goal "monotone f A r";
by (simp_tac (simpset() addsimps PO_simp) 1);
qed "CLF_E2";

Goal "f \\<in> CLF `` {cl} ==> f \\<in> CLF `` {dual cl}";
by (afs [CLF_def, CL_dualCL, monotone_dual] 1); 
by (afs [dualA_iff] 1);
qed "CLF_dual";

(* fixed points *)
Goal "P <= A";
by (simp_tac (simpset() addsimps [thm "P_def", fix_def]) 1);
by (Fast_tac 1);
qed "fixfE1";

Goal "x \\<in> P ==> f x = x";
by (afs [thm "P_def", fix_def] 1);
qed "fixfE2";

Goal "[| A <= B; x \\<in> fix (lam y: A. f y) A |] ==> x \\<in> fix f B";
by (forward_tac [export fixfE2] 1);
by (dtac ((export fixfE1) RS subsetD) 1);
by (asm_full_simp_tac (simpset() addsimps [fix_def, subsetD]) 1); 
qed "fixf_subset";

(* lemmas for Tarski, lub *)
Goal "H = {x. (x, f x) \\<in> r & x \\<in> A} ==> (lub H cl, f (lub H cl)) \\<in> r";
by (rtac lubE2 1);
by (Fast_tac 1);
by (rtac (CLF_E1 RS funcset_mem) 1);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
(* \\<forall>x:H. (x, f (lub H r)) \\<in> r *)
by (rtac ballI 1);
by (rtac transE 1);
by (rtac CompleteLatticeE13 1);
(* instantiates (x, ???z) \\<in> cl.<r> to (x, f x), because of the def of H *)
by (Fast_tac 1);
(* so it remains to show (f x, f (lub H cl)) \\<in> r *)
by (res_inst_tac [("f","f")] monotoneE 1);
by (rtac CLF_E2 1);
by (Fast_tac 1);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
by (rtac (lubE1 RS bspec) 1);
by (Fast_tac 1);
by (assume_tac 1);
qed "lubH_le_flubH";

Goal "[|  H = {x. (x, f x) \\<in> r & x \\<in> A} |] ==> (f (lub H cl), lub H cl) \\<in> r";
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

Goal "H = {x. (x, f x) \\<in> r & x \\<in> A} ==> lub H cl \\<in> P";
by (simp_tac (simpset() addsimps [thm "P_def", fix_def]) 1);
by (rtac conjI 1);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
by (rtac antisymE 1);
by (rtac CompleteLatticeE12 1);
by (afs [flubH_le_lubH] 1);
by (afs [lubH_le_flubH] 1);
qed "lubH_is_fixp";

Goal "[| H = {x. (x, f x) \\<in> r & x \\<in> A};  x \\<in> P |] ==> x \\<in> H";
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

Goal "H = {x. (x, f x) \\<in> r & x \\<in> A} ==> \\<forall>x \\<in> P. (x, lub H cl) \\<in> r";
by (rtac ballI 1);
by (rtac (lubE1 RS bspec) 1);
by (Fast_tac 1);
by (rtac fix_in_H 1);
by (REPEAT (atac 1));
qed "fixf_le_lubH";

Goal "H = {x. (x, f x) \\<in> r & x \\<in> A} ==> \\<forall>L. (\\<forall>y \\<in> P. (y,L) \\<in> r) --> (lub H cl, L) \\<in> r";
by (rtac allI 1);
by (rtac impI 1);
by (etac bspec 1);
by (rtac lubH_is_fixp 1);
by (assume_tac 1);
qed "lubH_least_fixf";

(* Tarski fixpoint theorem 1, first part *)
Goal "lub P cl = lub {x. (x, f x) \\<in> r & x \\<in> A} cl";
by (rtac sym 1);
by (rtac lubI 1);
by (rtac fixfE1 1);
by (rtac lub_in_lattice 1);
by (Fast_tac 1);
by (afs [fixf_le_lubH] 1);
by (afs [lubH_least_fixf] 1);
qed "T_thm_1_lub";

(* Tarski for glb *)
Goal "H = {x. (f x, x) \\<in> r & x \\<in> A} ==> glb H cl \\<in> P";
by (full_simp_tac 
    (simpset() addsimps [glb_dual_lub, thm "P_def"] @ PO_simp) 1);
by (rtac (dualA_iff RS subst) 1);
by (rtac (CL_dualCL RS (export lubH_is_fixp)) 1);
by (rtac (thm "f_cl" RS CLF_dual) 1);
by (afs [dualr_iff, dualA_iff] 1);
qed "glbH_is_fixp";

Goal "glb P cl = glb {x. (f x, x) \\<in> r & x \\<in> A} cl";
by (simp_tac (simpset() addsimps [glb_dual_lub, thm "P_def"] @ PO_simp) 1);
by (rtac (dualA_iff RS subst) 1);
by (rtac (CL_dualCL RS (export T_thm_1_lub) RS ssubst) 1);
by (rtac (thm "f_cl" RS CLF_dual) 1);
by (afs [dualr_iff] 1);
qed "T_thm_1_glb";

(* interval *)
Goal "refl A r ==> r <= A <*> A";
by (afs [refl_def] 1);
qed "reflE1";

Goal "(x, y) \\<in> r ==> x \\<in> A";
by (rtac SigmaD1 1);
by (rtac (reflE1 RS subsetD) 1);
by (rtac CompleteLatticeE11 1);
by (assume_tac 1);
qed "rel_imp_elem";

Goal "[| a \\<in> A; b \\<in> A |] ==> interval r a b <= A";
by (simp_tac (simpset() addsimps [interval_def]) 1);
by (blast_tac (claset() addIs [rel_imp_elem]) 1); 
qed "interval_subset";

Goal "[| (a, x) \\<in> r; (x, b) \\<in> r |] ==> x \\<in> interval r a b";
by (afs [interval_def] 1);
qed "intervalI";

Goalw [interval_def] "[| S <= interval r a b; x \\<in> S |] ==> (a, x) \\<in> r";
by (Fast_tac 1);
qed "interval_lemma1";

Goalw [interval_def] "[| S <= interval r a b; x \\<in> S |] ==> (x, b) \\<in> r";
by (Fast_tac 1);
qed "interval_lemma2";

Goal "[| S <= A; S \\<noteq> {};\
\        \\<forall>x \\<in> S. (a,x) \\<in> r; \\<forall>y \\<in> S. (y, L) \\<in> r |] ==> (a,L) \\<in> r";
by (blast_tac (claset() addIs [transE, PartialOrderE3]) 1);
qed "a_less_lub";

Goal "[| S <= A; S \\<noteq> {};\
\        \\<forall>x \\<in> S. (x,b) \\<in> r; \\<forall>y \\<in> S. (G, y) \\<in> r |] ==> (G,b) \\<in> r";
by (blast_tac (claset() addIs [transE, PartialOrderE3]) 1);
qed "glb_less_b";

Goal "[| a \\<in> A; b \\<in> A; S <= interval r a b |]==> S <= A";
by (afs [interval_subset RSN(2, subset_trans)] 1);
qed "S_intv_cl";

Goal "[| a \\<in> A; b \\<in> A; S <= interval r a b; \
\      S \\<noteq> {}; islub S cl L; interval r a b \\<noteq> {} |] ==> L \\<in> interval r a b";
by (rtac intervalI 1);
by (rtac a_less_lub 1);
by (assume_tac 2);
by (afs [S_intv_cl] 1);
by (rtac ballI 1);
by (afs [interval_lemma1] 1);
by (afs [islubE1] 1);
(* (L, b) \\<in> r *)
by (rtac islubE2 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac ballI 1);
by (afs [interval_lemma2] 1);
qed "L_in_interval";

Goal "[| a \\<in> A; b \\<in> A; interval r a b \\<noteq> {}; S <= interval r a b; isglb S cl G; \
\      S \\<noteq> {} |]   ==> G \\<in> interval r a b";
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

Goal "[| a \\<in> A; b \\<in> A; interval r a b \\<noteq> {} |]\
\  ==> (| pset = interval r a b, order = induced (interval r a b) r |) \\<in> PartialOrder";
by (rtac po_subset_po 1);
by (afs [interval_subset] 1);
qed "intervalPO";

Goal "[| a \\<in> A; b \\<in> A;\
\   interval r a b \\<noteq> {} |] ==> \\<forall>S. S <= interval r a b -->\
\         (\\<exists>L. islub S (| pset = interval r a b, order = induced (interval r a b) r |)  L)";
by (strip_tac 1);
by (forward_tac [S_intv_cl RS islubE] 1);
by (assume_tac 2);
by (assume_tac 1);
by (etac exE 1);
(* define the lub for the interval as *)
by (res_inst_tac [("x","if S = {} then a else L")] exI 1);
by (rtac (export islubI) 1);
(* (if S = {} then a else L) \\<in> interval r a b *)
by (asm_full_simp_tac
    (simpset() addsimps [CompleteLatticeE1,L_in_interval]) 1);
by (afs [left_in_interval] 1);
(* lub prop 1 *)
by (case_tac "S = {}" 1);
(* S = {}, y \\<in> S = False => everything *)
by (Fast_tac 1);
(* S \\<noteq> {} *)
by (Asm_full_simp_tac 1);
(* \\<forall>y:S. (y, L) \\<in> induced (interval r a b) r *)
by (rtac ballI 1);
by (afs [induced_def, L_in_interval] 1);
by (rtac conjI 1);
by (rtac subsetD 1);
by (afs [S_intv_cl] 1);
by (assume_tac 1);
by (afs [islubE1] 1);
(* \\<forall>z:interval r a b. (\\<forall>y:S. (y, z) \\<in> induced (interval r a b) r -->
      (if S = {} then a else L, z) \\<in> induced (interval r a b) r *)
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
(* S \\<noteq> {} *)
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

Goal "[| a \\<in> A; b \\<in> A; interval r a b \\<noteq> {} |]\
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

Goal "Bot cl \\<in> A";
by (simp_tac (simpset() addsimps [Bot_def,least_def]) 1);
by (rtac someI2 1);
by (fold_goals_tac [thm "A_def"]);
by (etac conjunct1 2);
by (rtac conjI 1);
by (rtac glb_in_lattice 1);
by (rtac subset_refl 1);
by (fold_goals_tac [thm "r_def"]);
by (afs [glbE1] 1);
qed "Bot_in_lattice";

Goal "Top cl \\<in> A";
by (simp_tac (simpset() addsimps [Top_dual_Bot, thm "A_def"]) 1);
by (rtac (dualA_iff RS subst) 1);
by (afs [export Bot_in_lattice,CL_dualCL] 1);
qed "Top_in_lattice";

Goal "x \\<in> A ==> (x, Top cl) \\<in> r";
by (simp_tac (simpset() addsimps [Top_def,greatest_def]) 1);
by (rtac someI2 1);
by (fold_goals_tac [thm "r_def", thm "A_def"]);
by (Fast_tac 2);
by (rtac conjI 1);
by (rtac lubE1 2);
by (afs [lub_in_lattice] 1);
by (rtac subset_refl 1);
qed "Top_prop";

Goal "x \\<in> A ==> (Bot cl, x) \\<in> r";
by (simp_tac (simpset() addsimps [Bot_dual_Top, thm "r_def"]) 1);
by (rtac (dualr_iff RS subst) 1);
by (rtac (export Top_prop) 1);
by (rtac CL_dualCL 1);
by (afs [dualA_iff, thm "A_def"] 1);
qed "Bot_prop";

Goal "x \\<in> A  ==> interval r x (Top cl) \\<noteq> {}";
by (rtac notI 1);
by (dres_inst_tac [("a","Top cl")] equals0D 1);
by (afs [interval_def] 1);
by (afs [refl_def,Top_in_lattice,Top_prop] 1);
qed "Top_intv_not_empty";

Goal "x \\<in> A ==> interval r (Bot cl) x \\<noteq> {}";
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
Goal "(| pset = P, order = induced P r|) \\<in> PartialOrder";
by (rtac po_subset_po 1);
by (rtac fixfE1 1);
qed "fixf_po";

Open_locale "Tarski";

Goal "Y <= A";
by (rtac (fixfE1 RSN(2,subset_trans)) 1);
by (rtac (thm "Y_ss") 1);
qed "Y_subset_A";

Goal "lub Y cl \\<in> A";
by (afs [Y_subset_A RS lub_in_lattice] 1);
qed "lubY_in_A";

Goal "(lub Y cl, f (lub Y cl)) \\<in> r";
by (rtac lubE2 1);
by (rtac Y_subset_A 1);
by (rtac (CLF_E1 RS funcset_mem) 1);
by (rtac lubY_in_A 1);
(* Y <= P ==> f x = x *)
by (rtac ballI 1);
by (res_inst_tac [("t","x")] (fixfE2 RS subst) 1);
by (etac (thm "Y_ss" RS subsetD) 1);
(* reduce (f x, f (lub Y cl)) \\<in> r to (x, lub Y cl) \\<in> r by monotonicity *)
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

Goal "x \\<in> intY1 \\<Longrightarrow> f x \\<in> intY1";
by (afs [thm "intY1_def", interval_def] 1);
by (rtac conjI 1);
by (rtac transE 1);
by (rtac CompleteLatticeE13 1);
by (rtac lubY_le_flubY 1);
(* (f (lub Y cl), f x) \\<in> r *)
by (res_inst_tac [("f","f")]monotoneE 1);
by (rtac CLF_E2 1);
by (rtac lubY_in_A 1);
by (afs [thm "intY1_def",interval_def, intY1_elem] 1);
by (afs [thm "intY1_def", interval_def] 1);
(* (f x, Top cl) \\<in> r *)
by (rtac Top_prop 1);
by (rtac (CLF_E1 RS funcset_mem) 1);
by (afs [thm "intY1_def",interval_def, intY1_elem] 1);
qed "intY1_f_closed";

Goal "(lam x: intY1. f x) \\<in> intY1 funcset intY1";
by (rtac restrictI 1);
by (etac intY1_f_closed 1); 
qed "intY1_func";

Goal "monotone (lam x: intY1. f x) intY1 (induced intY1 r)";
by (auto_tac (claset(), 
            simpset() addsimps [monotone_def, induced_def, intY1_f_closed])); 
by (blast_tac (claset() addIs [intY1_elem, CLF_E2 RS monotoneE]) 1); 
qed "intY1_mono";

Goalw [thm "intY1_def"]
    "(| pset = intY1, order = induced intY1 r |) \\<in> CompleteLattice";
by (rtac interv_is_compl_latt 1);
by (rtac lubY_in_A 1);
by (rtac Top_in_lattice 1);
by (rtac Top_intv_not_empty 1);
by (rtac lubY_in_A 1);
qed "intY1_is_cl";

Goalw  [thm "P_def"] "v \\<in> P";
by (res_inst_tac [("A","intY1")] fixf_subset 1);
by (rtac intY1_subset 1);
by (rewrite_goals_tac [thm "v_def"]);
by (rtac (simplify (simpset()) (intY1_is_cl RS export glbH_is_fixp)) 1);
by (afs [CLF_def, intY1_is_cl, intY1_func, intY1_mono] 1);
by (Simp_tac 1);
qed "v_in_P";

Goalw [thm "intY1_def"]
     "[| z \\<in> P; \\<forall>y\\<in>Y. (y, z) \\<in> induced P r |] ==> z \\<in> intY1";
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

Goal "[| z \\<in> P; \\<forall>y\\<in>Y. (y, z) \\<in> induced P r |]\
\     ==> ((lam x: intY1. f x) z, z) \\<in> induced intY1 r";
by (afs [induced_def, intY1_f_closed, z_in_interval] 1);
by (afs [fixfE2, fixfE1 RS subsetD, CompleteLatticeE11 RS reflE] 1);
qed "f'z_in_int_rel";

Goal "\\<exists>L. islub Y (| pset = P, order = induced P r |) L";
by (res_inst_tac [("x","v")] exI 1);
by (simp_tac (simpset() addsimps [islub_def]) 1);
(* v \\<in> P *)
by (afs [v_in_P] 1);
by (rtac conjI 1);
(* v is lub *)
(*  1. \\<forall>y:Y. (y, v) \\<in> induced P r *)
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
by (Force_tac 1); 
(* v is LEAST ub *)
by (Clarify_tac 1);
by (rtac indI 1);
by (afs [v_in_P] 2);
by (assume_tac 2);
by (rewrite_goals_tac [thm "v_def"]);
by (rtac indE 1);
by (rtac intY1_subset 2);
by (rtac (simplify (simpset()) (intY1_is_cl RS export (glbE1 RS bspec))) 1);
by (Force_tac 1); 
by (afs [induced_def, intY1_f_closed, z_in_interval] 1);
by (afs [fixfE2, fixfE1 RS subsetD, CompleteLatticeE11 RS reflE] 1);
qed "tarski_full_lemma";
val Tarski_full_lemma = Export tarski_full_lemma;

Close_locale "Tarski";

Goal "(| pset = P, order = induced P r|) \\<in> CompleteLattice";
by (rtac CompleteLatticeI_simp 1);
by (afs [fixf_po] 1);
by (Clarify_tac 1);
by (etac Tarski_full_lemma 1);
qed "Tarski_full";


Close_locale "CLF";
Close_locale "CL";
Close_locale "PO";



