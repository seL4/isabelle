(*  Title:      Relation.ML
    ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

(** Identity relation **)

Goalw [Id_def] "(a,a) : Id";  
by (Blast_tac 1);
qed "IdI";

val major::prems = Goalw [Id_def]
    "[| p: Id;  !!x.[| p = (x,x) |] ==> P  \
\    |] ==>  P";  
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (eresolve_tac prems 1);
qed "IdE";

Goalw [Id_def] "(a,b):Id = (a=b)";
by (Blast_tac 1);
qed "pair_in_Id_conv";
AddIffs [pair_in_Id_conv];

Goalw [refl_def] "reflexive Id";
by Auto_tac;
qed "reflexive_Id";

(*A strange result, since Id is also symmetric.*)
Goalw [antisym_def] "antisym Id";
by Auto_tac;
qed "antisym_Id";

Goalw [trans_def] "trans Id";
by Auto_tac;
qed "trans_Id";


(** Diagonal relation: indentity restricted to some set **)

(*** Equality : the diagonal relation ***)

Goalw [diag_def] "[| a=b;  a:A |] ==> (a,b) : diag(A)";
by (Blast_tac 1);
qed "diag_eqI";

val diagI = refl RS diag_eqI |> standard;

(*The general elimination rule*)
val major::prems = Goalw [diag_def]
    "[| c : diag(A);  \
\       !!x y. [| x:A;  c = (x,x) |] ==> P \
\    |] ==> P";
by (rtac (major RS UN_E) 1);
by (REPEAT (eresolve_tac [asm_rl,singletonE] 1 ORELSE resolve_tac prems 1));
qed "diagE";

AddSIs [diagI];
AddSEs [diagE];

Goal "((x,y) : diag A) = (x=y & x : A)";
by (Blast_tac 1);
qed "diag_iff";

Goal "diag(A) <= A <*> A";
by (Blast_tac 1);
qed "diag_subset_Times";



(** Composition of two relations **)

Goalw [comp_def]
    "[| (a,b):s; (b,c):r |] ==> (a,c) : r O s";
by (Blast_tac 1);
qed "compI";

(*proof requires higher-level assumptions or a delaying of hyp_subst_tac*)
val prems = Goalw [comp_def]
    "[| xz : r O s;  \
\       !!x y z. [| xz = (x,z);  (x,y):s;  (y,z):r |] ==> P \
\    |] ==> P";
by (cut_facts_tac prems 1);
by (REPEAT (eresolve_tac [CollectE, splitE, exE, conjE] 1 
     ORELSE ares_tac prems 1));
qed "compE";

val prems = Goal
    "[| (a,c) : r O s;  \
\       !!y. [| (a,y):s;  (y,c):r |] ==> P \
\    |] ==> P";
by (rtac compE 1);
by (REPEAT (ares_tac prems 1 ORELSE eresolve_tac [Pair_inject,ssubst] 1));
qed "compEpair";

AddIs [compI, IdI];
AddSEs [compE, IdE];

Goal "R O Id = R";
by (Fast_tac 1);
qed "R_O_Id";

Goal "Id O R = R";
by (Fast_tac 1);
qed "Id_O_R";

Addsimps [R_O_Id,Id_O_R];

Goal "(R O S) O T = R O (S O T)";
by (Blast_tac 1);
qed "O_assoc";

Goal "[| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)";
by (Blast_tac 1);
qed "comp_mono";

Goal "[| s <= A <*> B;  r <= B <*> C |] ==> (r O s) <= A <*> C";
by (Blast_tac 1);
qed "comp_subset_Sigma";

(** Natural deduction for refl(r) **)

val prems = Goalw [refl_def]
    "[| r <= A <*> A;  !! x. x:A ==> (x,x):r |] ==> refl A r";
by (REPEAT (ares_tac (prems@[ballI,conjI]) 1));
qed "reflI";

Goalw [refl_def] "[| refl A r; a:A |] ==> (a,a):r";
by (Blast_tac 1);
qed "reflD";

(** Natural deduction for antisym(r) **)

val prems = Goalw [antisym_def]
    "(!! x y. [| (x,y):r;  (y,x):r |] ==> x=y) ==> antisym(r)";
by (REPEAT (ares_tac (prems@[allI,impI]) 1));
qed "antisymI";

Goalw [antisym_def] "[| antisym(r);  (a,b):r;  (b,a):r |] ==> a=b";
by (Blast_tac 1);
qed "antisymD";

(** Natural deduction for trans(r) **)

val prems = Goalw [trans_def]
    "(!! x y z. [| (x,y):r;  (y,z):r |] ==> (x,z):r) ==> trans(r)";
by (REPEAT (ares_tac (prems@[allI,impI]) 1));
qed "transI";

Goalw [trans_def] "[| trans(r);  (a,b):r;  (b,c):r |] ==> (a,c):r";
by (Blast_tac 1);
qed "transD";

(** Natural deduction for r^-1 **)

Goalw [converse_def] "((a,b): r^-1) = ((b,a):r)";
by (Simp_tac 1);
qed "converse_iff";

AddIffs [converse_iff];

Goalw [converse_def] "(a,b):r ==> (b,a): r^-1";
by (Simp_tac 1);
qed "converseI";

Goalw [converse_def] "(a,b) : r^-1 ==> (b,a) : r";
by (Blast_tac 1);
qed "converseD";

(*More general than converseD, as it "splits" the member of the relation*)

val [major,minor] = Goalw [converse_def]
    "[| yx : r^-1;  \
\       !!x y. [| yx=(y,x);  (x,y):r |] ==> P \
\    |] ==> P";
by (rtac (major RS CollectE) 1);
by (REPEAT (eresolve_tac [splitE, bexE,exE, conjE, minor] 1));
by (assume_tac 1);
qed "converseE";
AddSEs [converseE];

Goalw [converse_def] "(r^-1)^-1 = r";
by (Blast_tac 1);
qed "converse_converse";
Addsimps [converse_converse];

Goal "(r O s)^-1 = s^-1 O r^-1";
by (Blast_tac 1);
qed "converse_comp";

Goal "Id^-1 = Id";
by (Blast_tac 1);
qed "converse_Id";
Addsimps [converse_Id];

Goal "(diag A) ^-1 = diag A";
by (Blast_tac 1);
qed "converse_diag";
Addsimps [converse_diag];

Goalw [refl_def] "refl A r ==> refl A (converse r)";
by (Blast_tac 1);
qed "refl_converse";

Goalw [antisym_def] "antisym (converse r) = antisym r";
by (Blast_tac 1);
qed "antisym_converse";

Goalw [trans_def] "trans (converse r) = trans r";
by (Blast_tac 1);
qed "trans_converse";

(** Domain **)

Goalw [Domain_def] "a: Domain(r) = (EX y. (a,y): r)";
by (Blast_tac 1);
qed "Domain_iff";

Goal "(a,b): r ==> a: Domain(r)";
by (etac (exI RS (Domain_iff RS iffD2)) 1) ;
qed "DomainI";

val prems= Goal "[| a : Domain(r);  !!y. (a,y): r ==> P |] ==> P";
by (rtac (Domain_iff RS iffD1 RS exE) 1);
by (REPEAT (ares_tac prems 1)) ;
qed "DomainE";

AddIs  [DomainI];
AddSEs [DomainE];

Goal "Domain Id = UNIV";
by (Blast_tac 1);
qed "Domain_Id";
Addsimps [Domain_Id];

Goal "Domain (diag A) = A";
by Auto_tac;
qed "Domain_diag";
Addsimps [Domain_diag];

Goal "Domain(A Un B) = Domain(A) Un Domain(B)";
by (Blast_tac 1);
qed "Domain_Un_eq";

Goal "Domain(A Int B) <= Domain(A) Int Domain(B)";
by (Blast_tac 1);
qed "Domain_Int_subset";

Goal "Domain(A) - Domain(B) <= Domain(A - B)";
by (Blast_tac 1);
qed "Domain_Diff_subset";

Goal "Domain (Union S) = (UN A:S. Domain A)";
by (Blast_tac 1);
qed "Domain_Union";

Goal "r <= s ==> Domain r <= Domain s";
by (Blast_tac 1);
qed "Domain_mono";


(** Range **)

Goalw [Domain_def, Range_def] "a: Range(r) = (EX y. (y,a): r)";
by (Blast_tac 1);
qed "Range_iff";

Goalw [Range_def] "(a,b): r ==> b : Range(r)";
by (etac (converseI RS DomainI) 1);
qed "RangeI";

val major::prems = Goalw [Range_def] 
    "[| b : Range(r);  !!x. (x,b): r ==> P |] ==> P";
by (rtac (major RS DomainE) 1);
by (resolve_tac prems 1);
by (etac converseD 1) ;
qed "RangeE";

AddIs  [RangeI];
AddSEs [RangeE];

Goal "Range Id = UNIV";
by (Blast_tac 1);
qed "Range_Id";
Addsimps [Range_Id];

Goal "Range (diag A) = A";
by Auto_tac;
qed "Range_diag";
Addsimps [Range_diag];

Goal "Range(A Un B) = Range(A) Un Range(B)";
by (Blast_tac 1);
qed "Range_Un_eq";

Goal "Range(A Int B) <= Range(A) Int Range(B)";
by (Blast_tac 1);
qed "Range_Int_subset";

Goal "Range(A) - Range(B) <= Range(A - B)";
by (Blast_tac 1);
qed "Range_Diff_subset";

Goal "Range (Union S) = (UN A:S. Range A)";
by (Blast_tac 1);
qed "Range_Union";


(*** Image of a set under a relation ***)

overload_1st_set "Relation.Image";

Goalw [Image_def] "b : r^^A = (? x:A. (x,b):r)";
by (Blast_tac 1);
qed "Image_iff";

Goalw [Image_def] "r^^{a} = {b. (a,b):r}";
by (Blast_tac 1);
qed "Image_singleton";

Goal "(b : r^^{a}) = ((a,b):r)";
by (rtac (Image_iff RS trans) 1);
by (Blast_tac 1);
qed "Image_singleton_iff";

AddIffs [Image_singleton_iff];

Goalw [Image_def] "[| (a,b): r;  a:A |] ==> b : r^^A";
by (Blast_tac 1);
qed "ImageI";

val major::prems = Goalw [Image_def]
    "[| b: r^^A;  !!x.[| (x,b): r;  x:A |] ==> P |] ==> P";
by (rtac (major RS CollectE) 1);
by (Clarify_tac 1);
by (rtac (hd prems) 1);
by (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ;
qed "ImageE";

AddIs  [ImageI];
AddSEs [ImageE];

(*This version's more effective when we already have the required "a"*)
Goal  "[| a:A;  (a,b): r |] ==> b : r^^A";
by (Blast_tac 1);
qed "rev_ImageI";


Goal "R^^{} = {}";
by (Blast_tac 1);
qed "Image_empty";

Addsimps [Image_empty];

Goal "Id ^^ A = A";
by (Blast_tac 1);
qed "Image_Id";

Goal "diag A ^^ B = A Int B";
by (Blast_tac 1);
qed "Image_diag";

Addsimps [Image_Id, Image_diag];

Goal "R ^^ (A Int B) <= R ^^ A Int R ^^ B";
by (Blast_tac 1);
qed "Image_Int_subset";

Goal "R ^^ (A Un B) = R ^^ A Un R ^^ B";
by (Blast_tac 1);
qed "Image_Un";

Goal "r <= A <*> B ==> r^^C <= B";
by (rtac subsetI 1);
by (REPEAT (eresolve_tac [asm_rl, ImageE, subsetD RS SigmaD2] 1)) ;
qed "Image_subset";

(*NOT suitable for rewriting*)
Goal "r^^B = (UN y: B. r^^{y})";
by (Blast_tac 1);
qed "Image_eq_UN";

Goal "[| r'<=r; A'<=A |] ==> (r' ^^ A') <= (r ^^ A)";
by (Blast_tac 1);
qed "Image_mono";

Goal "(r ^^ (UNION A B)) = (UN x:A.(r ^^ (B x)))";
by (Blast_tac 1);
qed "Image_UN";

(*Converse inclusion fails*)
Goal "(r ^^ (INTER A B)) <= (INT x:A.(r ^^ (B x)))";
by (Blast_tac 1);
qed "Image_INT_subset";

Goal "(r^^A <= B) = (A <= - ((r^-1) ^^ (-B)))";
by (Blast_tac 1);
qed "Image_subset_eq";

section "univalent";

Goalw [univalent_def]
     "!x y. (x,y):r --> (!z. (x,z):r --> y=z) ==> univalent r";
by (assume_tac 1);
qed "univalentI";

Goalw [univalent_def]
     "[| univalent r;  (x,y):r;  (x,z):r|] ==> y=z";
by Auto_tac;
qed "univalentD";


(** Graphs of partial functions **)

Goal "Domain{(x,y). y = f x & P x} = {x. P x}";
by (Blast_tac 1);
qed "Domain_partial_func";

Goal "Range{(x,y). y = f x & P x} = f``{x. P x}";
by (Blast_tac 1);
qed "Range_partial_func";


(** Composition of function and relation **)

Goalw [fun_rel_comp_def] "A <= B ==> fun_rel_comp f A <= fun_rel_comp f B";
by (Fast_tac 1);
qed "fun_rel_comp_mono";

Goalw [fun_rel_comp_def] "! x. ?! y. (f x, y) : R ==> ?! g. g : fun_rel_comp f R";
by (res_inst_tac [("a","%x. @y. (f x, y) : R")] ex1I 1);
by (rtac CollectI 1);
by (rtac allI 1);
by (etac allE 1);
by (rtac (select_eq_Ex RS iffD2) 1);
by (etac ex1_implies_ex 1);
by (rtac ext 1);
by (etac CollectE 1);
by (REPEAT (etac allE 1));
by (rtac (select1_equality RS sym) 1);
by (atac 1);
by (atac 1);
qed "fun_rel_comp_unique";
