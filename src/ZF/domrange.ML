(*  Title:      ZF/domrange
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Converse, domain, range of a relation or function
*)

(*** converse ***)

Goalw [converse_def] "<a,b>: converse(r) <-> <b,a>:r";
by (Blast_tac 1) ;
qed "converse_iff";

Goalw [converse_def] "<a,b>:r ==> <b,a>:converse(r)";
by (Blast_tac 1) ;
qed "converseI";

Goalw [converse_def] "<a,b> : converse(r) ==> <b,a> : r";
by (Blast_tac 1) ;
qed "converseD";

val [major,minor]= Goalw [converse_def] 
    "[| yx : converse(r);  \
\       !!x y. [| yx=<y,x>;  <x,y>:r |] ==> P \
\    |] ==> P";
by (rtac (major RS ReplaceE) 1);
by (REPEAT (eresolve_tac [exE, conjE, minor] 1));
by (hyp_subst_tac 1);
by (assume_tac 1) ;
qed "converseE";

Addsimps [converse_iff];
AddSIs [converseI];
AddSEs [converseD,converseE];

Goal "r<=Sigma(A,B) ==> converse(converse(r)) = r";
by (Blast_tac 1) ;
qed "converse_converse";

Goal "r<=A*B ==> converse(r)<=B*A";
by (Blast_tac 1) ;
qed "converse_type";

Goal "converse(A*B) = B*A";
by (Blast_tac 1) ;
qed "converse_prod";

Goal "converse(0) = 0";
by (Blast_tac 1) ;
qed "converse_empty";

Addsimps [converse_prod, converse_empty];

Goal "A <= Sigma(X,Y) ==> converse(A) <= converse(B) <-> A <= B";
by (Blast_tac 1) ;
qed "converse_subset_iff";


(*** domain ***)

Goalw [domain_def] "a: domain(r) <-> (EX y. <a,y>: r)";
by (Blast_tac 1) ;
qed "domain_iff";

Goal "<a,b>: r ==> a: domain(r)";
by (etac (exI RS (domain_iff RS iffD2)) 1) ;
qed "domainI";

val prems= Goal
    "[| a : domain(r);  !!y. <a,y>: r ==> P |] ==> P";
by (rtac (domain_iff RS iffD1 RS exE) 1);
by (REPEAT (ares_tac prems 1)) ;
qed "domainE";

AddIs  [domainI];
AddSEs [domainE];

Goal "domain(Sigma(A,B)) <= A";
by (Blast_tac 1) ;
qed "domain_subset";

(*** range ***)

Goalw [range_def]  "<a,b>: r ==> b : range(r)";
by (etac (converseI RS domainI) 1) ;
qed "rangeI";

val major::prems= Goalw [range_def] 
    "[| b : range(r);  !!x. <x,b>: r ==> P |] ==> P";
by (rtac (major RS domainE) 1);
by (resolve_tac prems 1);
by (etac converseD 1) ;
qed "rangeE";

AddIs  [rangeI];
AddSEs [rangeE];

Goalw [range_def]  "range(A*B) <= B";
by (stac converse_prod 1);
by (rtac domain_subset 1) ;
qed "range_subset";


(*** field ***)

Goalw [field_def]  "<a,b>: r ==> a : field(r)";
by (Blast_tac 1) ;
qed "fieldI1";

Goalw [field_def]  "<a,b>: r ==> b : field(r)";
by (Blast_tac 1) ;
qed "fieldI2";

val [prem]= Goalw [field_def] 
    "(~ <c,a>:r ==> <a,b>: r) ==> a : field(r)";
by (blast_tac (claset() addIs [prem]) 1) ;
qed "fieldCI";

val major::prems= Goalw [field_def] 
     "[| a : field(r);  \
\        !!x. <a,x>: r ==> P;  \
\        !!x. <x,a>: r ==> P        |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (eresolve_tac (prems@[domainE,rangeE]) 1)) ;
qed "fieldE";

AddIs  [fieldCI];
AddSEs [fieldE];

Goal "field(A*B) <= A Un B";
by (Blast_tac 1) ;
qed "field_subset";

Goalw [field_def] "domain(r) <= field(r)";
by (rtac Un_upper1 1) ;
qed "domain_subset_field";

Goalw [field_def] "range(r) <= field(r)";
by (rtac Un_upper2 1) ;
qed "range_subset_field";

Goal "r <= Sigma(A,B) ==> r <= domain(r)*range(r)";
by (Blast_tac 1) ;
qed "domain_times_range";

Goal "r <= Sigma(A,B) ==> r <= field(r)*field(r)";
by (Blast_tac 1) ;
qed "field_times_field";


(*** Image of a set under a function/relation ***)

Goalw [image_def] "b : r``A <-> (EX x:A. <x,b>:r)";
by (Blast_tac 1);
qed "image_iff";

Goal "b : r``{a} <-> <a,b>:r";
by (rtac (image_iff RS iff_trans) 1);
by (Blast_tac 1) ;
qed "image_singleton_iff";

Goalw [image_def] "[| <a,b>: r;  a:A |] ==> b : r``A";
by (Blast_tac 1) ;
qed "imageI";

val major::prems= Goalw [image_def] 
    "[| b: r``A;  !!x.[| <x,b>: r;  x:A |] ==> P |] ==> P";
by (rtac (major RS CollectE) 1);
by (REPEAT (etac bexE 1 ORELSE ares_tac prems 1)) ;
qed "imageE";

AddIs  [imageI];
AddSEs [imageE];

Goal "r <= A*B ==> r``C <= B";
by (Blast_tac 1) ;
qed "image_subset";


(*** Inverse image of a set under a function/relation ***)

Goalw [vimage_def,image_def,converse_def] 
    "a : r-``B <-> (EX y:B. <a,y>:r)";
by (Blast_tac 1) ;
qed "vimage_iff";

Goal "a : r-``{b} <-> <a,b>:r";
by (rtac (vimage_iff RS iff_trans) 1);
by (Blast_tac 1) ;
qed "vimage_singleton_iff";

Goalw [vimage_def] "[| <a,b>: r;  b:B |] ==> a : r-``B";
by (Blast_tac 1) ;
qed "vimageI";

val major::prems= Goalw [vimage_def] 
    "[| a: r-``B;  !!x.[| <a,x>: r;  x:B |] ==> P |] ==> P";
by (rtac (major RS imageE) 1);
by (REPEAT (etac converseD 1 ORELSE ares_tac prems 1)) ;
qed "vimageE";

Goalw [vimage_def] "r <= A*B ==> r-``C <= A";
by (etac (converse_type RS image_subset) 1) ;
qed "vimage_subset";


(** Theorem-proving for ZF set theory **)

AddIs  [vimageI];
AddSEs [vimageE];

val ZF_cs = claset() delrules [equalityI];

(** The Union of a set of relations is a relation -- Lemma for fun_Union **)
Goal "(ALL x:S. EX A B. x <= A*B) ==>  \
\                 Union(S) <= domain(Union(S)) * range(Union(S))";
by (Blast_tac 1);
qed "rel_Union";

(** The Union of 2 relations is a relation (Lemma for fun_Un)  **)
Goal "[| r <= A*B;  s <= C*D |] ==> (r Un s) <= (A Un C) * (B Un D)";
by (Blast_tac 1) ;
qed "rel_Un";

Goal "[| <a,c> : r; c~=b |] ==> domain(r-{<a,b>}) = domain(r)";
by (Blast_tac 1);
qed "domain_Diff_eq";

Goal "[| <c,b> : r; c~=a |] ==> range(r-{<a,b>}) = range(r)";
by (Blast_tac 1);
qed "range_Diff_eq";

