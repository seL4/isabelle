(*  Title:      Substitution.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

(* ------------------------------------------------------------------------- *)
(*   Arithmetic extensions                                                   *)
(* ------------------------------------------------------------------------- *)

goal Arith.thy
    "!!m.[| p < n; n:nat|] ==> n~=p";
by (Fast_tac 1);
qed "gt_not_eq";

val succ_pred = prove_goal Arith.thy 
    "!!i.[|j:nat; i:nat|] ==> i < j --> succ(j #- 1) = j"
 (fn prems =>[(induct_tac "j" 1),
              (Fast_tac 1),
              (Asm_simp_tac 1)]);

goal Arith.thy 
    "!!i.[|succ(x)<n; n:nat; x:nat|] ==> x < n #- 1 ";
by (rtac succ_leE 1);
by (forward_tac [nat_into_Ord RS le_refl RS lt_trans] 1 THEN assume_tac 1);
by (asm_simp_tac (simpset() addsimps [succ_pred]) 1);
qed "lt_pred";

goal Arith.thy 
    "!!i.[|n < succ(x); p<n; p:nat; n:nat; x:nat|] ==> n #- 1 < x ";
by (rtac succ_leE 1);
by (asm_simp_tac (simpset() addsimps [succ_pred]) 1);
qed "gt_pred";


Addsimps [nat_into_Ord, not_lt_iff_le, if_P, if_not_P];


(* ------------------------------------------------------------------------- *)
(*     lift_rec equality rules                                               *)
(* ------------------------------------------------------------------------- *)
Goal "[|n:nat; i:nat|] \
\     ==> lift_rec(Var(i),n) = (if i<n then Var(i) else Var(succ(i)))";
by (asm_simp_tac (simpset() addsimps [lift_rec_def]) 1);
qed "lift_rec_Var";

Goal "[|n:nat; i:nat; k:nat; k le i|] ==> lift_rec(Var(i),k) = Var(succ(i))";
by (asm_simp_tac (simpset() addsimps [lift_rec_def]) 1);
qed "lift_rec_le";

Goal "[|i:nat; k:nat; i<k |] ==> lift_rec(Var(i),k) = Var(i)";
by (asm_simp_tac (simpset() addsimps [lift_rec_def]) 1);
qed "lift_rec_gt";

Goal "[|n:nat; k:nat|] ==>   \
\        lift_rec(Fun(t),k) = Fun(lift_rec(t,succ(k)))";
by (asm_simp_tac (simpset() addsimps [lift_rec_def]) 1);
qed "lift_rec_Fun";

Goal "[|n:nat; k:nat|] ==>   \
\        lift_rec(App(b,f,a),k) = App(b,lift_rec(f,k),lift_rec(a,k))";
by (asm_simp_tac (simpset() addsimps [lift_rec_def]) 1);
qed "lift_rec_App";


(* ------------------------------------------------------------------------- *)
(*    substitution quality rules                                             *)
(* ------------------------------------------------------------------------- *)

Goal "[|i:nat; k:nat; u:redexes|]  \
\     ==> subst_rec(u,Var(i),k) =  \
\         (if k<i then Var(i #- 1) else if k=i then u else Var(i))";
by (asm_simp_tac (simpset() addsimps [subst_rec_def, gt_not_eq, leI]) 1);
qed "subst_Var";

Goal "[|n:nat; u:redexes|] ==> subst_rec(u,Var(n),n) = u";
by (asm_simp_tac (simpset() addsimps [subst_rec_def]) 1);
qed "subst_eq";

Goal "[|n:nat; u:redexes; p:nat; p<n|] ==>  \
\     subst_rec(u,Var(n),p) = Var(n #- 1)";
by (asm_simp_tac (simpset() addsimps [subst_rec_def]) 1);
qed "subst_gt";

Goal "[|n:nat; u:redexes; p:nat; n<p|] ==>  \
\     subst_rec(u,Var(n),p) = Var(n)";
by (asm_simp_tac (simpset() addsimps [subst_rec_def, gt_not_eq, leI]) 1);
qed "subst_lt";

Goal "[|p:nat; u:redexes|] ==>  \
\     subst_rec(u,Fun(t),p) = Fun(subst_rec(lift(u),t,succ(p))) ";
by (asm_simp_tac (simpset() addsimps [subst_rec_def]) 1);
qed "subst_Fun";

Goal "[|p:nat; u:redexes|] ==>  \
\     subst_rec(u,App(b,f,a),p) = App(b,subst_rec(u,f,p),subst_rec(u,a,p))";
by (asm_simp_tac (simpset() addsimps [subst_rec_def]) 1);
qed "subst_App";

(*But not lift_rec_Var, subst_Var: too many case splits*)
Addsimps [subst_Fun, subst_App];


Goal "u:redexes ==> ALL k:nat. lift_rec(u,k):redexes";
by (etac redexes.induct 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [lift_rec_Var,
				       lift_rec_Fun, lift_rec_App])));
qed_spec_mp "lift_rec_type";

Goal "v:redexes ==>  ALL n:nat. ALL u:redexes. subst_rec(u,v,n):redexes";
by (etac redexes.induct 1);
by (ALLGOALS(asm_simp_tac 
    (simpset() addsimps [subst_Var, lift_rec_type])));
qed_spec_mp "subst_type";


Addsimps [subst_eq, subst_gt, subst_lt, subst_type,
	  lift_rec_le, lift_rec_gt, lift_rec_Fun, lift_rec_App,
	  lift_rec_type];


(* ------------------------------------------------------------------------- *)
(*    lift and  substitution proofs                                          *)
(* ------------------------------------------------------------------------- *)

Goal "u:redexes ==> ALL n:nat. ALL i:nat. i le n -->   \
\       (lift_rec(lift_rec(u,i),succ(n)) = lift_rec(lift_rec(u,n),i))";
by (etac redexes.induct 1);
by (ALLGOALS Asm_simp_tac);
by Safe_tac;
by (case_tac "n < xa" 1);
by ((ftac lt_trans2 1) THEN (assume_tac 1));
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [lift_rec_Var, leI])));
qed "lift_lift_rec";

Goal "[|u:redexes; n:nat|] ==>  \
\      lift_rec(lift(u),succ(n)) = lift(lift_rec(u,n))";
by (asm_simp_tac (simpset() addsimps [lift_lift_rec]) 1);
qed "lift_lift";

Goal "v:redexes ==>  \
\      ALL n:nat. ALL m:nat. ALL u:redexes. n le m-->\
\         lift_rec(subst_rec(u,v,n),m) = \
\              subst_rec(lift_rec(u,m),lift_rec(v,succ(m)),n)";
by ((etac redexes.induct 1)
    THEN (ALLGOALS(asm_simp_tac (simpset() addsimps [lift_lift]))));
by Safe_tac;
by (excluded_middle_tac "n < x" 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("j","n")] leE 1);
by (asm_simp_tac (simpset() setloop (split_inside_tac [split_if])
			 addsimps [lift_rec_Var,subst_Var,
				   leI,gt_pred,succ_pred]) 1);
by (hyp_subst_tac 1);
by (Asm_simp_tac 1);
by (forw_inst_tac [("j","x")] lt_trans2 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [leI]) 1);
qed "lift_rec_subst_rec";

Goal "[|v:redexes; u:redexes; n:nat|] ==>  \
\        lift_rec(u/v,n) = lift_rec(u,n)/lift_rec(v,succ(n))";
by (asm_simp_tac (simpset() addsimps [lift_rec_subst_rec]) 1);
qed "lift_subst";


Goal "v:redexes ==>  \
\      ALL n:nat. ALL m:nat. ALL u:redexes. m le n-->\
\         lift_rec(subst_rec(u,v,n),m) = \
\              subst_rec(lift_rec(u,m),lift_rec(v,m),succ(n))";
by (etac redexes.induct 1
    THEN ALLGOALS(asm_simp_tac (simpset() addsimps [lift_lift])));
by Safe_tac;
by (excluded_middle_tac "n < x" 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("i","x")] leE 1);
by (ftac lt_trans1 1 THEN assume_tac 1);
by (ALLGOALS(asm_simp_tac 
             (simpset() addsimps [succ_pred,leI,gt_pred])));
by (asm_full_simp_tac (simpset() addsimps [leI]) 1);
by (case_tac "n < xa" 1);
by (Asm_full_simp_tac 2);
by (asm_simp_tac (simpset() addsimps [leI]) 1);
qed "lift_rec_subst_rec_lt";


Goal "u:redexes ==>  \
\       ALL n:nat. ALL v:redexes. subst_rec(v,lift_rec(u,n),n) =  u";
by (etac redexes.induct 1);
by Auto_tac;
by (case_tac "n < x" 1);
by Auto_tac;
qed "subst_rec_lift_rec";

Goal "v:redexes ==>  \
\       ALL m:nat. ALL n:nat. ALL u:redexes. ALL w:redexes. m le  n --> \
\    subst_rec(subst_rec(w,u,n),subst_rec(lift_rec(w,m),v,succ(n)),m)=\
\    subst_rec(w,subst_rec(u,v,m),n)";
by (etac redexes.induct 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps 
			   [lift_lift RS sym,lift_rec_subst_rec_lt])));
by Safe_tac;
by (excluded_middle_tac "n  le succ(xa)" 1);
by (Asm_full_simp_tac 1);
by (forward_tac [nat_into_Ord RS le_refl RS lt_trans] 1 THEN assume_tac 1);
by (etac leE 1);
by (asm_simp_tac (simpset() addsimps [succ_pred,lt_pred]) 2);
by (forward_tac [succ_leI RS lt_trans] 1 THEN assume_tac 1);
by (forw_inst_tac [("i","x")] 
    (nat_into_Ord RS le_refl RS lt_trans) 1 THEN assume_tac 1);
by (asm_simp_tac (simpset() addsimps [succ_pred,lt_pred]) 1);
by (eres_inst_tac [("i","n")] leE 1);
by (asm_simp_tac (simpset() addsimps [succ_pred,subst_rec_lift_rec,leI]) 2);
by (excluded_middle_tac "n < x" 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("j","n")] leE 1);
by (asm_simp_tac (simpset() addsimps [gt_pred]) 1);
by (asm_simp_tac (simpset() addsimps [subst_rec_lift_rec]) 1);
by (ftac lt_trans2 1 THEN assume_tac 1);
by (asm_simp_tac (simpset() addsimps [gt_pred]) 1);
qed "subst_rec_subst_rec";


Goal "[|v:redexes; u:redexes; w:redexes; n:nat|] ==>  \
\       subst_rec(w,u,n)/subst_rec(lift(w),v,succ(n)) = subst_rec(w,u/v,n)";
by (asm_simp_tac (simpset() addsimps [subst_rec_subst_rec]) 1);
qed "substitution";

(* ------------------------------------------------------------------------- *)
(*          Preservation lemmas                                              *)
(*          Substitution preserves comp and regular                          *)
(* ------------------------------------------------------------------------- *)


Goal "[|n:nat; u ~ v|] ==> ALL m:nat. lift_rec(u,m) ~ lift_rec(v,m)";
by (etac Scomp.induct 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [comp_refl])));
qed "lift_rec_preserve_comp";

Goal "u2 ~ v2 ==> ALL m:nat. ALL u1:redexes. ALL v1:redexes.\
\            u1 ~ v1--> subst_rec(u1,u2,m) ~ subst_rec(v1,v2,m)";
by (etac Scomp.induct 1);
by (ALLGOALS
    (asm_simp_tac
     (simpset() addsimps [subst_Var, lift_rec_preserve_comp, comp_refl])));
qed "subst_rec_preserve_comp";

Goal "regular(u) ==> ALL m:nat. regular(lift_rec(u,m))";
by (etac Sreg.induct 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [lift_rec_Var])));
qed "lift_rec_preserve_reg";

Goal "regular(v) ==>  \
\       ALL m:nat. ALL u:redexes. regular(u)-->regular(subst_rec(u,v,m))";
by (etac Sreg.induct 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [subst_Var,
						    lift_rec_preserve_reg])));
qed "subst_rec_preserve_reg";
