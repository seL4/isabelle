(*  Title:      Substitution.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Substitution;

(* ------------------------------------------------------------------------- *)
(*   Arithmetic extensions                                                   *)
(* ------------------------------------------------------------------------- *)

goal Arith.thy
    "!!m.[| p < n; n:nat|]==> n~=p";
by (Fast_tac 1);
val gt_not_eq = result();

val succ_pred = prove_goal Arith.thy 
    "!!i.[|j:nat; i:nat|]==> i < j --> succ(j #- 1) = j"
 (fn prems =>[(etac nat_induct 1),
              (Fast_tac 1),
              (Asm_simp_tac 1)]);

goal Arith.thy 
    "!!i.[|succ(x)<n; n:nat; x:nat|]==> x < n#-1 ";
by (rtac succ_leE 1);
by (forward_tac [nat_into_Ord RS le_refl RS lt_trans] 1 THEN assume_tac 1);
by (asm_simp_tac (!simpset addsimps [succ_pred]) 1);
val lt_pred = result();

goal Arith.thy 
    "!!i.[|n < succ(x); p<n; p:nat; n:nat; x:nat|]==> n#-1 < x ";
by (rtac succ_leE 1);
by (asm_simp_tac (!simpset addsimps [succ_pred]) 1);
val gt_pred = result();


Addsimps [nat_into_Ord, not_lt_iff_le, if_P, if_not_P];


(* ------------------------------------------------------------------------- *)
(*     lift_rec equality rules                                               *)
(* ------------------------------------------------------------------------- *)
goalw Substitution.thy [lift_rec_def] 
    "!!n.[|n:nat; i:nat|]==> lift_rec(Var(i),n) =if(i<n,Var(i),Var(succ(i)))";
by (Asm_full_simp_tac 1);
val lift_rec_Var = result();

goalw Substitution.thy [lift_rec_def] 
    "!!n.[|n:nat; i:nat; k:nat; k le i|]==> lift_rec(Var(i),k) = Var(succ(i))";
by (Asm_full_simp_tac 1);
val lift_rec_le = result();

goalw Substitution.thy [lift_rec_def] 
    "!!n.[|i:nat; k:nat; i<k |]==> lift_rec(Var(i),k) = Var(i)";
by (Asm_full_simp_tac 1);
val lift_rec_gt = result();

goalw Substitution.thy [lift_rec_def] 
    "!!n.[|n:nat; k:nat|]==>   \
\        lift_rec(Fun(t),k) = Fun(lift_rec(t,succ(k)))";
by (Asm_full_simp_tac 1);
val lift_rec_Fun = result();

goalw Substitution.thy [lift_rec_def] 
    "!!n.[|n:nat; k:nat|]==>   \
\        lift_rec(App(b,f,a),k) = App(b,lift_rec(f,k),lift_rec(a,k))";
by (Asm_full_simp_tac 1);
val lift_rec_App = result();

(* ------------------------------------------------------------------------- *)
(*    substitution quality rules                                             *)
(* ------------------------------------------------------------------------- *)

goalw Substitution.thy [subst_rec_def] 
    "!!n.[|i:nat; k:nat; u:redexes|]==>  \
\        subst_rec(u,Var(i),k) = if(k<i,Var(i#-1),if(k=i,u,Var(i)))";
by (asm_full_simp_tac (!simpset addsimps [gt_not_eq,leI]) 1);
val subst_Var = result();

goalw Substitution.thy [subst_rec_def] 
    "!!n.[|n:nat; u:redexes|]==> subst_rec(u,Var(n),n) = u";
by (asm_full_simp_tac (!simpset) 1);
val subst_eq = result();

goalw Substitution.thy [subst_rec_def] 
    "!!n.[|n:nat; u:redexes; p:nat; p<n|]==>  \
\        subst_rec(u,Var(n),p) = Var(n#-1)";
by (asm_full_simp_tac (!simpset) 1);
val subst_gt = result();

goalw Substitution.thy [subst_rec_def] 
    "!!n.[|n:nat; u:redexes; p:nat; n<p|]==>  \
\        subst_rec(u,Var(n),p) = Var(n)";
by (asm_full_simp_tac (!simpset addsimps [gt_not_eq,leI]) 1);
val subst_lt = result();

goalw Substitution.thy [subst_rec_def] 
    "!!n.[|p:nat; u:redexes|]==>  \
\        subst_rec(u,Fun(t),p) = Fun(subst_rec(lift(u),t,succ(p))) ";
by (asm_full_simp_tac (!simpset) 1);
val subst_Fun = result();

goalw Substitution.thy [subst_rec_def] 
    "!!n.[|p:nat; u:redexes|]==>  \
\        subst_rec(u,App(b,f,a),p) = App(b,subst_rec(u,f,p),subst_rec(u,a,p))";
by (asm_full_simp_tac (!simpset) 1);
val subst_App = result();

fun addsplit ss = (ss setloop (split_inside_tac [expand_if]) 
                addsimps [lift_rec_Var,subst_Var]);


goal Substitution.thy  
    "!!n.u:redexes ==> ALL k:nat.lift_rec(u,k):redexes";
by (eresolve_tac [redexes.induct] 1);
by (ALLGOALS(asm_full_simp_tac 
    ((addsplit (!simpset)) addsimps [lift_rec_Fun,lift_rec_App])));
val lift_rec_type_a = result();
val lift_rec_type = lift_rec_type_a RS bspec;

goalw Substitution.thy [] 
    "!!n.v:redexes ==>  ALL n:nat.ALL u:redexes.subst_rec(u,v,n):redexes";
by (eresolve_tac [redexes.induct] 1);
by (ALLGOALS(asm_full_simp_tac 
    ((addsplit (!simpset)) addsimps [subst_Fun,subst_App,
                       lift_rec_type])));
val subst_type_a = result();
val subst_type = subst_type_a RS bspec RS bspec;


Addsimps [subst_eq, subst_gt, subst_lt, subst_Fun, subst_App, subst_type,
	  lift_rec_le, lift_rec_gt, lift_rec_Fun, lift_rec_App,
	  lift_rec_type];


(* ------------------------------------------------------------------------- *)
(*    lift and  substitution proofs                                          *)
(* ------------------------------------------------------------------------- *)

goalw Substitution.thy [] 
    "!!n.u:redexes ==> ALL n:nat.ALL i:nat.i le n -->   \
\       (lift_rec(lift_rec(u,i),succ(n)) = lift_rec(lift_rec(u,n),i))";
by ((eresolve_tac [redexes.induct] 1)
    THEN (ALLGOALS Asm_simp_tac));
by (step_tac (!claset) 1);
by (excluded_middle_tac "na < xa" 1);
by ((forward_tac [lt_trans2] 2) THEN (assume_tac 2));
by (ALLGOALS(asm_full_simp_tac 
    ((addsplit (!simpset)) addsimps [leI])));
val lift_lift_rec = result();


goalw Substitution.thy [] 
    "!!n.[|u:redexes; n:nat|]==>  \
\      lift_rec(lift(u),succ(n)) = lift(lift_rec(u,n))";
by (asm_simp_tac (!simpset addsimps [lift_lift_rec]) 1);
val lift_lift = result();

goal Substitution.thy 
    "!!n.v:redexes ==>  \
\      ALL n:nat.ALL m:nat.ALL u:redexes.n le m-->\
\         lift_rec(subst_rec(u,v,n),m) = \
\              subst_rec(lift_rec(u,m),lift_rec(v,succ(m)),n)";
by ((eresolve_tac [redexes.induct] 1)
    THEN (ALLGOALS(asm_simp_tac (!simpset addsimps [lift_lift]))));
by (step_tac (!claset) 1);
by (excluded_middle_tac "na < x" 1);
by (asm_full_simp_tac (!simpset) 1);
by (eres_inst_tac [("j","na")] leE 1);
by (asm_full_simp_tac ((addsplit (!simpset)) 
                        addsimps [leI,gt_pred,succ_pred]) 1);
by (hyp_subst_tac 1);
by (asm_full_simp_tac (!simpset) 1);
by (forw_inst_tac [("j","x")] lt_trans2 1);
by (assume_tac 1);
by (asm_full_simp_tac (!simpset addsimps [leI]) 1);
val lift_rec_subst_rec = result();

goalw Substitution.thy [] 
    "!!n.[|v:redexes; u:redexes; n:nat|]==>  \
\        lift_rec(u/v,n) = lift_rec(u,n)/lift_rec(v,succ(n))";
by (asm_full_simp_tac (!simpset addsimps [lift_rec_subst_rec]) 1);
val lift_subst = result();


goalw Substitution.thy [] 
    "!!n.v:redexes ==>  \
\      ALL n:nat.ALL m:nat.ALL u:redexes.m le n-->\
\         lift_rec(subst_rec(u,v,n),m) = \
\              subst_rec(lift_rec(u,m),lift_rec(v,m),succ(n))";
by ((eresolve_tac [redexes.induct] 1)
    THEN (ALLGOALS(asm_simp_tac (!simpset addsimps [lift_lift]))));
by (step_tac (!claset) 1);
by (excluded_middle_tac "na < x" 1);
by (asm_full_simp_tac (!simpset) 1);
by (eres_inst_tac [("i","x")] leE 1);
by (forward_tac  [lt_trans1] 1 THEN assume_tac 1);
by (ALLGOALS(asm_full_simp_tac 
             (!simpset addsimps [succ_pred,leI,gt_pred])));
by (hyp_subst_tac 1);
by (asm_full_simp_tac (!simpset addsimps [leI]) 1);
by (excluded_middle_tac "na < xa" 1);
by (asm_full_simp_tac (!simpset) 1);
by (asm_full_simp_tac (!simpset addsimps [leI]) 1);
val lift_rec_subst_rec_lt = result();


goalw Substitution.thy [] 
    "!!n.u:redexes ==>  \
\       ALL n:nat.ALL v:redexes.subst_rec(v,lift_rec(u,n),n) =  u";
by ((eresolve_tac [redexes.induct] 1)
    THEN (ALLGOALS Asm_simp_tac));
by (step_tac (!claset) 1);
by (excluded_middle_tac "na < x" 1);
(* x <= na  *)
by (asm_full_simp_tac (!simpset) 1);
by (asm_full_simp_tac (!simpset) 1);
val subst_rec_lift_rec = result();

goal Substitution.thy  
    "!!n.v:redexes ==>  \
\       ALL m:nat.ALL n:nat.ALL u:redexes.ALL w:redexes.m le  n --> \
\    subst_rec(subst_rec(w,u,n),subst_rec(lift_rec(w,m),v,succ(n)),m)=\
\    subst_rec(w,subst_rec(u,v,m),n)";
by ((eresolve_tac [redexes.induct] 1) THEN 
     (ALLGOALS(asm_simp_tac (!simpset addsimps 
                             [lift_lift RS sym,lift_rec_subst_rec_lt]))));
by (step_tac (!claset) 1);
by (excluded_middle_tac "na  le succ(xa)" 1);
by (asm_full_simp_tac (!simpset) 1);
by (forward_tac [nat_into_Ord RS le_refl RS lt_trans] 1 THEN assume_tac 1);
by (etac leE 1);
by (asm_simp_tac (!simpset addsimps [succ_pred,lt_pred]) 2);
by (forward_tac [succ_leI RS lt_trans] 1 THEN assume_tac 1);
by (forw_inst_tac [("i","x")] 
    (nat_into_Ord RS le_refl RS lt_trans) 1 THEN assume_tac 1);
by (asm_simp_tac (!simpset addsimps [succ_pred,lt_pred]) 1);
by (eres_inst_tac [("i","na")] leE 1);
by (asm_full_simp_tac 
    (!simpset addsimps [succ_pred,subst_rec_lift_rec,leI]) 2);
by (excluded_middle_tac "na < x" 1);
by (asm_full_simp_tac (!simpset) 1);
by (eres_inst_tac [("j","na")] leE 1);
by (asm_simp_tac (!simpset addsimps [gt_pred]) 1);
by (asm_simp_tac (!simpset addsimps [subst_rec_lift_rec]) 1);
by (forward_tac [lt_trans2] 1 THEN assume_tac 1);
by (asm_simp_tac (!simpset addsimps [gt_pred]) 1);
val subst_rec_subst_rec = result();


goalw Substitution.thy [] 
    "!!n.[|v:redexes; u:redexes; w:redexes; n:nat|]==>  \
\       subst_rec(w,u,n)/subst_rec(lift(w),v,succ(n)) = subst_rec(w,u/v,n)";
by (asm_simp_tac (!simpset addsimps [subst_rec_subst_rec]) 1);
val substitution = result();

(* ------------------------------------------------------------------------- *)
(*          Preservation lemmas                                              *)
(*          Substitution preserves comp and regular                          *)
(* ------------------------------------------------------------------------- *)


goal Substitution.thy
    "!!n.[|n:nat; u ~ v|]==> ALL m:nat.lift_rec(u,m) ~ lift_rec(v,m)";
by (etac Scomp.induct 1);
by (ALLGOALS(asm_simp_tac (!simpset addsimps [comp_refl])));
val lift_rec_preserve_comp = result();

goal Substitution.thy
    "!!n.u2 ~ v2 ==> ALL m:nat.ALL u1:redexes.ALL v1:redexes.\
\            u1 ~ v1--> subst_rec(u1,u2,m) ~ subst_rec(v1,v2,m)";
by (etac Scomp.induct 1);
by (ALLGOALS(asm_full_simp_tac ((addsplit (!simpset)) addsimps 
            ([lift_rec_preserve_comp,comp_refl]))));
val subst_rec_preserve_comp = result();

goal Substitution.thy
    "!!n.regular(u) ==> ALL m:nat.regular(lift_rec(u,m))";
by (eresolve_tac [Sreg.induct] 1);
by (ALLGOALS(asm_full_simp_tac (addsplit (!simpset))));
val lift_rec_preserve_reg = result();

goal Substitution.thy
    "!!n.regular(v) ==>  \
\       ALL m:nat.ALL u:redexes.regular(u)-->regular(subst_rec(u,v,m))";
by (eresolve_tac [Sreg.induct] 1);
by (ALLGOALS(asm_full_simp_tac ((addsplit (!simpset)) addsimps 
            [lift_rec_preserve_reg])));
val subst_rec_preserve_reg = result();
