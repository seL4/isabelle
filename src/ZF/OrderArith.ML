(*  Title:      ZF/OrderArith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Towards ordinal arithmetic 
*)

open OrderArith;


(**** Addition of relations -- disjoint sum ****)

(** Rewrite rules.  Can be used to obtain introduction rules **)

goalw OrderArith.thy [radd_def] 
    "<Inl(a), Inr(b)> : radd(A,r,B,s)  <->  a:A & b:B";
by (Blast_tac 1);
qed "radd_Inl_Inr_iff";

goalw OrderArith.thy [radd_def] 
    "<Inl(a'), Inl(a)> : radd(A,r,B,s)  <->  a':A & a:A & <a',a>:r";
by (Blast_tac 1);
qed "radd_Inl_iff";

goalw OrderArith.thy [radd_def] 
    "<Inr(b'), Inr(b)> : radd(A,r,B,s) <->  b':B & b:B & <b',b>:s";
by (Blast_tac 1);
qed "radd_Inr_iff";

goalw OrderArith.thy [radd_def] 
    "<Inr(b), Inl(a)> : radd(A,r,B,s) <->  False";
by (Blast_tac 1);
qed "radd_Inr_Inl_iff";

(** Elimination Rule **)

val major::prems = goalw OrderArith.thy [radd_def]
    "[| <p',p> : radd(A,r,B,s);                 \
\       !!x y. [| p'=Inl(x); x:A; p=Inr(y); y:B |] ==> Q;       \
\       !!x' x. [| p'=Inl(x'); p=Inl(x); <x',x>: r; x':A; x:A |] ==> Q; \
\       !!y' y. [| p'=Inr(y'); p=Inr(y); <y',y>: s; y':B; y:B |] ==> Q  \
\    |] ==> Q";
by (cut_facts_tac [major] 1);
(*Split into the three cases*)
by (REPEAT_FIRST  (*can't use safe_tac: don't want hyp_subst_tac*)
    (eresolve_tac [CollectE, Pair_inject, conjE, exE, SigmaE, disjE]));
(*Apply each premise to correct subgoal; can't just use fast_tac
  because hyp_subst_tac would delete equalities too quickly*)
by (EVERY (map (fn prem => 
                EVERY1 [rtac prem, assume_tac, REPEAT o Fast_tac])
           prems));
qed "raddE";

(** Type checking **)

goalw OrderArith.thy [radd_def] "radd(A,r,B,s) <= (A+B) * (A+B)";
by (rtac Collect_subset 1);
qed "radd_type";

bind_thm ("field_radd", radd_type RS field_rel_subset);

(** Linearity **)

Addsimps [radd_Inl_iff, radd_Inr_iff, 
          radd_Inl_Inr_iff, radd_Inr_Inl_iff];

goalw OrderArith.thy [linear_def]
    "!!r s. [| linear(A,r);  linear(B,s) |] ==> linear(A+B,radd(A,r,B,s))";
by (REPEAT_FIRST (ares_tac [ballI] ORELSE' etac sumE));
by (ALLGOALS Asm_simp_tac);
qed "linear_radd";


(** Well-foundedness **)

goal OrderArith.thy
    "!!r s. [| wf[A](r);  wf[B](s) |] ==> wf[A+B](radd(A,r,B,s))";
by (rtac wf_onI2 1);
by (subgoal_tac "ALL x:A. Inl(x): Ba" 1);
(*Proving the lemma, which is needed twice!*)
by (thin_tac "y : A + B" 2);
by (rtac ballI 2);
by (eres_inst_tac [("r","r"),("a","x")] wf_on_induct 2 THEN assume_tac 2);
by (best_tac (!claset addSEs [raddE, bspec RS mp]) 2);
(*Returning to main part of proof*)
by (REPEAT_FIRST (eresolve_tac [sumE, ssubst]));
by (Blast_tac 1);
by (eres_inst_tac [("r","s"),("a","ya")] wf_on_induct 1 THEN assume_tac 1);
by (best_tac (!claset addSEs [raddE, bspec RS mp]) 1);
qed "wf_on_radd";

goal OrderArith.thy
     "!!r s. [| wf(r);  wf(s) |] ==> wf(radd(field(r),r,field(s),s))";
by (asm_full_simp_tac (!simpset addsimps [wf_iff_wf_on_field]) 1);
by (rtac (field_radd RSN (2, wf_on_subset_A)) 1);
by (REPEAT (ares_tac [wf_on_radd] 1));
qed "wf_radd";

goal OrderArith.thy 
    "!!r s. [| well_ord(A,r);  well_ord(B,s) |] ==> \
\           well_ord(A+B, radd(A,r,B,s))";
by (rtac well_ordI 1);
by (asm_full_simp_tac (!simpset addsimps [well_ord_def, wf_on_radd]) 1);
by (asm_full_simp_tac 
    (!simpset addsimps [well_ord_def, tot_ord_def, linear_radd]) 1);
qed "well_ord_radd";

(** An ord_iso congruence law **)

goal OrderArith.thy
 "!!f g. [| f: bij(A,C);  g: bij(B,D) |] ==> \
\        (lam z:A+B. case(%x. Inl(f`x), %y. Inr(g`y), z)) : bij(A+B, C+D)";
by (res_inst_tac 
        [("d", "case(%x. Inl(converse(f)`x), %y. Inr(converse(g)`y))")] 
    lam_bijective 1);
by (safe_tac (!claset addSEs [sumE]));
by (ALLGOALS (asm_simp_tac bij_inverse_ss));
qed "sum_bij";

goalw OrderArith.thy [ord_iso_def]
    "!!r s. [| f: ord_iso(A,r,A',r');  g: ord_iso(B,s,B',s') |] ==>     \
\           (lam z:A+B. case(%x. Inl(f`x), %y. Inr(g`y), z))            \
\           : ord_iso(A+B, radd(A,r,B,s), A'+B', radd(A',r',B',s'))";
by (safe_tac (!claset addSIs [sum_bij]));
(*Do the beta-reductions now*)
by (ALLGOALS (Asm_full_simp_tac));
by (safe_tac (!claset));
(*8 subgoals!*)
by (ALLGOALS
    (asm_full_simp_tac 
     (!simpset addcongs [conj_cong] addsimps [bij_is_fun RS apply_type])));
qed "sum_ord_iso_cong";

(*Could we prove an ord_iso result?  Perhaps 
     ord_iso(A+B, radd(A,r,B,s), A Un B, r Un s) *)
goal OrderArith.thy
    "!!A B. A Int B = 0 ==>     \
\           (lam z:A+B. case(%x. x, %y. y, z)) : bij(A+B, A Un B)";
by (res_inst_tac [("d", "%z. if(z:A, Inl(z), Inr(z))")] 
    lam_bijective 1);
by (blast_tac (!claset addSIs [if_type]) 2);
by (DEPTH_SOLVE_1 (eresolve_tac [case_type, UnI1, UnI2] 1));
by (safe_tac (!claset));
by (ALLGOALS (asm_simp_tac (!simpset setloop split_tac [expand_if])));
by (blast_tac (!claset addEs [equalityE]) 1);
qed "sum_disjoint_bij";

(** Associativity **)

goal OrderArith.thy
 "(lam z:(A+B)+C. case(case(Inl, %y. Inr(Inl(y))), %y. Inr(Inr(y)), z)) \
\ : bij((A+B)+C, A+(B+C))";
by (res_inst_tac [("d", "case(%x. Inl(Inl(x)), case(%x. Inl(Inr(x)), Inr))")] 
    lam_bijective 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop etac sumE)));
qed "sum_assoc_bij";

goal OrderArith.thy
 "(lam z:(A+B)+C. case(case(Inl, %y. Inr(Inl(y))), %y. Inr(Inr(y)), z)) \
\ : ord_iso((A+B)+C, radd(A+B, radd(A,r,B,s), C, t),    \
\           A+(B+C), radd(A, r, B+C, radd(B,s,C,t)))";
by (resolve_tac [sum_assoc_bij RS ord_isoI] 1);
by (REPEAT_FIRST (etac sumE));
by (ALLGOALS Asm_simp_tac);
qed "sum_assoc_ord_iso";


(**** Multiplication of relations -- lexicographic product ****)

(** Rewrite rule.  Can be used to obtain introduction rules **)

goalw OrderArith.thy [rmult_def] 
    "!!r s. <<a',b'>, <a,b>> : rmult(A,r,B,s) <->       \
\           (<a',a>: r  & a':A & a:A & b': B & b: B) |  \
\           (<b',b>: s  & a'=a & a:A & b': B & b: B)";
by (Blast_tac 1);
qed "rmult_iff";

Addsimps [rmult_iff];

val major::prems = goal OrderArith.thy
    "[| <<a',b'>, <a,b>> : rmult(A,r,B,s);              \
\       [| <a',a>: r;  a':A;  a:A;  b':B;  b:B |] ==> Q;        \
\       [| <b',b>: s;  a:A;  a'=a;  b':B;  b:B |] ==> Q \
\    |] ==> Q";
by (rtac (major RS (rmult_iff RS iffD1) RS disjE) 1);
by (DEPTH_SOLVE (eresolve_tac ([asm_rl, conjE] @ prems) 1));
qed "rmultE";

(** Type checking **)

goalw OrderArith.thy [rmult_def] "rmult(A,r,B,s) <= (A*B) * (A*B)";
by (rtac Collect_subset 1);
qed "rmult_type";

bind_thm ("field_rmult", (rmult_type RS field_rel_subset));

(** Linearity **)

val [lina,linb] = goal OrderArith.thy
    "[| linear(A,r);  linear(B,s) |] ==> linear(A*B,rmult(A,r,B,s))";
by (rewtac linear_def);    (*Note! the premises are NOT rewritten*)
by (REPEAT_FIRST (ares_tac [ballI] ORELSE' etac SigmaE));
by (Asm_simp_tac 1);
by (res_inst_tac [("x","xa"), ("y","xb")] (lina RS linearE) 1);
by (res_inst_tac [("x","ya"), ("y","yb")] (linb RS linearE) 4);
by (REPEAT_SOME (Blast_tac));
qed "linear_rmult";


(** Well-foundedness **)

goal OrderArith.thy
    "!!r s. [| wf[A](r);  wf[B](s) |] ==> wf[A*B](rmult(A,r,B,s))";
by (rtac wf_onI2 1);
by (etac SigmaE 1);
by (etac ssubst 1);
by (subgoal_tac "ALL b:B. <x,b>: Ba" 1);
by (Blast_tac 1);
by (eres_inst_tac [("a","x")] wf_on_induct 1 THEN assume_tac 1);
by (rtac ballI 1);
by (eres_inst_tac [("a","b")] wf_on_induct 1 THEN assume_tac 1);
by (best_tac (!claset addSEs [rmultE, bspec RS mp]) 1);
qed "wf_on_rmult";


goal OrderArith.thy
    "!!r s. [| wf(r);  wf(s) |] ==> wf(rmult(field(r),r,field(s),s))";
by (asm_full_simp_tac (!simpset addsimps [wf_iff_wf_on_field]) 1);
by (rtac (field_rmult RSN (2, wf_on_subset_A)) 1);
by (REPEAT (ares_tac [wf_on_rmult] 1));
qed "wf_rmult";

goal OrderArith.thy 
    "!!r s. [| well_ord(A,r);  well_ord(B,s) |] ==> \
\           well_ord(A*B, rmult(A,r,B,s))";
by (rtac well_ordI 1);
by (asm_full_simp_tac (!simpset addsimps [well_ord_def, wf_on_rmult]) 1);
by (asm_full_simp_tac 
    (!simpset addsimps [well_ord_def, tot_ord_def, linear_rmult]) 1);
qed "well_ord_rmult";


(** An ord_iso congruence law **)

goal OrderArith.thy
 "!!f g. [| f: bij(A,C);  g: bij(B,D) |] ==> \
\        (lam <x,y>:A*B. <f`x, g`y>) : bij(A*B, C*D)";
by (res_inst_tac [("d", "%<x,y>. <converse(f)`x, converse(g)`y>")] 
    lam_bijective 1);
by (safe_tac (!claset));
by (ALLGOALS (asm_simp_tac bij_inverse_ss));
qed "prod_bij";

goalw OrderArith.thy [ord_iso_def]
    "!!r s. [| f: ord_iso(A,r,A',r');  g: ord_iso(B,s,B',s') |] ==>     \
\           (lam <x,y>:A*B. <f`x, g`y>)                                 \
\           : ord_iso(A*B, rmult(A,r,B,s), A'*B', rmult(A',r',B',s'))";
by (safe_tac (!claset addSIs [prod_bij]));
by (ALLGOALS
    (asm_full_simp_tac (!simpset addsimps [bij_is_fun RS apply_type])));
by (Blast_tac 1);
by (blast_tac (!claset addIs [bij_is_inj RS inj_apply_equality]) 1);
qed "prod_ord_iso_cong";

goal OrderArith.thy "(lam z:A. <x,z>) : bij(A, {x}*A)";
by (res_inst_tac [("d", "snd")] lam_bijective 1);
by (safe_tac (!claset));
by (ALLGOALS Asm_simp_tac);
qed "singleton_prod_bij";

(*Used??*)
goal OrderArith.thy
 "!!x xr. well_ord({x},xr) ==>  \
\         (lam z:A. <x,z>) : ord_iso(A, r, {x}*A, rmult({x}, xr, A, r))";
by (resolve_tac [singleton_prod_bij RS ord_isoI] 1);
by (Asm_simp_tac 1);
by (blast_tac (!claset addEs [well_ord_is_wf RS wf_on_not_refl RS notE]) 1);
qed "singleton_prod_ord_iso";

(*Here we build a complicated function term, then simplify it using
  case_cong, id_conv, comp_lam, case_case.*)
goal OrderArith.thy
 "!!a. a~:C ==> \
\      (lam x:C*B + D. case(%x. x, %y.<a,y>, x)) \
\      : bij(C*B + D, C*B Un {a}*D)";
by (rtac subst_elem 1);
by (resolve_tac [id_bij RS sum_bij RS comp_bij] 1);
by (rtac singleton_prod_bij 1);
by (rtac sum_disjoint_bij 1);
by (Blast_tac 1);
by (asm_simp_tac (!simpset addcongs [case_cong] addsimps [id_conv]) 1);
by (resolve_tac [comp_lam RS trans RS sym] 1);
by (fast_tac (!claset addSEs [case_type]) 1);
by (asm_simp_tac (!simpset addsimps [case_case]) 1);
qed "prod_sum_singleton_bij";

goal OrderArith.thy
 "!!A. [| a:A;  well_ord(A,r) |] ==> \
\   (lam x:pred(A,a,r)*B + pred(B,b,s). case(%x. x, %y.<a,y>, x)) \
\   : ord_iso(pred(A,a,r)*B + pred(B,b,s),              \
\                 radd(A*B, rmult(A,r,B,s), B, s),      \
\             pred(A,a,r)*B Un {a}*pred(B,b,s), rmult(A,r,B,s))";
by (resolve_tac [prod_sum_singleton_bij RS ord_isoI] 1);
by (asm_simp_tac
    (!simpset addsimps [pred_iff, well_ord_is_wf RS wf_on_not_refl]) 1);
by (Asm_simp_tac 1);
by (REPEAT_FIRST (eresolve_tac [SigmaE, sumE, predE]));
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (blast_tac (!claset addEs [well_ord_is_wf RS wf_on_asym])));
qed "prod_sum_singleton_ord_iso";

(** Distributive law **)

goal OrderArith.thy
 "(lam <x,z>:(A+B)*C. case(%y. Inl(<y,z>), %y. Inr(<y,z>), x)) \
\ : bij((A+B)*C, (A*C)+(B*C))";
by (res_inst_tac
    [("d", "case(%<x,y>.<Inl(x),y>, %<x,y>.<Inr(x),y>)")] lam_bijective 1);
by (safe_tac (!claset addSEs [sumE]));
by (ALLGOALS Asm_simp_tac);
qed "sum_prod_distrib_bij";

goal OrderArith.thy
 "(lam <x,z>:(A+B)*C. case(%y. Inl(<y,z>), %y. Inr(<y,z>), x)) \
\ : ord_iso((A+B)*C, rmult(A+B, radd(A,r,B,s), C, t), \
\           (A*C)+(B*C), radd(A*C, rmult(A,r,C,t), B*C, rmult(B,s,C,t)))";
by (resolve_tac [sum_prod_distrib_bij RS ord_isoI] 1);
by (REPEAT_FIRST (eresolve_tac [SigmaE, sumE]));
by (ALLGOALS Asm_simp_tac);
qed "sum_prod_distrib_ord_iso";

(** Associativity **)

goal OrderArith.thy
 "(lam <<x,y>, z>:(A*B)*C. <x,<y,z>>) : bij((A*B)*C, A*(B*C))";
by (res_inst_tac [("d", "%<x, <y,z>>. <<x,y>, z>")] lam_bijective 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop etac SigmaE)));
qed "prod_assoc_bij";

goal OrderArith.thy
 "(lam <<x,y>, z>:(A*B)*C. <x,<y,z>>)                   \
\ : ord_iso((A*B)*C, rmult(A*B, rmult(A,r,B,s), C, t),  \
\           A*(B*C), rmult(A, r, B*C, rmult(B,s,C,t)))";
by (resolve_tac [prod_assoc_bij RS ord_isoI] 1);
by (REPEAT_FIRST (eresolve_tac [SigmaE, ssubst]));
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "prod_assoc_ord_iso";

(**** Inverse image of a relation ****)

(** Rewrite rule **)

goalw OrderArith.thy [rvimage_def] 
    "<a,b> : rvimage(A,f,r)  <->  <f`a,f`b>: r & a:A & b:A";
by (Blast_tac 1);
qed "rvimage_iff";

(** Type checking **)

goalw OrderArith.thy [rvimage_def] "rvimage(A,f,r) <= A*A";
by (rtac Collect_subset 1);
qed "rvimage_type";

bind_thm ("field_rvimage", (rvimage_type RS field_rel_subset));

goalw OrderArith.thy [rvimage_def] 
    "rvimage(A,f, converse(r)) = converse(rvimage(A,f,r))";
by (Blast_tac 1);
qed "rvimage_converse";


(** Partial Ordering Properties **)

goalw OrderArith.thy [irrefl_def, rvimage_def]
    "!!A B. [| f: inj(A,B);  irrefl(B,r) |] ==> irrefl(A, rvimage(A,f,r))";
by (blast_tac (!claset addIs [inj_is_fun RS apply_type]) 1);
qed "irrefl_rvimage";

goalw OrderArith.thy [trans_on_def, rvimage_def] 
    "!!A B. [| f: inj(A,B);  trans[B](r) |] ==> trans[A](rvimage(A,f,r))";
by (blast_tac (!claset addIs [inj_is_fun RS apply_type]) 1);
qed "trans_on_rvimage";

goalw OrderArith.thy [part_ord_def]
    "!!A B. [| f: inj(A,B);  part_ord(B,r) |] ==> part_ord(A, rvimage(A,f,r))";
by (blast_tac (!claset addSIs [irrefl_rvimage, trans_on_rvimage]) 1);
qed "part_ord_rvimage";

(** Linearity **)

val [finj,lin] = goalw OrderArith.thy [inj_def]
    "[| f: inj(A,B);  linear(B,r) |] ==> linear(A,rvimage(A,f,r))";
by (rewtac linear_def);    (*Note! the premises are NOT rewritten*)
by (REPEAT_FIRST (ares_tac [ballI]));
by (asm_simp_tac (!simpset addsimps [rvimage_iff]) 1);
by (cut_facts_tac [finj] 1);
by (res_inst_tac [("x","f`x"), ("y","f`y")] (lin RS linearE) 1);
by (REPEAT_SOME (blast_tac (!claset addIs [apply_funtype])));
qed "linear_rvimage";

goalw OrderArith.thy [tot_ord_def] 
    "!!A B. [| f: inj(A,B);  tot_ord(B,r) |] ==> tot_ord(A, rvimage(A,f,r))";
by (blast_tac (!claset addSIs [part_ord_rvimage, linear_rvimage]) 1);
qed "tot_ord_rvimage";


(** Well-foundedness **)

goal OrderArith.thy
    "!!r. [| f: A->B;  wf[B](r) |] ==> wf[A](rvimage(A,f,r))";
by (rtac wf_onI2 1);
by (subgoal_tac "ALL z:A. f`z=f`y --> z: Ba" 1);
by (Blast_tac 1);
by (eres_inst_tac [("a","f`y")] wf_on_induct 1);
by (blast_tac (!claset addSIs [apply_funtype]) 1);
by (blast_tac (!claset addSIs [apply_funtype] 
                       addSDs [rvimage_iff RS iffD1]) 1);
qed "wf_on_rvimage";

(*Note that we need only wf[A](...) and linear(A,...) to get the result!*)
goal OrderArith.thy 
    "!!r. [| f: inj(A,B);  well_ord(B,r) |] ==> well_ord(A, rvimage(A,f,r))";
by (rtac well_ordI 1);
by (rewrite_goals_tac [well_ord_def, tot_ord_def]);
by (blast_tac (!claset addSIs [wf_on_rvimage, inj_is_fun]) 1);
by (blast_tac (!claset addSIs [linear_rvimage]) 1);
qed "well_ord_rvimage";

goalw OrderArith.thy [ord_iso_def]
    "!!A B. f: bij(A,B) ==> f: ord_iso(A, rvimage(A,f,s), B, s)";
by (asm_full_simp_tac (!simpset addsimps [rvimage_iff]) 1);
qed "ord_iso_rvimage";

goalw OrderArith.thy [ord_iso_def, rvimage_def]
    "!!A B. f: ord_iso(A,r, B,s) ==> rvimage(A,f,s) = r Int A*A";
by (Blast_tac 1);
qed "ord_iso_rvimage_eq";
