(*  Title:      HOL/Lambda.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Substitution-lemmas.  Most of the proofs, esp. those about natural numbers,
are ported from Ole Rasmussen's ZF development.  In ZF, m<=n is syntactic
sugar for m<Suc(n). In HOL <= is a separate operator. Hence we have to prove
some compatibility lemmas.

*)

(*** Nat ***)

goal Nat.thy "!!i. [| i < Suc j; j < k |] ==> i < k";
br le_less_trans 1;
ba 2;
by(asm_full_simp_tac (nat_ss addsimps [le_def]) 1);
by(fast_tac (HOL_cs addEs [less_asym,less_anti_refl]) 1);
qed "lt_trans1";

goal Nat.thy "!!i. [| i < j; j < Suc(k) |] ==> i < k";
be less_le_trans 1;
by(asm_full_simp_tac (nat_ss addsimps [le_def]) 1);
by(fast_tac (HOL_cs addEs [less_asym,less_anti_refl]) 1);
qed "lt_trans2";

val major::prems = goal Nat.thy
  "[| i < Suc j; i < j ==> P; i = j ==> P |] ==> P";
br (major RS lessE) 1;
by(ALLGOALS(asm_full_simp_tac nat_ss));
by(resolve_tac prems 1 THEN etac sym 1);
by(fast_tac (HOL_cs addIs prems) 1);
qed "leqE";

goal Arith.thy "!!i. i < j ==> Suc(pred j) = j";
by(fast_tac (HOL_cs addEs [lessE] addss arith_ss) 1);
qed "Suc_pred";

goal Arith.thy "!!i. Suc i < j ==> i < pred j ";
by (resolve_tac [Suc_less_SucD] 1);
by (asm_simp_tac (arith_ss addsimps [Suc_pred]) 1);
qed "lt_pred";

goal Arith.thy "!!i. [| i < Suc j; k < i |] ==> pred i < j ";
by (resolve_tac [Suc_less_SucD] 1);
by (asm_simp_tac (arith_ss addsimps [Suc_pred]) 1);
qed "gt_pred";

(*** Lambda ***)

open Lambda;

val lambda_ss = arith_ss delsimps [less_Suc_eq] addsimps
  db.simps @ beta.intrs @
  [if_not_P, not_less_eq,
   subst_App,subst_Fun,
   lift_Var,lift_App,lift_Fun];

val lambda_cs = HOL_cs addSIs beta.intrs;

(*** Congruence rules for ->> ***)

goal Lambda.thy "!!s. s ->> s' ==> Fun s ->> Fun s'";
be rtrancl_induct 1;
by (ALLGOALS(fast_tac (lambda_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_beta_Fun";

goal Lambda.thy "!!s. s ->> s' ==> s @ t ->> s' @ t";
be rtrancl_induct 1;
by (ALLGOALS(fast_tac (lambda_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_beta_AppL";

goal Lambda.thy "!!s. t ->> t' ==> s @ t ->> s @ t'";
be rtrancl_induct 1;
by (ALLGOALS(fast_tac (lambda_cs addIs [rtrancl_refl,rtrancl_into_rtrancl])));
qed "rtrancl_beta_AppR";

goal Lambda.thy "!!s. [| s ->> s'; t ->> t' |] ==> s @ t ->> s' @ t'";
by (fast_tac (lambda_cs addIs
                [rtrancl_beta_AppL,rtrancl_beta_AppR,rtrancl_trans]) 1);
qed "rtrancl_beta_App";

(*** subst and lift ***)

fun addsplit ss = ss addsimps [subst_Var] setloop (split_tac [expand_if]);

goal Lambda.thy "(Var n)[u/n] = u";
by (asm_full_simp_tac (addsplit lambda_ss) 1);
qed "subst_eq";

goal Lambda.thy "!!s. m<n ==> (Var n)[u/m] = Var(pred n)";
by (asm_full_simp_tac (addsplit lambda_ss) 1);
qed "subst_gt";

goal Lambda.thy "!!s. n<m ==> (Var n)[u/m] = Var(n)";
by (asm_full_simp_tac (addsplit lambda_ss addsimps
                          [less_not_refl2 RS not_sym,less_SucI]) 1);
qed "subst_lt";

val lambda_ss = lambda_ss addsimps [subst_eq,subst_gt,subst_lt];

goal Lambda.thy
  "!n i. i < Suc n --> lift (lift s i) (Suc n) = lift (lift s n) i";
by(db.induct_tac "s" 1);
by(ALLGOALS(asm_simp_tac lambda_ss));
by(strip_tac 1);
by (excluded_middle_tac "nat < i" 1);
by ((forward_tac [lt_trans2] 2) THEN (assume_tac 2));
by (ALLGOALS(asm_full_simp_tac ((addsplit lambda_ss) addsimps [less_SucI])));
qed"lift_lift";

goal Lambda.thy "!m n s. n < Suc m --> \
\         lift (t[s/n]) m = (lift t (Suc m)) [lift s m / n]";
by(db.induct_tac "t" 1);
by(ALLGOALS(asm_simp_tac (lambda_ss addsimps [lift_lift])));
by(strip_tac 1);
by (excluded_middle_tac "nat < n" 1);
by (asm_full_simp_tac lambda_ss 1);
by (eres_inst_tac [("j","nat")] leqE 1);
by (asm_full_simp_tac ((addsplit lambda_ss) 
                        addsimps [less_SucI,gt_pred,Suc_pred]) 1);
by (hyp_subst_tac 1);
by (asm_simp_tac lambda_ss 1);
by (forw_inst_tac [("j","n")] lt_trans2 1);
by (assume_tac 1);
by (asm_full_simp_tac (addsplit lambda_ss addsimps [less_SucI]) 1);
qed "lift_subst";
val lambda_ss = lambda_ss addsimps [lift_subst];

goal Lambda.thy
  "!n m u. m < Suc n -->\
\         lift (v[u/n]) m = (lift v m) [lift u m / Suc n]";
by(db.induct_tac "v" 1);
by(ALLGOALS(asm_simp_tac (lambda_ss addsimps [lift_lift])));
by(strip_tac 1);
by (excluded_middle_tac "nat < n" 1);
by (asm_full_simp_tac lambda_ss 1);
by (eres_inst_tac [("i","n")] leqE 1);
by (forward_tac  [lt_trans1] 1 THEN assume_tac 1);
by (ALLGOALS(asm_full_simp_tac 
	     (lambda_ss addsimps [Suc_pred,less_SucI,gt_pred])));
by (hyp_subst_tac 1);
by (asm_full_simp_tac (lambda_ss addsimps [less_SucI]) 1);
by(split_tac [expand_if] 1);
by (asm_full_simp_tac (lambda_ss addsimps [less_SucI]) 1);
qed "lift_subst_lt";

goal Lambda.thy "!n v. (lift u n)[v/n] = u";
by(db.induct_tac "u" 1);
by(ALLGOALS(asm_simp_tac lambda_ss));
by(split_tac [expand_if] 1);
by(ALLGOALS(asm_full_simp_tac lambda_ss));
qed "subst_lift";
val lambda_ss = lambda_ss addsimps [subst_lift];


goal Lambda.thy "!m n u w. m < Suc n --> \
\ (v[lift w m / Suc n]) [u[w/n]/m] = (v[u/m])[w/n]";
by(db.induct_tac "v" 1);
by (ALLGOALS(asm_simp_tac (lambda_ss addsimps
                   [lift_lift RS spec RS spec RS mp RS sym,lift_subst_lt])));
by(strip_tac 1);
by (excluded_middle_tac "nat < Suc(Suc n)" 1);
by(asm_full_simp_tac lambda_ss 1);
by (forward_tac [lessI RS less_trans] 1);
by (eresolve_tac [leqE] 1);
by (asm_simp_tac (lambda_ss addsimps [Suc_pred,lt_pred]) 2);
by (forward_tac [Suc_mono RS less_trans] 1 THEN assume_tac 1);
by (forw_inst_tac [("i","m")] (lessI RS less_trans) 1);
by (asm_simp_tac (lambda_ss addsimps [Suc_pred,lt_pred]) 1);
by (eres_inst_tac [("i","nat")] leqE 1);
by (asm_full_simp_tac (lambda_ss addsimps [Suc_pred,less_SucI]) 2);
by (excluded_middle_tac "nat < m" 1);
by (asm_full_simp_tac lambda_ss 1);
by (eres_inst_tac [("j","nat")] leqE 1);
by (asm_simp_tac (lambda_ss addsimps [gt_pred]) 1);
by (asm_simp_tac lambda_ss 1);
by (forward_tac [lt_trans2] 1 THEN assume_tac 1);
by (asm_simp_tac (lambda_ss addsimps [gt_pred]) 1);
bind_thm("subst_subst", result() RS spec RS spec RS spec RS spec RS mp);
