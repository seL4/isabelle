(*  Title:      ZF/ex/Limit
    ID:         $Id$
    Author:     Sten Agerholm

The inverse limit construction.
*)
   
open Limit; 

(*----------------------------------------------------------------------*)
(* Useful goal commands.                                                *)
(*----------------------------------------------------------------------*)

val brr = fn thl => fn n => by(REPEAT(ares_tac thl n));
val trr = fn thl => fn n => (REPEAT(ares_tac thl n));
fun rotate n i = EVERY(replicate n (etac revcut_rl i));    

(*----------------------------------------------------------------------*)
(* Preliminary theorems.                                                *)
(*----------------------------------------------------------------------*)

val theI2 = prove_goal ZF.thy  (* From Larry *)
    "[| EX! x. P(x);  !!x. P(x) ==> Q(x) |] ==> Q(THE x.P(x))"
 (fn prems => [ resolve_tac prems 1, 
                rtac theI 1, 
                resolve_tac prems 1 ]);

(*----------------------------------------------------------------------*)
(* Basic results.                                                       *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [set_def] 
    "x:fst(D) ==> x:set(D)";
by (resolve_tac prems 1);
val set_I = result();

val prems = goalw Limit.thy [rel_def]
    "<x,y>:snd(D) ==> rel(D,x,y)";
by (resolve_tac prems 1);
val rel_I = result();

val prems = goalw Limit.thy [rel_def]
    "!!z. rel(D,x,y) ==> <x,y>:snd(D)";
by (assume_tac 1);
val rel_E = result();

(*----------------------------------------------------------------------*)
(* I/E/D rules for po and cpo.                                          *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [po_def]
    "[|po(D); x:set(D)|] ==> rel(D,x,x)";
by (rtac (hd prems RS conjunct1 RS bspec) 1);
by (resolve_tac prems 1);
val po_refl = result();

val [po,xy,yz,x,y,z] = goalw Limit.thy [po_def]
    "[|po(D); rel(D,x,y); rel(D,y,z); x:set(D);  \
\      y:set(D); z:set(D)|] ==> rel(D,x,z)";
br (po RS conjunct2 RS conjunct1 RS bspec RS bspec 
   RS bspec RS mp RS mp) 1;
by (rtac x 1); 
by (rtac y 1);
by (rtac z 1);
by (rtac xy 1); 
by (rtac yz 1);
val po_trans = result();

val prems = goalw Limit.thy [po_def]
    "[|po(D); rel(D,x,y); rel(D,y,x); x:set(D); y:set(D)|] ==> x = y";
by (rtac (hd prems RS conjunct2 RS conjunct2 RS bspec RS bspec RS mp RS mp) 1);
by (REPEAT(resolve_tac prems 1));
val po_antisym = result();

val prems = goalw Limit.thy [po_def]
    "[| !!x. x:set(D) ==> rel(D,x,x);   \
\       !!x y z. [| rel(D,x,y); rel(D,y,z); x:set(D); y:set(D); z:set(D)|] ==> \
\                rel(D,x,z);  \
\       !!x y. [| rel(D,x,y); rel(D,y,x); x:set(D); y:set(D)|] ==> x=y |] ==> \
\    po(D)";
by (safe_tac lemmas_cs);
brr prems 1;
val poI = result();

val prems = goalw Limit.thy [cpo_def]
    "[| po(D); !!X. chain(D,X) ==> islub(D,X,x(D,X))|] ==> cpo(D)";
by (safe_tac (lemmas_cs addSIs [exI]));
brr prems 1;
val cpoI = result();

val [cpo] = goalw Limit.thy [cpo_def] "cpo(D) ==> po(D)";
by (rtac (cpo RS conjunct1) 1);
val cpo_po = result();

val prems = goal Limit.thy
    "[|cpo(D); x:set(D)|] ==> rel(D,x,x)";
by (rtac po_refl 1);
by (REPEAT(resolve_tac ((hd prems RS cpo_po)::prems) 1));
val cpo_refl = result();

val prems = goal Limit.thy
    "[|cpo(D); rel(D,x,y); rel(D,y,z); x:set(D);  \
\      y:set(D); z:set(D)|] ==> rel(D,x,z)";
by (rtac po_trans 1);
by (REPEAT(resolve_tac ((hd prems RS cpo_po)::prems) 1));
val cpo_trans = result();

val prems = goal Limit.thy
    "[|cpo(D); rel(D,x,y); rel(D,y,x); x:set(D); y:set(D)|] ==> x = y";
by (rtac po_antisym 1);
by (REPEAT(resolve_tac ((hd prems RS cpo_po)::prems) 1));
val cpo_antisym = result();

val [cpo,chain,ex] = goalw Limit.thy [cpo_def] (* cpo_islub *)
  "[|cpo(D); chain(D,X);!!x. islub(D,X,x) ==> R|] ==> R";
by (rtac (chain RS (cpo RS conjunct2 RS spec RS mp) RS exE) 1); 
brr[ex]1; (* above theorem would loop *)
val cpo_islub = result();

(*----------------------------------------------------------------------*)
(* Theorems about isub and islub.                                       *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [islub_def]  (* islub_isub *)
    "islub(D,X,x) ==> isub(D,X,x)";
by (simp_tac (ZF_ss addsimps prems) 1);
val islub_isub = result();

val prems = goal Limit.thy
    "islub(D,X,x) ==> x:set(D)";
by (rtac (rewrite_rule[islub_def,isub_def](hd prems) RS conjunct1 RS conjunct1) 1);
val islub_in = result();

val prems = goal Limit.thy
    "[|islub(D,X,x); n:nat|] ==> rel(D,X`n,x)";
br (rewrite_rule[islub_def,isub_def](hd prems) RS conjunct1 
   RS conjunct2 RS bspec) 1;
by (resolve_tac prems 1);
val islub_ub = result();

val prems = goalw Limit.thy [islub_def]
    "[|islub(D,X,x); isub(D,X,y)|] ==> rel(D,x,y)";
by (rtac (hd prems RS conjunct2 RS spec RS mp) 1);
by (resolve_tac prems 1);
val islub_least = result();

val prems = goalw Limit.thy [islub_def]  (* islubI *)
    "[|isub(D,X,x); !!y. isub(D,X,y) ==> rel(D,x,y)|] ==> islub(D,X,x)";
by (safe_tac lemmas_cs);
by (REPEAT(ares_tac prems 1));
val islubI = result();

val prems = goalw Limit.thy [isub_def]  (* isubI *)
    "[|x:set(D);!!n. n:nat ==> rel(D,X`n,x)|] ==> isub(D,X,x)";
by (safe_tac lemmas_cs);
by (REPEAT(ares_tac prems 1));
val isubI = result();

val prems = goalw Limit.thy [isub_def]  (* isubE *)
    "!!z.[|isub(D,X,x);[|x:set(D);!!n.n:nat==>rel(D,X`n,x)|] ==> P|] ==> P";
by (safe_tac lemmas_cs);
by (asm_simp_tac ZF_ss 1);
val isubE = result();

val prems = goalw Limit.thy [isub_def]  (* isubD1 *)
    "isub(D,X,x) ==> x:set(D)";
by (simp_tac (ZF_ss addsimps prems) 1);
val isubD1 = result();

val prems = goalw Limit.thy [isub_def]  (* isubD2 *)
    "[|isub(D,X,x); n:nat|]==>rel(D,X`n,x)";
by (simp_tac (ZF_ss addsimps prems) 1);
val isubD2 = result();

val prems = goal Limit.thy
    "!!z. [|islub(D,X,x); islub(D,X,y); cpo(D)|] ==> x = y";
by (etac cpo_antisym 1);
by (rtac islub_least 2);
by (rtac islub_least 1);
brr[islub_isub,islub_in]1;
val islub_unique = result();

(*----------------------------------------------------------------------*)
(* lub gives the least upper bound of chains.                           *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [lub_def]
    "[|chain(D,X); cpo(D)|] ==> islub(D,X,lub(D,X))";
by (rtac cpo_islub 1);
brr prems 1;
by (rtac theI 1); (* loops when repeated *)
by (rtac ex1I 1);
by (assume_tac 1);
by (etac islub_unique 1);
brr prems 1;
val cpo_lub = result();

(*----------------------------------------------------------------------*)
(* Theorems about chains.                                               *)
(*----------------------------------------------------------------------*)

val chainI = prove_goalw Limit.thy [chain_def]
 "!!z.[|X:nat->set(D);!!n. n:nat ==> rel(D,X`n,X`succ(n))|] ==> chain(D,X)"
 (fn prems => [asm_simp_tac ZF_ss 1]);

val prems = goalw Limit.thy [chain_def]
    "chain(D,X) ==> X : nat -> set(D)";
by (asm_simp_tac (ZF_ss addsimps prems) 1);
val chain_fun = result();
    
val prems = goalw Limit.thy [chain_def]
    "[|chain(D,X); n:nat|] ==> X`n : set(D)";
by (rtac ((hd prems)RS conjunct1 RS apply_type) 1);
by (rtac (hd(tl prems)) 1);
val chain_in = result();
    
val prems = goalw Limit.thy [chain_def]
    "[|chain(D,X); n:nat|] ==> rel(D, X ` n, X ` succ(n))";
by (rtac ((hd prems)RS conjunct2 RS bspec) 1);
by (rtac (hd(tl prems)) 1);
val chain_rel = result();
    
val prems = goal Limit.thy  (* chain_rel_gen_add *)
    "[|chain(D,X); cpo(D); n:nat; m:nat|] ==> rel(D,X`n,(X`(m #+ n)))";
by (res_inst_tac [("n","m")] nat_induct 1);
by (ALLGOALS(simp_tac arith_ss));
by (rtac cpo_trans 3); (* loops if repeated *)
brr(cpo_refl::chain_in::chain_rel::nat_succI::add_type::prems) 1;
val chain_rel_gen_add = result();

val prems = goal Limit.thy  (* le_succ_eq *)
  "[| n le succ(x); ~ n le x; x : nat; n:nat |] ==> n = succ(x)";
by (rtac le_anti_sym 1);
by (resolve_tac prems 1);
by (simp_tac arith_ss 1);
by (rtac (not_le_iff_lt RS iffD1) 1);
by (REPEAT(resolve_tac (nat_into_Ord::prems) 1));
val le_succ_eq = result();

val prems = goal Limit.thy  (* chain_rel_gen *)
    "[|n le m; chain(D,X); cpo(D); n:nat; m:nat|] ==> rel(D,X`n,X`m)";
by (rtac impE 1);  (* The first three steps prepare for the induction proof *)
by (assume_tac 3);
by (rtac (hd prems) 2);
by (res_inst_tac [("n","m")] nat_induct 1);
by (safe_tac lemmas_cs);
by (asm_full_simp_tac (arith_ss addsimps prems) 2);
by (rtac cpo_trans 4);
by (rtac (le_succ_eq RS subst) 3);
brr(cpo_refl::chain_in::chain_rel::nat_0I::nat_succI::prems) 1;
val chain_rel_gen = result();

(*----------------------------------------------------------------------*)
(* Theorems about pcpos and bottom.                                     *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [pcpo_def]  (* pcpoI *)
    "[|!!y.y:set(D)==>rel(D,x,y); x:set(D); cpo(D)|]==>pcpo(D)";
by (rtac conjI 1);
by (resolve_tac prems 1);
by (rtac bexI 1);
by (rtac ballI 1);
by (resolve_tac prems 2);
brr prems 1;
val pcpoI = result();

val pcpo_cpo = prove_goalw Limit.thy [pcpo_def] "pcpo(D) ==> cpo(D)"
    (fn [pcpo] => [rtac(pcpo RS conjunct1) 1]);

val prems = goalw Limit.thy [pcpo_def] (* pcpo_bot_ex1 *)
    "pcpo(D) ==> EX! x. x:set(D) & (ALL y:set(D). rel(D,x,y))";
by (rtac (hd prems RS conjunct2 RS bexE) 1);
by (rtac ex1I 1);
by (safe_tac lemmas_cs);
by (assume_tac 1);
by (etac bspec 1);
by (assume_tac 1);
by (rtac cpo_antisym 1);
by (rtac (hd prems RS conjunct1) 1);
by (etac bspec 1);
by (assume_tac 1);
by (etac bspec 1);
by (REPEAT(atac 1));
val pcpo_bot_ex1 = result();

val prems = goalw Limit.thy [bot_def] (* bot_least *)
    "[| pcpo(D); y:set(D)|] ==> rel(D,bot(D),y)";
by (rtac theI2 1);
by (rtac pcpo_bot_ex1 1);
by (resolve_tac prems 1);
by (etac conjE 1);
by (etac bspec 1);
by (resolve_tac prems 1);
val bot_least = result();

val prems = goalw Limit.thy [bot_def] (* bot_in *)
    "pcpo(D) ==> bot(D):set(D)";
by (rtac theI2 1);
by (rtac pcpo_bot_ex1 1);
by (resolve_tac prems 1);
by (etac conjE 1);
by (assume_tac 1);
val bot_in = result();

val prems = goal Limit.thy  (* bot_unique *)
    "[| pcpo(D); x:set(D); !!y. y:set(D) ==> rel(D,x,y)|] ==> x = bot(D)";
by (rtac cpo_antisym 1);
brr(pcpo_cpo::bot_in::bot_least::prems) 1;
val bot_unique = result();

(*----------------------------------------------------------------------*)
(* Constant chains and lubs and cpos.                                   *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [chain_def] (* chain_const *)
    "[|x:set(D); cpo(D)|] ==> chain(D,(lam n:nat. x))";
by (rtac conjI 1);
by (rtac lam_type 1);
by (resolve_tac prems 1);
by (rtac ballI 1);
by (asm_simp_tac (ZF_ss addsimps [nat_succI]) 1);
brr(cpo_refl::prems) 1;
val chain_const = result();

val prems = goalw Limit.thy [islub_def,isub_def] (* islub_const *)
    "[|x:set(D); cpo(D)|] ==> islub(D,(lam n:nat. x),x)";
by (simp_tac ZF_ss 1);
by (safe_tac lemmas_cs);
by (etac bspec 3);
brr(cpo_refl::nat_0I::prems) 1;
val islub_const = result();

val prems = goal Limit.thy  (* lub_const *)
    "[|x:set(D); cpo(D)|] ==> lub(D,lam n:nat.x) = x";
by (rtac islub_unique 1);
by (rtac cpo_lub 1);
by (rtac chain_const 1);
by (REPEAT(resolve_tac prems 1));
by (rtac islub_const 1);
by (REPEAT(resolve_tac prems 1));
val lub_const = result();

(*----------------------------------------------------------------------*)
(* Taking the suffix of chains has no effect on ub's.                   *) 
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [isub_def,suffix_def]  (* isub_suffix *)
    "[|chain(D,X); cpo(D); n:nat|] ==> isub(D,suffix(X,n),x) <-> isub(D,X,x)";
by (simp_tac (ZF_ss addsimps prems) 1);
by (safe_tac lemmas_cs);
by (dtac bspec 2);
by (assume_tac 3);      (* to instantiate unknowns properly *)
by (rtac cpo_trans 1);
by (rtac chain_rel_gen_add 2);
by (dtac bspec 6);
by (assume_tac 7);       (* to instantiate unknowns properly *)
brr(chain_in::add_type::prems) 1;
val isub_suffix = result();

val prems = goalw Limit.thy [islub_def]  (* islub_suffix *)
    "[|chain(D,X); cpo(D); n:nat|] ==> islub(D,suffix(X,n),x) <-> islub(D,X,x)";
by (asm_simp_tac (FOL_ss addsimps isub_suffix::prems) 1);
val islub_suffix = result();

val prems = goalw Limit.thy [lub_def]  (* lub_suffix *)
    "[|chain(D,X); cpo(D); n:nat|] ==> lub(D,suffix(X,n)) = lub(D,X)";
by (asm_simp_tac (FOL_ss addsimps islub_suffix::prems) 1);
val lub_suffix = result();

(*----------------------------------------------------------------------*)
(* Dominate and subchain.                                               *) 
(*----------------------------------------------------------------------*)

val dominateI = prove_goalw Limit.thy [dominate_def]
  "[| !!m. m:nat ==> n(m):nat; !!m. m:nat ==> rel(D,X`m,Y`n(m))|] ==>   \
\  dominate(D,X,Y)"
  (fn prems => [rtac ballI 1,rtac bexI 1,REPEAT(ares_tac prems 1)]);

val [dom,isub,cpo,X,Y] = goal Limit.thy
  "[|dominate(D,X,Y); isub(D,Y,x); cpo(D);  \
\    X:nat->set(D); Y:nat->set(D)|] ==> isub(D,X,x)";
by (rewtac isub_def);
by (rtac conjI 1);
by (rtac (rewrite_rule[isub_def]isub RS conjunct1) 1);
by (rtac ballI 1);
by (rtac (rewrite_rule[dominate_def]dom RS bspec RS bexE) 1);
by (assume_tac 1);
by (rtac cpo_trans 1);
by (rtac cpo 1);
by (assume_tac 1);
by (rtac (rewrite_rule[isub_def]isub RS conjunct2 RS bspec) 1);
by (assume_tac 1);
by (etac (X RS apply_type) 1);
by (etac (Y RS apply_type) 1);
by (rtac (rewrite_rule[isub_def]isub RS conjunct1) 1);
val dominate_isub = result();

val [dom,Xlub,Ylub,cpo,X,Y] = goal Limit.thy
  "[|dominate(D,X,Y); islub(D,X,x); islub(D,Y,y); cpo(D);  \
\    X:nat->set(D); Y:nat->set(D)|] ==> rel(D,x,y)";
val Xub = rewrite_rule[islub_def]Xlub RS conjunct1;
val Yub = rewrite_rule[islub_def]Ylub RS conjunct1;
val Xub_y = Yub RS (dom RS dominate_isub);
val lem = Xub_y RS (rewrite_rule[islub_def]Xlub RS conjunct2 RS spec RS mp);
val thm = Y RS (X RS (cpo RS lem));
by (rtac thm 1);
val dominate_islub = result();

val prems = goalw Limit.thy [subchain_def]  (* subchainE *)
    "[|subchain(X,Y); n:nat;!!m. [|m:nat; X`n = Y`(n #+ m)|] ==> Q|] ==> Q";
by (rtac (hd prems RS bspec RS bexE) 1);
by (resolve_tac prems 2);
by (assume_tac 3);
by (REPEAT(ares_tac prems 1));
val subchainE = result();

val prems = goalw Limit.thy []  (* subchain_isub *)
    "[|subchain(Y,X); isub(D,X,x)|] ==> isub(D,Y,x)";
by (rtac isubI 1);
val [subch,ub] = prems;
by (rtac (ub RS isubD1) 1);
by (rtac (subch RS subchainE) 1);
by (assume_tac 1);
by (asm_simp_tac ZF_ss 1);
by (rtac isubD2 1);                (* br with Destruction rule ?? *)
by (resolve_tac prems 1);
by (asm_simp_tac arith_ss 1);
val subchain_isub = result();

val prems = goal Limit.thy  (* dominate_islub_eq *)
  "[|dominate(D,X,Y); subchain(Y,X); islub(D,X,x); islub(D,Y,y); cpo(D);  \
\    X:nat->set(D); Y:nat->set(D)|] ==> x = y";
by (rtac cpo_antisym 1);
by (resolve_tac prems 1);
by (rtac dominate_islub 1);
by (REPEAT(resolve_tac prems 1));
by (rtac islub_least 1);
by (REPEAT(resolve_tac prems 1));
by (rtac subchain_isub 1);
by (rtac islub_isub 2);
by (REPEAT(resolve_tac (islub_in::prems) 1));
val dominate_islub_eq = result();

(*----------------------------------------------------------------------*)
(* Matrix.                                                              *) 
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [matrix_def]  (* matrix_fun *)
    "matrix(D,M) ==> M : nat -> (nat -> set(D))";
by (simp_tac (ZF_ss addsimps prems) 1);
val matrix_fun = result();

val prems = goalw Limit.thy []  (* matrix_in_fun *)
    "[|matrix(D,M); n:nat|] ==> M`n : nat -> set(D)";
by (rtac apply_type 1);
by (REPEAT(resolve_tac(matrix_fun::prems) 1));
val matrix_in_fun = result();

val prems = goalw Limit.thy []  (* matrix_in *)
    "[|matrix(D,M); n:nat; m:nat|] ==> M`n`m : set(D)";
by (rtac apply_type 1);
by (REPEAT(resolve_tac(matrix_in_fun::prems) 1));
val matrix_in = result();

val prems = goalw Limit.thy [matrix_def]  (* matrix_rel_1_0 *)
    "[|matrix(D,M); n:nat; m:nat|] ==> rel(D,M`n`m,M`succ(n)`m)";
by (simp_tac (ZF_ss addsimps prems) 1);
val matrix_rel_1_0 = result();

val prems = goalw Limit.thy [matrix_def]  (* matrix_rel_0_1 *)
    "[|matrix(D,M); n:nat; m:nat|] ==> rel(D,M`n`m,M`n`succ(m))";
by (simp_tac (ZF_ss addsimps prems) 1);
val matrix_rel_0_1 = result();

val prems = goalw Limit.thy [matrix_def]  (* matrix_rel_1_1 *)
    "[|matrix(D,M); n:nat; m:nat|] ==> rel(D,M`n`m,M`succ(n)`succ(m))";
by (simp_tac (ZF_ss addsimps prems) 1);
val matrix_rel_1_1 = result();

val prems = goal Limit.thy  (* fun_swap *)
    "f:X->Y->Z ==> (lam y:Y. lam x:X. f`x`y):Y->X->Z";
by (rtac lam_type 1);
by (rtac lam_type 1);
by (rtac apply_type 1);
by (rtac apply_type 1);
by (REPEAT(ares_tac prems 1));
val fun_swap = result();

val prems = goalw Limit.thy [matrix_def]  (* matrix_sym_axis *)
    "!!z. matrix(D,M) ==> matrix(D,lam m:nat. lam n:nat. M`n`m)";
by (simp_tac arith_ss 1 THEN safe_tac lemmas_cs THEN 
REPEAT(asm_simp_tac (ZF_ss addsimps [fun_swap]) 1));
val matrix_sym_axis = result();

val prems = goalw Limit.thy [chain_def]  (* matrix_chain_diag *)
    "matrix(D,M) ==> chain(D,lam n:nat. M`n`n)";
by (safe_tac lemmas_cs);
by (rtac lam_type 1);
by (rtac matrix_in 1);
by (REPEAT(ares_tac prems 1));
by (asm_simp_tac arith_ss 1);
by (rtac matrix_rel_1_1 1);
by (REPEAT(ares_tac prems 1));
val matrix_chain_diag = result();

val prems = goalw Limit.thy [chain_def]  (* matrix_chain_left *)
    "[|matrix(D,M); n:nat|] ==> chain(D,M`n)";
by (safe_tac lemmas_cs);
by (rtac apply_type 1);
by (rtac matrix_fun 1);
by (REPEAT(ares_tac prems 1));
by (rtac matrix_rel_0_1 1);
by (REPEAT(ares_tac prems 1));
val matrix_chain_left = result();

val prems = goalw Limit.thy [chain_def]  (* matrix_chain_right *)
    "[|matrix(D,M); m:nat|] ==> chain(D,lam n:nat. M`n`m)";
by (safe_tac lemmas_cs);
by (asm_simp_tac(arith_ss addsimps prems) 2);
brr(lam_type::matrix_in::matrix_rel_1_0::prems) 1;
val matrix_chain_right = result();

val prems = goalw Limit.thy [matrix_def]  (* matrix_chainI *)
    "[|!!x.x:nat==>chain(D,M`x);!!y.y:nat==>chain(D,lam x:nat. M`x`y);   \
\      M:nat->nat->set(D); cpo(D)|] ==> matrix(D,M)";
by (safe_tac (lemmas_cs addSIs [ballI]));
by (cut_inst_tac[("y1","m"),("n","n")](hd(tl prems) RS chain_rel) 2);
by (asm_full_simp_tac arith_ss 4);
by (rtac cpo_trans 5);
by (cut_inst_tac[("y1","m"),("n","n")](hd(tl prems) RS chain_rel) 6);
by (asm_full_simp_tac arith_ss 8);
by (TRYALL(rtac (chain_fun RS apply_type)));
brr(chain_rel::nat_succI::prems) 1;
val matrix_chainI = result();

val lemma = prove_goal Limit.thy
    "!!z.[|m : nat; rel(D, (lam n:nat. M`n`n)`m, y)|] ==> rel(D,M`m`m, y)"
    (fn prems => [asm_full_simp_tac ZF_ss 1]);

val lemma2 = prove_goal Limit.thy
    "!!z.[|x:nat; m:nat; rel(D,(lam n:nat.M`n`m1)`x,(lam n:nat.M`n`m1)`m)|] ==> \
\        rel(D,M`x`m1,M`m`m1)"
    (fn prems => [asm_full_simp_tac ZF_ss 1]);

val prems = goalw Limit.thy []  (* isub_lemma *)
    "[|isub(D,(lam n:nat. M`n`n),y); matrix(D,M); cpo(D)|] ==>  \
\    isub(D,(lam n:nat. lub(D,lam m:nat. M`n`m)),y)";
by (rewtac isub_def);
by (safe_tac lemmas_cs);
by (rtac isubD1 1);
by (resolve_tac prems 1);
by (asm_simp_tac ZF_ss 1);
by (cut_inst_tac[("a","n")](hd(tl prems) RS matrix_fun RS apply_type) 1);
by (assume_tac 1);
by (asm_simp_tac ZF_ss 1);
by (rtac islub_least 1);
by (rtac cpo_lub 1);
by (rtac matrix_chain_left 1);
by (resolve_tac prems 1);
by (assume_tac 1);
by (resolve_tac prems 1);
by (rewtac isub_def);
by (safe_tac lemmas_cs);
by (rtac isubD1 1);
by (resolve_tac prems 1);
by (cut_inst_tac[("P","n le na")]excluded_middle 1);
by (safe_tac lemmas_cs);
by (rtac cpo_trans 1);
by (resolve_tac prems 1);
by (rtac (not_le_iff_lt RS iffD1 RS leI RS chain_rel_gen) 1);
by (assume_tac 3);
by (REPEAT(ares_tac (nat_into_Ord::matrix_chain_left::prems) 1));
by (rtac lemma 1);
by (rtac isubD2 2);
by (REPEAT(ares_tac (matrix_in::isubD1::prems) 1));
by (rtac cpo_trans 1);
by (resolve_tac prems 1);
by (rtac lemma2 1);
by (rtac lemma 4);
by (rtac isubD2 5);
by (REPEAT(ares_tac
  ([chain_rel_gen,matrix_chain_right,matrix_in,isubD1]@prems) 1));
val isub_lemma = result();

val prems = goalw Limit.thy [chain_def]  (* matrix_chain_lub *)
    "[|matrix(D,M); cpo(D)|] ==> chain(D,lam n:nat.lub(D,lam m:nat.M`n`m))";
by (safe_tac lemmas_cs);
by (rtac lam_type 1);
by (rtac islub_in 1);
by (rtac cpo_lub 1);
by (resolve_tac prems 2);
by (asm_simp_tac arith_ss 2);
by (rtac chainI 1);
by (rtac lam_type 1);
by (REPEAT(ares_tac (matrix_in::prems) 1));
by (asm_simp_tac arith_ss 1);
by (rtac matrix_rel_0_1 1);
by (REPEAT(ares_tac prems 1));
by (asm_simp_tac (arith_ss addsimps 
    [hd prems RS matrix_chain_left RS chain_fun RS eta]) 1);
by (rtac dominate_islub 1);
by (rtac cpo_lub 3);
by (rtac cpo_lub 2);
by (rewtac dominate_def);
by (rtac ballI 1);
by (rtac bexI 1);
by (assume_tac 2);
back();  (* Backtracking...... *)
by (rtac matrix_rel_1_0 1);
by (REPEAT(ares_tac (matrix_chain_left::nat_succI::chain_fun::prems) 1));
val matrix_chain_lub = result();

val prems = goal Limit.thy  (* isub_eq *)
    "[|matrix(D,M); cpo(D)|] ==>  \
\    isub(D,(lam n:nat. lub(D,lam m:nat. M`n`m)),y) <->  \
\    isub(D,(lam n:nat. M`n`n),y)";
by (rtac iffI 1);
by (rtac dominate_isub 1);
by (assume_tac 2);
by (rewtac dominate_def);
by (rtac ballI 1);
by (rtac bexI 1);
by (assume_tac 2);
by (asm_simp_tac ZF_ss 1);
by (asm_simp_tac (arith_ss addsimps 
    [hd prems RS matrix_chain_left RS chain_fun RS eta]) 1);
by (rtac islub_ub 1);
by (rtac cpo_lub 1);
by (REPEAT(ares_tac 
(matrix_chain_left::matrix_chain_diag::chain_fun::matrix_chain_lub::prems) 1));
by (rtac isub_lemma 1);
by (REPEAT(ares_tac prems 1));
val isub_eq = result();

val lemma1 = prove_goalw Limit.thy [lub_def]  
    "lub(D,(lam n:nat. lub(D,lam m:nat. M`n`m))) =   \
\    (THE x. islub(D, (lam n:nat. lub(D,lam m:nat. M`n`m)), x))"
 (fn prems => [fast_tac ZF_cs 1]);

val lemma2 = prove_goalw Limit.thy [lub_def]  
    "lub(D,(lam n:nat. M`n`n)) =   \
\    (THE x. islub(D, (lam n:nat. M`n`n), x))"
 (fn prems => [fast_tac ZF_cs 1]);

val prems = goalw Limit.thy []  (* lub_matrix_diag *)
    "[|matrix(D,M); cpo(D)|] ==>  \
\    lub(D,(lam n:nat. lub(D,lam m:nat. M`n`m))) =  \
\    lub(D,(lam n:nat. M`n`n))";
by (simp_tac (arith_ss addsimps [lemma1,lemma2]) 1);
by (rewtac islub_def);
by (simp_tac (FOL_ss addsimps [hd(tl prems) RS (hd prems RS isub_eq)]) 1);
val lub_matrix_diag = result();

val [matrix,cpo] = goalw Limit.thy []  (* lub_matrix_diag_sym *)
    "[|matrix(D,M); cpo(D)|] ==>  \
\    lub(D,(lam m:nat. lub(D,lam n:nat. M`n`m))) =  \
\    lub(D,(lam n:nat. M`n`n))";
by (cut_facts_tac[cpo RS (matrix RS matrix_sym_axis RS lub_matrix_diag)]1);
by (asm_full_simp_tac ZF_ss 1);
val lub_matrix_diag_sym = result();

(*----------------------------------------------------------------------*)
(* I/E/D rules for mono and cont.                                       *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [mono_def]  (* monoI *)
    "[|f:set(D)->set(E);   \
\      !!x y. [|rel(D,x,y); x:set(D); y:set(D)|] ==> rel(E,f`x,f`y)|] ==>   \
\     f:mono(D,E)";
by (fast_tac(ZF_cs addSIs prems) 1);
val monoI = result();

val prems = goal Limit.thy
    "f:mono(D,E) ==> f:set(D)->set(E)";
by (rtac (rewrite_rule[mono_def](hd prems) RS CollectD1) 1);
val mono_fun = result();

val prems = goal Limit.thy
    "[|f:mono(D,E); x:set(D)|] ==> f`x:set(E)";
by (rtac (hd prems RS mono_fun RS apply_type) 1);
by (resolve_tac prems 1);
val mono_map = result();

val prems = goal Limit.thy
    "[|f:mono(D,E); rel(D,x,y); x:set(D); y:set(D)|] ==> rel(E,f`x,f`y)";
by (rtac (rewrite_rule[mono_def](hd prems) RS CollectD2 RS bspec RS bspec RS mp) 1);
by (REPEAT(resolve_tac prems 1));
val mono_mono = result();

val prems = goalw Limit.thy [cont_def,mono_def]  (* contI *)
    "[|f:set(D)->set(E);   \
\      !!x y. [|rel(D,x,y); x:set(D); y:set(D)|] ==> rel(E,f`x,f`y);   \
\      !!X. chain(D,X) ==> f`lub(D,X) = lub(E,lam n:nat. f`(X`n))|] ==>   \
\     f:cont(D,E)";
by (fast_tac(ZF_cs addSIs prems) 1);
val contI = result();

val prems = goal Limit.thy 
    "f:cont(D,E) ==> f:mono(D,E)";
by (rtac (rewrite_rule[cont_def](hd prems) RS CollectD1) 1);
val cont2mono = result();

val prems = goal Limit.thy
    "f:cont(D,E) ==> f:set(D)->set(E)";
by (rtac (rewrite_rule[cont_def](hd prems) RS CollectD1 RS mono_fun) 1);
val cont_fun = result();

val prems = goal Limit.thy
    "[|f:cont(D,E); x:set(D)|] ==> f`x:set(E)";
by (rtac (hd prems RS cont_fun RS apply_type) 1);
by (resolve_tac prems 1);
val cont_map = result();

val prems = goal Limit.thy
    "[|f:cont(D,E); rel(D,x,y); x:set(D); y:set(D)|] ==> rel(E,f`x,f`y)";
by (rtac (rewrite_rule[cont_def](hd prems) RS CollectD1 RS mono_mono) 1);
by (REPEAT(resolve_tac prems 1));
val cont_mono = result();

val prems = goal Limit.thy
    "[|f:cont(D,E); chain(D,X)|] ==> f`(lub(D,X)) = lub(E,lam n:nat. f`(X`n))";
by (rtac (rewrite_rule[cont_def](hd prems) RS CollectD2 RS spec RS mp) 1);
by (REPEAT(resolve_tac prems 1));
val cont_lub = result();

(*----------------------------------------------------------------------*)
(* Continuity and chains.                                               *) 
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy []  (* mono_chain *)
    "[|f:mono(D,E); chain(D,X)|] ==> chain(E,lam n:nat. f`(X`n))";
by (rewtac chain_def);
by (simp_tac arith_ss 1);
by (safe_tac lemmas_cs);
by (rtac lam_type 1);
by (rtac mono_map 1);
by (resolve_tac prems 1);
by (rtac chain_in 1);
by (REPEAT(ares_tac prems 1));
by (rtac mono_mono 1);
by (resolve_tac prems 1);
by (rtac chain_rel 1);
by (REPEAT(ares_tac prems 1));
by (rtac chain_in 1);
by (rtac chain_in 3);
by (REPEAT(ares_tac (nat_succI::prems) 1));
val mono_chain = result();

val prems = goalw Limit.thy []  (* cont_chain *)
    "[|f:cont(D,E); chain(D,X)|] ==> chain(E,lam n:nat. f`(X`n))";
by (rtac mono_chain 1);
by (REPEAT(resolve_tac (cont2mono::prems) 1));
val cont_chain = result();

(*----------------------------------------------------------------------*)
(* I/E/D rules about (set+rel) cf, the continuous function space.       *)
(*----------------------------------------------------------------------*)

(* The following development more difficult with cpo-as-relation approach. *)

val prems = goalw Limit.thy [set_def,cf_def]
    "!!z. f:set(cf(D,E)) ==> f:cont(D,E)";
by (asm_full_simp_tac ZF_ss 1);
val in_cf = result();
val cf_cont = result();

val prems = goalw Limit.thy [set_def,cf_def]  (* Non-trivial with relation *)
    "!!z. f:cont(D,E) ==> f:set(cf(D,E))";
by (asm_full_simp_tac ZF_ss 1);
val cont_cf = result();

(* rel_cf originally an equality. Now stated as two rules. Seemed easiest. 
   Besides, now complicated by typing assumptions. *)

val prems = goal Limit.thy
    "[|!!x. x:set(D) ==> rel(E,f`x,g`x); f:cont(D,E); g:cont(D,E)|] ==> \
\    rel(cf(D,E),f,g)";
by (rtac rel_I 1);
by (simp_tac (ZF_ss addsimps [cf_def]) 1);
by (safe_tac lemmas_cs);
brr prems 1;
val rel_cfI = result();

val prems = goalw Limit.thy [rel_def,cf_def]
    "!!z. [|rel(cf(D,E),f,g); x:set(D)|] ==> rel(E,f`x,g`x)";
by (asm_full_simp_tac ZF_ss 1);
val rel_cf = result();

(*----------------------------------------------------------------------*)
(* Theorems about the continuous function space.                        *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy []  (* chain_cf *)
    "[| chain(cf(D,E),X); x:set(D)|] ==> chain(E,lam n:nat. X`n`x)";
by (rtac chainI 1);
by (rtac lam_type 1);
by (rtac apply_type 1);
by (resolve_tac prems 2);
by (REPEAT(ares_tac([cont_fun,in_cf,chain_in]@prems) 1));
by (asm_simp_tac arith_ss 1);
by (REPEAT(ares_tac([rel_cf,chain_rel]@prems) 1));
val chain_cf = result();

val prems = goal Limit.thy  (* matrix_lemma *)
    "[|chain(cf(D,E),X); chain(D,Xa); cpo(D); cpo(E) |] ==>   \
\    matrix(E,lam x:nat. lam xa:nat. X`x`(Xa`xa))";
by (rtac matrix_chainI 1);
by (asm_simp_tac ZF_ss 1);
by (asm_simp_tac ZF_ss 2);
by (rtac chainI 1);
by (rtac lam_type 1);
by (rtac apply_type 1);
by (rtac (chain_in RS cf_cont RS cont_fun) 1);
by (REPEAT(ares_tac prems 1));
by (rtac chain_in 1);
by (REPEAT(ares_tac prems 1));
by (asm_simp_tac arith_ss 1);
by (rtac cont_mono 1);
by (rtac (chain_in RS cf_cont) 1);
brr prems 1;
brr (chain_rel::chain_in::nat_succI::prems) 1;
by (rtac chainI 1);
by (rtac lam_type 1);
by (rtac apply_type 1);
by (rtac (chain_in RS cf_cont RS cont_fun) 1);
by (REPEAT(ares_tac prems 1));
by (rtac chain_in 1);
by (REPEAT(ares_tac prems 1));
by (asm_simp_tac arith_ss 1);
by (rtac rel_cf 1);
brr (chain_in::chain_rel::prems) 1;
by (rtac lam_type 1);
by (rtac lam_type 1);
by (rtac apply_type 1);
by (rtac (chain_in RS cf_cont RS cont_fun) 1);
brr prems 1;
by (rtac chain_in 1);
brr prems 1;
val matrix_lemma = result();

val prems = goal Limit.thy  (* chain_cf_lub_cont *)
    "[|chain(cf(D,E),X); cpo(D); cpo(E) |] ==> \
\    (lam x:set(D). lub(E, lam n:nat. X ` n ` x)) : cont(D, E)";
by (rtac contI 1);
by (rtac lam_type 1);
by (REPEAT(ares_tac((chain_cf RS cpo_lub RS islub_in)::prems) 1));
by (asm_simp_tac ZF_ss 1);
by (rtac dominate_islub 1);
by (REPEAT(ares_tac((chain_cf RS cpo_lub)::prems) 2));
by (rtac dominateI 1);
by (assume_tac 1);
by (asm_simp_tac ZF_ss 1);
by (REPEAT(ares_tac ((chain_in RS cf_cont RS cont_mono)::prems) 1));
by (REPEAT(ares_tac ((chain_cf RS chain_fun)::prems) 1));
by (stac beta 1);
by (REPEAT(ares_tac((cpo_lub RS islub_in)::prems) 1));
by (asm_simp_tac(ZF_ss addsimps[hd prems RS chain_in RS cf_cont RS cont_lub]) 1);
by (forward_tac[hd prems RS matrix_lemma RS lub_matrix_diag]1);
brr prems 1;
by (asm_full_simp_tac ZF_ss 1);
by (asm_simp_tac(ZF_ss addsimps[chain_in RS beta]) 1);
by (dtac (hd prems RS matrix_lemma RS lub_matrix_diag_sym) 1);
brr prems 1;
by (asm_full_simp_tac ZF_ss 1);
val chain_cf_lub_cont = result();

val prems = goal Limit.thy  (* islub_cf *)
    "[| chain(cf(D,E),X); cpo(D); cpo(E)|] ==>   \
\     islub(cf(D,E), X, lam x:set(D). lub(E,lam n:nat. X`n`x))";
by (rtac islubI 1);
by (rtac isubI 1);
by (rtac (chain_cf_lub_cont RS cont_cf) 1);
brr prems 1;
by (rtac rel_cfI 1);
by (asm_simp_tac ZF_ss 1);
by (dtac (hd(tl(tl prems)) RSN(2,hd prems RS chain_cf RS cpo_lub RS islub_ub)) 1);
by (assume_tac 1);
by (asm_full_simp_tac ZF_ss 1);
brr(cf_cont::chain_in::prems) 1;
brr(cont_cf::chain_cf_lub_cont::prems) 1;
by (rtac rel_cfI 1);
by (asm_simp_tac ZF_ss 1);
by (forward_tac[hd(tl(tl prems)) RSN(2,hd prems RS chain_cf RS cpo_lub RS 
   islub_least)]1);
by (assume_tac 2);
brr (chain_cf_lub_cont::isubD1::cf_cont::prems) 2;
by (rtac isubI 1);
brr((cf_cont RS cont_fun RS apply_type)::[isubD1]) 1;
by (asm_simp_tac ZF_ss 1);
by (etac (isubD2 RS rel_cf) 1);
brr [] 1;
val islub_cf = result();

val prems = goal Limit.thy  (* cpo_cf *)
    "[| cpo(D); cpo(E)|] ==> cpo(cf(D,E))";
by (rtac (poI RS cpoI) 1);
by (rtac rel_cfI 1);
brr(cpo_refl::(cf_cont RS cont_fun RS apply_type)::cf_cont::prems) 1;
by (rtac rel_cfI 1);
by (rtac cpo_trans 1);
by (resolve_tac prems 1);
by (etac rel_cf 1);
by (assume_tac 1);
by (rtac rel_cf 1);
by (assume_tac 1);
brr[cf_cont RS cont_fun RS apply_type,cf_cont]1;
by (rtac fun_extension 1);
brr[cf_cont RS cont_fun]1;
by (rtac cpo_antisym 1);
by (rtac (hd(tl prems)) 1);
by (etac rel_cf 1);
by (assume_tac 1);
by (rtac rel_cf 1);
by (assume_tac 1);
brr[cf_cont RS cont_fun RS apply_type]1;
by (dtac islub_cf 1);
brr prems 1;
val cpo_cf = result();

val prems = goal Limit.thy  (* lub_cf *)
    "[| chain(cf(D,E),X); cpo(D); cpo(E)|] ==>   \
\     lub(cf(D,E), X) = (lam x:set(D). lub(E,lam n:nat. X`n`x))";
by (rtac islub_unique 1);
brr (cpo_lub::islub_cf::cpo_cf::prems) 1;
val lub_cf = result();

val const_fun = prove_goal ZF.thy  
    "y:set(E) ==> (lam x:set(D).y): set(D)->set(E)"
  (fn prems => [rtac lam_type 1,rtac (hd prems) 1]);

val prems = goal Limit.thy  (* const_cont *)
    "[|y:set(E); cpo(D); cpo(E)|] ==> (lam x:set(D).y) : cont(D,E)";
by (rtac contI 1);
by (asm_simp_tac ZF_ss 2);
brr(const_fun::cpo_refl::prems) 1;
by (asm_simp_tac(ZF_ss addsimps(chain_in::(cpo_lub RS islub_in)::
    lub_const::prems)) 1);
val const_cont = result();

val prems = goal Limit.thy  (* cf_least *)
    "[|cpo(D); pcpo(E); y:cont(D,E)|]==>rel(cf(D,E),(lam x:set(D).bot(E)),y)";
by (rtac rel_cfI 1);
by (asm_simp_tac ZF_ss 1);
brr(bot_least::bot_in::apply_type::cont_fun::const_cont::
    cpo_cf::(prems@[pcpo_cpo])) 1;
val cf_least = result();

val prems = goal Limit.thy  (* pcpo_cf *)
    "[|cpo(D); pcpo(E)|] ==> pcpo(cf(D,E))";
by (rtac pcpoI 1);
brr(cf_least::bot_in::(const_cont RS cont_cf)::cf_cont::
    cpo_cf::(prems@[pcpo_cpo])) 1;
val pcpo_cf = result();

val prems = goal Limit.thy  (* bot_cf *)
    "[|cpo(D); pcpo(E)|] ==> bot(cf(D,E)) = (lam x:set(D).bot(E))";
by (rtac (bot_unique RS sym) 1);
brr(pcpo_cf::cf_least::(bot_in RS const_cont RS cont_cf)::
    cf_cont::(prems@[pcpo_cpo])) 1;
val bot_cf = result();

(*----------------------------------------------------------------------*)
(* Identity and composition.                                            *)
(*----------------------------------------------------------------------*)

val id_thm = prove_goalw Perm.thy [id_def] "x:X ==> (id(X)`x) = x"
  (fn prems => [simp_tac(ZF_ss addsimps prems) 1]);

val prems = goal Limit.thy  (* id_cont *)
    "cpo(D) ==> id(set(D)):cont(D,D)";
by (rtac contI 1);
by (rtac id_type 1);
by (asm_simp_tac (ZF_ss addsimps[id_thm]) 1);
by (asm_simp_tac(ZF_ss addsimps(id_thm::(cpo_lub RS islub_in)::
    chain_in::(chain_fun RS eta)::prems)) 1);
val id_cont = result();

val comp_cont_apply = cont_fun RSN(2,cont_fun RS comp_fun_apply);

val prems = goal Limit.thy  (* comp_pres_cont *)
    "[| f:cont(D',E); g:cont(D,D'); cpo(D)|] ==> f O g : cont(D,E)";
by (rtac contI 1);
by (stac comp_cont_apply 2);
by (stac comp_cont_apply 5);
by (rtac cont_mono 8);
by (rtac cont_mono 9); (* 15 subgoals *)
brr(comp_fun::cont_fun::cont_map::prems) 1; (* proves all but the lub case *)
by (stac comp_cont_apply 1);
by (stac cont_lub 4);
by (stac cont_lub 6);
by (asm_full_simp_tac(ZF_ss addsimps (* RS: new subgoals contain unknowns *)
    [hd prems RS (hd(tl prems) RS comp_cont_apply),chain_in]) 8);
brr((cpo_lub RS islub_in)::cont_chain::prems) 1;
val comp_pres_cont = result();

val prems = goal Limit.thy  (* comp_mono *)
    "[| f:cont(D',E); g:cont(D,D'); f':cont(D',E); g':cont(D,D');   \
\       rel(cf(D',E),f,f'); rel(cf(D,D'),g,g'); cpo(D); cpo(E) |] ==>   \
\    rel(cf(D,E),f O g,f' O g')";
by (rtac rel_cfI 1); (* extra proof obl: f O g and f' O g' cont. Extra asm cpo(D). *)
by (stac comp_cont_apply 1);
by (stac comp_cont_apply 4);
by (rtac cpo_trans 7);
brr(rel_cf::cont_mono::cont_map::comp_pres_cont::prems) 1;
val comp_mono = result();

val prems = goal Limit.thy  (* chain_cf_comp *)
    "[| chain(cf(D',E),X); chain(cf(D,D'),Y); cpo(D); cpo(E)|] ==>  \
\    chain(cf(D,E),lam n:nat. X`n O Y`n)";
by (rtac chainI 1);
by (asm_simp_tac arith_ss 2);
by (rtac rel_cfI 2);
by (stac comp_cont_apply 2);
by (stac comp_cont_apply 5); 
by (rtac cpo_trans 8); 
by (rtac rel_cf 9);
by (rtac cont_mono 11);
brr(lam_type::comp_pres_cont::cont_cf::(chain_in RS cf_cont)::cont_map::
    chain_rel::rel_cf::nat_succI::prems) 1;
val chain_cf_comp = result();

val prems = goal Limit.thy  (* comp_lubs *)
    "[| chain(cf(D',E),X); chain(cf(D,D'),Y); cpo(D); cpo(D'); cpo(E)|] ==>  \
\    lub(cf(D',E),X) O lub(cf(D,D'),Y) = lub(cf(D,E),lam n:nat. X`n O Y`n)";
by (rtac fun_extension 1);
by (stac lub_cf 3);
brr(comp_fun::(cf_cont RS cont_fun)::(cpo_lub RS islub_in)::cpo_cf::
    chain_cf_comp::prems) 1;
by (cut_facts_tac[hd prems,hd(tl prems)]1);
by (asm_simp_tac(ZF_ss addsimps((chain_in RS cf_cont RSN(3,chain_in RS 
    cf_cont RS comp_cont_apply))::(tl(tl prems)))) 1);
by (stac comp_cont_apply 1);
brr((cpo_lub RS islub_in RS cf_cont)::cpo_cf::prems) 1;
by (asm_simp_tac(ZF_ss addsimps(lub_cf::
 (hd(tl prems)RS chain_cf RSN(2,hd prems RS chain_in RS cf_cont RS cont_lub))::
 (hd(tl prems) RS chain_cf RS cpo_lub RS islub_in)::prems)) 1);
by (cut_inst_tac[("M","lam xa:nat. lam xb:nat. X`xa`(Y`xb`x)")]
   lub_matrix_diag 1);
by (asm_full_simp_tac ZF_ss 3);
by (rtac matrix_chainI 1);
by (asm_simp_tac ZF_ss 1);
by (asm_simp_tac ZF_ss 2); 
by (forward_tac[hd(tl prems) RSN(2,(hd prems RS chain_in RS cf_cont) RS 
    (chain_cf RSN(2,cont_chain)))]1); (* Here, Isabelle was a bitch! *)
by (asm_full_simp_tac ZF_ss 2);
by (assume_tac 1);
by (rtac chain_cf 1);
brr((cont_fun RS apply_type)::(chain_in RS cf_cont)::lam_type::prems) 1;
val comp_lubs = result();

(*----------------------------------------------------------------------*)
(* A couple (out of many) theorems about arithmetic.                    *)
(*----------------------------------------------------------------------*)

val prems = goal Arith.thy  (* le_cases *)
   "[|m:nat; n:nat|] ==> m le n | n le m";
by (safe_tac lemmas_cs);
brr((not_le_iff_lt RS iffD1 RS leI)::nat_into_Ord::prems) 1;
val le_cases = result();

val prems = goal Arith.thy  (* lt_cases *)
   "[|m:nat; n:nat|] ==> m < n | n le m";
by (safe_tac lemmas_cs);
brr((not_le_iff_lt RS iffD1)::nat_into_Ord::prems) 1;
val lt_cases = result();

(*----------------------------------------------------------------------*)
(* Theorems about projpair.                                             *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [projpair_def]  (* projpairI *)
    "!!x. [| e:cont(D,E); p:cont(E,D); p O e = id(set(D));   \
\       rel(cf(E,E))(e O p)(id(set(E)))|] ==> projpair(D,E,e,p)";
by (fast_tac FOL_cs 1);
val projpairI = result();

val prems = goalw Limit.thy [projpair_def]  (* projpairE *)
    "[| projpair(D,E,e,p);   \
\       [| e:cont(D,E); p:cont(E,D); p O e = id(set(D));   \
\          rel(cf(E,E))(e O p)(id(set(E)))|] ==> Q |] ==> Q";
by (rtac (hd(tl prems)) 1);
by (REPEAT(asm_simp_tac(FOL_ss addsimps[hd prems]) 1));
val projpairE = result();

val prems = goal Limit.thy  (* projpair_e_cont *)
    "projpair(D,E,e,p) ==> e:cont(D,E)";
by (rtac projpairE 1);
by (REPEAT(ares_tac prems 1));
val projpair_e_cont = result();

val prems = goal Limit.thy  (* projpair_p_cont *)
    "projpair(D,E,e,p) ==> p:cont(E,D)";
by (rtac projpairE 1);
by (REPEAT(ares_tac prems 1));
val projpair_p_cont = result();

val prems = goal Limit.thy  (* projpair_eq *)
    "projpair(D,E,e,p) ==> p O e = id(set(D))";
by (rtac projpairE 1);
by (REPEAT(ares_tac prems 1));
val projpair_eq = result();

val prems = goal Limit.thy  (* projpair_rel *)
    "projpair(D,E,e,p) ==> rel(cf(E,E))(e O p)(id(set(E)))";
by (rtac projpairE 1);
by (REPEAT(ares_tac prems 1));
val projpair_rel = result();

val projpairDs = [projpair_e_cont,projpair_p_cont,projpair_eq,projpair_rel];

(*----------------------------------------------------------------------*)
(* NB! projpair_e_cont and projpair_p_cont cannot be used repeatedly    *)
(*     at the same time since both match a goal of the form f:cont(X,Y).*)
(*----------------------------------------------------------------------*)

(*----------------------------------------------------------------------*)
(* Uniqueness of embedding projection pairs.                            *)
(*----------------------------------------------------------------------*)

val id_comp = fun_is_rel RS left_comp_id;
val comp_id = fun_is_rel RS right_comp_id;

val prems = goal Limit.thy (* lemma1 *)
    "[|cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p');  \
\      rel(cf(D,E),e,e')|] ==> rel(cf(E,D),p',p)";
val [_,_,p1,p2,_] = prems;
(* The two theorems proj_e_cont and proj_p_cont are useless unless they 
   are used manually, one at a time. Therefore the following contl.     *)
val contl = [p1 RS projpair_e_cont,p1 RS projpair_p_cont,
            p2 RS projpair_e_cont,p2 RS projpair_p_cont];
by (rtac (p2 RS projpair_p_cont RS cont_fun RS id_comp RS subst) 1);
by (rtac (p1 RS projpair_eq RS subst) 1);
by (rtac cpo_trans 1);
brr(cpo_cf::prems) 1; 
(* The following corresponds to EXISTS_TAC, non-trivial instantiation. *)
by (res_inst_tac[("f","p O (e' O p')")]cont_cf 4);
by (stac comp_assoc 1);
brr(cpo_refl::cpo_cf::cont_cf::comp_mono::comp_pres_cont::(contl@prems)) 1;
by (res_inst_tac[("P","%x. rel(cf(E,D),p O e' O p',x)")]
    (p1 RS projpair_p_cont RS cont_fun RS comp_id RS subst) 1);
by (rtac comp_mono 1);
brr(cpo_refl::cpo_cf::cont_cf::comp_mono::comp_pres_cont::id_cont::
    projpair_rel::(contl@prems)) 1;
val lemma1 = result();

val prems = goal Limit.thy (* lemma2 *)
    "[|cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p');  \
\      rel(cf(E,D),p',p)|] ==> rel(cf(D,E),e,e')";
val [_,_,p1,p2,_] = prems;
val contl = [p1 RS projpair_e_cont,p1 RS projpair_p_cont,
            p2 RS projpair_e_cont,p2 RS projpair_p_cont];
by (rtac (p1 RS projpair_e_cont RS cont_fun RS comp_id RS subst) 1);
by (rtac (p2 RS projpair_eq RS subst) 1);
by (rtac cpo_trans 1);
brr(cpo_cf::prems) 1; 
by (res_inst_tac[("f","(e O p) O e'")]cont_cf 4);
by (stac comp_assoc 1);
brr((cpo_cf RS cpo_refl)::cont_cf::comp_mono::comp_pres_cont::(contl@prems)) 1;
by (res_inst_tac[("P","%x. rel(cf(D,E),(e O p) O e',x)")]
    (p2 RS projpair_e_cont RS cont_fun RS id_comp RS subst) 1);
brr((cpo_cf RS cpo_refl)::cont_cf::comp_mono::id_cont::comp_pres_cont::projpair_rel::
    (contl@prems)) 1;
val lemma2 = result();

val prems = goal Limit.thy (* projpair_unique *)
    "[|cpo(D); cpo(E); projpair(D,E,e,p); projpair(D,E,e',p')|] ==>  \
\    (e=e')<->(p=p')";
val [_,_,p1,p2] = prems;
val contl = [p1 RS projpair_e_cont,p1 RS projpair_p_cont,
            p2 RS projpair_e_cont,p2 RS projpair_p_cont];
by (rtac iffI 1);
by (rtac cpo_antisym 1);
by (rtac lemma1 2);
(* First some existentials are instantiated. *)
by (resolve_tac prems 4);
by (resolve_tac prems 4);
by (asm_simp_tac FOL_ss 4);
brr(cpo_cf::cpo_refl::cont_cf::projpair_e_cont::prems) 1;
by (rtac lemma1 1);
brr prems 1;
by (asm_simp_tac FOL_ss 1); 
brr(cpo_cf::cpo_refl::cont_cf::(contl @ prems)) 1;
by (rtac cpo_antisym 1);
by (rtac lemma2 2);
(* First some existentials are instantiated. *)
by (resolve_tac prems 4);
by (resolve_tac prems 4);
by (asm_simp_tac FOL_ss 4);
brr(cpo_cf::cpo_refl::cont_cf::projpair_p_cont::prems) 1;
by (rtac lemma2 1);
brr prems 1;
by (asm_simp_tac FOL_ss 1); 
brr(cpo_cf::cpo_refl::cont_cf::(contl @ prems)) 1;
val projpair_unique = result();

(* Slightly different, more asms, since THE chooses the unique element. *)

val prems = goalw Limit.thy [emb_def,Rp_def] (* embRp *)
    "[|emb(D,E,e); cpo(D); cpo(E)|] ==> projpair(D,E,e,Rp(D,E,e))";
by (rtac theI2 1);
by (assume_tac 2);
by (rtac ((hd prems) RS exE) 1);
by (rtac ex1I 1);
by (assume_tac 1);
by (rtac (projpair_unique RS iffD1) 1);
by (assume_tac 3); (* To instantiate variables. *)
brr (refl::prems) 1;
val embRp = result();

val embI = prove_goalw Limit.thy [emb_def]
    "!!x. projpair(D,E,e,p) ==> emb(D,E,e)"
  (fn prems => [fast_tac FOL_cs 1]);

val prems = goal Limit.thy  (* Rp_unique *)
    "[|projpair(D,E,e,p); cpo(D); cpo(E)|] ==> Rp(D,E,e) = p";
by (rtac (projpair_unique RS iffD1) 1);
by (rtac embRp 3); (* To instantiate variables. *)
brr (embI::refl::prems) 1;
val Rp_unique = result();

val emb_cont = prove_goalw Limit.thy [emb_def]
    "emb(D,E,e) ==> e:cont(D,E)"
  (fn prems => [rtac(hd prems RS exE) 1,rtac projpair_e_cont 1,atac 1]);

(* The following three theorems have cpo asms due to THE (uniqueness). *)

val Rp_cont = embRp RS projpair_p_cont;
val embRp_eq = embRp RS projpair_eq;
val embRp_rel = embRp RS projpair_rel;

val id_apply = prove_goalw Perm.thy [id_def]
    "!!z. x:A ==> id(A)`x = x"
  (fn prems => [asm_simp_tac ZF_ss 1]);

val prems = goal Limit.thy  (* embRp_eq_thm *)
    "[|emb(D,E,e); x:set(D); cpo(D); cpo(E)|] ==> Rp(D,E,e)`(e`x) = x";
by (rtac (comp_fun_apply RS subst) 1);
brr(Rp_cont::emb_cont::cont_fun::prems) 1;
by (stac embRp_eq 1);
brr(id_apply::prems) 1;
val embRp_eq_thm = result();


(*----------------------------------------------------------------------*)
(* The identity embedding.                                              *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [projpair_def]  (* projpair_id *)
    "cpo(D) ==> projpair(D,D,id(set(D)),id(set(D)))";
by (safe_tac lemmas_cs);
brr(id_cont::id_comp::id_type::prems) 1;
by (stac id_comp 1); (* Matches almost anything *)
brr(id_cont::id_type::cpo_refl::cpo_cf::cont_cf::prems) 1;
val projpair_id = result();

val prems = goal Limit.thy  (* emb_id *)
    "cpo(D) ==> emb(D,D,id(set(D)))";
brr(embI::projpair_id::prems) 1;
val emb_id = result();

val prems = goal Limit.thy  (* Rp_id *)
    "cpo(D) ==> Rp(D,D,id(set(D))) = id(set(D))";
brr(Rp_unique::projpair_id::prems) 1;
val Rp_id = result();

(*----------------------------------------------------------------------*)
(* Composition preserves embeddings.                                    *)
(*----------------------------------------------------------------------*)

(* Considerably shorter, only partly due to a simpler comp_assoc. *)
(* Proof in HOL-ST: 70 lines (minus 14 due to comp_assoc complication). *)
(* Proof in Isa/ZF: 23 lines (compared to 56: 60% reduction). *)

val prems = goalw Limit.thy [projpair_def]  (* lemma *)
    "[|emb(D,D',e); emb(D',E,e'); cpo(D); cpo(D'); cpo(E)|] ==>  \
\    projpair(D,E,e' O e,(Rp(D,D',e)) O (Rp(D',E,e')))";
by (safe_tac lemmas_cs);
brr(comp_pres_cont::Rp_cont::emb_cont::prems) 1;
by (rtac (comp_assoc RS subst) 1);
by (res_inst_tac[("t1","e'")](comp_assoc RS ssubst) 1);
by (stac embRp_eq 1); (* Matches everything due to subst/ssubst. *)
brr prems 1;
by (stac comp_id 1);
brr(cont_fun::Rp_cont::embRp_eq::prems) 1;
by (rtac (comp_assoc RS subst) 1);
by (res_inst_tac[("t1","Rp(D,D',e)")](comp_assoc RS ssubst) 1);
by (rtac cpo_trans 1);
brr(cpo_cf::prems) 1;
by (rtac comp_mono 1);
by (rtac cpo_refl 6);
brr(cont_cf::Rp_cont::prems) 7; 
brr(cpo_cf::prems) 6;
by (rtac comp_mono 5);
brr(embRp_rel::prems) 10;
brr((cpo_cf RS cpo_refl)::cont_cf::Rp_cont::prems) 9;
by (stac comp_id 10);
by (rtac embRp_rel 11); 
(* There are 16 subgoals at this point. All are proved immediately by: *)
brr(comp_pres_cont::Rp_cont::id_cont::emb_cont::cont_fun::cont_cf::prems) 1;
val lemma = result();

(* The use of RS is great in places like the following, both ugly in HOL. *)

val emb_comp = lemma RS embI;
val Rp_comp = lemma RS Rp_unique;

(*----------------------------------------------------------------------*)
(* Infinite cartesian product.                                          *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [set_def,iprod_def]  (* iprodI *)
    "!!z. x:(PROD n:nat. set(DD`n)) ==> x:set(iprod(DD))";
by (asm_full_simp_tac ZF_ss 1);
val iprodI = result();

(* Proof with non-reflexive relation approach:
by (rtac CollectI 1);
by (rtac domainI 1);
by (rtac CollectI 1);
by (simp_tac(ZF_ss addsimps prems) 1);
by (rtac (hd prems) 1);
by (simp_tac ZF_ss 1);
by (rtac ballI 1);
by (dtac ((hd prems) RS apply_type) 1);
by (etac CollectE 1);
by (assume_tac 1);
by (rtac rel_I 1);
by (rtac CollectI 1);
by (fast_tac(ZF_cs addSIs prems) 1);
by (rtac ballI 1);
by (simp_tac ZF_ss 1);
by (dtac ((hd prems) RS apply_type) 1);
by (etac CollectE 1);
by (assume_tac 1);
*)

val prems = goalw Limit.thy [set_def,iprod_def]  (* iprodE *)
    "!!z. x:set(iprod(DD)) ==> x:(PROD n:nat. set(DD`n))";
by (asm_full_simp_tac ZF_ss 1);
val iprodE = result();

(* Contains typing conditions in contrast to HOL-ST *)

val prems = goalw Limit.thy [iprod_def] (* rel_iprodI *)
    "[|!!n. n:nat ==> rel(DD`n,f`n,g`n); f:(PROD n:nat. set(DD`n));  \
\      g:(PROD n:nat. set(DD`n))|] ==> rel(iprod(DD),f,g)";
by (rtac rel_I 1);
by (simp_tac ZF_ss 1);
by (safe_tac lemmas_cs);
brr prems 1;
val rel_iprodI = result();

val prems = goalw Limit.thy [iprod_def] (* rel_iprodE *)
    "[|rel(iprod(DD),f,g); n:nat|] ==> rel(DD`n,f`n,g`n)";
by (cut_facts_tac[hd prems RS rel_E]1);
by (asm_full_simp_tac ZF_ss 1);
by (safe_tac lemmas_cs);
by (etac bspec 1);
by (resolve_tac prems 1);
val rel_iprodE = result();

(* Some special theorems like dProdApIn_cpo and other `_cpo' 
   probably not needed in Isabelle, wait and see. *)

val prems = goalw Limit.thy [chain_def]  (* chain_iprod *)
    "[|chain(iprod(DD),X);!!n. n:nat ==> cpo(DD`n); n:nat|] ==>  \
\    chain(DD`n,lam m:nat.X`m`n)";
by (safe_tac lemmas_cs);
by (rtac lam_type 1);
by (rtac apply_type 1);
by (rtac iprodE 1);
by (etac (hd prems RS conjunct1 RS apply_type) 1);
by (resolve_tac prems 1);
by (asm_simp_tac(arith_ss addsimps prems) 1);
by (rtac rel_iprodE 1);
by (asm_simp_tac (arith_ss addsimps prems) 1);
by (resolve_tac prems 1);
val chain_iprod = result();

val prems = goalw Limit.thy [islub_def,isub_def]  (* islub_iprod *)
    "[|chain(iprod(DD),X);!!n. n:nat ==> cpo(DD`n)|] ==>   \
\    islub(iprod(DD),X,lam n:nat. lub(DD`n,lam m:nat.X`m`n))";
by (safe_tac lemmas_cs);
by (rtac iprodI 1);
by (rtac lam_type 1); 
brr((chain_iprod RS cpo_lub RS islub_in)::prems) 1;
by (rtac rel_iprodI 1);
by (asm_simp_tac ZF_ss 1);
(* Here, HOL resolution is handy, Isabelle resolution bad. *)
by (res_inst_tac[("P","%t. rel(DD`na,t,lub(DD`na,lam x:nat. X`x`na))"),
    ("b1","%n. X`n`na")](beta RS subst) 1);
brr((chain_iprod RS cpo_lub RS islub_ub)::iprodE::chain_in::prems) 1;
brr(iprodI::lam_type::(chain_iprod RS cpo_lub RS islub_in)::prems) 1;
by (rtac rel_iprodI 1);
by (asm_simp_tac ZF_ss 1);
brr(islub_least::(chain_iprod RS cpo_lub)::prems) 1;
by (rewtac isub_def);
by (safe_tac lemmas_cs);
by (etac (iprodE RS apply_type) 1);
by (assume_tac 1);
by (asm_simp_tac ZF_ss 1);
by (dtac bspec 1);
by (etac rel_iprodE 2);
brr(lam_type::(chain_iprod RS cpo_lub RS islub_in)::iprodE::prems) 1;
val islub_iprod = result();

val prems = goal Limit.thy (* cpo_iprod *)
    "(!!n. n:nat ==> cpo(DD`n)) ==> cpo(iprod(DD))";
brr(cpoI::poI::[]) 1;
by (rtac rel_iprodI 1); (* not repeated: want to solve 1 and leave 2 unchanged *)
brr(cpo_refl::(iprodE RS apply_type)::iprodE::prems) 1;
by (rtac rel_iprodI 1);
by (dtac rel_iprodE 1);
by (dtac rel_iprodE 2);
brr(cpo_trans::(iprodE RS apply_type)::iprodE::prems) 1;
by (rtac fun_extension 1);
brr(cpo_antisym::rel_iprodE::(iprodE RS apply_type)::iprodE::prems) 1;
brr(islub_iprod::prems) 1;
val cpo_iprod = result();

val prems = goalw Limit.thy [islub_def,isub_def]  (* lub_iprod *)
    "[|chain(iprod(DD),X);!!n. n:nat ==> cpo(DD`n)|] ==>   \
\    lub(iprod(DD),X) = (lam n:nat. lub(DD`n,lam m:nat.X`m`n))";
brr((cpo_lub RS islub_unique)::islub_iprod::cpo_iprod::prems) 1;
val lub_iprod = result();

(*----------------------------------------------------------------------*)
(* The notion of subcpo.                                                *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [subcpo_def]  (* subcpoI *)
    "[|set(D)<=set(E);  \
\      !!x y. [|x:set(D); y:set(D)|] ==> rel(D,x,y)<->rel(E,x,y);  \
\      !!X. chain(D,X) ==> lub(E,X) : set(D)|] ==> subcpo(D,E)";
by (safe_tac lemmas_cs);
by (asm_full_simp_tac(ZF_ss addsimps prems) 2);
by (asm_simp_tac(ZF_ss addsimps prems) 2);
brr(prems@[subsetD]) 1;
val subcpoI = result();

val subcpo_subset = prove_goalw Limit.thy [subcpo_def]  
    "!!x. subcpo(D,E) ==> set(D)<=set(E)"
  (fn prems => [fast_tac FOL_cs 1]);

val subcpo_rel_eq = prove_goalw Limit.thy [subcpo_def]  
    " [|subcpo(D,E); x:set(D); y:set(D)|] ==> rel(D,x,y)<->rel(E,x,y)"
  (fn prems => 
   [trr((hd prems RS conjunct2 RS conjunct1 RS bspec RS bspec)::prems) 1]);

val subcpo_relD1 = subcpo_rel_eq RS iffD1;
val subcpo_relD2 = subcpo_rel_eq RS iffD2;

val subcpo_lub = prove_goalw Limit.thy [subcpo_def]  
    "[|subcpo(D,E); chain(D,X)|] ==> lub(E,X) : set(D)"
  (fn prems => 
   [rtac(hd prems RS conjunct2 RS conjunct2 RS spec RS impE) 1,trr prems 1]);

val prems = goal Limit.thy  (* chain_subcpo *)
    "[|subcpo(D,E); chain(D,X)|] ==> chain(E,X)";
by (rtac chainI 1);
by (rtac Pi_type 1);
brr(chain_fun::prems) 1;
by (rtac subsetD 1);
brr(subcpo_subset::chain_in::(hd prems RS subcpo_relD1)::nat_succI::
    chain_rel::prems) 1;
val chain_subcpo = result();

val prems = goal Limit.thy  (* ub_subcpo *)
    "[|subcpo(D,E); chain(D,X); isub(D,X,x)|] ==> isub(E,X,x)";
brr(isubI::(hd prems RS subcpo_subset RS subsetD)::
    (hd prems RS subcpo_relD1)::prems) 1;
brr(isubD1::prems) 1;
brr((hd prems RS subcpo_relD1)::chain_in::isubD1::isubD2::prems) 1;
val ub_subcpo = result();
        
(* STRIP_TAC and HOL resolution is efficient sometimes. The following
   theorem is proved easily in HOL without intro and elim rules. *)

val prems = goal Limit.thy  (* islub_subcpo *)
    "[|subcpo(D,E); cpo(E); chain(D,X)|] ==> islub(D,X,lub(E,X))";
brr[islubI,isubI]1;
brr(subcpo_lub::(hd prems RS subcpo_relD2)::chain_in::islub_ub::islub_least::
    cpo_lub::(hd prems RS chain_subcpo)::isubD1::(hd prems RS ub_subcpo)::
    prems) 1;
val islub_subcpo = result();

val prems = goal Limit.thy  (* subcpo_cpo *)
    "[|subcpo(D,E); cpo(E)|] ==> cpo(D)";
brr[cpoI,poI]1;
(* Changing the order of the assumptions, otherwise full_simp doesn't work. *)
by (asm_full_simp_tac(ZF_ss addsimps[hd prems RS subcpo_rel_eq]) 1);
brr(cpo_refl::(hd prems RS subcpo_subset RS subsetD)::prems) 1;
by (dtac (imp_refl RS mp) 1);
by (dtac (imp_refl RS mp) 1);
by (asm_full_simp_tac(ZF_ss addsimps[hd prems RS subcpo_rel_eq]) 1);
brr(cpo_trans::(hd prems RS subcpo_subset RS subsetD)::prems) 1;
(* Changing the order of the assumptions, otherwise full_simp doesn't work. *)
by (dtac (imp_refl RS mp) 1);
by (dtac (imp_refl RS mp) 1);
by (asm_full_simp_tac(ZF_ss addsimps[hd prems RS subcpo_rel_eq]) 1);
brr(cpo_antisym::(hd prems RS subcpo_subset RS subsetD)::prems) 1;
brr(islub_subcpo::prems) 1;
val subcpo_cpo = result();

val prems = goal Limit.thy  (* lub_subcpo *)
    "[|subcpo(D,E); cpo(E); chain(D,X)|] ==> lub(D,X) = lub(E,X)";
brr((cpo_lub RS islub_unique)::islub_subcpo::(hd prems RS subcpo_cpo)::prems) 1;
val lub_subcpo = result();

(*----------------------------------------------------------------------*)
(* Making subcpos using mkcpo.                                          *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [set_def,mkcpo_def]  (* mkcpoI *)
    "!!z. [|x:set(D); P(x)|] ==> x:set(mkcpo(D,P))";
by (simp_tac ZF_ss 1);
brr(conjI::prems) 1;
val mkcpoI = result();

(* Old proof where cpos are non-reflexive relations.
by (rewtac set_def); (* Annoying, cannot just rewrite once. *)
by (rtac CollectI 1);
by (rtac domainI 1);
by (rtac CollectI 1);
(* Now, work on subgoal 2 (and 3) to instantiate unknown. *)
by (simp_tac ZF_ss 2);
by (rtac conjI 2);
by (rtac conjI 3);
by (resolve_tac prems 3);
by (simp_tac(ZF_ss addsimps [rewrite_rule[set_def](hd prems)]) 1);
by (resolve_tac prems 1);
by (rtac cpo_refl 1);
by (resolve_tac prems 1);
by (rtac rel_I 1);
by (rtac CollectI 1);
by (fast_tac(ZF_cs addSIs [rewrite_rule[set_def](hd prems)]) 1);
by (simp_tac ZF_ss 1);
brr(conjI::cpo_refl::prems) 1;
*)

val prems = goalw Limit.thy [set_def,mkcpo_def]  (* mkcpoD1 *)
    "!!z. x:set(mkcpo(D,P))==> x:set(D)";
by (asm_full_simp_tac ZF_ss 1);
val mkcpoD1 = result();

val prems = goalw Limit.thy [set_def,mkcpo_def]  (* mkcpoD2 *)
    "!!z. x:set(mkcpo(D,P))==> P(x)";
by (asm_full_simp_tac ZF_ss 1);
val mkcpoD2 = result();

val prems = goalw Limit.thy [rel_def,mkcpo_def]  (* rel_mkcpoE *)
    "!!a. rel(mkcpo(D,P),x,y) ==> rel(D,x,y)";
by (asm_full_simp_tac ZF_ss 1);
val rel_mkcpoE = result();

val rel_mkcpo = prove_goalw Limit.thy [mkcpo_def,rel_def,set_def]
    "!!z. [|x:set(D); y:set(D)|] ==> rel(mkcpo(D,P),x,y) <-> rel(D,x,y)"
 (fn prems => [asm_simp_tac ZF_ss 1]);

(* The HOL proof is simpler, problems due to cpos as purely in ZF. *)
(* And chains as set functions. *)

val prems = goal Limit.thy  (* chain_mkcpo *)
    "chain(mkcpo(D,P),X) ==> chain(D,X)";
by (rtac chainI 1);
(*---begin additional---*)
by (rtac Pi_type 1);
brr(chain_fun::prems) 1;
brr((chain_in RS mkcpoD1)::prems) 1;
(*---end additional---*)
by (rtac (rel_mkcpo RS iffD1) 1);
(*---begin additional---*)
by (rtac mkcpoD1 1); 
by (rtac mkcpoD1 2); 
brr(chain_in::nat_succI::prems) 1; 
(*---end additional---*)
brr(chain_rel::prems) 1;
val chain_mkcpo = result();

val prems = goal Limit.thy  (* subcpo_mkcpo *)
    "[|!!X. chain(mkcpo(D,P),X) ==> P(lub(D,X)); cpo(D)|] ==>   \
\    subcpo(mkcpo(D,P),D)";
brr(subcpoI::subsetI::prems) 1;
by (rtac rel_mkcpo 2);
by (REPEAT(etac mkcpoD1 1)); 
brr(mkcpoI::(cpo_lub RS islub_in)::chain_mkcpo::prems) 1;
val subcpo_mkcpo = result();

(*----------------------------------------------------------------------*)
(* Embedding projection chains of cpos.                                 *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [emb_chain_def]  (* emb_chainI *)
    "[|!!n. n:nat ==> cpo(DD`n);   \
\      !!n. n:nat ==> emb(DD`n,DD`succ(n),ee`n)|] ==> emb_chain(DD,ee)";
by (safe_tac lemmas_cs);
brr prems 1;
val emb_chainI = result();

val emb_chain_cpo = prove_goalw Limit.thy [emb_chain_def] 
    "!!x. [|emb_chain(DD,ee); n:nat|] ==> cpo(DD`n)"
  (fn prems => [fast_tac ZF_cs 1]);

val emb_chain_emb = prove_goalw Limit.thy [emb_chain_def] 
    "!!x. [|emb_chain(DD,ee); n:nat|] ==> emb(DD`n,DD`succ(n),ee`n)"
  (fn prems => [fast_tac ZF_cs 1]);

(*----------------------------------------------------------------------*)
(* Dinf, the inverse Limit.                                             *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [Dinf_def]  (* DinfI *)
    "[|x:(PROD n:nat. set(DD`n));  \
\      !!n. n:nat ==> Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n|] ==>   \
\    x:set(Dinf(DD,ee))";
brr(mkcpoI::iprodI::ballI::prems) 1;
val DinfI = result();

val prems = goalw Limit.thy [Dinf_def]  (* DinfD1 *)
    "x:set(Dinf(DD,ee)) ==> x:(PROD n:nat. set(DD`n))";
by (rtac iprodE 1);
by (rtac mkcpoD1 1);
by (resolve_tac prems 1);
val DinfD1 = result();
val Dinf_prod = DinfD1;

val prems = goalw Limit.thy [Dinf_def]  (* DinfD2 *)
    "[|x:set(Dinf(DD,ee)); n:nat|] ==>   \
\    Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n";
by (asm_simp_tac(ZF_ss addsimps[(hd prems RS mkcpoD2),hd(tl prems)]) 1);
val DinfD2 = result();
val Dinf_eq = DinfD2;

(* At first, rel_DinfI was stated too strongly, because rel_mkcpo was too:
val prems = goalw Limit.thy [Dinf_def]  (* rel_DinfI *)
    "[|!!n. n:nat ==> rel(DD`n,x`n,y`n);  \
\      x:set(Dinf(DD,ee)); y:set(Dinf(DD,ee))|] ==> rel(Dinf(DD,ee),x,y)";
by (rtac (rel_mkcpo RS iffD2) 1);
brr prems 1;
brr(rel_iprodI::rewrite_rule[Dinf_def]DinfD1::prems) 1;
val rel_DinfI = result();
*)

val prems = goalw Limit.thy [Dinf_def]  (* rel_DinfI *)
    "[|!!n. n:nat ==> rel(DD`n,x`n,y`n);  \
\      x:(PROD n:nat. set(DD`n)); y:(PROD n:nat. set(DD`n))|] ==>   \
\    rel(Dinf(DD,ee),x,y)";
by (rtac (rel_mkcpo RS iffD2) 1);
brr(rel_iprodI::iprodI::prems) 1;
val rel_DinfI = result();

val prems = goalw Limit.thy [Dinf_def]  (* rel_Dinf *)
    "[|rel(Dinf(DD,ee),x,y); n:nat|] ==> rel(DD`n,x`n,y`n)";
by (rtac (hd prems RS rel_mkcpoE RS rel_iprodE) 1);
by (resolve_tac prems 1);
val rel_Dinf = result();

val chain_Dinf = prove_goalw Limit.thy [Dinf_def] 
    "chain(Dinf(DD,ee),X) ==> chain(iprod(DD),X)"
  (fn prems => [rtac(hd prems RS chain_mkcpo) 1]);

val prems = goalw Limit.thy [Dinf_def]  (* subcpo_Dinf *)
    "emb_chain(DD,ee) ==> subcpo(Dinf(DD,ee),iprod(DD))";
by (rtac subcpo_mkcpo 1);
by (fold_tac [Dinf_def]);
by (rtac ballI 1);
by (stac lub_iprod 1);
brr(chain_Dinf::(hd prems RS emb_chain_cpo)::[]) 1;
by (asm_simp_tac arith_ss 1);
by (stac (Rp_cont RS cont_lub) 1);
brr(emb_chain_cpo::emb_chain_emb::nat_succI::chain_iprod::chain_Dinf::prems) 1;
(* Useful simplification, ugly in HOL. *)
by (asm_simp_tac(arith_ss addsimps(DinfD2::chain_in::[])) 1);
brr(cpo_iprod::emb_chain_cpo::prems) 1;
val subcpo_Dinf = result();

(* Simple example of existential reasoning in Isabelle versus HOL. *)

val prems = goal Limit.thy  (* cpo_Dinf *)
  "emb_chain(DD,ee) ==> cpo(Dinf(DD,ee))";
by (rtac subcpo_cpo 1);
brr(subcpo_Dinf::cpo_iprod::emb_chain_cpo::prems) 1;;
val cpo_Dinf = result();

(* Again and again the proofs are much easier to WRITE in Isabelle, but 
  the proof steps are essentially the same (I think). *)

val prems = goal Limit.thy  (* lub_Dinf *)
    "[|chain(Dinf(DD,ee),X); emb_chain(DD,ee)|] ==>  \
\    lub(Dinf(DD,ee),X) = (lam n:nat. lub(DD`n,lam m:nat. X`m`n))";
by (stac (subcpo_Dinf RS lub_subcpo) 1);
brr(cpo_iprod::emb_chain_cpo::lub_iprod::chain_Dinf::prems) 1;
val lub_Dinf = result();

(*----------------------------------------------------------------------*)
(* Generalising embedddings D_m -> D_{m+1} to embeddings D_m -> D_n,    *)
(* defined as eps(DD,ee,m,n), via e_less and e_gr.                      *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [e_less_def]  (* e_less_eq *)
    "!!x. m:nat ==> e_less(DD,ee,m,m) = id(set(DD`m))";
by (asm_simp_tac (arith_ss addsimps[diff_self_eq_0]) 1);
val e_less_eq = result();
 
(* ARITH_CONV proves the following in HOL. Would like something similar 
   in Isabelle/ZF. *)

goalw Arith.thy []  (* lemma_succ_sub *)
    "!!z. [|n:nat; m:nat|] ==> succ(m#+n)#-m = succ(n)";
(*Uses add_succ_right the wrong way round!*)
by (asm_simp_tac(nat_ss addsimps [add_succ_right RS sym, diff_add_inverse]) 1);
val lemma_succ_sub = result();

val prems = goalw Limit.thy [e_less_def] (* e_less_add *)
    "!!x. [|m:nat; k:nat|] ==>    \
\         e_less(DD,ee,m,succ(m#+k)) = (ee`(m#+k))O(e_less(DD,ee,m,m#+k))";
by (asm_simp_tac (arith_ss addsimps [lemma_succ_sub,diff_add_inverse]) 1);
val e_less_add = result();

(* Again, would like more theorems about arithmetic. *)
(* Well, HOL has much better support and automation of natural numbers. *)

val add1 = prove_goal Limit.thy
    "!!x. n:nat ==> succ(n) = n #+ 1"
  (fn prems => 
      [asm_simp_tac (arith_ss addsimps[add_succ_right,add_0_right]) 1]);

val prems = goal Limit.thy  (* succ_sub1 *)
    "x:nat ==> 0 < x --> succ(x#-1)=x";
by (res_inst_tac[("n","x")]nat_induct 1);
by (resolve_tac prems 1);
by (fast_tac lt_cs 1);
by (safe_tac lemmas_cs);
by (asm_simp_tac arith_ss 1);
by (asm_simp_tac arith_ss 1);
val succ_sub1 = result();

val prems = goal Limit.thy (* succ_le_pos *)
    "[|m:nat; k:nat|] ==> succ(m) le m #+ k --> 0 < k";
by (res_inst_tac[("n","m")]nat_induct 1);
by (resolve_tac prems 1);
by (rtac impI 1);
by (asm_full_simp_tac(arith_ss addsimps prems) 1);
by (safe_tac lemmas_cs);
by (asm_full_simp_tac(arith_ss addsimps prems) 1); (* Surprise, surprise. *)
val succ_le_pos = result();

val prems = goal Limit.thy  (* lemma_le_exists *)
    "!!z. [|n:nat; m:nat|] ==> m le n --> (EX k:nat. n = m #+ k)";
by (res_inst_tac[("n","m")]nat_induct 1);
by (assume_tac 1);
by (safe_tac lemmas_cs);
by (rtac bexI 1);
by (rtac (add_0 RS sym) 1);
by (assume_tac 1);
by (asm_full_simp_tac arith_ss 1);
(* Great, by luck I found lt_cs. Such cs's and ss's should be documented. *)
by (fast_tac lt_cs 1); 
by (asm_simp_tac (nat_ss addsimps[add_succ, add_succ_right RS sym]) 1);
by (rtac bexI 1);
by (stac (succ_sub1 RS mp) 1);
(* Instantiation. *)
by (rtac refl 3);
by (assume_tac 1);
by (rtac (succ_le_pos RS mp) 1);
by (assume_tac 3); (* Instantiation *)
brr[]1;
by (asm_simp_tac arith_ss 1);
val lemma_le_exists = result();

val prems = goal Limit.thy  (* le_exists *)
    "[|m le n;!!x. [|n=m#+x; x:nat|] ==> Q; m:nat; n:nat|] ==> Q";
by (rtac (lemma_le_exists RS mp RS bexE) 1);
by (rtac (hd(tl prems)) 4);
by (assume_tac 4);
brr prems 1;
val le_exists = result();

val prems = goal Limit.thy  (* e_less_le *)
    "[|m le n; m:nat; n:nat|] ==>   \
\    e_less(DD,ee,m,succ(n)) = ee`n O e_less(DD,ee,m,n)";
by (rtac le_exists 1);
by (resolve_tac prems 1);
by (asm_simp_tac(ZF_ss addsimps(e_less_add::prems)) 1);
brr prems 1;
val e_less_le = result();

(* All theorems assume variables m and n are natural numbers. *)

val prems = goal Limit.thy  (* e_less_succ *)
    "m:nat ==> e_less(DD,ee,m,succ(m)) = ee`m O id(set(DD`m))";
by (asm_simp_tac(arith_ss addsimps(e_less_le::e_less_eq::prems)) 1);
val e_less_succ = result();

val prems = goal Limit.thy  (* e_less_succ_emb *)
    "[|!!n. n:nat ==> emb(DD`n,DD`succ(n),ee`n); m:nat|] ==>   \
\    e_less(DD,ee,m,succ(m)) = ee`m";
by (asm_simp_tac(arith_ss addsimps(e_less_succ::prems)) 1);
by (stac comp_id 1);
brr(emb_cont::cont_fun::refl::prems) 1;
val e_less_succ_emb = result();

(* Compare this proof with the HOL one, here we do type checking. *)
(* In any case the one below was very easy to write. *)

val prems = goal Limit.thy  (* emb_e_less_add *)
    "[|emb_chain(DD,ee); m:nat; k:nat|] ==>   \
\    emb(DD`m,DD`(m#+k),e_less(DD,ee,m,m#+k))";
by (res_inst_tac[("n","k")]nat_induct 1);
by (resolve_tac prems 1);
by (asm_simp_tac(ZF_ss addsimps(add_0_right::e_less_eq::prems)) 1);
brr(emb_id::emb_chain_cpo::prems) 1;
by (asm_simp_tac(ZF_ss addsimps(add_succ_right::e_less_add::prems)) 1);
brr(emb_comp::emb_chain_emb::emb_chain_cpo::add_type::nat_succI::prems) 1;
val emb_e_less_add = result();

val prems = goal Limit.thy  (* emb_e_less *)
    "[|m le n; emb_chain(DD,ee); m:nat; n:nat|] ==>   \
\    emb(DD`m,DD`n,e_less(DD,ee,m,n))";
(* same proof as e_less_le *)
by (rtac le_exists 1);
by (resolve_tac prems 1);
by (asm_simp_tac(ZF_ss addsimps(emb_e_less_add::prems)) 1);
brr prems 1;
val emb_e_less = result();

val comp_mono_eq = prove_goal Limit.thy
    "!!z.[|f=f'; g=g'|] ==> f O g = f' O g'"
  (fn prems => [asm_simp_tac ZF_ss 1]);

(* Typing, typing, typing, three irritating assumptions. Extra theorems
   needed in proof, but no real difficulty. *)
(* Note also the object-level implication for induction on k. This
   must be removed later to allow the theorems to be used for simp. 
   Therefore this theorem is only a lemma. *)

val prems = goal Limit.thy  (* e_less_split_add_lemma *)
    "[| emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    n le k --> \
\    e_less(DD,ee,m,m#+k) = e_less(DD,ee,m#+n,m#+k) O e_less(DD,ee,m,m#+n)";
by (res_inst_tac[("n","k")]nat_induct 1);
by (resolve_tac prems 1);
by (rtac impI 1);
by (asm_full_simp_tac(ZF_ss addsimps
    (le0_iff::add_0_right::e_less_eq::(id_type RS id_comp)::prems)) 1);
by (asm_simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps(add_succ_right::e_less_add::
    add_type::nat_succI::prems)) 1);
(* Again and again, simplification is a pain. When does it work, when not? *)
by (stac e_less_le 1);
brr(add_le_mono::nat_le_refl::add_type::nat_succI::prems) 1;
by (stac comp_assoc 1);
brr(comp_mono_eq::refl::[]) 1;
(* by(asm_simp_tac ZF_ss 1); *)
by (asm_simp_tac(ZF_ss addsimps(e_less_eq::add_type::nat_succI::prems)) 1);
by (stac id_comp 1); (* simp cannot unify/inst right, use brr below(?). *)
brr((emb_e_less_add RS emb_cont RS cont_fun)::refl::nat_succI::prems) 1;
val e_less_split_add_lemma = result();

val e_less_split_add = prove_goal Limit.thy  
    "[| n le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    e_less(DD,ee,m,m#+k) = e_less(DD,ee,m#+n,m#+k) O e_less(DD,ee,m,m#+n)"
  (fn prems => [trr((e_less_split_add_lemma RS mp)::prems) 1]);

val prems = goalw Limit.thy [e_gr_def]  (* e_gr_eq *)
    "!!x. m:nat ==> e_gr(DD,ee,m,m) = id(set(DD`m))";
by (asm_simp_tac (arith_ss addsimps[diff_self_eq_0]) 1);
val e_gr_eq = result();

val prems = goalw Limit.thy [e_gr_def] (* e_gr_add *)
    "!!x. [|n:nat; k:nat|] ==>    \
\         e_gr(DD,ee,succ(n#+k),n) =   \
\         e_gr(DD,ee,n#+k,n) O Rp(DD`(n#+k),DD`succ(n#+k),ee`(n#+k))";
by (asm_simp_tac (arith_ss addsimps [lemma_succ_sub,diff_add_inverse]) 1);
val e_gr_add = result();

val prems = goal Limit.thy  (* e_gr_le *)
    "[|n le m; m:nat; n:nat|] ==>   \
\    e_gr(DD,ee,succ(m),n) = e_gr(DD,ee,m,n) O Rp(DD`m,DD`succ(m),ee`m)";
by (rtac le_exists 1);
by (resolve_tac prems 1);
by (asm_simp_tac(ZF_ss addsimps(e_gr_add::prems)) 1);
brr prems 1;
val e_gr_le = result();

val prems = goal Limit.thy  (* e_gr_succ *)
    "m:nat ==>   \
\    e_gr(DD,ee,succ(m),m) = id(set(DD`m)) O Rp(DD`m,DD`succ(m),ee`m)";
by (asm_simp_tac(arith_ss addsimps(e_gr_le::e_gr_eq::prems)) 1);
val e_gr_succ = result();

(* Cpo asm's due to THE uniqueness. *)

val prems = goal Limit.thy  (* e_gr_succ_emb *)
    "[|emb_chain(DD,ee); m:nat|] ==>   \
\    e_gr(DD,ee,succ(m),m) = Rp(DD`m,DD`succ(m),ee`m)";
by (asm_simp_tac(arith_ss addsimps(e_gr_succ::prems)) 1);
by (stac id_comp 1);
brr(Rp_cont::cont_fun::refl::emb_chain_cpo::emb_chain_emb::nat_succI::prems) 1;
val e_gr_succ_emb = result();

val prems = goal Limit.thy  (* e_gr_fun_add *)
    "[|emb_chain(DD,ee); n:nat; k:nat|] ==>   \
\    e_gr(DD,ee,n#+k,n): set(DD`(n#+k))->set(DD`n)";
by (res_inst_tac[("n","k")]nat_induct 1);
by (resolve_tac prems 1);
by (asm_simp_tac(ZF_ss addsimps(add_0_right::e_gr_eq::id_type::prems)) 1);
by (asm_simp_tac(ZF_ss addsimps(add_succ_right::e_gr_add::prems)) 1);
brr(comp_fun::Rp_cont::cont_fun::emb_chain_emb::emb_chain_cpo::add_type::
    nat_succI::prems) 1;
val e_gr_fun_add = result();

val prems = goal Limit.thy  (* e_gr_fun *)
    "[|n le m; emb_chain(DD,ee); m:nat; n:nat|] ==>   \
\    e_gr(DD,ee,m,n): set(DD`m)->set(DD`n)";
by (rtac le_exists 1);
by (resolve_tac prems 1);
by (asm_simp_tac(ZF_ss addsimps(e_gr_fun_add::prems)) 1);
brr prems 1;
val e_gr_fun = result();

val prems = goal Limit.thy  (* e_gr_split_add_lemma *)
    "[| emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    m le k --> \
\    e_gr(DD,ee,n#+k,n) = e_gr(DD,ee,n#+m,n) O e_gr(DD,ee,n#+k,n#+m)";
by (res_inst_tac[("n","k")]nat_induct 1);
by (resolve_tac prems 1);
by (rtac impI 1);
by (asm_full_simp_tac(ZF_ss addsimps
    (le0_iff::add_0_right::e_gr_eq::(id_type RS comp_id)::prems)) 1);
by (asm_simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps(add_succ_right::e_gr_add::
    add_type::nat_succI::prems)) 1);
(* Again and again, simplification is a pain. When does it work, when not? *)
by (stac e_gr_le 1);
brr(add_le_mono::nat_le_refl::add_type::nat_succI::prems) 1;
by (stac comp_assoc 1);
brr(comp_mono_eq::refl::[]) 1;
(* New direct subgoal *)
by (asm_simp_tac(ZF_ss addsimps(e_gr_eq::add_type::nat_succI::prems)) 1);
by (stac comp_id 1); (* simp cannot unify/inst right, use brr below(?). *)
brr(e_gr_fun::add_type::refl::add_le_self::nat_succI::prems) 1;
val e_gr_split_add_lemma = result();

val e_gr_split_add = prove_goal Limit.thy  
    "[| m le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    e_gr(DD,ee,n#+k,n) = e_gr(DD,ee,n#+m,n) O e_gr(DD,ee,n#+k,n#+m)"
  (fn prems => [trr((e_gr_split_add_lemma RS mp)::prems) 1]);

val e_less_cont = prove_goal Limit.thy  
    "[|m le n; emb_chain(DD,ee); m:nat; n:nat|] ==>   \
\    e_less(DD,ee,m,n):cont(DD`m,DD`n)"
  (fn prems => [trr(emb_cont::emb_e_less::prems) 1]);

val prems = goal Limit.thy  (* e_gr_cont_lemma *)
    "[|emb_chain(DD,ee); m:nat; n:nat|] ==>   \
\    n le m --> e_gr(DD,ee,m,n):cont(DD`m,DD`n)";
by (res_inst_tac[("n","m")]nat_induct 1);
by (resolve_tac prems 1);
by (asm_full_simp_tac(ZF_ss addsimps
    (le0_iff::e_gr_eq::nat_0I::prems)) 1);
brr(impI::id_cont::emb_chain_cpo::nat_0I::prems) 1;
by (asm_full_simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps(e_gr_le::prems)) 1);
brr(comp_pres_cont::Rp_cont::emb_chain_cpo::emb_chain_emb::nat_succI::prems) 1;
by (asm_simp_tac(ZF_ss addsimps(e_gr_eq::nat_succI::prems)) 1);
brr(id_cont::emb_chain_cpo::nat_succI::prems) 1;
val e_gr_cont_lemma = result();

val prems = goal Limit.thy  (* e_gr_cont *)
    "[|n le m; emb_chain(DD,ee); m:nat; n:nat|] ==>   \
\    e_gr(DD,ee,m,n):cont(DD`m,DD`n)";
brr((e_gr_cont_lemma RS mp)::prems) 1;
val e_gr_cont = result();

(* Considerably shorter.... 57 against 26 *)

val prems = goal Limit.thy  (* e_less_e_gr_split_add *)
    "[|n le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>   \
\    e_less(DD,ee,m,m#+n) = e_gr(DD,ee,m#+k,m#+n) O e_less(DD,ee,m,m#+k)";
(* Use mp to prepare for induction. *)
by (rtac mp 1);
by (resolve_tac prems 2);
by (res_inst_tac[("n","k")]nat_induct 1);
by (resolve_tac prems 1);
by (asm_full_simp_tac(ZF_ss addsimps
    (le0_iff::add_0_right::e_gr_eq::e_less_eq::(id_type RS id_comp)::prems)) 1);
by (simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps(add_succ_right::e_gr_le::e_less_le::
   add_le_self::nat_le_refl::add_le_mono::add_type::prems)) 1);
by (stac comp_assoc 1);
by (res_inst_tac[("s1","ee`(m#+x)")](comp_assoc RS subst) 1);
by (stac embRp_eq 1);
brr(emb_chain_emb::add_type::emb_chain_cpo::nat_succI::prems) 1;
by (stac id_comp 1);
brr((e_less_cont RS cont_fun)::add_type::add_le_self::refl::prems) 1;
by (asm_full_simp_tac(ZF_ss addsimps(e_gr_eq::nat_succI::add_type::prems)) 1);
by (stac id_comp 1);
brr((e_less_cont RS cont_fun)::add_type::nat_succI::add_le_self::refl::prems) 1;
val e_less_e_gr_split_add = result();

(* Again considerably shorter, and easy to obtain from the previous thm. *)

val prems = goal Limit.thy  (* e_gr_e_less_split_add *)
    "[|m le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>   \
\    e_gr(DD,ee,n#+m,n) = e_gr(DD,ee,n#+k,n) O e_less(DD,ee,n#+m,n#+k)";
(* Use mp to prepare for induction. *)
by (rtac mp 1);
by (resolve_tac prems 2);
by (res_inst_tac[("n","k")]nat_induct 1);
by (resolve_tac prems 1);
by (asm_full_simp_tac(arith_ss addsimps
    (add_0_right::e_gr_eq::e_less_eq::(id_type RS id_comp)::prems)) 1);
by (simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps(add_succ_right::e_gr_le::e_less_le::
   add_le_self::nat_le_refl::add_le_mono::add_type::prems)) 1);
by (stac comp_assoc 1);
by (res_inst_tac[("s1","ee`(n#+x)")](comp_assoc RS subst) 1);
by (stac embRp_eq 1);
brr(emb_chain_emb::add_type::emb_chain_cpo::nat_succI::prems) 1;
by (stac id_comp 1);
brr((e_less_cont RS cont_fun)::add_type::add_le_mono::nat_le_refl::refl::
    prems) 1;
by (asm_full_simp_tac(ZF_ss addsimps(e_less_eq::nat_succI::add_type::prems)) 1);
by (stac comp_id 1);
brr((e_gr_cont RS cont_fun)::add_type::nat_succI::add_le_self::refl::prems) 1;
val e_gr_e_less_split_add = result();

val prems = goalw Limit.thy [eps_def]  (* emb_eps *)
    "[|m le n; emb_chain(DD,ee); m:nat; n:nat|] ==>   \
\    emb(DD`m,DD`n,eps(DD,ee,m,n))";
by (asm_simp_tac(ZF_ss addsimps prems) 1);
brr(emb_e_less::prems) 1;
val emb_eps = result();

val prems = goalw Limit.thy [eps_def]  (* eps_fun *)
    "[|emb_chain(DD,ee); m:nat; n:nat|] ==>   \
\    eps(DD,ee,m,n): set(DD`m)->set(DD`n)";
by (rtac (expand_if RS iffD2) 1);
by (safe_tac lemmas_cs);
brr((e_less_cont RS cont_fun)::prems) 1;
brr((not_le_iff_lt RS iffD1 RS leI)::e_gr_fun::nat_into_Ord::prems) 1;
val eps_fun = result();

val eps_id = prove_goalw Limit.thy [eps_def]  
    "n:nat ==> eps(DD,ee,n,n) = id(set(DD`n))"
  (fn prems => [simp_tac(ZF_ss addsimps(e_less_eq::nat_le_refl::prems)) 1]);

val eps_e_less_add = prove_goalw Limit.thy [eps_def]
    "[|m:nat; n:nat|] ==> eps(DD,ee,m,m#+n) = e_less(DD,ee,m,m#+n)"
  (fn prems => [simp_tac(ZF_ss addsimps(add_le_self::prems)) 1]);

val eps_e_less = prove_goalw Limit.thy [eps_def]
    "[|m le n; m:nat; n:nat|] ==> eps(DD,ee,m,n) = e_less(DD,ee,m,n)"
  (fn prems => [simp_tac(ZF_ss addsimps prems) 1]);

val shift_asm = imp_refl RS mp;

val prems = goalw Limit.thy [eps_def]  (* eps_e_gr_add *)
    "[|n:nat; k:nat|] ==> eps(DD,ee,n#+k,n) = e_gr(DD,ee,n#+k,n)";
by (rtac (expand_if RS iffD2) 1);
by (safe_tac lemmas_cs);
by (etac leE 1);
(* Must control rewriting by instantiating a variable. *)
by (asm_full_simp_tac(arith_ss addsimps
     ((hd prems RS nat_into_Ord RS not_le_iff_lt RS iff_sym)::nat_into_Ord::
      add_le_self::prems)) 1);
by (asm_simp_tac(ZF_ss addsimps(e_less_eq::e_gr_eq::prems)) 1);
val eps_e_gr_add = result();

val prems = goalw Limit.thy []  (* eps_e_gr *)
    "[|n le m; m:nat; n:nat|] ==> eps(DD,ee,m,n) = e_gr(DD,ee,m,n)";
by (rtac le_exists 1);
by (resolve_tac prems 1);
by (asm_simp_tac(ZF_ss addsimps(eps_e_gr_add::prems)) 1);
brr prems 1;
val eps_e_gr = result();

val prems = goal Limit.thy  (* eps_succ_ee *)
    "[|!!n. n:nat ==> emb(DD`n,DD`succ(n),ee`n); m:nat|] ==>  \
\    eps(DD,ee,m,succ(m)) = ee`m";
by (asm_simp_tac(arith_ss addsimps(eps_e_less::le_succ_iff::e_less_succ_emb::
   prems)) 1);
val eps_succ_ee = result();

val prems = goal Limit.thy  (* eps_succ_Rp *)
    "[|emb_chain(DD,ee); m:nat|] ==>  \
\    eps(DD,ee,succ(m),m) = Rp(DD`m,DD`succ(m),ee`m)";
by (asm_simp_tac(arith_ss addsimps(eps_e_gr::le_succ_iff::e_gr_succ_emb::
   prems)) 1);
val eps_succ_Rp = result();

val prems = goal Limit.thy  (* eps_cont *)
    "[|emb_chain(DD,ee); m:nat; n:nat|] ==> eps(DD,ee,m,n): cont(DD`m,DD`n)";
by (rtac (le_cases RS disjE) 1);
by (resolve_tac prems 1);
by (rtac (hd(rev prems)) 1);
by (asm_simp_tac(ZF_ss addsimps(eps_e_less::e_less_cont::prems)) 1);
by (asm_simp_tac(ZF_ss addsimps(eps_e_gr::e_gr_cont::prems)) 1);
val eps_cont = result();

(* Theorems about splitting. *)

val prems = goal Limit.thy  (* eps_split_add_left *)
    "[|n le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,m,m#+k) = eps(DD,ee,m#+n,m#+k) O eps(DD,ee,m,m#+n)";
by (asm_simp_tac(arith_ss addsimps 
    (eps_e_less::add_le_self::add_le_mono::prems)) 1);
brr(e_less_split_add::prems) 1;
val eps_split_add_left = result();

val prems = goal Limit.thy  (* eps_split_add_left_rev *)
    "[|n le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,m,m#+n) = eps(DD,ee,m#+k,m#+n) O eps(DD,ee,m,m#+k)";
by (asm_simp_tac(arith_ss addsimps 
    (eps_e_less_add::eps_e_gr::add_le_self::add_le_mono::prems)) 1);
brr(e_less_e_gr_split_add::prems) 1;
val eps_split_add_left_rev = result();

val prems = goal Limit.thy  (* eps_split_add_right *)
    "[|m le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,n#+k,n) = eps(DD,ee,n#+m,n) O eps(DD,ee,n#+k,n#+m)";
by (asm_simp_tac(arith_ss addsimps 
    (eps_e_gr::add_le_self::add_le_mono::prems)) 1);
brr(e_gr_split_add::prems) 1;
val eps_split_add_right = result();

val prems = goal Limit.thy  (* eps_split_add_right_rev *)
    "[|m le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,n#+m,n) = eps(DD,ee,n#+k,n) O eps(DD,ee,n#+m,n#+k)";
by (asm_simp_tac(arith_ss addsimps 
    (eps_e_gr_add::eps_e_less::add_le_self::add_le_mono::prems)) 1);
brr(e_gr_e_less_split_add::prems) 1;
val eps_split_add_right_rev = result();

(* Arithmetic, little support in Isabelle/ZF. *)

val prems = goal Arith.thy  (* add_le_elim1 *)
    "[|m#+n le m#+k; m:nat; n:nat; k:nat|] ==> n le k";
by (rtac mp 1);
by (resolve_tac prems 2);
by (res_inst_tac[("n","n")]nat_induct 1);
by (resolve_tac prems 1);
by (simp_tac (arith_ss addsimps prems) 1);
by (safe_tac lemmas_cs);
by (asm_full_simp_tac (ZF_ss addsimps 
    (not_le_iff_lt::succ_le_iff::add_succ::add_succ_right::
     add_type::nat_into_Ord::prems)) 1);
by (etac lt_asym 1);
by (assume_tac 1);
by (asm_full_simp_tac (ZF_ss addsimps add_succ_right::succ_le_iff::prems) 1);
by (asm_full_simp_tac (ZF_ss addsimps 
    (add_succ::le_iff::add_type::nat_into_Ord::prems)) 1);
by (safe_tac lemmas_cs);
by (etac lt_irrefl 1);
val add_le_elim1 = result();

val prems = goal Limit.thy  (* le_exists_lemma *)
    "[|n le k; k le m;  \
\      !!p q. [|p le q; k=n#+p; m=n#+q; p:nat; q:nat|] ==> R; \
\      m:nat; n:nat; k:nat|]==>R";
by (rtac (hd prems RS le_exists) 1);
by (rtac (le_exists) 1);
by (rtac le_trans 1);
(* Careful *)
by (resolve_tac prems 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
by (assume_tac 2);
by (assume_tac 2);
by (cut_facts_tac[hd prems,hd(tl prems)]1);
by (asm_full_simp_tac arith_ss 1);
by (etac add_le_elim1 1);
brr prems 1;
val le_exists_lemma = result();

val prems = goal Limit.thy  (* eps_split_left_le *)
    "[|m le k; k le n; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac le_exists_lemma 1);
brr prems 1;
by (asm_simp_tac ZF_ss 1);
brr(eps_split_add_left::prems) 1;
val eps_split_left_le = result();

val prems = goal Limit.thy  (* eps_split_left_le_rev *)
    "[|m le n; n le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac le_exists_lemma 1);
brr prems 1;
by (asm_simp_tac ZF_ss 1);
brr(eps_split_add_left_rev::prems) 1;
val eps_split_left_le_rev = result();

val prems = goal Limit.thy  (* eps_split_right_le *)
    "[|n le k; k le m; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac le_exists_lemma 1);
brr prems 1;
by (asm_simp_tac ZF_ss 1);
brr(eps_split_add_right::prems) 1;
val eps_split_right_le = result();

val prems = goal Limit.thy  (* eps_split_right_le_rev *)
    "[|n le m; m le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac le_exists_lemma 1);
brr prems 1;
by (asm_simp_tac ZF_ss 1);
brr(eps_split_add_right_rev::prems) 1;
val eps_split_right_le_rev = result();

(* The desired two theorems about `splitting'. *)

val prems = goal Limit.thy  (* eps_split_left *)
    "[|m le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac (le_cases RS disjE) 1);
by (rtac eps_split_right_le_rev 4);
by (assume_tac 4);
by (rtac (le_cases RS disjE) 3);
by (rtac eps_split_left_le 5);
by (assume_tac 6);
by (rtac eps_split_left_le_rev 10);
brr prems 1; (* 20 trivial subgoals *)
val eps_split_left = result();

val prems = goal Limit.thy  (* eps_split_right *)
    "[|n le k; emb_chain(DD,ee); m:nat; n:nat; k:nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac (le_cases RS disjE) 1);
by (rtac eps_split_left_le_rev 3);
by (assume_tac 3);
by (rtac (le_cases RS disjE) 8);
by (rtac eps_split_right_le 10);
by (assume_tac 11);
by (rtac eps_split_right_le_rev 15);
brr prems 1; (* 20 trivial subgoals *)
val eps_split_right = result();

(*----------------------------------------------------------------------*)
(* That was eps: D_m -> D_n, NEXT rho_emb: D_n -> Dinf.                 *)
(*----------------------------------------------------------------------*)

(* Considerably shorter. *)

val prems = goalw Limit.thy [rho_emb_def] (* rho_emb_fun *)
    "[|emb_chain(DD,ee); n:nat|] ==>   \
\    rho_emb(DD,ee,n): set(DD`n) -> set(Dinf(DD,ee))";
brr(lam_type::DinfI::(eps_cont RS cont_fun RS apply_type)::prems) 1;
by (asm_simp_tac arith_ss 1);
by (rtac (le_cases RS disjE) 1);
by (rtac nat_succI 1);
by (assume_tac 1);
by (resolve_tac prems 1);
(* The easiest would be to apply add1 everywhere also in the assumptions, 
   but since x le y is x<succ(y) simplification does too much with this thm. *)
by (stac eps_split_right_le 1);
by (assume_tac 2);
by (asm_simp_tac(ZF_ss addsimps (add1::[])) 1);
brr(add_le_self::nat_0I::nat_succI::prems) 1;
by (asm_simp_tac(ZF_ss addsimps(eps_succ_Rp::prems)) 1);
by (stac comp_fun_apply 1);
brr(eps_fun::nat_succI::(Rp_cont RS cont_fun)::emb_chain_emb::
    emb_chain_cpo::refl::prems) 1;
(* Now the second part of the proof. Slightly different than HOL. *)
by (asm_simp_tac(ZF_ss addsimps(eps_e_less::nat_succI::prems)) 1);
by (etac (le_iff RS iffD1 RS disjE) 1);
by (asm_simp_tac(ZF_ss addsimps(e_less_le::prems)) 1);
by (stac comp_fun_apply 1);
brr(e_less_cont::cont_fun::emb_chain_emb::emb_cont::prems) 1;
by (stac embRp_eq_thm 1);
brr(emb_chain_emb::(e_less_cont RS cont_fun RS apply_type)::emb_chain_cpo::
    nat_succI::prems) 1;
by (asm_simp_tac(ZF_ss addsimps(eps_e_less::prems)) 1);
by (dtac shift_asm 1);
by (asm_full_simp_tac(ZF_ss addsimps(eps_succ_Rp::e_less_eq::id_apply::
   nat_succI::prems)) 1);
val rho_emb_fun = result();

val rho_emb_apply1 = prove_goalw Limit.thy [rho_emb_def]
    "!!z. x:set(DD`n) ==> rho_emb(DD,ee,n)`x = (lam m:nat. eps(DD,ee,n,m)`x)"
  (fn prems => [asm_simp_tac ZF_ss 1]);

val rho_emb_apply2 = prove_goalw Limit.thy [rho_emb_def]
    "!!z. [|x:set(DD`n); m:nat|] ==> rho_emb(DD,ee,n)`x`m = eps(DD,ee,n,m)`x"
  (fn prems => [asm_simp_tac ZF_ss 1]);

val rho_emb_id = prove_goal Limit.thy 
  "!!z. [| x:set(DD`n); n:nat|] ==> rho_emb(DD,ee,n)`x`n = x"
  (fn prems => [asm_simp_tac(ZF_ss addsimps[rho_emb_apply2,eps_id,id_thm]) 1]);

(* Shorter proof, 23 against 62. *)

val prems = goalw Limit.thy [] (* rho_emb_cont *)
    "[|emb_chain(DD,ee); n:nat|] ==>   \
\    rho_emb(DD,ee,n): cont(DD`n,Dinf(DD,ee))";
by (rtac contI 1);
brr(rho_emb_fun::prems) 1;
by (rtac rel_DinfI 1);
by (SELECT_GOAL(rewtac rho_emb_def) 1);
by (asm_simp_tac ZF_ss 1);
brr((eps_cont RS cont_mono)::Dinf_prod::apply_type::rho_emb_fun::prems) 1;
(* Continuity, different order, slightly different proofs. *)
by (stac lub_Dinf 1);
by (rtac chainI 1);
brr(lam_type::(rho_emb_fun RS apply_type)::chain_in::prems) 1;
by (asm_simp_tac arith_ss 1);
by (rtac rel_DinfI 1);
by (asm_simp_tac(arith_ss addsimps (rho_emb_apply2::chain_in::[])) 1);
brr((eps_cont RS cont_mono)::chain_rel::Dinf_prod::
    (rho_emb_fun RS apply_type)::chain_in::nat_succI::prems) 1;
(* Now, back to the result of applying lub_Dinf *)
by (asm_simp_tac(arith_ss addsimps (rho_emb_apply2::chain_in::[])) 1);
by (stac rho_emb_apply1 1);
brr((cpo_lub RS islub_in)::emb_chain_cpo::prems) 1;
by (rtac fun_extension 1);
brr(lam_type::(eps_cont RS cont_fun RS apply_type)::(cpo_lub RS islub_in)::
    emb_chain_cpo::prems) 1;
brr(cont_chain::eps_cont::emb_chain_cpo::prems) 1;
by (asm_simp_tac arith_ss 1);
by (asm_simp_tac(ZF_ss addsimps((eps_cont RS cont_lub)::prems)) 1);
val rho_emb_cont = result();

(* 32 vs 61, using safe_tac with imp in asm would be unfortunate (5steps) *)

val prems = goalw Limit.thy [] (* lemma1 *)
    "[|m le n; emb_chain(DD,ee); x:set(Dinf(DD,ee)); m:nat; n:nat|] ==>   \
\    rel(DD`n,e_less(DD,ee,m,n)`(x`m),x`n)";
by (rtac impE 1 THEN atac 3 THEN rtac(hd prems) 2);  (* For induction proof *)
by (res_inst_tac[("n","n")]nat_induct 1);
by (rtac impI 2);
by (asm_full_simp_tac (arith_ss addsimps (e_less_eq::prems)) 2);
by (stac id_thm 2);
brr(apply_type::Dinf_prod::cpo_refl::emb_chain_cpo::nat_0I::prems) 1;
by (asm_full_simp_tac (arith_ss addsimps [le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (dtac mp 1 THEN atac 1);
by (rtac cpo_trans 1);
by (stac e_less_le 2);
brr(emb_chain_cpo::nat_succI::prems) 1;
by (stac comp_fun_apply 1);
brr((emb_chain_emb RS emb_cont)::e_less_cont::cont_fun::apply_type::
    Dinf_prod::prems) 1;
by (res_inst_tac[("y","x`xa")](emb_chain_emb RS emb_cont RS cont_mono) 1);
brr((e_less_cont RS cont_fun)::apply_type::Dinf_prod::prems) 1;
by (res_inst_tac[("x1","x"),("n1","xa")](Dinf_eq RS subst) 1);
by (rtac (comp_fun_apply RS subst) 3);
by (res_inst_tac
  [("P",
    "%z. rel(DD ` succ(xa), \
\    (ee ` xa O Rp(?DD46(xa) ` xa,?DD46(xa) ` succ(xa),?ee46(xa) ` xa)) ` \
\            (x ` succ(xa)),z)")](id_thm RS subst) 6);
by (rtac rel_cf 7); 
(* Dinf and cont_fun doesn't go well together, both Pi(_,%x._). *)
(* brr solves 11 of 12 subgoals *)
brr((hd(tl(tl prems)) RS Dinf_prod RS apply_type)::cont_fun::Rp_cont::
    e_less_cont::emb_cont::emb_chain_emb::emb_chain_cpo::apply_type::
    embRp_rel::(disjI1 RS (le_succ_iff RS iffD2))::nat_succI::prems) 1;
by (asm_full_simp_tac (arith_ss addsimps (e_less_eq::prems)) 1);
by (stac id_thm 1);
brr(apply_type::Dinf_prod::cpo_refl::emb_chain_cpo::nat_succI::prems) 1;
val lemma1 = result();

(* 18 vs 40 *)

val prems = goalw Limit.thy [] (* lemma2 *)
    "[|n le m; emb_chain(DD,ee); x:set(Dinf(DD,ee)); m:nat; n:nat|] ==>   \
\    rel(DD`n,e_gr(DD,ee,m,n)`(x`m),x`n)";
by (rtac impE 1 THEN atac 3 THEN rtac(hd prems) 2);  (* For induction proof *)
by (res_inst_tac[("n","m")]nat_induct 1);
by (rtac impI 2);
by (asm_full_simp_tac (arith_ss addsimps (e_gr_eq::prems)) 2);
by (stac id_thm 2);
brr(apply_type::Dinf_prod::cpo_refl::emb_chain_cpo::nat_0I::prems) 1;
by (asm_full_simp_tac (arith_ss addsimps [le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (dtac mp 1 THEN atac 1);
by (stac e_gr_le 1);
by (stac comp_fun_apply 4);
by (stac Dinf_eq 7);
brr(emb_chain_emb::emb_chain_cpo::Rp_cont::e_gr_cont::cont_fun::emb_cont::
    apply_type::Dinf_prod::nat_succI::prems) 1;
by (asm_full_simp_tac (arith_ss addsimps (e_gr_eq::prems)) 1);
by (stac id_thm 1);
brr(apply_type::Dinf_prod::cpo_refl::emb_chain_cpo::nat_succI::prems) 1;
val lemma2 = result();

val prems = goalw ZF.thy [if_def]
  "[| P==>R(a); ~P==>R(b) |] ==> R(if(P,a,b))";
by (excluded_middle_tac"P"1);
by (ALLGOALS(asm_simp_tac ZF_ss THEN' rtac theI2));
by (ALLGOALS(asm_full_simp_tac FOL_ss));
brr(ex1I::refl::prems) 1;
val if_case = result();

val prems = goalw Limit.thy [eps_def] (* eps1 *)
    "[|emb_chain(DD,ee); x:set(Dinf(DD,ee)); m:nat; n:nat|] ==>   \
\    rel(DD`n,eps(DD,ee,m,n)`(x`m),x`n)";
by (rtac if_case 1);
brr(lemma1::(not_le_iff_lt RS iffD1 RS leI RS lemma2)::nat_into_Ord::prems) 1;
val eps1 = result();

(* The following theorem is needed/useful due to type check for rel_cfI, 
   but also elsewhere. 
   Look for occurences of rel_cfI, rel_DinfI, etc to evaluate the problem. *)

val prems = goal Limit.thy (* lam_Dinf_cont *)
  "[| emb_chain(DD,ee); n:nat |] ==> \
\  (lam x:set(Dinf(DD,ee)). x`n) : cont(Dinf(DD,ee),DD`n)";
by (rtac contI 1);
brr(lam_type::apply_type::Dinf_prod::prems) 1;
by (asm_simp_tac ZF_ss 1);
brr(rel_Dinf::prems) 1;
by (stac beta 1);
brr(cpo_Dinf::islub_in::cpo_lub::prems) 1;
by (asm_simp_tac(ZF_ss addsimps(chain_in::lub_Dinf::prems)) 1);
val lam_Dinf_cont = result();

val prems = goalw Limit.thy  [rho_proj_def] (* rho_projpair *)
    "[| emb_chain(DD,ee); n:nat |] ==> \
\    projpair(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n),rho_proj(DD,ee,n))";
by (rtac projpairI 1);
brr(rho_emb_cont::prems) 1;
(* lemma used, introduced because same fact needed below due to rel_cfI. *)
brr(lam_Dinf_cont::prems) 1;
(*-----------------------------------------------*)
(* This part is 7 lines, but 30 in HOL (75% reduction!) *)
by (rtac fun_extension 1);
by (stac id_thm 3);
by (stac comp_fun_apply 4);
by (stac beta 7);
by (stac rho_emb_id 8);
brr(comp_fun::id_type::lam_type::rho_emb_fun::(Dinf_prod RS apply_type)::
    apply_type::refl::prems) 1;
(*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
by (rtac rel_cfI 1); (* ------------------>>>Yields type cond, not in HOL *)
by (stac id_thm 1);
by (stac comp_fun_apply 2);
by (stac beta 5);
by (stac rho_emb_apply1 6);
by (rtac rel_DinfI 7); (* ------------------>>>Yields type cond, not in HOL *)
by (stac beta 7);
brr(eps1::lam_type::rho_emb_fun::eps_fun:: (* Dinf_prod bad with lam_type *)
    (Dinf_prod RS apply_type)::refl::prems) 1;
brr(apply_type::eps_fun::Dinf_prod::comp_pres_cont::rho_emb_cont::
    lam_Dinf_cont::id_cont::cpo_Dinf::emb_chain_cpo::prems) 1;
val rho_projpair = result();

val prems = goalw Limit.thy [emb_def]
  "[| emb_chain(DD,ee); n:nat |] ==> emb(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))";
brr(exI::rho_projpair::prems) 1;
val emb_rho_emb = result();

val prems = goal Limit.thy 
  "[| emb_chain(DD,ee); n:nat |] ==>   \
\  rho_proj(DD,ee,n) : cont(Dinf(DD,ee),DD`n)";
brr(rho_projpair::projpair_p_cont::prems) 1;
val rho_proj_cont = result();

(*----------------------------------------------------------------------*)
(* Commutivity and universality.                                        *)
(*----------------------------------------------------------------------*)

val prems = goalw Limit.thy [commute_def]  (* commuteI *)
  "[| !!n. n:nat ==> emb(DD`n,E,r(n));   \
\     !!m n. [|m le n; m:nat; n:nat|] ==> r(n) O eps(DD,ee,m,n) = r(m) |] ==>  \
\  commute(DD,ee,E,r)";
by (safe_tac lemmas_cs);
brr prems 1;
val commuteI = result();

val prems = goalw Limit.thy [commute_def]  (* commute_emb *)
  "!!z. [| commute(DD,ee,E,r); n:nat |] ==> emb(DD`n,E,r(n))";
by (fast_tac ZF_cs 1);
val commute_emb = result();

val prems = goalw Limit.thy [commute_def]  (* commute_eq *)
  "!!z. [| commute(DD,ee,E,r); m le n; m:nat; n:nat |] ==>   \
\       r(n) O eps(DD,ee,m,n) = r(m) ";
by (fast_tac ZF_cs 1);
val commute_eq = result();

(* Shorter proof: 11 vs 46 lines. *)

val prems = goal Limit.thy (* rho_emb_commute *)
  "emb_chain(DD,ee) ==> commute(DD,ee,Dinf(DD,ee),rho_emb(DD,ee))";
by (rtac commuteI 1);
brr(emb_rho_emb::prems) 1;
by (rtac fun_extension 1);       (* Manual instantiation in HOL. *)
by (stac comp_fun_apply 3);
by (rtac fun_extension 6); (* Next, clean up and instantiate unknowns *)
brr(comp_fun::rho_emb_fun::eps_fun::Dinf_prod::apply_type::prems) 1; 
by (asm_simp_tac
    (ZF_ss addsimps(rho_emb_apply2::(eps_fun RS apply_type)::prems)) 1);
by (rtac (comp_fun_apply RS subst) 1);
by (rtac (eps_split_left RS subst) 4);
brr(eps_fun::refl::prems) 1;
val rho_emb_commute = result();

val le_succ = prove_goal Arith.thy "n:nat ==> n le succ(n)"
 (fn prems =>
   [REPEAT (ares_tac
    ((disjI1 RS(le_succ_iff RS iffD2))::le_refl::nat_into_Ord::prems) 1)]);

(* Shorter proof: 21 vs 83 (106 - 23, due to OAssoc complication) *)

val prems = goal Limit.thy (* commute_chain *)
  "[| commute(DD,ee,E,r); emb_chain(DD,ee); cpo(E) |] ==>  \
\  chain(cf(E,E),lam n:nat. r(n) O Rp(DD`n,E,r(n)))";
val emb_r = hd prems RS commute_emb; (* To avoid BACKTRACKING !! *)
by (rtac chainI 1);
brr(lam_type::cont_cf::comp_pres_cont::emb_r::Rp_cont::emb_cont::
    emb_chain_cpo::prems) 1;
by (asm_simp_tac arith_ss 1);
by (res_inst_tac[("r1","r"),("m1","n")](commute_eq RS subst) 1);
brr(le_succ::nat_succI::prems) 1;
by (stac Rp_comp 1);
brr(emb_eps::emb_r::emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (rtac (comp_assoc RS subst) 1);   (* Remember that comp_assoc is simpler in Isa *)
by (res_inst_tac[("r1","r(succ(n))")](comp_assoc RS ssubst) 1);
by (rtac comp_mono 1);
brr(comp_pres_cont::eps_cont::emb_eps::emb_r::Rp_cont::emb_cont::
    emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (res_inst_tac[("b","r(succ(n))")](comp_id RS subst) 1); (* 1 subst too much *)
by (rtac comp_mono 2);
brr(comp_pres_cont::eps_cont::emb_eps::emb_id::emb_r::Rp_cont::emb_cont::
    cont_fun::emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (stac comp_id 1); (* Undo's "1 subst too much", typing next anyway *)
brr(cont_fun::Rp_cont::emb_cont::emb_r::cpo_refl::cont_cf::cpo_cf::
    emb_chain_cpo::embRp_rel::emb_eps::le_succ::nat_succI::prems) 1;
val commute_chain = result();

val prems = goal Limit.thy (* rho_emb_chain *)
  "emb_chain(DD,ee) ==>  \
\  chain(cf(Dinf(DD,ee),Dinf(DD,ee)),   \
\        lam n:nat. rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))";
brr(commute_chain::rho_emb_commute::cpo_Dinf::prems) 1;
val rho_emb_chain = result();

val prems = goal Limit.thy (* rho_emb_chain_apply1 *)
  "[| emb_chain(DD,ee); x:set(Dinf(DD,ee)) |] ==>  \
\  chain(Dinf(DD,ee),   \
\        lam n:nat.   \
\         (rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))`x)";
by (cut_facts_tac[hd(tl prems) RS (hd prems RS (rho_emb_chain RS chain_cf))]1);
by (asm_full_simp_tac ZF_ss 1);
val rho_emb_chain_apply1 = result();

val prems = goal Limit.thy
  "[| chain(iprod(DD),X); emb_chain(DD,ee); n:nat |] ==>  \
\  chain(DD`n,lam m:nat. X `m `n)";
brr(chain_iprod::emb_chain_cpo::prems) 1;
val chain_iprod_emb_chain = result();

val prems = goal Limit.thy (* rho_emb_chain_apply2 *)
  "[| emb_chain(DD,ee); x:set(Dinf(DD,ee)); n:nat |] ==>  \
\  chain  \
\   (DD`n,   \
\    lam xa:nat.  \
\     (rho_emb(DD, ee, xa) O Rp(DD ` xa, Dinf(DD, ee),rho_emb(DD, ee, xa))) ` \
\      x ` n)";
by (cut_facts_tac
   [hd(tl(tl prems)) RS (hd prems RS (hd(tl prems) RS (hd prems RS 
    (rho_emb_chain_apply1 RS chain_Dinf RS chain_iprod_emb_chain))))]1);
by (asm_full_simp_tac ZF_ss 1);
val rho_emb_chain_apply2 = result();

(* Shorter proof: 32 vs 72 (roughly), Isabelle proof has lemmas. *)

val prems = goal Limit.thy (* rho_emb_lub *)
  "emb_chain(DD,ee) ==>  \
\  lub(cf(Dinf(DD,ee),Dinf(DD,ee)),   \
\      lam n:nat. rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))) = \
\  id(set(Dinf(DD,ee)))";
by (rtac cpo_antisym 1);
by (rtac cpo_cf 1); (* Instantiate variable, continued below (would loop otherwise) *)
brr(cpo_Dinf::prems) 1; 
by (rtac islub_least 1);
brr(cpo_lub::rho_emb_chain::cpo_cf::cpo_Dinf::isubI::cont_cf::id_cont::prems) 1;
by (asm_simp_tac ZF_ss 1);
brr(embRp_rel::emb_rho_emb::emb_chain_cpo::cpo_Dinf::prems) 1;
by (rtac rel_cfI 1);
by (asm_simp_tac
    (ZF_ss addsimps(id_thm::lub_cf::rho_emb_chain::cpo_Dinf::prems)) 1);
by (rtac rel_DinfI 1); (* Addtional assumptions *)
by (stac lub_Dinf 1);
brr(rho_emb_chain_apply1::prems) 1;  
brr(Dinf_prod::(cpo_lub RS islub_in)::id_cont::cpo_Dinf::cpo_cf::cf_cont::
    rho_emb_chain::rho_emb_chain_apply1::(id_cont RS cont_cf)::prems) 2;
by (asm_simp_tac ZF_ss 1);
by (rtac dominate_islub 1);
by (rtac cpo_lub 3);
brr(rho_emb_chain_apply2::emb_chain_cpo::prems) 3;
by (res_inst_tac[("x1","x`n")](chain_const RS chain_fun) 3);
brr(islub_const::apply_type::Dinf_prod::emb_chain_cpo::chain_fun::
    rho_emb_chain_apply2::prems) 2;
by (rtac dominateI 1);
by (assume_tac 1); 
by (asm_simp_tac ZF_ss 1);
by (stac comp_fun_apply 1);
brr(cont_fun::Rp_cont::emb_cont::emb_rho_emb::cpo_Dinf::emb_chain_cpo::prems) 1;
by (stac ((rho_projpair RS Rp_unique)) 1);
by (SELECT_GOAL(rewtac rho_proj_def) 5);
by (asm_simp_tac ZF_ss 5);
by (stac rho_emb_id 5);
brr(cpo_refl::cpo_Dinf::apply_type::Dinf_prod::emb_chain_cpo::prems) 1;
val rho_emb_lub = result();

val prems = goal Limit.thy (* theta_chain, almost same prf as commute_chain *)
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \
\  chain(cf(E,G),lam n:nat. f(n) O Rp(DD`n,E,r(n)))";
val emb_r = hd prems RS commute_emb;     (* Used in the rest of the FILE *)
val emb_f = hd(tl prems) RS commute_emb; (* Used in the rest of the FILE *)
by (rtac chainI 1);
brr(lam_type::cont_cf::comp_pres_cont::emb_r::emb_f::
    Rp_cont::emb_cont::emb_chain_cpo::prems) 1;
by (asm_simp_tac arith_ss 1);
by (res_inst_tac[("r1","r"),("m1","n")](commute_eq RS subst) 1);
by (res_inst_tac[("r1","f"),("m1","n")](commute_eq RS subst) 5);
brr(le_succ::nat_succI::prems) 1;
by (stac Rp_comp 1);
brr(emb_eps::emb_r::emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (rtac (comp_assoc RS subst) 1);   (* Remember that comp_assoc is simpler in Isa *)
by (res_inst_tac[("r1","f(succ(n))")](comp_assoc RS ssubst) 1);
by (rtac comp_mono 1);
brr(comp_pres_cont::eps_cont::emb_eps::emb_r::emb_f::Rp_cont::
    emb_cont::emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (res_inst_tac[("b","f(succ(n))")](comp_id RS subst) 1); (* 1 subst too much *)
by (rtac comp_mono 2);
brr(comp_pres_cont::eps_cont::emb_eps::emb_id::emb_r::emb_f::Rp_cont::
    emb_cont::cont_fun::emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (stac comp_id 1); (* Undo's "1 subst too much", typing next anyway *)
brr(cont_fun::Rp_cont::emb_cont::emb_r::emb_f::cpo_refl::cont_cf::
    cpo_cf::emb_chain_cpo::embRp_rel::emb_eps::le_succ::nat_succI::prems) 1;
val theta_chain = result();

val prems = goal Limit.thy (* theta_proj_chain, same prf as theta_chain *)
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \
\  chain(cf(G,E),lam n:nat. r(n) O Rp(DD`n,G,f(n)))";
by (rtac chainI 1);
brr(lam_type::cont_cf::comp_pres_cont::emb_r::emb_f::
    Rp_cont::emb_cont::emb_chain_cpo::prems) 1;
by (asm_simp_tac arith_ss 1);
by (res_inst_tac[("r1","r"),("m1","n")](commute_eq RS subst) 1);
by (res_inst_tac[("r1","f"),("m1","n")](commute_eq RS subst) 5);
brr(le_succ::nat_succI::prems) 1;
by (stac Rp_comp 1);
brr(emb_eps::emb_f::emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (rtac (comp_assoc RS subst) 1);   (* Remember that comp_assoc is simpler in Isa *)
by (res_inst_tac[("r1","r(succ(n))")](comp_assoc RS ssubst) 1);
by (rtac comp_mono 1);
brr(comp_pres_cont::eps_cont::emb_eps::emb_r::emb_f::Rp_cont::
    emb_cont::emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (res_inst_tac[("b","r(succ(n))")](comp_id RS subst) 1); (* 1 subst too much *)
by (rtac comp_mono 2);
brr(comp_pres_cont::eps_cont::emb_eps::emb_id::emb_r::emb_f::Rp_cont::
    emb_cont::cont_fun::emb_chain_cpo::le_succ::nat_succI::prems) 1;
by (stac comp_id 1); (* Undo's "1 subst too much", typing next anyway *)
brr(cont_fun::Rp_cont::emb_cont::emb_r::emb_f::cpo_refl::cont_cf::
    cpo_cf::emb_chain_cpo::embRp_rel::emb_eps::le_succ::nat_succI::prems) 1;
val theta_proj_chain = result();

(* Simplification with comp_assoc is possible inside a lam-abstraction,
   because it does not have assumptions. If it had, as the HOL-ST theorem 
   too strongly has, we would be in deep trouble due to the lack of proper
   conditional rewriting (a HOL contrib provides something that works). *)

(* Controlled simplification inside lambda: introduce lemmas *)

val prems = goal Limit.thy
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G); x:nat |] ==>  \
\  r(x) O Rp(DD ` x, G, f(x)) O f(x) O Rp(DD ` x, E, r(x)) =  \
\  r(x) O Rp(DD ` x, E, r(x))";
by (res_inst_tac[("s1","f(x)")](comp_assoc RS subst) 1);
by (stac embRp_eq 1);
by (stac id_comp 4);
brr(cont_fun::Rp_cont::emb_r::emb_f::emb_chain_cpo::refl::prems) 1;
val lemma = result();

val lemma_assoc = prove_goal Limit.thy "a O b O c O d = a O (b O c) O d"
  (fn prems => [simp_tac (ZF_ss addsimps[comp_assoc]) 1]);

fun elem n l = if n = 1 then hd l else elem(n-1)(tl l);

(* Shorter proof (but lemmas): 19 vs 79 (103 - 24, due to OAssoc)  *)

val prems = goalw Limit.thy [projpair_def,rho_proj_def] (* theta_projpair *)
  "[| lub(cf(E,E), lam n:nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));  \
\     commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \  
\  projpair   \
\   (E,G,   \
\    lub(cf(E,G), lam n:nat. f(n) O Rp(DD`n,E,r(n))),  \
\    lub(cf(G,E), lam n:nat. r(n) O Rp(DD`n,G,f(n))))";
by (safe_tac lemmas_cs);
by (stac comp_lubs 3);
(* The following one line is 15 lines in HOL, and includes existentials. *)
brr(cf_cont::islub_in::cpo_lub::cpo_cf::theta_chain::theta_proj_chain::prems) 1;
by (simp_tac (ZF_ss addsimps[comp_assoc]) 1);
by (simp_tac (ZF_ss addsimps[(tl prems) MRS lemma]) 1);
by (stac comp_lubs 2);
brr(cf_cont::islub_in::cpo_lub::cpo_cf::theta_chain::theta_proj_chain::prems) 1;
by (simp_tac (ZF_ss addsimps[comp_assoc]) 1);
by (simp_tac (ZF_ss addsimps[
   [elem 3 prems,elem 2 prems,elem 4 prems,elem 6 prems, elem 5 prems] 
   MRS lemma]) 1);
by (rtac dominate_islub 1);
by (rtac cpo_lub 2);
brr(commute_chain::emb_f::islub_const::cont_cf::id_cont::cpo_cf::
    chain_fun::chain_const::prems) 2;
by (rtac dominateI 1);
by (assume_tac 1); 
by (asm_simp_tac ZF_ss 1);
brr(embRp_rel::emb_f::emb_chain_cpo::prems) 1;
val theta_projpair = result();

val prems = goalw Limit.thy [emb_def] (* emb_theta *)
  "[| lub(cf(E,E), lam n:nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));  \
\     commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \  
\  emb(E,G,lub(cf(E,G), lam n:nat. f(n) O Rp(DD`n,E,r(n))))";
by (rtac exI 1);
by (rtac (prems MRS theta_projpair) 1);
val emb_theta = result();

val prems = goal Limit.thy (* mono_lemma *)
  "[| g:cont(D,D'); cpo(D); cpo(D'); cpo(E) |] ==>  \
\  (lam f : cont(D',E). f O g) : mono(cf(D',E),cf(D,E))";
by (rtac monoI 1);
by (REPEAT(dtac cf_cont 2));
by (asm_simp_tac ZF_ss 2);
by (rtac comp_mono 2);
by (SELECT_GOAL(rewrite_goals_tac[set_def,cf_def]) 1);
by (asm_simp_tac ZF_ss 1);
brr(lam_type::comp_pres_cont::cpo_cf::cpo_refl::cont_cf::prems) 1;
val mono_lemma = result();

(* PAINFUL: wish condrew with difficult conds on term bound in lam-abs. *)
(* Introduces need for lemmas. *)

val prems = goal Limit.thy
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G); n:nat |] ==>  \  
\  (lam na:nat. (lam f:cont(E, G). f O r(n)) `  \
\  ((lam n:nat. f(n) O Rp(DD ` n, E, r(n))) ` na)) =  \
\   (lam na:nat. (f(na) O Rp(DD ` na, E, r(na))) O r(n))";
by (rtac fun_extension 1);
by (stac beta 3);
by (stac beta 4);
by (stac beta 5);
by (rtac lam_type 1);
by (stac beta 1);
by (ALLGOALS(asm_simp_tac (ZF_ss addsimps prems)));
brr(lam_type::comp_pres_cont::Rp_cont::emb_cont::emb_r::emb_f::
    emb_chain_cpo::prems) 1;
val lemma = result();

val prems = goal Limit.thy (* chain_lemma *)
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G); n:nat |] ==>  \  
\  chain(cf(DD`n,G),lam x:nat. (f(x) O Rp(DD ` x, E, r(x))) O r(n))";
by (cut_facts_tac[(rev(tl(rev prems)) MRS theta_chain) RS 
    (elem 5 prems RS (elem 4 prems RS ((elem 6 prems RS 
    (elem 3 prems RS emb_chain_cpo)) RS (elem 6 prems RS 
    (emb_r RS emb_cont RS mono_lemma RS mono_chain)))))]1);
by (rtac ((prems MRS lemma) RS subst) 1);
by (assume_tac 1);
val chain_lemma = result();

val prems = goalw Limit.thy [suffix_def] (* suffix_lemma *)
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G); cpo(DD`x); x:nat |] ==>  \  
\  suffix(lam n:nat. (f(n) O Rp(DD`n,E,r(n))) O r(x),x) = (lam n:nat. f(x))";
by (simp_tac (arith_ss addsimps prems) 1);
by (rtac fun_extension 1); 
brr(lam_type::comp_fun::cont_fun::Rp_cont::emb_cont::emb_r::emb_f::
    add_type::emb_chain_cpo::prems) 1;
by (asm_simp_tac ZF_ss 1);
by (res_inst_tac[("r1","r"),("m1","x")](commute_eq RS subst) 1);
brr(emb_r::add_le_self::add_type::prems) 1;
by (stac comp_assoc 1);
by (stac lemma_assoc 1);
by (stac embRp_eq 1);
by (stac id_comp 4);
by (stac ((hd(tl prems) RS commute_eq)) 5); (* avoid eta_contraction:=true. *)
brr(emb_r::add_type::eps_fun::add_le_self::refl::emb_chain_cpo::prems) 1;
val suffix_lemma = result();

val mediatingI = prove_goalw Limit.thy [mediating_def]
  "[|emb(E,G,t);!!n.n:nat ==> f(n) = t O r(n) |]==>mediating(E,G,r,f,t)"
 (fn prems => [safe_tac lemmas_cs,trr prems 1]);

val mediating_emb = prove_goalw Limit.thy [mediating_def]
  "!!z. mediating(E,G,r,f,t) ==> emb(E,G,t)"
 (fn prems => [fast_tac ZF_cs 1]);

val mediating_eq = prove_goalw Limit.thy [mediating_def]
  "!!z. [| mediating(E,G,r,f,t); n:nat |] ==> f(n) = t O r(n)"
 (fn prems => [fast_tac ZF_cs 1]);

val prems = goal Limit.thy (* lub_universal_mediating *)
  "[| lub(cf(E,E), lam n:nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));  \
\     commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \  
\  mediating(E,G,r,f,lub(cf(E,G), lam n:nat. f(n) O Rp(DD`n,E,r(n))))";
brr(mediatingI::emb_theta::prems) 1;
by (res_inst_tac[("b","r(n)")](lub_const RS subst) 1);
by (stac comp_lubs 3);
brr(cont_cf::emb_cont::emb_r::cpo_cf::theta_chain::chain_const::
    emb_chain_cpo::prems) 1;
by (simp_tac ZF_ss 1);
by (rtac (lub_suffix RS subst) 1);
brr(chain_lemma::cpo_cf::emb_chain_cpo::prems) 1;
by (stac (tl prems MRS suffix_lemma) 1);
by (stac lub_const 3);
brr(cont_cf::emb_cont::emb_f::cpo_cf::emb_chain_cpo::refl::prems) 1;
val lub_universal_mediating = result();

val prems = goal Limit.thy (* lub_universal_unique *)
  "[| mediating(E,G,r,f,t);    \
\     lub(cf(E,E), lam n:nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));   \
\     commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>   \
\  t = lub(cf(E,G), lam n:nat. f(n) O Rp(DD`n,E,r(n)))";
by (res_inst_tac[("b","t")](comp_id RS subst) 1);
by (rtac (hd(tl prems) RS subst) 2);
by (res_inst_tac[("b","t")](lub_const RS subst) 2);
by (stac comp_lubs 4);
by (simp_tac (ZF_ss addsimps(comp_assoc::(hd prems RS mediating_eq)::prems)) 9);
brr(cont_fun::emb_cont::mediating_emb::cont_cf::cpo_cf::chain_const::
    commute_chain::emb_chain_cpo::prems) 1;
val lub_universal_unique = result();

(*---------------------------------------------------------------------*)
(* Dinf yields the inverse_limit, stated as rho_emb_commute and        *)
(* Dinf_universal.                                                     *)
(*---------------------------------------------------------------------*)

val prems = goal Limit.thy (* Dinf_universal *)
  "[| commute(DD,ee,G,f); emb_chain(DD,ee); cpo(G) |] ==>   \
\  mediating   \
\   (Dinf(DD,ee),G,rho_emb(DD,ee),f,   \
\    lub(cf(Dinf(DD,ee),G),   \
\        lam n:nat. f(n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))) &  \
\  (ALL t. mediating(Dinf(DD,ee),G,rho_emb(DD,ee),f,t) -->  \
\    t = lub(cf(Dinf(DD,ee),G),   \
\        lam n:nat. f(n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))))";
by (safe_tac lemmas_cs);
brr(lub_universal_mediating::rho_emb_commute::rho_emb_lub::cpo_Dinf::prems) 1;
brr(lub_universal_unique::rho_emb_commute::rho_emb_lub::cpo_Dinf::prems) 1;
val Dinf_universal = result();

