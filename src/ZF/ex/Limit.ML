(*  Title:      ZF/ex/Limit
    ID:         $Id$
    Author:     Sten Agerholm

The inverse limit construction.

(Proofs tidied up considerably by lcp)
*)
   
val nat_linear_le = [nat_into_Ord,nat_into_Ord] MRS Ord_linear_le;

(*----------------------------------------------------------------------*)
(* Useful goal commands.                                                *)
(*----------------------------------------------------------------------*)

val brr = fn thl => fn n => by (REPEAT(ares_tac thl n));

(*----------------------------------------------------------------------*)
(* Basic results.                                                       *)
(*----------------------------------------------------------------------*)

Goalw [set_def] "x \\<in> fst(D) ==> x \\<in> set(D)";
by (assume_tac 1);
qed "set_I";

Goalw [rel_def] "<x,y>:snd(D) ==> rel(D,x,y)";
by (assume_tac 1);
qed "rel_I";

Goalw [rel_def] "rel(D,x,y) ==> <x,y>:snd(D)";
by (assume_tac 1);
qed "rel_E";

(*----------------------------------------------------------------------*)
(* I/E/D rules for po and cpo.                                          *)
(*----------------------------------------------------------------------*)

Goalw [po_def] "[|po(D); x \\<in> set(D)|] ==> rel(D,x,x)";
by (Blast_tac 1);
qed "po_refl";

Goalw [po_def] "[|po(D); rel(D,x,y); rel(D,y,z); x \\<in> set(D);  \
\                 y \\<in> set(D); z \\<in> set(D)|] ==> rel(D,x,z)";
by (Blast_tac 1);
qed "po_trans";

Goalw [po_def]
    "[|po(D); rel(D,x,y); rel(D,y,x); x \\<in> set(D); y \\<in> set(D)|] ==> x = y";
by (Blast_tac 1);
qed "po_antisym";

val prems = Goalw [po_def]
    "[| !!x. x \\<in> set(D) ==> rel(D,x,x);   \
\       !!x y z. [| rel(D,x,y); rel(D,y,z); x \\<in> set(D); y \\<in> set(D); z \\<in> set(D)|] ==> \
\                rel(D,x,z);  \
\       !!x y. [| rel(D,x,y); rel(D,y,x); x \\<in> set(D); y \\<in> set(D)|] ==> x=y |] ==> \
\    po(D)";
by (blast_tac (claset() addIs prems) 1);
qed "poI";

val prems = Goalw [cpo_def]
    "[| po(D); !!X. chain(D,X) ==> islub(D,X,x(D,X))|] ==> cpo(D)";
by (blast_tac (claset() addIs prems) 1);
qed "cpoI";

Goalw [cpo_def] "cpo(D) ==> po(D)";
by (Blast_tac 1);
qed "cpo_po";

Goal "[|cpo(D); x \\<in> set(D)|] ==> rel(D,x,x)";
by (blast_tac (claset() addIs [po_refl, cpo_po]) 1);
qed "cpo_refl";

Addsimps [cpo_refl];
AddSIs   [cpo_refl];
AddTCs   [cpo_refl];

Goal "[|cpo(D); rel(D,x,y); rel(D,y,z); x \\<in> set(D);  \
\       y \\<in> set(D); z \\<in> set(D)|] ==> rel(D,x,z)";
by (blast_tac (claset() addIs [cpo_po, po_trans]) 1);
qed "cpo_trans";

Goal "[|cpo(D); rel(D,x,y); rel(D,y,x); x \\<in> set(D); y \\<in> set(D)|] ==> x = y";
by (blast_tac (claset() addIs [cpo_po, po_antisym]) 1);
qed "cpo_antisym";

val [cpo,chain,ex] = Goalw [cpo_def] 
  "[|cpo(D); chain(D,X);  !!x. islub(D,X,x) ==> R|] ==> R";
by (rtac (chain RS (cpo RS conjunct2 RS spec RS mp) RS exE) 1); 
by (etac ex 1);
qed "cpo_islub";

(*----------------------------------------------------------------------*)
(* Theorems about isub and islub.                                       *)
(*----------------------------------------------------------------------*)

Goalw [islub_def] "islub(D,X,x) ==> isub(D,X,x)";
by (Asm_simp_tac 1);
qed "islub_isub";

Goalw [islub_def,isub_def] "islub(D,X,x) ==> x \\<in> set(D)";
by (Asm_simp_tac 1);
qed "islub_in";

Goalw [islub_def,isub_def] "[|islub(D,X,x); n \\<in> nat|] ==> rel(D,X`n,x)";
by (Asm_simp_tac 1);
qed "islub_ub";

Goalw [islub_def] "[|islub(D,X,x); isub(D,X,y)|] ==> rel(D,x,y)";
by (Blast_tac 1);
qed "islub_least";

val prems = Goalw [islub_def]  (* islubI *)
    "[|isub(D,X,x); !!y. isub(D,X,y) ==> rel(D,x,y)|] ==> islub(D,X,x)";
by (blast_tac (claset() addIs prems) 1);
qed "islubI";

val prems = Goalw [isub_def]  (* isubI *)
    "[|x \\<in> set(D);  !!n. n \\<in> nat ==> rel(D,X`n,x)|] ==> isub(D,X,x)";
by (blast_tac (claset() addIs prems) 1);
qed "isubI";

val prems = Goalw [isub_def]  (* isubE *)
    "[|isub(D,X,x); [|x \\<in> set(D);  !!n. n \\<in> nat==>rel(D,X`n,x)|] ==> P \
\    |] ==> P";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "isubE";

Goalw [isub_def] "isub(D,X,x) ==> x \\<in> set(D)";
by (Asm_simp_tac 1);
qed "isubD1";

Goalw [isub_def] "[|isub(D,X,x); n \\<in> nat|]==>rel(D,X`n,x)";
by (Asm_simp_tac 1);
qed "isubD2";

Goal "[|islub(D,X,x); islub(D,X,y); cpo(D)|] ==> x = y";
by (blast_tac (claset() addIs [cpo_antisym,islub_least,
                               islub_isub,islub_in]) 1);
qed "islub_unique";

(*----------------------------------------------------------------------*)
(* lub gives the least upper bound of chains.                           *)
(*----------------------------------------------------------------------*)

Goalw [lub_def] "[|chain(D,X); cpo(D)|] ==> islub(D,X,lub(D,X))";
by (best_tac (claset() addEs [cpo_islub] addIs [theI, islub_unique]) 1);
qed "cpo_lub";

(*----------------------------------------------------------------------*)
(* Theorems about chains.                                               *)
(*----------------------------------------------------------------------*)

val prems = Goalw [chain_def]
 "[|X \\<in> nat->set(D);  !!n. n \\<in> nat ==> rel(D,X`n,X`succ(n))|] ==> chain(D,X)";
by (blast_tac (claset() addIs prems) 1);
qed "chainI";

Goalw [chain_def] "chain(D,X) ==> X \\<in> nat -> set(D)";
by (Asm_simp_tac 1);
qed "chain_fun";

Goalw [chain_def] "[|chain(D,X); n \\<in> nat|] ==> X`n \\<in> set(D)";
by (blast_tac (claset() addDs [apply_type]) 1);
qed "chain_in";

Goalw [chain_def] "[|chain(D,X); n \\<in> nat|] ==> rel(D, X ` n, X ` succ(n))";
by (Blast_tac 1);
qed "chain_rel";

Addsimps [chain_in, chain_rel];
AddTCs   [chain_fun, chain_in, chain_rel];

Goal "[|chain(D,X); cpo(D); n \\<in> nat; m \\<in> nat|] ==> rel(D,X`n,(X`(m #+ n)))";
by (induct_tac "m" 1);
by (auto_tac (claset() addIs [cpo_trans], simpset()));  
qed "chain_rel_gen_add";

Goal  (* chain_rel_gen *)
    "[|n le m; chain(D,X); cpo(D); m \\<in> nat|] ==> rel(D,X`n,X`m)";
by (ftac lt_nat_in_nat 1 THEN etac nat_succI 1);
by (etac rev_mp 1);  (*prepare the induction*)
by (induct_tac "m" 1);
by (auto_tac (claset() addIs [cpo_trans],
	      simpset() addsimps [le_iff]));
qed "chain_rel_gen";

(*----------------------------------------------------------------------*)
(* Theorems about pcpos and bottom.                                     *)
(*----------------------------------------------------------------------*)

val prems = Goalw [pcpo_def]  (* pcpoI *)
    "[|!!y. y \\<in> set(D)==>rel(D,x,y); x \\<in> set(D); cpo(D)|]==>pcpo(D)";
by (auto_tac (claset() addIs prems, simpset()));
qed "pcpoI";

Goalw [pcpo_def] "pcpo(D) ==> cpo(D)";
by (etac conjunct1 1);
qed "pcpo_cpo";

Goalw [pcpo_def] (* pcpo_bot_ex1 *)
    "pcpo(D) ==> \\<exists>! x. x \\<in> set(D) & (\\<forall>y \\<in> set(D). rel(D,x,y))";
by (blast_tac (claset() addIs [cpo_antisym]) 1);
qed "pcpo_bot_ex1";

Goalw [bot_def] (* bot_least *)
    "[| pcpo(D); y \\<in> set(D)|] ==> rel(D,bot(D),y)";
by (best_tac (claset() addIs [pcpo_bot_ex1 RS theI2]) 1);
qed "bot_least";

Goalw [bot_def] (* bot_in *)
    "pcpo(D) ==> bot(D):set(D)";
by (best_tac (claset() addIs [pcpo_bot_ex1 RS theI2]) 1);
qed "bot_in";

AddTCs [pcpo_cpo, bot_least, bot_in];

val prems = Goal  (* bot_unique *)
    "[| pcpo(D); x \\<in> set(D); !!y. y \\<in> set(D) ==> rel(D,x,y)|] ==> x = bot(D)";
by (blast_tac (claset() addIs ([cpo_antisym,pcpo_cpo,bot_in,bot_least]@
                               prems)) 1);
qed "bot_unique";

(*----------------------------------------------------------------------*)
(* Constant chains and lubs and cpos.                                   *)
(*----------------------------------------------------------------------*)

Goalw [chain_def] "[|x \\<in> set(D); cpo(D)|] ==> chain(D,(\\<lambda>n \\<in> nat. x))";
by (asm_simp_tac (simpset() addsimps [lam_type, nat_succI]) 1);
qed "chain_const";

Goalw [islub_def,isub_def] 
   "[|x \\<in> set(D); cpo(D)|] ==> islub(D,(\\<lambda>n \\<in> nat. x),x)";
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "islub_const";

Goal "[|x \\<in> set(D); cpo(D)|] ==> lub(D,\\<lambda>n \\<in> nat. x) = x";
by (blast_tac (claset() addIs [islub_unique, cpo_lub,
			       chain_const, islub_const]) 1);
qed "lub_const";

(*----------------------------------------------------------------------*)
(* Taking the suffix of chains has no effect on ub's.                   *) 
(*----------------------------------------------------------------------*)

Goalw [isub_def,suffix_def]  (* isub_suffix *)
    "[| chain(D,X); cpo(D) |] ==> isub(D,suffix(X,n),x) <-> isub(D,X,x)";
by Safe_tac;
by (dres_inst_tac [("x","na")] bspec 1);
by (auto_tac (claset() addIs [cpo_trans, chain_rel_gen_add], simpset()));
qed "isub_suffix";

Goalw [islub_def]  (* islub_suffix *)
  "[|chain(D,X); cpo(D)|] ==> islub(D,suffix(X,n),x) <-> islub(D,X,x)";
by (asm_simp_tac (simpset() addsimps [isub_suffix]) 1);
qed "islub_suffix";

Goalw [lub_def]  (* lub_suffix *)
    "[|chain(D,X); cpo(D)|] ==> lub(D,suffix(X,n)) = lub(D,X)";
by (asm_simp_tac (simpset() addsimps [islub_suffix]) 1);
qed "lub_suffix";

(*----------------------------------------------------------------------*)
(* Dominate and subchain.                                               *) 
(*----------------------------------------------------------------------*)

val prems = Goalw [dominate_def]
  "[| !!m. m \\<in> nat ==> n(m):nat; !!m. m \\<in> nat ==> rel(D,X`m,Y`n(m))|] ==>   \
\  dominate(D,X,Y)";
by (blast_tac (claset() addIs prems) 1);
qed "dominateI"; 

Goalw [isub_def, dominate_def]
  "[|dominate(D,X,Y); isub(D,Y,x); cpo(D);  \
\    X \\<in> nat->set(D); Y \\<in> nat->set(D)|] ==> isub(D,X,x)";
by (Asm_full_simp_tac 1);  
by (blast_tac (claset() addIs [cpo_trans] addSIs [apply_funtype]) 1);
qed "dominate_isub";

Goalw [islub_def]
  "[|dominate(D,X,Y); islub(D,X,x); islub(D,Y,y); cpo(D);  \
\    X \\<in> nat->set(D); Y \\<in> nat->set(D)|] ==> rel(D,x,y)";
by (blast_tac (claset() addIs [dominate_isub]) 1);
qed "dominate_islub";

Goalw [isub_def, subchain_def]
     "[|subchain(Y,X); isub(D,X,x)|] ==> isub(D,Y,x)";
by (Force_tac 1);
qed "subchain_isub";

Goal "[|dominate(D,X,Y); subchain(Y,X); islub(D,X,x); islub(D,Y,y); cpo(D);  \
\    X \\<in> nat->set(D); Y \\<in> nat->set(D)|] ==> x = y";
by (blast_tac (claset() addIs [cpo_antisym, dominate_islub, islub_least,
			       subchain_isub, islub_isub, islub_in]) 1);
qed "dominate_islub_eq";

(*----------------------------------------------------------------------*)
(* Matrix.                                                              *) 
(*----------------------------------------------------------------------*)

Goalw [matrix_def]  (* matrix_fun *)
    "matrix(D,M) ==> M \\<in> nat -> (nat -> set(D))";
by (Asm_simp_tac 1);
qed "matrix_fun";

Goal "[|matrix(D,M); n \\<in> nat|] ==> M`n \\<in> nat -> set(D)";
by (blast_tac (claset() addIs [apply_funtype, matrix_fun]) 1);
qed "matrix_in_fun";

Goal "[|matrix(D,M); n \\<in> nat; m \\<in> nat|] ==> M`n`m \\<in> set(D)";
by (blast_tac (claset() addIs [apply_funtype, matrix_in_fun]) 1);
qed "matrix_in";

Goalw [matrix_def]  (* matrix_rel_1_0 *)
    "[|matrix(D,M); n \\<in> nat; m \\<in> nat|] ==> rel(D,M`n`m,M`succ(n)`m)";
by (Asm_simp_tac 1);
qed "matrix_rel_1_0";

Goalw [matrix_def]  (* matrix_rel_0_1 *)
    "[|matrix(D,M); n \\<in> nat; m \\<in> nat|] ==> rel(D,M`n`m,M`n`succ(m))";
by (Asm_simp_tac 1);
qed "matrix_rel_0_1";

Goalw [matrix_def]  (* matrix_rel_1_1 *)
    "[|matrix(D,M); n \\<in> nat; m \\<in> nat|] ==> rel(D,M`n`m,M`succ(n)`succ(m))";
by (Asm_simp_tac 1);
qed "matrix_rel_1_1";

Goal "f \\<in> X->Y->Z ==> (\\<lambda>y \\<in> Y. \\<lambda>x \\<in> X. f`x`y):Y->X->Z";
by (blast_tac (claset() addIs [lam_type, apply_funtype]) 1);
qed "fun_swap";

Goalw [matrix_def]  (* matrix_sym_axis *)
    "matrix(D,M) ==> matrix(D,\\<lambda>m \\<in> nat. \\<lambda>n \\<in> nat. M`n`m)";
by (asm_simp_tac (simpset() addsimps [fun_swap]) 1);
qed "matrix_sym_axis";

Goalw [chain_def]  (* matrix_chain_diag *)
    "matrix(D,M) ==> chain(D,\\<lambda>n \\<in> nat. M`n`n)";
by (auto_tac (claset() addIs [lam_type, matrix_in, matrix_rel_1_1], 
              simpset()));
qed "matrix_chain_diag";

Goalw [chain_def]  (* matrix_chain_left *)
    "[|matrix(D,M); n \\<in> nat|] ==> chain(D,M`n)";
by (auto_tac (claset() addIs [matrix_fun RS apply_type, matrix_in, 
                              matrix_rel_0_1],   simpset()));
qed "matrix_chain_left";

Goalw [chain_def]  (* matrix_chain_right *)
    "[|matrix(D,M); m \\<in> nat|] ==> chain(D,\\<lambda>n \\<in> nat. M`n`m)";
by (auto_tac (claset() addIs [lam_type,matrix_in,matrix_rel_1_0],
	      simpset()));
qed "matrix_chain_right";

val xprem::yprem::prems = Goalw [matrix_def]  (* matrix_chainI *)
    "[|!!x. x \\<in> nat==>chain(D,M`x);  !!y. y \\<in> nat==>chain(D,\\<lambda>x \\<in> nat. M`x`y);   \
\      M \\<in> nat->nat->set(D); cpo(D)|] ==> matrix(D,M)";
by Safe_tac;
by (cut_inst_tac[("y1","m"),("n","n")] (yprem RS chain_rel) 2);
by (Asm_full_simp_tac 4);
by (rtac cpo_trans 5);
by (cut_inst_tac[("y1","m"),("n","n")] (yprem RS chain_rel) 6);
by (Asm_full_simp_tac 8);
by (typecheck_tac (tcset() addTCs (chain_fun RS apply_type)::
		                  xprem::yprem::prems));
qed "matrix_chainI";

Goal "[|m \\<in> nat; rel(D, (\\<lambda>n \\<in> nat. M`n`n)`m, y)|] ==> rel(D,M`m`m, y)";
by (Asm_full_simp_tac 1);
qed "lemma";

Goal "[|x \\<in> nat; m \\<in> nat; rel(D,(\\<lambda>n \\<in> nat. M`n`m1)`x,(\\<lambda>n \\<in> nat. M`n`m1)`m)|] \
\     ==> rel(D,M`x`m1,M`m`m1)";
by (Asm_full_simp_tac 1);
qed "lemma2";

Goalw [isub_def]  (* isub_lemma *)
    "[|isub(D, \\<lambda>n \\<in> nat. M`n`n, y); matrix(D,M); cpo(D)|] ==>  \
\    isub(D, \\<lambda>n \\<in> nat. lub(D,\\<lambda>m \\<in> nat. M`n`m), y)";
by Safe_tac;
by (Asm_simp_tac 1);
by (forward_tac [matrix_fun RS apply_type] 1);
by (assume_tac 1);
by (Asm_simp_tac 1);
by (rtac (matrix_chain_left RS cpo_lub RS islub_least) 1);
by (REPEAT (assume_tac 1));
by (rewtac isub_def);
by Safe_tac;
by (excluded_middle_tac "n le na" 1);
by (rtac cpo_trans 1);
by (assume_tac 1);
by (rtac (not_le_iff_lt RS iffD1 RS leI RS chain_rel_gen) 1);
by (assume_tac 3);
by (REPEAT(ares_tac [nat_into_Ord,matrix_chain_left] 1));
by (rtac lemma 1);
by (assume_tac 1);
by (Blast_tac 1);
by (REPEAT(ares_tac [matrix_in] 1));
by (rtac cpo_trans 1);
by (assume_tac 1);
by (rtac lemma2 1);
by (rtac lemma 4);
by (Blast_tac 5);
by (REPEAT(ares_tac [chain_rel_gen,matrix_chain_right,matrix_in,isubD1] 1));
qed "isub_lemma";

Goalw [chain_def]  (* matrix_chain_lub *)
    "[|matrix(D,M); cpo(D)|] ==> chain(D,\\<lambda>n \\<in> nat. lub(D,\\<lambda>m \\<in> nat. M`n`m))";
by Safe_tac;
by (rtac lam_type 1);
by (rtac islub_in 1);
by (rtac cpo_lub 1);
by (assume_tac 2);
by (Asm_simp_tac 2);
by (rtac chainI 1);
by (rtac lam_type 1);
by (REPEAT(ares_tac [matrix_in] 1));
by (Asm_simp_tac 1);
by (rtac matrix_rel_0_1 1);
by (REPEAT(assume_tac 1));
by (asm_simp_tac (simpset() addsimps 
		  [matrix_chain_left RS chain_fun RS eta]) 1);
by (rtac dominate_islub 1);
by (rtac cpo_lub 3);
by (rtac cpo_lub 2);
by (rewtac dominate_def);
by (REPEAT(ares_tac [matrix_chain_left,nat_succI,chain_fun] 2));
by (blast_tac (claset() addIs [matrix_rel_1_0]) 1);
qed "matrix_chain_lub";

Goal  (* isub_eq *)
    "[|matrix(D,M); cpo(D)|] ==>  \
\    isub(D,(\\<lambda>n \\<in> nat. lub(D,\\<lambda>m \\<in> nat. M`n`m)),y) <->  \
\    isub(D,(\\<lambda>n \\<in> nat. M`n`n),y)";
by (rtac iffI 1);
by (rtac dominate_isub 1);
by (assume_tac 2);
by (rewtac dominate_def);
by (rtac ballI 1);
by (rtac bexI 1);
by Auto_tac;  
by (asm_simp_tac (simpset() addsimps 
		  [matrix_chain_left RS chain_fun RS eta]) 1);
by (rtac islub_ub 1);
by (rtac cpo_lub 1);
by (REPEAT(ares_tac [matrix_chain_left,matrix_chain_diag,chain_fun,
                     matrix_chain_lub, isub_lemma] 1));
qed "isub_eq";

Goalw [lub_def]  
    "lub(D,(\\<lambda>n \\<in> nat. lub(D,\\<lambda>m \\<in> nat. M`n`m))) =   \
\    (THE x. islub(D, (\\<lambda>n \\<in> nat. lub(D,\\<lambda>m \\<in> nat. M`n`m)), x))";
by (Blast_tac 1);
qed "lemma1";

Goalw [lub_def]  
    "lub(D,(\\<lambda>n \\<in> nat. M`n`n)) =   \
\    (THE x. islub(D, (\\<lambda>n \\<in> nat. M`n`n), x))";
by (Blast_tac 1);
qed "lemma2";

Goal  (* lub_matrix_diag *)
    "[|matrix(D,M); cpo(D)|] ==>  \
\    lub(D,(\\<lambda>n \\<in> nat. lub(D,\\<lambda>m \\<in> nat. M`n`m))) =  \
\    lub(D,(\\<lambda>n \\<in> nat. M`n`n))";
by (simp_tac (simpset() addsimps [lemma1,lemma2]) 1);
by (asm_simp_tac (simpset() addsimps [islub_def, isub_eq]) 1);
qed "lub_matrix_diag";

Goal  (* lub_matrix_diag_sym *)
    "[|matrix(D,M); cpo(D)|] ==>  \
\    lub(D,(\\<lambda>m \\<in> nat. lub(D,\\<lambda>n \\<in> nat. M`n`m))) =  \
\    lub(D,(\\<lambda>n \\<in> nat. M`n`n))";
by (dtac (matrix_sym_axis RS lub_matrix_diag) 1);
by Auto_tac;
qed "lub_matrix_diag_sym";

(*----------------------------------------------------------------------*)
(* I/E/D rules for mono and cont.                                       *)
(*----------------------------------------------------------------------*)

val prems = Goalw [mono_def]  (* monoI *)
    "[|f \\<in> set(D)->set(E);   \
\      !!x y. [|rel(D,x,y); x \\<in> set(D); y \\<in> set(D)|] ==> rel(E,f`x,f`y)|] ==>   \
\     f \\<in> mono(D,E)";
by (blast_tac(claset() addSIs prems) 1);
qed "monoI";

Goalw [mono_def] "f \\<in> mono(D,E) ==> f \\<in> set(D)->set(E)";
by (Fast_tac 1);
qed "mono_fun";

Goal "[|f \\<in> mono(D,E); x \\<in> set(D)|] ==> f`x \\<in> set(E)";
by (blast_tac(claset() addSIs [mono_fun RS apply_type]) 1);
qed "mono_map";

Goalw [mono_def]
    "[|f \\<in> mono(D,E); rel(D,x,y); x \\<in> set(D); y \\<in> set(D)|] ==> rel(E,f`x,f`y)";
by (Blast_tac 1);
qed "mono_mono";

val prems = Goalw [cont_def,mono_def]  (* contI *)
    "[|f \\<in> set(D)->set(E);   \
\      !!x y. [|rel(D,x,y); x \\<in> set(D); y \\<in> set(D)|] ==> rel(E,f`x,f`y);   \
\      !!X. chain(D,X) ==> f`lub(D,X) = lub(E,\\<lambda>n \\<in> nat. f`(X`n))|] ==>   \
\     f \\<in> cont(D,E)";
by (fast_tac(claset() addSIs prems) 1);
qed "contI";

Goalw [cont_def] "f \\<in> cont(D,E) ==> f \\<in> mono(D,E)";
by (Blast_tac 1);
qed "cont2mono";

Goalw [cont_def] "f \\<in> cont(D,E) ==> f \\<in> set(D)->set(E)";
by (rtac mono_fun 1);
by (Blast_tac 1);
qed "cont_fun";

Goal "[|f \\<in> cont(D,E); x \\<in> set(D)|] ==> f`x \\<in> set(E)";
by (blast_tac(claset() addSIs [cont_fun RS apply_type]) 1);
qed "cont_map";

AddTCs [comp_fun, cont_fun, cont_map];

Goalw [cont_def]
    "[|f \\<in> cont(D,E); rel(D,x,y); x \\<in> set(D); y \\<in> set(D)|] ==> rel(E,f`x,f`y)";
by (blast_tac(claset() addSIs [mono_mono]) 1);
qed "cont_mono";

Goalw [cont_def]
    "[|f \\<in> cont(D,E); chain(D,X)|] ==> f`(lub(D,X)) = lub(E,\\<lambda>n \\<in> nat. f`(X`n))";
by (Blast_tac 1);
qed "cont_lub";

(*----------------------------------------------------------------------*)
(* Continuity and chains.                                               *) 
(*----------------------------------------------------------------------*)

Goal "[|f \\<in> mono(D,E); chain(D,X)|] ==> chain(E,\\<lambda>n \\<in> nat. f`(X`n))";
by (simp_tac (simpset() addsimps [chain_def]) 1);
by (blast_tac(claset() addIs [lam_type, mono_map, chain_in, 
			      mono_mono, chain_rel]) 1);
qed "mono_chain";

Goal "[|f \\<in> cont(D,E); chain(D,X)|] ==> chain(E,\\<lambda>n \\<in> nat. f`(X`n))";
by (blast_tac(claset() addIs [mono_chain, cont2mono]) 1);
qed "cont_chain";

(*----------------------------------------------------------------------*)
(* I/E/D rules about (set+rel) cf, the continuous function space.       *)
(*----------------------------------------------------------------------*)

(* The following development more difficult with cpo-as-relation approach. *)

Goalw [set_def,cf_def] "f \\<in> set(cf(D,E)) ==> f \\<in> cont(D,E)";
by (Asm_full_simp_tac 1);
qed "cf_cont";

Goalw [set_def,cf_def]  (* Non-trivial with relation *)
    "f \\<in> cont(D,E) ==> f \\<in> set(cf(D,E))";
by (Asm_full_simp_tac 1);
qed "cont_cf";

(* rel_cf originally an equality. Now stated as two rules. Seemed easiest. 
   Besides, now complicated by typing assumptions. *)

val prems = Goal
    "[|!!x. x \\<in> set(D) ==> rel(E,f`x,g`x); f \\<in> cont(D,E); g \\<in> cont(D,E)|] ==> \
\    rel(cf(D,E),f,g)";
by (asm_simp_tac (simpset() addsimps [rel_I, cf_def]@prems) 1);
qed "rel_cfI";

Goalw [rel_def,cf_def] "[|rel(cf(D,E),f,g); x \\<in> set(D)|] ==> rel(E,f`x,g`x)";
by (Asm_full_simp_tac 1);
qed "rel_cf";

(*----------------------------------------------------------------------*)
(* Theorems about the continuous function space.                        *)
(*----------------------------------------------------------------------*)

Goal  (* chain_cf *)
    "[| chain(cf(D,E),X); x \\<in> set(D)|] ==> chain(E,\\<lambda>n \\<in> nat. X`n`x)";
by (rtac chainI 1);
by (blast_tac (claset() addIs [lam_type, apply_funtype, cont_fun,
                               cf_cont,chain_in]) 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [rel_cf,chain_rel]) 1);
qed "chain_cf";

Goal  (* matrix_lemma *)
    "[|chain(cf(D,E),X); chain(D,Xa); cpo(D); cpo(E) |] ==>   \
\    matrix(E,\\<lambda>x \\<in> nat. \\<lambda>xa \\<in> nat. X`x`(Xa`xa))";
by (rtac matrix_chainI 1);
by Auto_tac;  
by (rtac chainI 1);
by (blast_tac (claset() addIs [lam_type, apply_funtype, cont_fun,
                               cf_cont,chain_in]) 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [cont_mono, nat_succI, chain_rel,
                               cf_cont,chain_in]) 1);
by (rtac chainI 1);
by (blast_tac (claset() addIs [lam_type, apply_funtype, cont_fun,
                               cf_cont,chain_in]) 1);
by (Asm_simp_tac 1);
by (rtac rel_cf 1);
brr [chain_in,chain_rel] 1;
by (blast_tac (claset() addIs [lam_type, apply_funtype, cont_fun,
                               cf_cont,chain_in]) 1);
qed "matrix_lemma";

Goal  (* chain_cf_lub_cont *)
    "[|chain(cf(D,E),X); cpo(D); cpo(E) |] ==> \
\    (\\<lambda>x \\<in> set(D). lub(E, \\<lambda>n \\<in> nat. X ` n ` x)) \\<in> cont(D, E)";
by (rtac contI 1);
by (rtac lam_type 1);
by (REPEAT(ares_tac[chain_cf RS cpo_lub RS islub_in] 1));
by (Asm_simp_tac 1);
by (rtac dominate_islub 1);
by (REPEAT(ares_tac[chain_cf RS cpo_lub] 2));
by (rtac dominateI 1);
by (assume_tac 1);
by (Asm_simp_tac 1);
by (REPEAT(ares_tac [chain_in RS cf_cont RS cont_mono] 1));
by (REPEAT(ares_tac [chain_cf RS chain_fun] 1));
by (stac beta 1);
by (REPEAT(ares_tac [cpo_lub RS islub_in] 1));
by (asm_simp_tac(simpset() addsimps[chain_in RS cf_cont RS cont_lub]) 1);
by (forward_tac[matrix_lemma RS lub_matrix_diag]1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac(simpset() addsimps[chain_in RS beta]) 1);
by (dtac (matrix_lemma RS lub_matrix_diag_sym) 1);
by Auto_tac;
qed "chain_cf_lub_cont";

Goal  (* islub_cf *)
    "[| chain(cf(D,E),X); cpo(D); cpo(E)|] ==>   \
\     islub(cf(D,E), X, \\<lambda>x \\<in> set(D). lub(E,\\<lambda>n \\<in> nat. X`n`x))";
by (rtac islubI 1);
by (rtac isubI 1);
by (rtac (chain_cf_lub_cont RS cont_cf) 1);
by (REPEAT (assume_tac 1));
by (rtac rel_cfI 1);
by (fast_tac (claset() addSDs [chain_cf RS cpo_lub RS islub_ub]
                       addss simpset()) 1);
by (blast_tac (claset() addIs [cf_cont,chain_in]) 1);
by (blast_tac (claset() addIs [cont_cf,chain_cf_lub_cont]) 1);
by (rtac rel_cfI 1);
by (Asm_simp_tac 1);
by (REPEAT (blast_tac (claset() addIs [chain_cf_lub_cont,isubD1,cf_cont]) 2));
by (best_tac (claset() addIs [chain_cf RS cpo_lub RS islub_least,
			      cf_cont RS cont_fun RS apply_type, isubI]
		       addEs [isubD2 RS rel_cf, isubD1]
                       addss simpset()) 1);
qed "islub_cf";

Goal  (* cpo_cf *)
    "[| cpo(D); cpo(E)|] ==> cpo(cf(D,E))";
by (rtac (poI RS cpoI) 1);
by (rtac rel_cfI 1);
brr[cpo_refl, cf_cont RS cont_fun RS apply_type, cf_cont] 1;
by (rtac rel_cfI 1);
by (rtac cpo_trans 1);
by (assume_tac 1);
by (etac rel_cf 1);
by (assume_tac 1);
by (rtac rel_cf 1);
by (assume_tac 1);
brr[cf_cont RS cont_fun RS apply_type,cf_cont]1;
by (rtac fun_extension 1);
brr[cf_cont RS cont_fun]1;
by (fast_tac (claset() addIs [islub_cf]) 2);
by (blast_tac (claset() addIs [cpo_antisym,rel_cf,
			       cf_cont RS cont_fun RS apply_type]) 1);

qed "cpo_cf";

AddTCs [cpo_cf];

Goal "[| chain(cf(D,E),X); cpo(D); cpo(E)|] ==>   \
\     lub(cf(D,E), X) = (\\<lambda>x \\<in> set(D). lub(E,\\<lambda>n \\<in> nat. X`n`x))";
by (blast_tac (claset() addIs [islub_unique,cpo_lub,islub_cf,cpo_cf]) 1);
qed "lub_cf";

Goal "[|y \\<in> set(E); cpo(D); cpo(E)|] ==> (\\<lambda>x \\<in> set(D).y) \\<in> cont(D,E)";
by (rtac contI 1);
by (Asm_simp_tac 2);
by (blast_tac (claset() addIs [lam_type]) 1);
by (asm_simp_tac(simpset() addsimps [chain_in, cpo_lub RS islub_in,
				     lub_const]) 1);
qed "const_cont";

Goal "[|cpo(D); pcpo(E); y \\<in> cont(D,E)|]==>rel(cf(D,E),(\\<lambda>x \\<in> set(D).bot(E)),y)";
by (rtac rel_cfI 1);
by (Asm_simp_tac 1);
by (ALLGOALS (type_solver_tac (tcset() addTCs [cont_fun, const_cont]) []));
qed "cf_least";

Goal  (* pcpo_cf *)
    "[|cpo(D); pcpo(E)|] ==> pcpo(cf(D,E))";
by (rtac pcpoI 1);
brr[cf_least, bot_in, const_cont RS cont_cf, cf_cont, cpo_cf, pcpo_cpo] 1;
qed "pcpo_cf";

Goal  (* bot_cf *)
    "[|cpo(D); pcpo(E)|] ==> bot(cf(D,E)) = (\\<lambda>x \\<in> set(D).bot(E))";
by (blast_tac (claset() addIs [bot_unique RS sym, pcpo_cf, cf_least, 
                   bot_in RS const_cont RS cont_cf, cf_cont, pcpo_cpo])1);
qed "bot_cf";

(*----------------------------------------------------------------------*)
(* Identity and composition.                                            *)
(*----------------------------------------------------------------------*)

Goal  (* id_cont *)
    "cpo(D) ==> id(set(D)):cont(D,D)";
by (asm_simp_tac(simpset() addsimps[id_type, contI, cpo_lub RS islub_in, 
				    chain_fun RS eta]) 1);
qed "id_cont";

AddTCs [id_cont];

val comp_cont_apply = cont_fun RSN(2,cont_fun RS comp_fun_apply);

Goal  (* comp_pres_cont *)
    "[| f \\<in> cont(D',E); g \\<in> cont(D,D'); cpo(D)|] ==> f O g \\<in> cont(D,E)";
by (rtac contI 1);
by (stac comp_cont_apply 2);
by (stac comp_cont_apply 5);
by (rtac cont_mono 8);
by (rtac cont_mono 9); (* 15 subgoals *)
by Typecheck_tac; (* proves all but the lub case *)
by (stac comp_cont_apply 1);
by (stac cont_lub 4);
by (stac cont_lub 6);
by (asm_full_simp_tac(simpset() addsimps [comp_cont_apply,chain_in]) 8);
by (auto_tac (claset() addIs [cpo_lub RS islub_in, cont_chain], simpset()));
qed "comp_pres_cont";

AddTCs [comp_pres_cont];

Goal  (* comp_mono *)
    "[| f \\<in> cont(D',E); g \\<in> cont(D,D'); f':cont(D',E); g':cont(D,D');   \
\       rel(cf(D',E),f,f'); rel(cf(D,D'),g,g'); cpo(D); cpo(E) |] ==>   \
\    rel(cf(D,E),f O g,f' O g')";
by (rtac rel_cfI 1); (* extra proof obl: f O g and f' O g' cont. Extra asm cpo(D). *)
by (stac comp_cont_apply 1);
by (stac comp_cont_apply 4);
by (rtac cpo_trans 7);
by (REPEAT (ares_tac [rel_cf,cont_mono,cont_map,comp_pres_cont] 1));
qed "comp_mono";

Goal  (* chain_cf_comp *)
    "[| chain(cf(D',E),X); chain(cf(D,D'),Y); cpo(D); cpo(E)|] ==>  \
\    chain(cf(D,E),\\<lambda>n \\<in> nat. X`n O Y`n)";
by (rtac chainI 1);
by (Asm_simp_tac 2);
by (rtac rel_cfI 2);
by (stac comp_cont_apply 2);
by (stac comp_cont_apply 5); 
by (rtac cpo_trans 8); 
by (rtac rel_cf 9);
by (rtac cont_mono 11);
brr[lam_type, comp_pres_cont, cont_cf, chain_in RS cf_cont, cont_map, chain_rel,rel_cf,nat_succI] 1;
qed "chain_cf_comp";

Goal  (* comp_lubs *)
    "[| chain(cf(D',E),X); chain(cf(D,D'),Y); cpo(D); cpo(D'); cpo(E)|] ==>  \
\    lub(cf(D',E),X) O lub(cf(D,D'),Y) = lub(cf(D,E),\\<lambda>n \\<in> nat. X`n O Y`n)";
by (rtac fun_extension 1);
by (stac lub_cf 3);
brr[comp_fun, cf_cont RS cont_fun, cpo_lub RS islub_in, cpo_cf, chain_cf_comp] 1;
by (asm_simp_tac(simpset()
		 addsimps[chain_in RS 
			  cf_cont RSN(3,chain_in RS 
				      cf_cont RS comp_cont_apply)]) 1);
by (stac comp_cont_apply 1);
brr[cpo_lub RS islub_in RS cf_cont, cpo_cf] 1;
by (asm_simp_tac(simpset() addsimps
		 [lub_cf,chain_cf, chain_in RS cf_cont RS cont_lub,
		  chain_cf RS cpo_lub RS islub_in]) 1);
by (cut_inst_tac[("M","\\<lambda>xa \\<in> nat. \\<lambda>xb \\<in> nat. X`xa`(Y`xb`x)")]
   lub_matrix_diag 1);
by (Asm_full_simp_tac 3);
by (rtac matrix_chainI 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 2);
by (dtac (chain_in RS cf_cont) 1 THEN atac 1);
by (fast_tac (claset() addDs [chain_cf RSN(2,cont_chain)]
	      addss simpset()) 1);
by (rtac chain_cf 1);
by (REPEAT (ares_tac [cont_fun RS apply_type, chain_in RS cf_cont, 
		      lam_type] 1));
qed "comp_lubs";

(*----------------------------------------------------------------------*)
(* Theorems about projpair.                                             *)
(*----------------------------------------------------------------------*)

Goalw [projpair_def]  (* projpairI *)
    "[| e \\<in> cont(D,E); p \\<in> cont(E,D); p O e = id(set(D));   \
\       rel(cf(E,E))(e O p)(id(set(E)))|] ==> projpair(D,E,e,p)";
by (Fast_tac 1);
qed "projpairI";

Goalw [projpair_def] "projpair(D,E,e,p) ==> e \\<in> cont(D,E)";
by Auto_tac;  
qed "projpair_e_cont";

Goalw [projpair_def] "projpair(D,E,e,p) ==> p \\<in> cont(E,D)";
by Auto_tac;  
qed "projpair_p_cont";

Goalw [projpair_def] "projpair(D,E,e,p) ==> p O e = id(set(D))";
by Auto_tac;  
qed "projpair_eq";

Goalw [projpair_def] "projpair(D,E,e,p) ==> rel(cf(E,E))(e O p)(id(set(E)))";
by Auto_tac;  
qed "projpair_rel";

val projpairDs = [projpair_e_cont,projpair_p_cont,projpair_eq,projpair_rel];

(*----------------------------------------------------------------------*)
(* NB! projpair_e_cont and projpair_p_cont cannot be used repeatedly    *)
(*     at the same time since both match a goal of the form f \\<in> cont(X,Y).*)
(*----------------------------------------------------------------------*)

(*----------------------------------------------------------------------*)
(* Uniqueness of embedding projection pairs.                            *)
(*----------------------------------------------------------------------*)

val id_comp = fun_is_rel RS left_comp_id;
val comp_id = fun_is_rel RS right_comp_id;

val prems = goal thy (* lemma1 *)
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

val prems = goal thy (* lemma2 *)
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
brr((cpo_cf RS cpo_refl)::cont_cf::comp_mono::id_cont::comp_pres_cont::projpair_rel::(contl@prems)) 1;
val lemma2 = result();

val prems = goal thy (* projpair_unique *)
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
by (Asm_simp_tac 4);
brr([cpo_cf,cpo_refl,cont_cf,projpair_e_cont]@prems) 1;
by (rtac lemma1 1);
by (REPEAT (ares_tac prems 1));
by (Asm_simp_tac 1); 
brr(cpo_cf::cpo_refl::cont_cf::(contl @ prems)) 1;
by (rtac cpo_antisym 1);
by (rtac lemma2 2);
(* First some existentials are instantiated. *)
by (resolve_tac prems 4);
by (resolve_tac prems 4);
by (Asm_simp_tac 4);
brr([cpo_cf,cpo_refl,cont_cf,projpair_p_cont]@prems) 1;
by (rtac lemma2 1);
by (REPEAT (ares_tac prems 1));
by (Asm_simp_tac 1); 
brr(cpo_cf::cpo_refl::cont_cf::(contl @ prems)) 1;
qed "projpair_unique";

(* Slightly different, more asms, since THE chooses the unique element. *)

Goalw [emb_def,Rp_def] (* embRp *)
    "[|emb(D,E,e); cpo(D); cpo(E)|] ==> projpair(D,E,e,Rp(D,E,e))";
by (rtac theI2 1);
by (assume_tac 2);
by (blast_tac (claset() addIs [projpair_unique RS iffD1]) 1);
qed "embRp";

Goalw [emb_def] "projpair(D,E,e,p) ==> emb(D,E,e)";
by Auto_tac;  
qed "embI";

Goal "[|projpair(D,E,e,p); cpo(D); cpo(E)|] ==> Rp(D,E,e) = p";
by (blast_tac (claset() addIs [embRp, embI, projpair_unique RS iffD1]) 1);
qed "Rp_unique";

Goalw [emb_def] "emb(D,E,e) ==> e \\<in> cont(D,E)";
by (blast_tac (claset() addIs [projpair_e_cont]) 1);
qed "emb_cont";

(* The following three theorems have cpo asms due to THE (uniqueness). *)

bind_thm ("Rp_cont", embRp RS projpair_p_cont);
bind_thm ("embRp_eq", embRp RS projpair_eq);
bind_thm ("embRp_rel", embRp RS projpair_rel);

AddTCs [emb_cont, Rp_cont];

Goal  (* embRp_eq_thm *)
    "[|emb(D,E,e); x \\<in> set(D); cpo(D); cpo(E)|] ==> Rp(D,E,e)`(e`x) = x";
by (rtac (comp_fun_apply RS subst) 1);
brr[Rp_cont,emb_cont,cont_fun] 1;
by (stac embRp_eq 1);
by (auto_tac (claset() addIs [id_conv], simpset()));
qed "embRp_eq_thm";


(*----------------------------------------------------------------------*)
(* The identity embedding.                                              *)
(*----------------------------------------------------------------------*)

Goalw [projpair_def]  (* projpair_id *)
    "cpo(D) ==> projpair(D,D,id(set(D)),id(set(D)))";
by Safe_tac;
brr[id_cont,id_comp,id_type] 1;
by (stac id_comp 1); (* Matches almost anything *)
brr[id_cont,id_type,cpo_refl,cpo_cf,cont_cf] 1;
qed "projpair_id";

Goal  (* emb_id *)
    "cpo(D) ==> emb(D,D,id(set(D)))";
by (auto_tac (claset() addIs [embI,projpair_id], simpset()));
qed "emb_id";

Goal  (* Rp_id *)
    "cpo(D) ==> Rp(D,D,id(set(D))) = id(set(D))";
by (auto_tac (claset() addIs [Rp_unique,projpair_id], simpset()));
qed "Rp_id";

(*----------------------------------------------------------------------*)
(* Composition preserves embeddings.                                    *)
(*----------------------------------------------------------------------*)

(* Considerably shorter, only partly due to a simpler comp_assoc. *)
(* Proof in HOL-ST: 70 lines (minus 14 due to comp_assoc complication). *)
(* Proof in Isa/ZF: 23 lines (compared to 56: 60% reduction). *)

Goalw [projpair_def]  (* lemma *)
    "[|emb(D,D',e); emb(D',E,e'); cpo(D); cpo(D'); cpo(E)|] ==>  \
\    projpair(D,E,e' O e,(Rp(D,D',e)) O (Rp(D',E,e')))";
by Safe_tac;
brr[comp_pres_cont,Rp_cont,emb_cont] 1;
by (rtac (comp_assoc RS subst) 1);
by (res_inst_tac[("t1","e'")](comp_assoc RS ssubst) 1);
by (stac embRp_eq 1); (* Matches everything due to subst/ssubst. *)
by (REPEAT (assume_tac 1));
by (stac comp_id 1);
brr[cont_fun,Rp_cont,embRp_eq] 1;
by (rtac (comp_assoc RS subst) 1);
by (res_inst_tac[("t1","Rp(D,D',e)")](comp_assoc RS ssubst) 1);
by (rtac cpo_trans 1);
brr[cpo_cf] 1;
by (rtac comp_mono 1);
by (rtac cpo_refl 6);
brr[cont_cf,Rp_cont] 7; 
brr[cpo_cf] 6;
by (rtac comp_mono 5);
brr[embRp_rel] 10;
brr[cpo_cf RS cpo_refl, cont_cf,Rp_cont] 9;
by (stac comp_id 10);
by (rtac embRp_rel 11); 
(* There are 16 subgoals at this point. All are proved immediately by: *)
by (REPEAT (ares_tac [comp_pres_cont,Rp_cont,id_cont,
		      emb_cont,cont_fun,cont_cf] 1));
val lemma = result();

(* The use of RS is great in places like the following, both ugly in HOL. *)

val emb_comp = lemma RS embI;
val Rp_comp = lemma RS Rp_unique;

(*----------------------------------------------------------------------*)
(* Infinite cartesian product.                                          *)
(*----------------------------------------------------------------------*)

Goalw [set_def,iprod_def]  (* iprodI *)
    "x:(\\<Pi>n \\<in> nat. set(DD`n)) ==> x \\<in> set(iprod(DD))";
by (Asm_full_simp_tac 1);
qed "iprodI";

Goalw [set_def,iprod_def]  (* iprodE *)
    "x \\<in> set(iprod(DD)) ==> x:(\\<Pi>n \\<in> nat. set(DD`n))";
by (Asm_full_simp_tac 1);
qed "iprodE";

(* Contains typing conditions in contrast to HOL-ST *)

val prems = Goalw [iprod_def] (* rel_iprodI *)
    "[|!!n. n \\<in> nat ==> rel(DD`n,f`n,g`n); f:(\\<Pi>n \\<in> nat. set(DD`n));  \
\      g:(\\<Pi>n \\<in> nat. set(DD`n))|] ==> rel(iprod(DD),f,g)";
by (rtac rel_I 1);
by (Simp_tac 1);
by Safe_tac;
by (REPEAT (ares_tac prems 1));
qed "rel_iprodI";

Goalw [iprod_def]
    "[|rel(iprod(DD),f,g); n \\<in> nat|] ==> rel(DD`n,f`n,g`n)";
by (fast_tac (claset() addDs [rel_E] addss simpset()) 1);
qed "rel_iprodE";

(* Some special theorems like dProdApIn_cpo and other `_cpo' 
   probably not needed in Isabelle, wait and see. *)

val prems = Goalw [chain_def]  (* chain_iprod *)
    "[|chain(iprod(DD),X);  !!n. n \\<in> nat ==> cpo(DD`n); n \\<in> nat|] ==>  \
\    chain(DD`n,\\<lambda>m \\<in> nat. X`m`n)";
by Safe_tac;
by (rtac lam_type 1);
by (rtac apply_type 1);
by (rtac iprodE 1);
by (etac (hd prems RS conjunct1 RS apply_type) 1);
by (resolve_tac prems 1);
by (asm_simp_tac(simpset() addsimps prems) 1);
by (rtac rel_iprodE 1);
by (asm_simp_tac (simpset() addsimps prems) 1);
by (resolve_tac prems 1);
qed "chain_iprod";

val prems = Goalw [islub_def,isub_def]  (* islub_iprod *)
    "[|chain(iprod(DD),X);  !!n. n \\<in> nat ==> cpo(DD`n)|] ==>   \
\    islub(iprod(DD),X,\\<lambda>n \\<in> nat. lub(DD`n,\\<lambda>m \\<in> nat. X`m`n))";
by Safe_tac;
by (rtac iprodI 1);
by (rtac lam_type 1); 
brr((chain_iprod RS cpo_lub RS islub_in)::prems) 1;
by (rtac rel_iprodI 1);
by (Asm_simp_tac 1);
(* Here, HOL resolution is handy, Isabelle resolution bad. *)
by (res_inst_tac[("P","%t. rel(DD`na,t,lub(DD`na,\\<lambda>x \\<in> nat. X`x`na))"),
    ("b1","%n. X`n`na")](beta RS subst) 1);
brr((chain_iprod RS cpo_lub RS islub_ub)::iprodE::chain_in::prems) 1;
brr(iprodI::lam_type::(chain_iprod RS cpo_lub RS islub_in)::prems) 1;
by (rtac rel_iprodI 1);
by (Asm_simp_tac 1);
brr(islub_least::(chain_iprod RS cpo_lub)::prems) 1;
by (rewtac isub_def);
by Safe_tac;
by (etac (iprodE RS apply_type) 1);
by (assume_tac 1);
by (Asm_simp_tac 1);
by (dtac bspec 1);
by (etac rel_iprodE 2);
brr(lam_type::(chain_iprod RS cpo_lub RS islub_in)::iprodE::prems) 1;
qed "islub_iprod";

val prems = Goal (* cpo_iprod *)
    "(!!n. n \\<in> nat ==> cpo(DD`n)) ==> cpo(iprod(DD))";
brr[cpoI,poI] 1;
by (rtac rel_iprodI 1); (* not repeated: want to solve 1 and leave 2 unchanged *)
brr(cpo_refl::(iprodE RS apply_type)::iprodE::prems) 1;
by (rtac rel_iprodI 1);
by (dtac rel_iprodE 1);
by (dtac rel_iprodE 2);
brr(cpo_trans::(iprodE RS apply_type)::iprodE::prems) 1;
by (rtac fun_extension 1);
brr(cpo_antisym::rel_iprodE::(iprodE RS apply_type)::iprodE::prems) 1;
brr(islub_iprod::prems) 1;
qed "cpo_iprod";

AddTCs [cpo_iprod];

val prems = Goalw [islub_def,isub_def]  (* lub_iprod *)
    "[|chain(iprod(DD),X);  !!n. n \\<in> nat ==> cpo(DD`n)|] ==>   \
\    lub(iprod(DD),X) = (\\<lambda>n \\<in> nat. lub(DD`n,\\<lambda>m \\<in> nat. X`m`n))";
brr((cpo_lub RS islub_unique)::islub_iprod::cpo_iprod::prems) 1;
qed "lub_iprod";

(*----------------------------------------------------------------------*)
(* The notion of subcpo.                                                *)
(*----------------------------------------------------------------------*)

val prems = Goalw [subcpo_def]  (* subcpoI *)
    "[|set(D)<=set(E);  \
\      !!x y. [|x \\<in> set(D); y \\<in> set(D)|] ==> rel(D,x,y)<->rel(E,x,y);  \
\      !!X. chain(D,X) ==> lub(E,X) \\<in> set(D)|] ==> subcpo(D,E)";
by Safe_tac;
by (asm_full_simp_tac(simpset() addsimps prems) 2);
by (asm_simp_tac(simpset() addsimps prems) 2);
brr(prems@[subsetD]) 1;
qed "subcpoI";

Goalw [subcpo_def] "subcpo(D,E) ==> set(D)<=set(E)";
by Auto_tac;  
qed "subcpo_subset";

Goalw [subcpo_def]  
    "[|subcpo(D,E); x \\<in> set(D); y \\<in> set(D)|] ==> rel(D,x,y)<->rel(E,x,y)";
by (Blast_tac 1);
qed "subcpo_rel_eq";

val subcpo_relD1 = subcpo_rel_eq RS iffD1;
val subcpo_relD2 = subcpo_rel_eq RS iffD2;

Goalw [subcpo_def] "[|subcpo(D,E); chain(D,X)|] ==> lub(E,X) \\<in> set(D)";
by (Blast_tac 1);
qed "subcpo_lub";

Goal "[|subcpo(D,E); chain(D,X)|] ==> chain(E,X)";
by (rtac (Pi_type RS chainI) 1);
by (REPEAT
    (blast_tac (claset() addIs [chain_fun, subcpo_relD1, 
				subcpo_subset RS subsetD,
				chain_in, chain_rel]) 1));
qed "chain_subcpo";

Goal "[|subcpo(D,E); chain(D,X); isub(D,X,x)|] ==> isub(E,X,x)";
by (blast_tac (claset() addIs [isubI, subcpo_relD1,subcpo_relD1, 
			       chain_in, isubD1, isubD2,
			       subcpo_subset RS subsetD,
			       chain_in, chain_rel]) 1);
qed "ub_subcpo";
        
Goal "[|subcpo(D,E); cpo(E); chain(D,X)|] ==> islub(D,X,lub(E,X))";
by (blast_tac (claset() addIs [islubI, isubI, subcpo_lub, 
			       subcpo_relD2, chain_in, 
			       islub_ub, islub_least, cpo_lub,
			       chain_subcpo, isubD1, ub_subcpo]) 1);
qed "islub_subcpo";

Goal "[|subcpo(D,E); cpo(E)|] ==> cpo(D)";
brr[cpoI,poI]1;
by (asm_full_simp_tac(simpset() addsimps[subcpo_rel_eq]) 1);
brr[cpo_refl, subcpo_subset RS subsetD] 1;
by (rotate_tac ~3 1);
by (asm_full_simp_tac(simpset() addsimps[subcpo_rel_eq]) 1);
by (blast_tac (claset() addIs [subcpo_subset RS subsetD, cpo_trans]) 1);
(* Changing the order of the assumptions, otherwise full_simp doesn't work. *)
by (rotate_tac ~2 1);
by (asm_full_simp_tac(simpset() addsimps[subcpo_rel_eq]) 1);
by (blast_tac (claset() addIs [cpo_antisym, subcpo_subset RS subsetD])  1);
by (fast_tac (claset() addIs [islub_subcpo])  1);
qed "subcpo_cpo";

Goal "[|subcpo(D,E); cpo(E); chain(D,X)|] ==> lub(D,X) = lub(E,X)";
by (blast_tac (claset() addIs [cpo_lub RS islub_unique, 
			       islub_subcpo, subcpo_cpo])  1);
qed "lub_subcpo";

(*----------------------------------------------------------------------*)
(* Making subcpos using mkcpo.                                          *)
(*----------------------------------------------------------------------*)

Goalw [set_def,mkcpo_def] "[|x \\<in> set(D); P(x)|] ==> x \\<in> set(mkcpo(D,P))";
by Auto_tac;
qed "mkcpoI";

(* Old proof where cpos are non-reflexive relations.
by (rewtac set_def); (* Annoying, cannot just rewrite once. *)
by (rtac CollectI 1);
by (rtac domainI 1);
by (rtac CollectI 1);
(* Now, work on subgoal 2 (and 3) to instantiate unknown. *)
by (Simp_tac 2);
by (rtac conjI 2);
by (rtac conjI 3);
by (resolve_tac prems 3);
by (simp_tac(simpset() addsimps [rewrite_rule[set_def](hd prems)]) 1);
by (resolve_tac prems 1);
by (rtac cpo_refl 1);
by (resolve_tac prems 1);
by (rtac rel_I 1);
by (rtac CollectI 1);
by (fast_tac(claset() addSIs [rewrite_rule[set_def](hd prems)]) 1);
by (Simp_tac 1);
brr[conjI,cpo_refl] 1;
*)

Goalw [set_def,mkcpo_def]  (* mkcpoD1 *)
    "x \\<in> set(mkcpo(D,P))==> x \\<in> set(D)";
by (Asm_full_simp_tac 1);
qed "mkcpoD1";

Goalw [set_def,mkcpo_def]  (* mkcpoD2 *)
    "x \\<in> set(mkcpo(D,P))==> P(x)";
by (Asm_full_simp_tac 1);
qed "mkcpoD2";

Goalw [rel_def,mkcpo_def]  (* rel_mkcpoE *)
    "rel(mkcpo(D,P),x,y) ==> rel(D,x,y)";
by (Asm_full_simp_tac 1);
qed "rel_mkcpoE";

Goalw [mkcpo_def,rel_def,set_def]
    "[|x \\<in> set(D); y \\<in> set(D)|] ==> rel(mkcpo(D,P),x,y) <-> rel(D,x,y)";
by Auto_tac;  
qed "rel_mkcpo";

Goal  (* chain_mkcpo *)
    "chain(mkcpo(D,P),X) ==> chain(D,X)";
by (rtac chainI 1);
by (blast_tac (claset() addIs [Pi_type, chain_fun, chain_in RS mkcpoD1]) 1);
by (blast_tac (claset() addIs [rel_mkcpo RS iffD1, chain_rel, mkcpoD1, 
                               chain_in,nat_succI]) 1);
qed "chain_mkcpo";

val prems = Goal  (* subcpo_mkcpo *)
    "[|!!X. chain(mkcpo(D,P),X) ==> P(lub(D,X)); cpo(D)|] ==>   \
\    subcpo(mkcpo(D,P),D)";
brr(subcpoI::subsetI::prems) 1;
by (rtac rel_mkcpo 2);
by (REPEAT(etac mkcpoD1 1)); 
brr(mkcpoI::(cpo_lub RS islub_in)::chain_mkcpo::prems) 1;
qed "subcpo_mkcpo";

(*----------------------------------------------------------------------*)
(* Embedding projection chains of cpos.                                 *)
(*----------------------------------------------------------------------*)

val prems = Goalw [emb_chain_def]  (* emb_chainI *)
    "[|!!n. n \\<in> nat ==> cpo(DD`n);   \
\      !!n. n \\<in> nat ==> emb(DD`n,DD`succ(n),ee`n)|] ==> emb_chain(DD,ee)";
by Safe_tac;
by (REPEAT (ares_tac prems 1));
qed "emb_chainI";

Goalw [emb_chain_def] "[|emb_chain(DD,ee); n \\<in> nat|] ==> cpo(DD`n)";
by (Fast_tac 1);
qed "emb_chain_cpo";

AddTCs [emb_chain_cpo];

Goalw [emb_chain_def] 
    "[|emb_chain(DD,ee); n \\<in> nat|] ==> emb(DD`n,DD`succ(n),ee`n)";
by (Fast_tac 1);
qed "emb_chain_emb";

(*----------------------------------------------------------------------*)
(* Dinf, the inverse Limit.                                             *)
(*----------------------------------------------------------------------*)

val prems = Goalw [Dinf_def]  (* DinfI *)
    "[|x:(\\<Pi>n \\<in> nat. set(DD`n));  \
\      !!n. n \\<in> nat ==> Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n|] ==>   \
\    x \\<in> set(Dinf(DD,ee))";
brr(mkcpoI::iprodI::ballI::prems) 1;
qed "DinfI";

Goalw [Dinf_def] "x \\<in> set(Dinf(DD,ee)) ==> x:(\\<Pi>n \\<in> nat. set(DD`n))";
by (etac (mkcpoD1 RS iprodE) 1);
qed "Dinf_prod";

Goalw [Dinf_def]
    "[|x \\<in> set(Dinf(DD,ee)); n \\<in> nat|] ==>   \
\    Rp(DD`n,DD`succ(n),ee`n)`(x`succ(n)) = x`n";
by (blast_tac (claset() addDs [mkcpoD2])  1);
qed "Dinf_eq";

val prems = Goalw [Dinf_def] 
    "[|!!n. n \\<in> nat ==> rel(DD`n,x`n,y`n);  \
\      x:(\\<Pi>n \\<in> nat. set(DD`n)); y:(\\<Pi>n \\<in> nat. set(DD`n))|] ==>   \
\    rel(Dinf(DD,ee),x,y)";
by (rtac (rel_mkcpo RS iffD2) 1);
brr(rel_iprodI::iprodI::prems) 1;
qed "rel_DinfI";

Goalw [Dinf_def] "[|rel(Dinf(DD,ee),x,y); n \\<in> nat|] ==> rel(DD`n,x`n,y`n)";
by (etac (rel_mkcpoE RS rel_iprodE) 1);
by (assume_tac 1);
qed "rel_Dinf";

Goalw [Dinf_def] "chain(Dinf(DD,ee),X) ==> chain(iprod(DD),X)";
by (etac chain_mkcpo 1);
qed "chain_Dinf";

Goalw [Dinf_def]  (* subcpo_Dinf *)
    "emb_chain(DD,ee) ==> subcpo(Dinf(DD,ee),iprod(DD))";
by (rtac subcpo_mkcpo 1);
by (fold_tac [Dinf_def]);
by (rtac ballI 1);
by (stac lub_iprod 1);
brr[chain_Dinf, emb_chain_cpo] 1;
by (Asm_simp_tac 1);
by (stac (Rp_cont RS cont_lub) 1);
brr[emb_chain_cpo,emb_chain_emb,nat_succI,chain_iprod,chain_Dinf] 1;
(* Useful simplification, ugly in HOL. *)
by (asm_simp_tac(simpset() addsimps[Dinf_eq,chain_in]) 1);
by (auto_tac (claset() addIs [cpo_iprod,emb_chain_cpo], simpset()));
qed "subcpo_Dinf";

(* Simple example of existential reasoning in Isabelle versus HOL. *)

Goal "emb_chain(DD,ee) ==> cpo(Dinf(DD,ee))";
by (rtac subcpo_cpo 1);
by (etac subcpo_Dinf 1);
by (auto_tac (claset() addIs [cpo_iprod, emb_chain_cpo], simpset()));
qed "cpo_Dinf";

(* Again and again the proofs are much easier to WRITE in Isabelle, but 
  the proof steps are essentially the same (I think). *)

Goal  (* lub_Dinf *)
    "[|chain(Dinf(DD,ee),X); emb_chain(DD,ee)|] ==>  \
\    lub(Dinf(DD,ee),X) = (\\<lambda>n \\<in> nat. lub(DD`n,\\<lambda>m \\<in> nat. X`m`n))";
by (stac (subcpo_Dinf RS lub_subcpo) 1);
by (auto_tac (claset() addIs [cpo_iprod,emb_chain_cpo,lub_iprod,chain_Dinf], simpset()));
qed "lub_Dinf";

(*----------------------------------------------------------------------*)
(* Generalising embedddings D_m -> D_{m+1} to embeddings D_m -> D_n,    *)
(* defined as eps(DD,ee,m,n), via e_less and e_gr.                      *)
(*----------------------------------------------------------------------*)

Goalw [e_less_def]  (* e_less_eq *)
    "m \\<in> nat ==> e_less(DD,ee,m,m) = id(set(DD`m))";
by (asm_simp_tac (simpset() addsimps[diff_self_eq_0]) 1);
qed "e_less_eq";
 
Goal "succ(m#+n)#-m = succ(natify(n))";
by (Asm_simp_tac 1);
val lemma_succ_sub = result();

Goalw [e_less_def]
     "e_less(DD,ee,m,succ(m#+k)) = (ee`(m#+k))O(e_less(DD,ee,m,m#+k))";
by (asm_simp_tac (simpset() addsimps [lemma_succ_sub,diff_add_inverse]) 1);
qed "e_less_add";

Goal "n \\<in> nat ==> succ(n) = n #+ 1";
by (Asm_simp_tac 1);
qed "add1";

Goal "[| m le n; n \\<in> nat |] ==> \\<exists>k \\<in> nat. n = m #+ k";
by (dtac less_imp_succ_add 1);
by Auto_tac;  
val lemma_le_exists = result();

val prems = Goal
    "[| m le n;  !!x. [|n=m#+x; x \\<in> nat|] ==> Q;  n \\<in> nat |] ==> Q";
by (rtac (lemma_le_exists RS bexE) 1);
by (DEPTH_SOLVE (ares_tac prems 1));
qed "le_exists";

Goal "[| m le n;  n \\<in> nat |] ==>   \
\     e_less(DD,ee,m,succ(n)) = ee`n O e_less(DD,ee,m,n)";
by (rtac le_exists 1);
by (assume_tac 1);
by (asm_simp_tac(simpset() addsimps[e_less_add]) 1);
by (assume_tac 1);
qed "e_less_le";

(* All theorems assume variables m and n are natural numbers. *)

Goal "m \\<in> nat ==> e_less(DD,ee,m,succ(m)) = ee`m O id(set(DD`m))";
by (asm_simp_tac(simpset() addsimps[e_less_le, e_less_eq]) 1);
qed "e_less_succ";

val prems = Goal
    "[|!!n. n \\<in> nat ==> emb(DD`n,DD`succ(n),ee`n); m \\<in> nat|] ==>   \
\    e_less(DD,ee,m,succ(m)) = ee`m";
by (asm_simp_tac(simpset() addsimps e_less_succ::prems) 1);
by (stac comp_id 1);
brr(emb_cont::cont_fun::refl::prems) 1;
qed "e_less_succ_emb";

(* Compare this proof with the HOL one, here we do type checking. *)
(* In any case the one below was very easy to write. *)

Goal "[| emb_chain(DD,ee); m \\<in> nat |] ==>   \
\     emb(DD`m, DD`(m#+k), e_less(DD,ee,m,m#+k))";
by (subgoal_tac "emb(DD`m, DD`(m#+natify(k)), e_less(DD,ee,m,m#+natify(k)))" 1);
by (res_inst_tac [("n","natify(k)")] nat_induct 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps[e_less_eq])));
brr[emb_id,emb_chain_cpo] 1;
by (asm_simp_tac(simpset() addsimps[e_less_add]) 1);
by (auto_tac (claset() addIs [emb_comp,emb_chain_emb,emb_chain_cpo,add_type],
	      simpset()));
qed "emb_e_less_add";

Goal "[| m le n;  emb_chain(DD,ee);  n \\<in> nat |] ==>   \
\    emb(DD`m, DD`n, e_less(DD,ee,m,n))";
by (ftac lt_nat_in_nat 1);
by (etac nat_succI 1);
(* same proof as e_less_le *)
by (rtac le_exists 1);
by (assume_tac 1);
by (asm_simp_tac(simpset() addsimps[emb_e_less_add]) 1);
by (assume_tac 1);
qed "emb_e_less";

Goal "[|f=f'; g=g'|] ==> f O g = f' O g'";
by (Asm_simp_tac 1);
qed "comp_mono_eq";

(* Typing, typing, typing, three irritating assumptions. Extra theorems
   needed in proof, but no real difficulty. *)
(* Note also the object-level implication for induction on k. This
   must be removed later to allow the theorems to be used for simp. 
   Therefore this theorem is only a lemma. *)

Goal  (* e_less_split_add_lemma *)
    "[| emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    n le k --> \
\    e_less(DD,ee,m,m#+k) = e_less(DD,ee,m#+n,m#+k) O e_less(DD,ee,m,m#+n)";
by (induct_tac "k" 1);
by (asm_full_simp_tac(simpset() addsimps [e_less_eq, id_type RS id_comp]) 1);
by (asm_simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps[add_succ_right, e_less_add, add_type,nat_succI]) 1);
(* Again and again, simplification is a pain. When does it work, when not? *)
by (stac e_less_le 1);
brr[add_le_mono,nat_le_refl,add_type,nat_succI] 1;
by (stac comp_assoc 1);
brr[comp_mono_eq,refl] 1;
by (asm_simp_tac(ZF_ss addsimps[e_less_eq,add_type,nat_succI]) 1);
by (stac id_comp 1); (* simp cannot unify/inst right, use brr below(?). *)
by (REPEAT (ares_tac [emb_e_less_add RS emb_cont RS cont_fun, refl,
		      nat_succI] 1));
qed "e_less_split_add_lemma";

Goal "[| n le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\     e_less(DD,ee,m,m#+k) = e_less(DD,ee,m#+n,m#+k) O e_less(DD,ee,m,m#+n)";
by (blast_tac (claset() addIs [e_less_split_add_lemma RS mp]) 1);
qed "e_less_split_add";

Goalw [e_gr_def]  (* e_gr_eq *)
    "m \\<in> nat ==> e_gr(DD,ee,m,m) = id(set(DD`m))";
by (asm_simp_tac (simpset() addsimps[diff_self_eq_0]) 1);
qed "e_gr_eq";

Goalw [e_gr_def] (* e_gr_add *)
    "[|n \\<in> nat; k \\<in> nat|] ==>    \
\         e_gr(DD,ee,succ(n#+k),n) =   \
\         e_gr(DD,ee,n#+k,n) O Rp(DD`(n#+k),DD`succ(n#+k),ee`(n#+k))";
by (asm_simp_tac (simpset() addsimps [lemma_succ_sub,diff_add_inverse]) 1);
qed "e_gr_add";

Goal "[|n le m; m \\<in> nat; n \\<in> nat|] ==>   \
\    e_gr(DD,ee,succ(m),n) = e_gr(DD,ee,m,n) O Rp(DD`m,DD`succ(m),ee`m)";
by (etac le_exists 1);
by (asm_simp_tac(simpset() addsimps[e_gr_add]) 1);
by (REPEAT (assume_tac 1));
qed "e_gr_le";

Goal "m \\<in> nat ==>   \
\    e_gr(DD,ee,succ(m),m) = id(set(DD`m)) O Rp(DD`m,DD`succ(m),ee`m)";
by (asm_simp_tac(simpset() addsimps[e_gr_le,e_gr_eq]) 1);
qed "e_gr_succ";

(* Cpo asm's due to THE uniqueness. *)

Goal "[|emb_chain(DD,ee); m \\<in> nat|] ==>   \
\    e_gr(DD,ee,succ(m),m) = Rp(DD`m,DD`succ(m),ee`m)";
by (asm_simp_tac(simpset() addsimps[e_gr_succ]) 1);
by (blast_tac (claset() addIs [id_comp, Rp_cont,cont_fun,
			       emb_chain_cpo,emb_chain_emb])  1);
qed "e_gr_succ_emb";

Goal  (* e_gr_fun_add *)
    "[|emb_chain(DD,ee); n \\<in> nat; k \\<in> nat|] ==>   \
\    e_gr(DD,ee,n#+k,n): set(DD`(n#+k))->set(DD`n)";
by (induct_tac "k" 1);
by (asm_simp_tac(simpset() addsimps[e_gr_eq,id_type]) 1);
by (asm_simp_tac(simpset() addsimps[e_gr_add]) 1);
brr[comp_fun, Rp_cont, cont_fun, emb_chain_emb, emb_chain_cpo, add_type, nat_succI] 1;
qed "e_gr_fun_add";

Goal  (* e_gr_fun *)
    "[|n le m; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat|] ==>   \
\    e_gr(DD,ee,m,n): set(DD`m)->set(DD`n)";
by (rtac le_exists 1);
by (assume_tac 1);
by (asm_simp_tac(simpset() addsimps[e_gr_fun_add]) 1);
by (REPEAT (assume_tac 1));
qed "e_gr_fun";

Goal  (* e_gr_split_add_lemma *)
    "[| emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    m le k --> \
\    e_gr(DD,ee,n#+k,n) = e_gr(DD,ee,n#+m,n) O e_gr(DD,ee,n#+k,n#+m)";
by (induct_tac "k" 1);
by (rtac impI 1);
by (asm_full_simp_tac(simpset() addsimps
		      [le0_iff, e_gr_eq, id_type RS comp_id]) 1);
by (asm_simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps[add_succ_right, e_gr_add, add_type,nat_succI]) 1);
(* Again and again, simplification is a pain. When does it work, when not? *)
by (stac e_gr_le 1);
brr[add_le_mono,nat_le_refl,add_type,nat_succI] 1;
by (stac comp_assoc 1);
brr[comp_mono_eq,refl] 1;
(* New direct subgoal *)
by (asm_simp_tac(ZF_ss addsimps[e_gr_eq,add_type,nat_succI]) 1);
by (stac comp_id 1); (* simp cannot unify/inst right, use brr below(?). *)
by (REPEAT (ares_tac [e_gr_fun,add_type,refl,add_le_self,nat_succI] 1));
qed "e_gr_split_add_lemma";

Goal "[| m le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\     e_gr(DD,ee,n#+k,n) = e_gr(DD,ee,n#+m,n) O e_gr(DD,ee,n#+k,n#+m)";
by (blast_tac (claset() addIs [e_gr_split_add_lemma RS mp]) 1);
qed "e_gr_split_add";

Goal "[|m le n; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat|] ==>   \
\     e_less(DD,ee,m,n):cont(DD`m,DD`n)";
by (blast_tac (claset() addIs [emb_cont, emb_e_less]) 1);
qed "e_less_cont";

Goal  (* e_gr_cont *)
    "[|n le m; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat|] ==>   \
\    e_gr(DD,ee,m,n):cont(DD`m,DD`n)";
by (etac rev_mp 1);
by (induct_tac "m" 1);
by (asm_full_simp_tac(simpset() addsimps [le0_iff,e_gr_eq,nat_0I]) 1);
brr[impI,id_cont,emb_chain_cpo,nat_0I] 1;
by (asm_full_simp_tac(simpset() addsimps[le_succ_iff]) 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(simpset() addsimps[e_gr_le]) 1);
brr[comp_pres_cont,Rp_cont,emb_chain_cpo,emb_chain_emb,nat_succI] 1;
by (asm_simp_tac(simpset() addsimps[e_gr_eq,nat_succI]) 1);
by (auto_tac (claset() addIs [id_cont,emb_chain_cpo], simpset()));
qed "e_gr_cont";

(* Considerably shorter.... 57 against 26 *)

Goal  (* e_less_e_gr_split_add *)
    "[|n le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>   \
\    e_less(DD,ee,m,m#+n) = e_gr(DD,ee,m#+k,m#+n) O e_less(DD,ee,m,m#+k)";
(* Use mp to prepare for induction. *)
by (etac rev_mp 1);
by (induct_tac "k" 1);
by (asm_full_simp_tac(simpset() addsimps
		      [e_gr_eq, e_less_eq, id_type RS id_comp]) 1);
by (simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps[add_succ_right, e_gr_le, e_less_le, add_le_self,nat_le_refl,add_le_mono,add_type]) 1);
by (stac comp_assoc 1);
by (res_inst_tac[("s1","ee`(m#+x)")](comp_assoc RS subst) 1);
by (stac embRp_eq 1);
brr[emb_chain_emb,add_type,emb_chain_cpo,nat_succI] 1;
by (stac id_comp 1);
brr[e_less_cont RS cont_fun, add_type,add_le_self,refl] 1;
by (asm_full_simp_tac(ZF_ss addsimps[e_gr_eq,nat_succI,add_type]) 1);
by (stac id_comp 1);
by (REPEAT (ares_tac [e_less_cont RS cont_fun, add_type,
		      nat_succI,add_le_self,refl] 1));
qed "e_less_e_gr_split_add";

(* Again considerably shorter, and easy to obtain from the previous thm. *)

Goal  (* e_gr_e_less_split_add *)
    "[|m le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>   \
\    e_gr(DD,ee,n#+m,n) = e_gr(DD,ee,n#+k,n) O e_less(DD,ee,n#+m,n#+k)";
(* Use mp to prepare for induction. *)
by (etac rev_mp 1);
by (induct_tac "k" 1);
by (asm_full_simp_tac(simpset() addsimps
		      [e_gr_eq, e_less_eq, id_type RS id_comp]) 1);
by (simp_tac(ZF_ss addsimps[le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (etac impE 1);
by (assume_tac 1);
by (asm_simp_tac(ZF_ss addsimps[add_succ_right, e_gr_le, e_less_le, add_le_self,nat_le_refl,add_le_mono,add_type]) 1);
by (stac comp_assoc 1);
by (res_inst_tac[("s1","ee`(n#+x)")](comp_assoc RS subst) 1);
by (stac embRp_eq 1);
brr[emb_chain_emb,add_type,emb_chain_cpo,nat_succI] 1;
by (stac id_comp 1);
brr[e_less_cont RS cont_fun, add_type, add_le_mono, nat_le_refl, refl] 1;
by (asm_full_simp_tac(ZF_ss addsimps[e_less_eq,nat_succI,add_type]) 1);
by (stac comp_id 1);
by (REPEAT (ares_tac [e_gr_cont RS cont_fun, add_type,nat_succI,add_le_self,
		      refl] 1));
qed "e_gr_e_less_split_add";


Goalw [eps_def]  (* emb_eps *)
    "[|m le n; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat|] ==>   \
\    emb(DD`m,DD`n,eps(DD,ee,m,n))";
by (asm_simp_tac(simpset()) 1);
brr[emb_e_less] 1;
qed "emb_eps";

Goalw [eps_def]  (* eps_fun *)
    "[|emb_chain(DD,ee); m \\<in> nat; n \\<in> nat|] ==>   \
\    eps(DD,ee,m,n): set(DD`m)->set(DD`n)";
by (rtac (split_if RS iffD2) 1);
by Safe_tac;
brr[e_less_cont RS cont_fun] 1;
by (auto_tac (claset() addIs [not_le_iff_lt RS iffD1 RS leI, e_gr_fun,nat_into_Ord], simpset()));
qed "eps_fun";

Goalw [eps_def] "n \\<in> nat ==> eps(DD,ee,n,n) = id(set(DD`n))";
by (asm_simp_tac(simpset() addsimps [e_less_eq]) 1);
qed "eps_id";

Goalw [eps_def]
    "[|m \\<in> nat; n \\<in> nat|] ==> eps(DD,ee,m,m#+n) = e_less(DD,ee,m,m#+n)";
by (asm_simp_tac(simpset() addsimps [add_le_self]) 1);
qed "eps_e_less_add";

Goalw [eps_def]
    "[|m le n; m \\<in> nat; n \\<in> nat|] ==> eps(DD,ee,m,n) = e_less(DD,ee,m,n)";
by (Asm_simp_tac 1);
qed "eps_e_less";

Goalw [eps_def]  (* eps_e_gr_add *)
    "[|n \\<in> nat; k \\<in> nat|] ==> eps(DD,ee,n#+k,n) = e_gr(DD,ee,n#+k,n)";
by (rtac (split_if RS iffD2) 1);
by Safe_tac;
by (etac leE 1);
by (asm_simp_tac(simpset() addsimps[e_less_eq,e_gr_eq]) 2);
(* Must control rewriting by instantiating a variable. *)
by (asm_full_simp_tac
    (simpset() addsimps
     [inst "i1" "n" (nat_into_Ord RS not_le_iff_lt RS iff_sym),
      add_le_self]) 1);
qed "eps_e_gr_add";

Goal  (* eps_e_gr *)
    "[|n le m; m \\<in> nat; n \\<in> nat|] ==> eps(DD,ee,m,n) = e_gr(DD,ee,m,n)";
by (rtac le_exists 1);
by (assume_tac 1);
by (asm_simp_tac(simpset() addsimps[eps_e_gr_add]) 1);
by (REPEAT (assume_tac 1));
qed "eps_e_gr";

val prems = Goal  (* eps_succ_ee *)
    "[|!!n. n \\<in> nat ==> emb(DD`n,DD`succ(n),ee`n); m \\<in> nat|] ==>  \
\    eps(DD,ee,m,succ(m)) = ee`m";
by (asm_simp_tac(simpset() addsimps eps_e_less::le_succ_iff::e_less_succ_emb::
   prems) 1);
qed "eps_succ_ee";

Goal  (* eps_succ_Rp *)
    "[|emb_chain(DD,ee); m \\<in> nat|] ==>  \
\    eps(DD,ee,succ(m),m) = Rp(DD`m,DD`succ(m),ee`m)";
by (asm_simp_tac(simpset() addsimps eps_e_gr::le_succ_iff::e_gr_succ_emb::
   prems) 1);
qed "eps_succ_Rp";

Goal  (* eps_cont *)
    "[|emb_chain(DD,ee); m \\<in> nat; n \\<in> nat|] ==> eps(DD,ee,m,n): cont(DD`m,DD`n)";
by (res_inst_tac [("i","m"),("j","n")] nat_linear_le 1);
by (ALLGOALS (asm_simp_tac(simpset() addsimps [eps_e_less,e_less_cont,
					       eps_e_gr,e_gr_cont])));     
qed "eps_cont";

(* Theorems about splitting. *)

Goal  (* eps_split_add_left *)
    "[|n le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,m,m#+k) = eps(DD,ee,m#+n,m#+k) O eps(DD,ee,m,m#+n)";
by (asm_simp_tac(simpset() addsimps 
    [eps_e_less,add_le_self,add_le_mono]) 1);
by (auto_tac (claset() addIs [e_less_split_add], simpset()));
qed "eps_split_add_left";

Goal  (* eps_split_add_left_rev *)
    "[|n le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,m,m#+n) = eps(DD,ee,m#+k,m#+n) O eps(DD,ee,m,m#+k)";
by (asm_simp_tac(simpset() addsimps 
    [eps_e_less_add,eps_e_gr,add_le_self,add_le_mono]) 1);
by (auto_tac (claset() addIs [e_less_e_gr_split_add], simpset()));
qed "eps_split_add_left_rev";

Goal  (* eps_split_add_right *)
    "[|m le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,n#+k,n) = eps(DD,ee,n#+m,n) O eps(DD,ee,n#+k,n#+m)";
by (asm_simp_tac(simpset() addsimps 
    [eps_e_gr,add_le_self,add_le_mono]) 1);
by (auto_tac (claset() addIs [e_gr_split_add], simpset()));
qed "eps_split_add_right";

Goal  (* eps_split_add_right_rev *)
    "[|m le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,n#+m,n) = eps(DD,ee,n#+k,n) O eps(DD,ee,n#+m,n#+k)";
by (asm_simp_tac(simpset() addsimps 
    [eps_e_gr_add,eps_e_less,add_le_self,add_le_mono]) 1);
by (auto_tac (claset() addIs [e_gr_e_less_split_add], simpset()));
qed "eps_split_add_right_rev";

(* Arithmetic *)

val [prem1,prem2,prem3,prem4] = Goal
    "[| n le k; k le m;  \
\       !!p q. [|p le q; k=n#+p; m=n#+q; p \\<in> nat; q \\<in> nat|] ==> R; \
\       m \\<in> nat |]==>R";
by (rtac (prem1 RS le_exists) 1);
by (simp_tac (simpset() addsimps [prem2 RS lt_nat_in_nat, prem4]) 2);
by (rtac ([prem1,prem2] MRS le_trans RS le_exists) 1);
by (rtac prem4 2);
by (rtac prem3 1);
by (assume_tac 2);
by (assume_tac 2);
by (cut_facts_tac [prem1,prem2] 1);
by Auto_tac;
qed "le_exists_lemma";

Goal  (* eps_split_left_le *)
    "[|m le k; k le n; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac le_exists_lemma 1);
by (REPEAT (assume_tac 1));
by (Asm_simp_tac 1);
by (auto_tac (claset() addIs [eps_split_add_left], simpset()));
qed "eps_split_left_le";

Goal  (* eps_split_left_le_rev *)
    "[|m le n; n le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac le_exists_lemma 1);
by (REPEAT (assume_tac 1));
by (Asm_simp_tac 1);
by (auto_tac (claset() addIs [eps_split_add_left_rev], simpset()));
qed "eps_split_left_le_rev";

Goal  (* eps_split_right_le *)
    "[|n le k; k le m; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac le_exists_lemma 1);
by (REPEAT (assume_tac 1));
by (Asm_simp_tac 1);
by (auto_tac (claset() addIs [eps_split_add_right], simpset()));
qed "eps_split_right_le";

Goal  (* eps_split_right_le_rev *)
    "[|n le m; m le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac le_exists_lemma 1);
by (REPEAT (assume_tac 1));
by (Asm_simp_tac 1);
by (auto_tac (claset() addIs [eps_split_add_right_rev], simpset()));
qed "eps_split_right_le_rev";

(* The desired two theorems about `splitting'. *)

Goal  (* eps_split_left *)
    "[|m le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac nat_linear_le 1);
by (rtac eps_split_right_le_rev 4);
by (assume_tac 4);
by (rtac nat_linear_le 3);
by (rtac eps_split_left_le 5);
by (assume_tac 6);
by (rtac eps_split_left_le_rev 10);
by (REPEAT (assume_tac 1)); (* 20 trivial subgoals *)
qed "eps_split_left";

Goal  (* eps_split_right *)
    "[|n le k; emb_chain(DD,ee); m \\<in> nat; n \\<in> nat; k \\<in> nat|] ==>  \
\    eps(DD,ee,m,n) = eps(DD,ee,k,n) O eps(DD,ee,m,k)";
by (rtac nat_linear_le 1);
by (rtac eps_split_left_le_rev 3);
by (assume_tac 3);
by (rtac nat_linear_le 8);
by (rtac eps_split_right_le 10);
by (assume_tac 11);
by (rtac eps_split_right_le_rev 15);
by (REPEAT (assume_tac 1)); (* 20 trivial subgoals *)
qed "eps_split_right";

(*----------------------------------------------------------------------*)
(* That was eps: D_m -> D_n, NEXT rho_emb: D_n -> Dinf.                 *)
(*----------------------------------------------------------------------*)

(* Considerably shorter. *)

Goalw [rho_emb_def] (* rho_emb_fun *)
    "[|emb_chain(DD,ee); n \\<in> nat|] ==>   \
\    rho_emb(DD,ee,n): set(DD`n) -> set(Dinf(DD,ee))";
brr[lam_type, DinfI, eps_cont RS cont_fun RS apply_type] 1;
by (Asm_simp_tac 1);
by (res_inst_tac [("i","succ(na)"),("j","n")] nat_linear_le 1);
by (Blast_tac 1);
by (assume_tac 1);
(* The easiest would be to apply add1 everywhere also in the assumptions, 
   but since x le y is x<succ(y) simplification does too much with this thm. *)
by (stac eps_split_right_le 1);
by (assume_tac 2);
by (asm_simp_tac(FOL_ss addsimps [add1]) 1);
brr[add_le_self,nat_0I,nat_succI] 1;
by (asm_simp_tac(simpset() addsimps[eps_succ_Rp]) 1);
by (stac comp_fun_apply 1);
brr[eps_fun, nat_succI, Rp_cont RS cont_fun, emb_chain_emb, emb_chain_cpo,refl] 1;
(* Now the second part of the proof. Slightly different than HOL. *)
by (asm_simp_tac(simpset() addsimps[eps_e_less,nat_succI]) 1);
by (etac (le_iff RS iffD1 RS disjE) 1);
by (asm_simp_tac(simpset() addsimps[e_less_le]) 1);
by (stac comp_fun_apply 1);
brr[e_less_cont,cont_fun,emb_chain_emb,emb_cont] 1;
by (stac embRp_eq_thm 1);
brr[emb_chain_emb, e_less_cont RS cont_fun RS apply_type, emb_chain_cpo, nat_succI] 1;
by (asm_simp_tac(simpset() addsimps[eps_e_less]) 1);
by (dtac asm_rl 1);
by (asm_full_simp_tac(simpset() addsimps[eps_succ_Rp, e_less_eq, id_conv, nat_succI]) 1);
qed "rho_emb_fun";

Goalw [rho_emb_def]
    "x \\<in> set(DD`n) ==> rho_emb(DD,ee,n)`x = (\\<lambda>m \\<in> nat. eps(DD,ee,n,m)`x)";
by (Asm_simp_tac 1);
qed "rho_emb_apply1";

Goalw [rho_emb_def]
    "[|x \\<in> set(DD`n); m \\<in> nat|] ==> rho_emb(DD,ee,n)`x`m = eps(DD,ee,n,m)`x";
by (Asm_simp_tac 1);
qed "rho_emb_apply2";

Goal "[| x \\<in> set(DD`n); n \\<in> nat|] ==> rho_emb(DD,ee,n)`x`n = x";
by (asm_simp_tac(simpset() addsimps[rho_emb_apply2,eps_id]) 1);
qed "rho_emb_id";

(* Shorter proof, 23 against 62. *)

Goal (* rho_emb_cont *)
    "[|emb_chain(DD,ee); n \\<in> nat|] ==>   \
\    rho_emb(DD,ee,n): cont(DD`n,Dinf(DD,ee))";
by (rtac contI 1);
brr[rho_emb_fun] 1;
by (rtac rel_DinfI 1);
by (SELECT_GOAL(rewtac rho_emb_def) 1);
by (Asm_simp_tac 1);
brr[eps_cont RS cont_mono, Dinf_prod,apply_type,rho_emb_fun] 1;
(* Continuity, different order, slightly different proofs. *)
by (stac lub_Dinf 1);
by (rtac chainI 1);
brr[lam_type, rho_emb_fun RS apply_type, chain_in] 1;
by (Asm_simp_tac 1);
by (rtac rel_DinfI 1);
by (asm_simp_tac(simpset() addsimps [rho_emb_apply2,chain_in]) 1);
brr[eps_cont RS cont_mono, chain_rel, Dinf_prod, rho_emb_fun RS apply_type, chain_in,nat_succI] 1;
(* Now, back to the result of applying lub_Dinf *)
by (asm_simp_tac(simpset() addsimps [rho_emb_apply2,chain_in]) 1);
by (stac rho_emb_apply1 1);
brr[cpo_lub RS islub_in, emb_chain_cpo] 1;
by (rtac fun_extension 1);
brr[lam_type, eps_cont RS cont_fun RS apply_type, cpo_lub RS islub_in, emb_chain_cpo] 1;
brr[cont_chain,eps_cont,emb_chain_cpo] 1;
by (Asm_simp_tac 1);
by (asm_simp_tac(simpset() addsimps[eps_cont RS cont_lub]) 1);
qed "rho_emb_cont";

(* 32 vs 61, using safe_tac with imp in asm would be unfortunate (5steps) *)

Goal (* lemma1 *)
    "[|m le n; emb_chain(DD,ee); x \\<in> set(Dinf(DD,ee)); m \\<in> nat; n \\<in> nat|] ==>   \
\    rel(DD`n,e_less(DD,ee,m,n)`(x`m),x`n)";
by (etac rev_mp 1);  (* For induction proof *)
by (induct_tac "n" 1);
by (rtac impI 1);
by (asm_full_simp_tac (simpset() addsimps [e_less_eq]) 1);
by (stac id_conv 1);
brr[apply_type,Dinf_prod,cpo_refl,emb_chain_cpo,nat_0I] 1;
by (asm_full_simp_tac (simpset() addsimps [le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (dtac mp 1 THEN atac 1);
by (rtac cpo_trans 1);
by (stac e_less_le 2);
brr[emb_chain_cpo,nat_succI] 1;
by (stac comp_fun_apply 1);
brr[emb_chain_emb RS emb_cont, e_less_cont, cont_fun, apply_type, Dinf_prod] 1;
by (res_inst_tac[("y","x`xa")](emb_chain_emb RS emb_cont RS cont_mono) 1);
brr[e_less_cont RS cont_fun, apply_type,Dinf_prod] 1;
by (res_inst_tac[("x1","x"),("n1","xa")](Dinf_eq RS subst) 1);
by (rtac (comp_fun_apply RS subst) 3);
by (res_inst_tac
  [("P",
    "%z. rel(DD ` succ(xa), \
\    (ee ` xa O Rp(?DD46(xa) ` xa,?DD46(xa) ` succ(xa),?ee46(xa) ` xa)) ` \
\            (x ` succ(xa)),z)")](id_conv RS subst) 6);
by (rtac rel_cf 7); 
(* Dinf and cont_fun doesn't go well together, both Pi(_,%x._). *)
(* brr solves 11 of 12 subgoals *)
brr[Dinf_prod RS apply_type, cont_fun, Rp_cont, e_less_cont, emb_cont, emb_chain_emb, emb_chain_cpo, apply_type, embRp_rel, disjI1 RS (le_succ_iff RS iffD2), nat_succI] 1;
by (asm_full_simp_tac (simpset() addsimps [e_less_eq]) 1);
by (stac id_conv 1);
by (auto_tac (claset() addIs [apply_type,Dinf_prod,emb_chain_cpo], simpset()));
val lemma1 = result();

(* 18 vs 40 *)

Goal (* lemma2 *)
    "[|n le m; emb_chain(DD,ee); x \\<in> set(Dinf(DD,ee)); m \\<in> nat; n \\<in> nat|] ==>   \
\    rel(DD`n,e_gr(DD,ee,m,n)`(x`m),x`n)";
by (etac rev_mp 1);  (* For induction proof *)
by (induct_tac "m" 1);
by (rtac impI 1);
by (asm_full_simp_tac (simpset() addsimps [e_gr_eq]) 1);
by (stac id_conv 1);
brr[apply_type,Dinf_prod,cpo_refl,emb_chain_cpo,nat_0I] 1;
by (asm_full_simp_tac (simpset() addsimps [le_succ_iff]) 1);
by (rtac impI 1);
by (etac disjE 1);
by (dtac mp 1 THEN atac 1);
by (stac e_gr_le 1);
by (stac comp_fun_apply 4);
by (stac Dinf_eq 7);
brr[emb_chain_emb, emb_chain_cpo, Rp_cont, e_gr_cont, cont_fun, emb_cont, apply_type,Dinf_prod,nat_succI] 1;
by (asm_full_simp_tac (simpset() addsimps [e_gr_eq]) 1);
by (stac id_conv 1);
by (auto_tac (claset() addIs [apply_type,Dinf_prod,emb_chain_cpo], simpset()));
val lemma2 = result();

Goalw [eps_def] (* eps1 *)
    "[|emb_chain(DD,ee); x \\<in> set(Dinf(DD,ee)); m \\<in> nat; n \\<in> nat|] ==>   \
\    rel(DD`n,eps(DD,ee,m,n)`(x`m),x`n)";
by (split_tac [split_if] 1);
brr[conjI, impI, lemma1, not_le_iff_lt RS iffD1 RS leI RS lemma2, nat_into_Ord] 1;
qed "eps1";

(* The following theorem is needed/useful due to type check for rel_cfI, 
   but also elsewhere. 
   Look for occurences of rel_cfI, rel_DinfI, etc to evaluate the problem. *)

Goal (* lam_Dinf_cont *)
  "[| emb_chain(DD,ee); n \\<in> nat |] ==> \
\  (\\<lambda>x \\<in> set(Dinf(DD,ee)). x`n) \\<in> cont(Dinf(DD,ee),DD`n)";
by (rtac contI 1);
brr[lam_type,apply_type,Dinf_prod] 1;
by (Asm_simp_tac 1);
brr[rel_Dinf] 1;
by (stac beta 1);
by (auto_tac (claset() addIs [cpo_Dinf,islub_in,cpo_lub], simpset()));
by (asm_simp_tac(simpset() addsimps[chain_in,lub_Dinf]) 1);
qed "lam_Dinf_cont";

Goalw  [rho_proj_def] (* rho_projpair *)
    "[| emb_chain(DD,ee); n \\<in> nat |] ==> \
\    projpair(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n),rho_proj(DD,ee,n))";
by (rtac projpairI 1);
brr[rho_emb_cont] 1;
(* lemma used, introduced because same fact needed below due to rel_cfI. *)
brr[lam_Dinf_cont] 1;
(*-----------------------------------------------*)
(* This part is 7 lines, but 30 in HOL (75% reduction!) *)
by (rtac fun_extension 1);
by (stac id_conv 3);
by (stac comp_fun_apply 4);
by (stac beta 7);
by (stac rho_emb_id 8);
brr[comp_fun, id_type, lam_type, rho_emb_fun, Dinf_prod RS apply_type, apply_type,refl] 1;
(*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
by (rtac rel_cfI 1); (* ------------------>>>Yields type cond, not in HOL *)
by (stac id_conv 1);
by (stac comp_fun_apply 2);
by (stac beta 5);
by (stac rho_emb_apply1 6);
by (rtac rel_DinfI 7); (* ------------------>>>Yields type cond, not in HOL *)
by (stac beta 7);
brr(eps1::lam_type::rho_emb_fun::eps_fun:: (* Dinf_prod bad with lam_type *)
    [Dinf_prod RS apply_type, refl]) 1;
brr[apply_type, eps_fun, Dinf_prod, comp_pres_cont, rho_emb_cont, lam_Dinf_cont,id_cont,cpo_Dinf,emb_chain_cpo] 1;
qed "rho_projpair";

Goalw [emb_def]
  "[| emb_chain(DD,ee); n \\<in> nat |] ==> emb(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))";
by (auto_tac (claset() addIs [exI,rho_projpair], simpset()));
qed "emb_rho_emb";

Goal "[| emb_chain(DD,ee); n \\<in> nat |] ==>   \
\  rho_proj(DD,ee,n) \\<in> cont(Dinf(DD,ee),DD`n)";
by (auto_tac (claset() addIs [rho_projpair,projpair_p_cont], simpset()));
qed "rho_proj_cont";

(*----------------------------------------------------------------------*)
(* Commutivity and universality.                                        *)
(*----------------------------------------------------------------------*)

val prems = Goalw [commute_def]  (* commuteI *)
  "[| !!n. n \\<in> nat ==> emb(DD`n,E,r(n));   \
\     !!m n. [|m le n; m \\<in> nat; n \\<in> nat|] ==> r(n) O eps(DD,ee,m,n) = r(m) |] ==>  \
\  commute(DD,ee,E,r)";
by Safe_tac;
by (REPEAT (ares_tac prems 1));
qed "commuteI";

Goalw [commute_def]  (* commute_emb *)
  "[| commute(DD,ee,E,r); n \\<in> nat |] ==> emb(DD`n,E,r(n))";
by (Fast_tac 1);
qed "commute_emb";

AddTCs [commute_emb];

Goalw [commute_def]  (* commute_eq *)
  "[| commute(DD,ee,E,r); m le n; m \\<in> nat; n \\<in> nat |] ==>   \
\  r(n) O eps(DD,ee,m,n) = r(m) ";
by (Blast_tac 1);
qed "commute_eq";

(* Shorter proof: 11 vs 46 lines. *)

Goal (* rho_emb_commute *)
  "emb_chain(DD,ee) ==> commute(DD,ee,Dinf(DD,ee),rho_emb(DD,ee))";
by (rtac commuteI 1);
brr[emb_rho_emb] 1;
by (rtac fun_extension 1);       (* Manual instantiation in HOL. *)
by (stac comp_fun_apply 3);
by (rtac fun_extension 6); (* Next, clean up and instantiate unknowns *)
brr[comp_fun,rho_emb_fun,eps_fun,Dinf_prod,apply_type] 1; 
by (asm_simp_tac
    (simpset() addsimps[rho_emb_apply2, eps_fun RS apply_type]) 1);
by (rtac (comp_fun_apply RS subst) 1);
by (rtac (eps_split_left RS subst) 4);
by (auto_tac (claset() addIs [eps_fun], simpset()));
qed "rho_emb_commute";

val prems = goal Arith.thy "n \\<in> nat ==> n le succ(n)";
by (REPEAT (ares_tac ((disjI1 RS(le_succ_iff RS iffD2))::le_refl::nat_into_Ord::prems) 1));
qed "le_succ";

(* Shorter proof: 21 vs 83 (106 - 23, due to OAssoc complication) *)

Goal (* commute_chain *)
  "[| commute(DD,ee,E,r); emb_chain(DD,ee); cpo(E) |] ==>  \
\  chain(cf(E,E),\\<lambda>n \\<in> nat. r(n) O Rp(DD`n,E,r(n)))";
by (rtac chainI 1);
by (blast_tac (claset() addIs [lam_type, cont_cf, comp_pres_cont, commute_emb, Rp_cont, emb_cont, emb_chain_cpo]) 1);
by (Asm_simp_tac 1);
by (res_inst_tac[("r1","r"),("m1","n")](commute_eq RS subst) 1);
brr[le_succ,nat_succI] 1;
by (stac Rp_comp 1);
brr[emb_eps,commute_emb,emb_chain_cpo,le_succ,nat_succI] 1;
by (rtac (comp_assoc RS subst) 1);   (* Remember that comp_assoc is simpler in Isa *)
by (res_inst_tac[("r1","r(succ(n))")](comp_assoc RS ssubst) 1);
by (rtac comp_mono 1);
by (REPEAT 
    (blast_tac (claset() addIs [comp_pres_cont, eps_cont, emb_eps, 
				commute_emb, Rp_cont, emb_cont, 
				emb_chain_cpo,le_succ]) 1));
by (res_inst_tac[("b","r(succ(n))")](comp_id RS subst) 1); (* 1 subst too much *)
by (rtac comp_mono 2);
by (REPEAT
    (blast_tac (claset() addIs [comp_pres_cont, eps_cont, emb_eps, emb_id, 
				commute_emb, Rp_cont, emb_cont, cont_fun,
				emb_chain_cpo,le_succ]) 1));
by (stac comp_id 1); (* Undoes "1 subst too much", typing next anyway *)
by (REPEAT
    (blast_tac (claset() addIs [cont_fun, Rp_cont, emb_cont, commute_emb, 
				cont_cf, cpo_cf, emb_chain_cpo,
				embRp_rel,emb_eps,le_succ]) 1));
qed "commute_chain";

Goal (* rho_emb_chain *)
  "emb_chain(DD,ee) ==>  \
\  chain(cf(Dinf(DD,ee),Dinf(DD,ee)),   \
\        \\<lambda>n \\<in> nat. rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))";
by (auto_tac (claset() addIs [commute_chain,rho_emb_commute,cpo_Dinf], simpset()));
qed "rho_emb_chain";

Goal "[| emb_chain(DD,ee); x \\<in> set(Dinf(DD,ee)) |] ==>  \
\     chain(Dinf(DD,ee),   \
\         \\<lambda>n \\<in> nat.   \
\          (rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))`x)";
by (dtac (rho_emb_chain RS chain_cf) 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
qed "rho_emb_chain_apply1";

Goal "[| chain(iprod(DD),X); emb_chain(DD,ee); n \\<in> nat |] ==>  \
\     chain(DD`n,\\<lambda>m \\<in> nat. X `m `n)";
by (auto_tac (claset() addIs [chain_iprod,emb_chain_cpo], simpset()));
qed "chain_iprod_emb_chain";

Goal (* rho_emb_chain_apply2 *)
  "[| emb_chain(DD,ee); x \\<in> set(Dinf(DD,ee)); n \\<in> nat |] ==>  \
\  chain  \
\   (DD`n,   \
\    \\<lambda>xa \\<in> nat.  \
\     (rho_emb(DD, ee, xa) O Rp(DD ` xa, Dinf(DD, ee),rho_emb(DD, ee, xa))) ` \
\      x ` n)";
by (forward_tac [rho_emb_chain_apply1 RS chain_Dinf RS chain_iprod_emb_chain] 1);
by Auto_tac;
qed "rho_emb_chain_apply2";

(* Shorter proof: 32 vs 72 (roughly), Isabelle proof has lemmas. *)

Goal (* rho_emb_lub *)
  "emb_chain(DD,ee) ==>  \
\  lub(cf(Dinf(DD,ee),Dinf(DD,ee)),   \
\      \\<lambda>n \\<in> nat. rho_emb(DD,ee,n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))) = \
\  id(set(Dinf(DD,ee)))";
by (rtac cpo_antisym 1);
by (rtac cpo_cf 1); (* Instantiate variable, continued below (would loop otherwise) *)
brr[cpo_Dinf] 1; 
by (rtac islub_least 1);
brr[cpo_lub,rho_emb_chain,cpo_cf,cpo_Dinf,isubI,cont_cf,id_cont] 1;
by (Asm_simp_tac 1);
brr[embRp_rel,emb_rho_emb,emb_chain_cpo,cpo_Dinf] 1;
by (rtac rel_cfI 1);
by (asm_simp_tac (simpset() addsimps[lub_cf,rho_emb_chain,cpo_Dinf]) 1);
by (rtac rel_DinfI 1); (* Addtional assumptions *)
by (stac lub_Dinf 1);
brr[rho_emb_chain_apply1] 1;  
brr[Dinf_prod, cpo_lub RS islub_in, id_cont, cpo_Dinf, cpo_cf, cf_cont, rho_emb_chain, rho_emb_chain_apply1, id_cont RS cont_cf] 2;
by (Asm_simp_tac 1);
by (rtac dominate_islub 1);
by (rtac cpo_lub 3);
brr[rho_emb_chain_apply2,emb_chain_cpo] 3;
by (res_inst_tac[("x1","x`n")](chain_const RS chain_fun) 3);
brr[islub_const, apply_type, Dinf_prod, emb_chain_cpo, chain_fun, rho_emb_chain_apply2] 2;
by (rtac dominateI 1);
by (assume_tac 1); 
by (Asm_simp_tac 1);
by (stac comp_fun_apply 1);
brr[cont_fun,Rp_cont,emb_cont,emb_rho_emb,cpo_Dinf,emb_chain_cpo] 1;
by (stac ((rho_projpair RS Rp_unique)) 1);
by (SELECT_GOAL(rewtac rho_proj_def) 5);
by (Asm_simp_tac 5);
by (stac rho_emb_id 5);
by (auto_tac (claset() addIs [cpo_Dinf,apply_type,Dinf_prod,emb_chain_cpo], 
	      simpset()));
qed "rho_emb_lub";

Goal (* theta_chain, almost same prf as commute_chain *)
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \
\  chain(cf(E,G),\\<lambda>n \\<in> nat. f(n) O Rp(DD`n,E,r(n)))";
by (rtac chainI 1);
by (blast_tac (claset() addIs [lam_type, cont_cf, comp_pres_cont, commute_emb, Rp_cont,emb_cont,emb_chain_cpo]) 1);
by (Asm_simp_tac 1);
by (res_inst_tac[("r1","r"),("m1","n")](commute_eq RS subst) 1);
by (res_inst_tac[("r1","f"),("m1","n")](commute_eq RS subst) 5);
brr[le_succ,nat_succI] 1;
by (stac Rp_comp 1);
brr[emb_eps,commute_emb,emb_chain_cpo,le_succ,nat_succI] 1;
by (rtac (comp_assoc RS subst) 1);   (* Remember that comp_assoc is simpler in Isa *)
by (res_inst_tac[("r1","f(succ(n))")](comp_assoc RS ssubst) 1);
by (rtac comp_mono 1);
by (REPEAT (blast_tac (claset() addIs [comp_pres_cont, eps_cont, emb_eps, commute_emb, Rp_cont, emb_cont,emb_chain_cpo,le_succ]) 1));
by (res_inst_tac[("b","f(succ(n))")](comp_id RS subst) 1); (* 1 subst too much *)
by (rtac comp_mono 2);
by (REPEAT (blast_tac (claset() addIs[comp_pres_cont, eps_cont, emb_eps, emb_id, commute_emb, Rp_cont, emb_cont,cont_fun,emb_chain_cpo,le_succ]) 1));
by (stac comp_id 1); (* Undoes "1 subst too much", typing next anyway *)
by (REPEAT
    (blast_tac (claset() addIs[cont_fun, Rp_cont, emb_cont, commute_emb,
			       cont_cf, cpo_cf,emb_chain_cpo,
			       embRp_rel,emb_eps,le_succ]) 1));
qed "theta_chain";

Goal (* theta_proj_chain, same prf as theta_chain *)
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \
\  chain(cf(G,E),\\<lambda>n \\<in> nat. r(n) O Rp(DD`n,G,f(n)))";
by (rtac chainI 1);
by (blast_tac (claset() addIs [lam_type, cont_cf, comp_pres_cont, commute_emb, Rp_cont,emb_cont,emb_chain_cpo]) 1);
by (Asm_simp_tac 1);
by (res_inst_tac[("r1","r"),("m1","n")](commute_eq RS subst) 1);
by (res_inst_tac[("r1","f"),("m1","n")](commute_eq RS subst) 5);
brr[le_succ,nat_succI] 1;
by (stac Rp_comp 1);
brr[emb_eps,commute_emb,emb_chain_cpo,le_succ,nat_succI] 1;
by (rtac (comp_assoc RS subst) 1);   (* Remember that comp_assoc is simpler in Isa *)
by (res_inst_tac[("r1","r(succ(n))")](comp_assoc RS ssubst) 1);
by (rtac comp_mono 1);
by (REPEAT (blast_tac (claset() addIs [comp_pres_cont, eps_cont, emb_eps, commute_emb, Rp_cont, emb_cont,emb_chain_cpo,le_succ]) 1));
by (res_inst_tac[("b","r(succ(n))")](comp_id RS subst) 1); (* 1 subst too much *)
by (rtac comp_mono 2);
by (REPEAT (blast_tac (claset() addIs[comp_pres_cont, eps_cont, emb_eps, emb_id, commute_emb, Rp_cont, emb_cont,cont_fun,emb_chain_cpo,le_succ]) 1));
by (stac comp_id 1); (* Undoes "1 subst too much", typing next anyway *)
by (REPEAT
    (blast_tac (claset() addIs[cont_fun, Rp_cont, emb_cont, commute_emb, 
			       cont_cf, cpo_cf,emb_chain_cpo,embRp_rel,
			       emb_eps,le_succ]) 1));
qed "theta_proj_chain";

(* Simplification with comp_assoc is possible inside a \\<lambda>-abstraction,
   because it does not have assumptions. If it had, as the HOL-ST theorem 
   too strongly has, we would be in deep trouble due to the lack of proper
   conditional rewriting (a HOL contrib provides something that works). *)

(* Controlled simplification inside lambda: introduce lemmas *)

Goal "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G); x \\<in> nat |] ==>  \
\  r(x) O Rp(DD ` x, G, f(x)) O f(x) O Rp(DD ` x, E, r(x)) =  \
\  r(x) O Rp(DD ` x, E, r(x))";
by (res_inst_tac[("s1","f(x)")](comp_assoc RS subst) 1);
by (stac embRp_eq 1);
by (stac id_comp 4);
by (auto_tac (claset() addIs [cont_fun,Rp_cont,commute_emb,emb_chain_cpo], 
	      simpset()));
val lemma = result();


(* Shorter proof (but lemmas): 19 vs 79 (103 - 24, due to OAssoc)  *)

Goalw [projpair_def,rho_proj_def] (* theta_projpair *)
  "[| lub(cf(E,E), \\<lambda>n \\<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));  \
\     commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \  
\  projpair   \
\   (E,G,   \
\    lub(cf(E,G), \\<lambda>n \\<in> nat. f(n) O Rp(DD`n,E,r(n))),  \
\    lub(cf(G,E), \\<lambda>n \\<in> nat. r(n) O Rp(DD`n,G,f(n))))";
by Safe_tac;
by (stac comp_lubs 3);
(* The following one line is 15 lines in HOL, and includes existentials. *)
brr[cf_cont,islub_in,cpo_lub,cpo_cf,theta_chain,theta_proj_chain] 1;
by (simp_tac (simpset() addsimps[comp_assoc]) 1);
by (asm_simp_tac (simpset() addsimps[lemma]) 1);
by (stac comp_lubs 1);
brr[cf_cont,islub_in,cpo_lub,cpo_cf,theta_chain,theta_proj_chain] 1;
by (simp_tac (simpset() addsimps[comp_assoc]) 1);
by (asm_simp_tac (simpset() addsimps[lemma]) 1);
by (rtac dominate_islub 1);
by (rtac cpo_lub 2);
brr[commute_chain, commute_emb, islub_const, cont_cf, id_cont,
    cpo_cf, chain_fun,chain_const] 2;
by (rtac dominateI 1);
by (assume_tac 1); 
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [embRp_rel,commute_emb,emb_chain_cpo]) 1);
qed "theta_projpair";

Goalw [emb_def]
  "[| lub(cf(E,E), \\<lambda>n \\<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));  \
\     commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \  
\  emb(E,G,lub(cf(E,G), \\<lambda>n \\<in> nat. f(n) O Rp(DD`n,E,r(n))))";
by (blast_tac (claset() addIs [theta_projpair]) 1);
qed "emb_theta";

Goal (* mono_lemma *)
  "[| g \\<in> cont(D,D'); cpo(D); cpo(D'); cpo(E) |] ==>  \
\  (\\<lambda>f \\<in> cont(D',E). f O g) \\<in> mono(cf(D',E),cf(D,E))";
by (rtac monoI 1);
by (REPEAT(dtac cf_cont 2));
by (Asm_simp_tac 2);
by (rtac comp_mono 2);
by (SELECT_GOAL(rewrite_goals_tac[set_def,cf_def]) 1);
by (Asm_simp_tac 1);
by (auto_tac (claset() addIs [lam_type,comp_pres_cont,cpo_cf,cont_cf], 
	      simpset()));
qed "mono_lemma";

Goal "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\        emb_chain(DD,ee); cpo(E); cpo(G); n \\<in> nat |] ==>  \  
\     (\\<lambda>na \\<in> nat. (\\<lambda>f \\<in> cont(E, G). f O r(n)) `  \
\      ((\\<lambda>n \\<in> nat. f(n) O Rp(DD ` n, E, r(n))) ` na))  = \
\     (\\<lambda>na \\<in> nat. (f(na) O Rp(DD ` na, E, r(na))) O r(n))";
by (rtac fun_extension 1);
by (fast_tac (claset() addIs [lam_type]) 1);
by (Asm_simp_tac 2);
by (fast_tac (claset() addIs [lam_type]) 1);
val lemma = result();

Goal "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\        emb_chain(DD,ee); cpo(E); cpo(G); n \\<in> nat |] ==>  \  
\     chain(cf(DD`n,G),\\<lambda>x \\<in> nat. (f(x) O Rp(DD ` x, E, r(x))) O r(n))";
by (rtac (lemma RS subst) 1);
by (REPEAT
    (blast_tac (claset() addIs[theta_chain,emb_chain_cpo,
		 commute_emb RS emb_cont RS mono_lemma RS mono_chain]) 1));
qed "chain_lemma";

Goalw [suffix_def] (* suffix_lemma *)
  "[| commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G); cpo(DD`x); x \\<in> nat |] ==>  \  
\  suffix(\\<lambda>n \\<in> nat. (f(n) O Rp(DD`n,E,r(n))) O r(x),x) = (\\<lambda>n \\<in> nat. f(x))";
by (Asm_simp_tac 1);
by (rtac (lam_type RS fun_extension) 1); 
by (REPEAT (blast_tac (claset() addIs [lam_type, comp_fun, cont_fun, Rp_cont, emb_cont, commute_emb, add_type,emb_chain_cpo]) 1));
by (Asm_simp_tac 1);
by (subgoal_tac "f(x #+ xa) O      \
\                (Rp(DD ` (x #+ xa), E, r(x #+ xa)) O r(x #+ xa)) O  \
\                eps(DD, ee, x, x #+ xa)   =   f(x)" 1);
by (asm_simp_tac (simpset() addsimps [embRp_eq,eps_fun RS id_comp,commute_emb,
				      emb_chain_cpo]) 2);
by (blast_tac (claset() addIs [commute_eq,add_type,add_le_self]) 2);
by (asm_full_simp_tac 
    (simpset() addsimps [comp_assoc,commute_eq,add_le_self]) 1);
qed "suffix_lemma";



val prems = Goalw [mediating_def]
  "[|emb(E,G,t);  !!n. n \\<in> nat ==> f(n) = t O r(n) |]==>mediating(E,G,r,f,t)";
by (Safe_tac);
by (REPEAT (ares_tac prems 1));
qed "mediatingI";

Goalw [mediating_def] "mediating(E,G,r,f,t) ==> emb(E,G,t)";
by (Fast_tac 1);
qed "mediating_emb";

Goalw [mediating_def] "[| mediating(E,G,r,f,t); n \\<in> nat |] ==> f(n) = t O r(n)";
by (Blast_tac 1);
qed "mediating_eq";

Goal (* lub_universal_mediating *)
  "[| lub(cf(E,E), \\<lambda>n \\<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));  \
\     commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>  \  
\  mediating(E,G,r,f,lub(cf(E,G), \\<lambda>n \\<in> nat. f(n) O Rp(DD`n,E,r(n))))";
brr[mediatingI,emb_theta] 1;
by (res_inst_tac[("b","r(n)")](lub_const RS subst) 1);
by (stac comp_lubs 3);
by (REPEAT (blast_tac (claset() addIs [cont_cf, emb_cont, commute_emb, cpo_cf, theta_chain, chain_const, emb_chain_cpo]) 1));
by (Simp_tac 1);
by (res_inst_tac [("n1","n")] (lub_suffix RS subst) 1);
brr[chain_lemma,cpo_cf,emb_chain_cpo] 1;
by (asm_simp_tac 
    (simpset() addsimps [suffix_lemma, lub_const, cont_cf, emb_cont, 
			 commute_emb, cpo_cf, emb_chain_cpo]) 1);
qed "lub_universal_mediating";

Goal (* lub_universal_unique *)
  "[| mediating(E,G,r,f,t);    \
\     lub(cf(E,E), \\<lambda>n \\<in> nat. r(n) O Rp(DD`n,E,r(n))) = id(set(E));   \
\     commute(DD,ee,E,r); commute(DD,ee,G,f);   \
\     emb_chain(DD,ee); cpo(E); cpo(G) |] ==>   \
\  t = lub(cf(E,G), \\<lambda>n \\<in> nat. f(n) O Rp(DD`n,E,r(n)))";
by (res_inst_tac[("b","t")](comp_id RS subst) 1);
by (etac subst 2);
by (res_inst_tac[("b","t")](lub_const RS subst) 2);
by (stac comp_lubs 4);
by (asm_simp_tac (simpset() addsimps [comp_assoc, 
				      inst "f" "f" mediating_eq]) 9);
brr[cont_fun, emb_cont, mediating_emb, cont_cf, cpo_cf, chain_const, 
    commute_chain,emb_chain_cpo] 1;
qed "lub_universal_unique";

(*---------------------------------------------------------------------*)
(* Dinf yields the inverse_limit, stated as rho_emb_commute and        *)
(* Dinf_universal.                                                     *)
(*---------------------------------------------------------------------*)

Goal (* Dinf_universal *)
  "[| commute(DD,ee,G,f); emb_chain(DD,ee); cpo(G) |] ==>   \
\  mediating   \
\   (Dinf(DD,ee),G,rho_emb(DD,ee),f,   \
\    lub(cf(Dinf(DD,ee),G),   \
\        \\<lambda>n \\<in> nat. f(n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n)))) &  \
\  (\\<forall>t. mediating(Dinf(DD,ee),G,rho_emb(DD,ee),f,t) -->  \
\    t = lub(cf(Dinf(DD,ee),G),   \
\        \\<lambda>n \\<in> nat. f(n) O Rp(DD`n,Dinf(DD,ee),rho_emb(DD,ee,n))))";
by Safe_tac;
brr[lub_universal_mediating,rho_emb_commute,rho_emb_lub,cpo_Dinf] 1;
by (auto_tac (claset() addIs [lub_universal_unique,rho_emb_commute,rho_emb_lub,cpo_Dinf], simpset()));
qed "Dinf_universal";

