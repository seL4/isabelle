(*  Title:      HOLCF/IOA/meta_theory/Seq.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

*)  

Addsimps (sfinite.intrs @ seq.rews);


(* Instead of adding UU_neq_nil every equation UU~=x could be changed to x~=UU *)
Goal "UU ~=nil";
by (res_inst_tac [("s1","UU"),("t1","nil")]  (sym RS rev_contrapos) 1);
by (REPEAT (Simp_tac 1));
qed"UU_neq_nil";

Addsimps [UU_neq_nil];




(* ------------------------------------------------------------------------------------- *)


(* ----------------------------------------------------  *)
       section "recursive equations of operators";
(* ----------------------------------------------------  *)


(* ----------------------------------------------------------- *)
(*                        smap                                 *)
(* ----------------------------------------------------------- *)

bind_thm ("smap_unfold", fix_prover2 thy smap_def 
   "smap = (LAM f tr. case tr of  \
 \                         nil  => nil \
 \                       | x##xs => f`x ## smap`f`xs)");

Goal "smap`f`nil=nil"; 
by (stac smap_unfold 1);
by (Simp_tac 1);
qed"smap_nil";

Goal "smap`f`UU=UU"; 
by (stac smap_unfold 1);
by (Simp_tac 1);
qed"smap_UU";

Goal 
"[|x~=UU|] ==> smap`f`(x##xs)= (f`x)##smap`f`xs"; 
by (rtac trans 1);
by (stac smap_unfold 1);
by (Asm_full_simp_tac 1);
by (rtac refl 1);
qed"smap_cons";

(* ----------------------------------------------------------- *)
(*                        sfilter                              *)
(* ----------------------------------------------------------- *)

bind_thm ("sfilter_unfold", fix_prover2 thy sfilter_def 
  "sfilter = (LAM P tr. case tr of  \
 \         nil   => nil \
 \       | x##xs => If P`x then x##(sfilter`P`xs) else sfilter`P`xs fi)");

Goal "sfilter`P`nil=nil";
by (stac sfilter_unfold 1);
by (Simp_tac 1);
qed"sfilter_nil";

Goal "sfilter`P`UU=UU";
by (stac sfilter_unfold 1);
by (Simp_tac 1);
qed"sfilter_UU";

Goal 
"x~=UU ==> sfilter`P`(x##xs)=   \
\             (If P`x then x##(sfilter`P`xs) else sfilter`P`xs fi)";
by (rtac trans 1);
by (stac sfilter_unfold 1);
by (Asm_full_simp_tac 1);
by (rtac refl 1);
qed"sfilter_cons";

(* ----------------------------------------------------------- *)
(*                        sforall2                             *)
(* ----------------------------------------------------------- *)

bind_thm ("sforall2_unfold", fix_prover2 thy sforall2_def 
   "sforall2 = (LAM P tr. case tr of  \
 \                         nil   => TT \
 \                       | x##xs => (P`x andalso sforall2`P`xs))");

Goal "sforall2`P`nil=TT"; 
by (stac sforall2_unfold 1);
by (Simp_tac 1);
qed"sforall2_nil";

Goal "sforall2`P`UU=UU"; 
by (stac sforall2_unfold 1);
by (Simp_tac 1);
qed"sforall2_UU";

Goal 
"x~=UU ==> sforall2`P`(x##xs)= ((P`x) andalso sforall2`P`xs)";
by (rtac trans 1);
by (stac sforall2_unfold 1);
by (Asm_full_simp_tac 1);
by (rtac refl 1);
qed"sforall2_cons";


(* ----------------------------------------------------------- *)
(*                        stakewhile                           *)
(* ----------------------------------------------------------- *)


bind_thm ("stakewhile_unfold", fix_prover2 thy stakewhile_def 
   "stakewhile = (LAM P tr. case tr of  \
 \                         nil   => nil \
 \                       | x##xs => (If P`x then x##(stakewhile`P`xs) else nil fi))");

Goal "stakewhile`P`nil=nil"; 
by (stac stakewhile_unfold 1);
by (Simp_tac 1);
qed"stakewhile_nil";

Goal "stakewhile`P`UU=UU"; 
by (stac stakewhile_unfold 1);
by (Simp_tac 1);
qed"stakewhile_UU";

Goal 
"x~=UU ==> stakewhile`P`(x##xs) =   \
\             (If P`x then x##(stakewhile`P`xs) else nil fi)";
by (rtac trans 1);
by (stac stakewhile_unfold 1);
by (Asm_full_simp_tac 1);
by (rtac refl 1);
qed"stakewhile_cons";

(* ----------------------------------------------------------- *)
(*                        sdropwhile                           *)
(* ----------------------------------------------------------- *)


bind_thm ("sdropwhile_unfold", fix_prover2 thy sdropwhile_def 
   "sdropwhile = (LAM P tr. case tr of  \
 \                         nil   => nil \
 \                       | x##xs => (If P`x then sdropwhile`P`xs else tr fi))");

Goal "sdropwhile`P`nil=nil"; 
by (stac sdropwhile_unfold 1);
by (Simp_tac 1);
qed"sdropwhile_nil";

Goal "sdropwhile`P`UU=UU"; 
by (stac sdropwhile_unfold 1);
by (Simp_tac 1);
qed"sdropwhile_UU";

Goal 
"x~=UU ==> sdropwhile`P`(x##xs) =   \
\             (If P`x then sdropwhile`P`xs else x##xs fi)";
by (rtac trans 1);
by (stac sdropwhile_unfold 1);
by (Asm_full_simp_tac 1);
by (rtac refl 1);
qed"sdropwhile_cons";


(* ----------------------------------------------------------- *)
(*                        slast                                 *)
(* ----------------------------------------------------------- *)


bind_thm ("slast_unfold", fix_prover2 thy slast_def 
   "slast = (LAM tr. case tr of  \
 \                         nil   => UU \
 \                       | x##xs => (If is_nil`xs then x else slast`xs fi))");


Goal "slast`nil=UU"; 
by (stac slast_unfold 1);
by (Simp_tac 1);
qed"slast_nil";

Goal "slast`UU=UU"; 
by (stac slast_unfold 1);
by (Simp_tac 1);
qed"slast_UU";

Goal 
"x~=UU ==> slast`(x##xs)= (If is_nil`xs then x else slast`xs fi)";
by (rtac trans 1);
by (stac slast_unfold 1);
by (Asm_full_simp_tac 1);
by (rtac refl 1);
qed"slast_cons";


(* ----------------------------------------------------------- *)
(*                        sconc                                 *)
(* ----------------------------------------------------------- *)

bind_thm ("sconc_unfold", fix_prover2 thy sconc_def 
   "sconc = (LAM t1 t2. case t1 of  \
 \                         nil   => t2 \
 \                       | x##xs => x ## (xs @@ t2))");


Goal "nil @@ y = y"; 
by (stac sconc_unfold 1);
by (Simp_tac 1);
qed"sconc_nil";

Goal "UU @@ y=UU"; 
by (stac sconc_unfold 1);
by (Simp_tac 1);
qed"sconc_UU";

Goal "(x##xs) @@ y=x##(xs @@ y)";
by (rtac trans 1);
by (stac sconc_unfold 1);
by (Asm_full_simp_tac 1);
by (case_tac "x=UU" 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"sconc_cons";

Addsimps [sconc_nil,sconc_UU,sconc_cons];


(* ----------------------------------------------------------- *)
(*                        sflat                                 *)
(* ----------------------------------------------------------- *)

bind_thm ("sflat_unfold", fix_prover2 thy sflat_def 
   "sflat = (LAM tr. case tr of  \
 \                         nil   => nil \
 \                       | x##xs => x @@ sflat`xs)");

Goal "sflat`nil=nil"; 
by (stac sflat_unfold 1);
by (Simp_tac 1);
qed"sflat_nil";

Goal "sflat`UU=UU"; 
by (stac sflat_unfold 1);
by (Simp_tac 1);
qed"sflat_UU";

Goal "sflat`(x##xs)= x@@(sflat`xs)"; 
by (rtac trans 1);
by (stac sflat_unfold 1);
by (Asm_full_simp_tac 1);
by (case_tac "x=UU" 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"sflat_cons";




(* ----------------------------------------------------------- *)
(*                        szip                                 *)
(* ----------------------------------------------------------- *)

bind_thm ("szip_unfold", fix_prover2 thy szip_def 
   "szip = (LAM t1 t2. case t1 of \
\               nil   => nil    \
\             | x##xs => (case t2 of     \
\                          nil => UU    \
\                        | y##ys => <x,y>##(szip`xs`ys)))");

Goal "szip`nil`y=nil"; 
by (stac szip_unfold 1);
by (Simp_tac 1);
qed"szip_nil";

Goal "szip`UU`y=UU"; 
by (stac szip_unfold 1);
by (Simp_tac 1);
qed"szip_UU1";

Goal "x~=nil ==> szip`x`UU=UU"; 
by (stac szip_unfold 1);
by (Asm_full_simp_tac 1);
by (res_inst_tac [("x","x")] seq.casedist 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"szip_UU2";

Goal "x~=UU ==> szip`(x##xs)`nil=UU";
by (rtac trans 1);
by (stac szip_unfold 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"szip_cons_nil";

Goal "[| x~=UU; y~=UU|] ==> szip`(x##xs)`(y##ys) = <x,y>##szip`xs`ys";
by (rtac trans 1);
by (stac szip_unfold 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"szip_cons";


Addsimps [sfilter_UU,sfilter_nil,sfilter_cons,
          smap_UU,smap_nil,smap_cons,
          sforall2_UU,sforall2_nil,sforall2_cons,
          slast_UU,slast_nil,slast_cons,
          stakewhile_UU, stakewhile_nil, stakewhile_cons, 
          sdropwhile_UU, sdropwhile_nil, sdropwhile_cons,
          sflat_UU,sflat_nil,sflat_cons,
          szip_UU1,szip_UU2,szip_nil,szip_cons_nil,szip_cons]; 



(* ------------------------------------------------------------------------------------- *)

section "scons, nil";

Goal 
 "[|x~=UU;y~=UU|]==> (x##xs=y##ys) = (x=y & xs=ys)";
by (rtac iffI 1);
by (etac (hd seq.injects) 1);
by Auto_tac;
qed"scons_inject_eq";

Goal "nil<<x ==> nil=x";
by (res_inst_tac [("x","x")] seq.casedist 1);
by (hyp_subst_tac 1);
by (etac antisym_less 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
qed"nil_less_is_nil";

(* ------------------------------------------------------------------------------------- *)

section "sfilter, sforall, sconc";


Goal  "(if b then tr1 else tr2) @@ tr \
        \= (if b then tr1 @@ tr else tr2 @@ tr)";
by (res_inst_tac [("P","b"),("Q","b")] impCE 1);
by (fast_tac HOL_cs 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"if_and_sconc";

Addsimps [if_and_sconc];


Goal "sfilter`P`(x @@ y) = (sfilter`P`x @@ sfilter`P`y)";

by (res_inst_tac[("x","x")] seq.ind 1);
(* adm *)
by (Simp_tac 1);
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (asm_full_simp_tac (simpset() setloop split_If_tac) 1);
qed"sfiltersconc";

Goal "sforall P (stakewhile`P`x)";
by (simp_tac (simpset() addsimps [sforall_def]) 1);
by (res_inst_tac[("x","x")] seq.ind 1);
(* adm *)
by (simp_tac (simpset() addsimps [adm_trick_1]) 1);
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (asm_full_simp_tac (simpset() setloop split_If_tac) 1);
qed"sforallPstakewhileP";

Goal "sforall P (sfilter`P`x)";
by (simp_tac (simpset() addsimps [sforall_def]) 1);
by (res_inst_tac[("x","x")] seq.ind 1);
(* adm *)
by (simp_tac (simpset() addsimps [adm_trick_1]) 1);
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (asm_full_simp_tac (simpset() setloop split_If_tac) 1);
qed"forallPsfilterP";



(* ------------------------------------------------------------------------------------- *)

section "Finite";

(* ----------------------------------------------------  *)
(* Proofs of rewrite rules for Finite:                  *)
(* 1. Finite(nil),   (by definition)                    *)
(* 2. ~Finite(UU),                                      *)
(* 3. a~=UU==> Finite(a##x)=Finite(x)                  *)
(* ----------------------------------------------------  *)

Goal "Finite x --> x~=UU";
by (rtac impI 1);
by (etac sfinite.induct 1);
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed"Finite_UU_a";

Goal "~(Finite UU)";
by (cut_inst_tac [("x","UU")]Finite_UU_a  1);
by (fast_tac HOL_cs 1);
qed"Finite_UU";

Goal "Finite x --> a~=UU --> x=a##xs --> Finite xs";
by (strip_tac 1);
by (etac sfinite.elim 1);
by (fast_tac (HOL_cs addss simpset()) 1);
by (fast_tac (HOL_cs addSDs seq.injects) 1);
qed"Finite_cons_a";

Goal "a~=UU ==>(Finite (a##x)) = (Finite x)";
by (rtac iffI 1);
by (rtac (Finite_cons_a RS mp RS mp RS mp) 1);
by (REPEAT (assume_tac 1));
by (fast_tac HOL_cs 1);
by (Asm_full_simp_tac 1);
qed"Finite_cons";

Addsimps [Finite_UU];


(* ------------------------------------------------------------------------------------- *)

section "induction";


(*--------------------------------   *)
(* Extensions to Induction Theorems  *)
(*--------------------------------   *)


qed_goalw "seq_finite_ind_lemma" thy  [seq.finite_def]
"(!!n. P(seq_take n`s)) ==>  seq_finite(s) -->P(s)"
 (fn prems =>
        [
        (strip_tac 1),
        (etac exE 1),
        (etac subst 1),
        (resolve_tac prems 1)
        ]);


Goal "!!P.[|P(UU);P(nil);\
\  !! x s1.[|x~=UU;P(s1)|] ==> P(x##s1)\
\  |] ==> seq_finite(s) --> P(s)";
by (rtac seq_finite_ind_lemma 1);
by (etac seq.finite_ind 1);
 by (assume_tac 1);
by (Asm_full_simp_tac 1);
qed"seq_finite_ind";


