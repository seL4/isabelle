(*  Title:      HOLCF/IOA/meta_theory/Seq.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

*)  

Addsimps (sfinite.intrs @ seq.rews);


(* Instead of adding UU_neq_nil every equation UU~=x could be changed to x~=UU *)
goal thy "UU ~=nil";
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
 \                         nil   => nil \
 \                       | x##xs => f`x ## smap`f`xs)");

goal thy "smap`f`nil=nil"; 
by (stac smap_unfold 1);
by (Simp_tac 1);
qed"smap_nil";

goal thy "smap`f`UU=UU"; 
by (stac smap_unfold 1);
by (Simp_tac 1);
qed"smap_UU";

goal thy 
"!!x.[|x~=UU|] ==> smap`f`(x##xs)= (f`x)##smap`f`xs"; 
br trans 1;
by (stac smap_unfold 1);
by (Asm_full_simp_tac 1);
br refl 1;
qed"smap_cons";

(* ----------------------------------------------------------- *)
(*                        sfilter                              *)
(* ----------------------------------------------------------- *)

bind_thm ("sfilter_unfold", fix_prover2 thy sfilter_def 
  "sfilter = (LAM P tr. case tr of  \
 \         nil   => nil \
 \       | x##xs => If P`x then x##(sfilter`P`xs) else sfilter`P`xs fi)");

goal thy "sfilter`P`nil=nil";
by (stac sfilter_unfold 1);
by (Simp_tac 1);
qed"sfilter_nil";

goal thy "sfilter`P`UU=UU";
by (stac sfilter_unfold 1);
by (Simp_tac 1);
qed"sfilter_UU";

goal thy 
"!!x.x~=UU ==> sfilter`P`(x##xs)=   \
\             (If P`x then x##(sfilter`P`xs) else sfilter`P`xs fi)";
br trans 1;
by (stac sfilter_unfold 1);
by (Asm_full_simp_tac 1);
br refl 1;
qed"sfilter_cons";

(* ----------------------------------------------------------- *)
(*                        sforall2                             *)
(* ----------------------------------------------------------- *)

bind_thm ("sforall2_unfold", fix_prover2 thy sforall2_def 
   "sforall2 = (LAM P tr. case tr of  \
 \                         nil   => TT \
 \                       | x##xs => (P`x andalso sforall2`P`xs))");

goal thy "sforall2`P`nil=TT"; 
by (stac sforall2_unfold 1);
by (Simp_tac 1);
qed"sforall2_nil";

goal thy "sforall2`P`UU=UU"; 
by (stac sforall2_unfold 1);
by (Simp_tac 1);
qed"sforall2_UU";

goal thy 
"!!x.x~=UU ==> sforall2`P`(x##xs)= ((P`x) andalso sforall2`P`xs)";
br trans 1;
by (stac sforall2_unfold 1);
by (Asm_full_simp_tac 1);
br refl 1;
qed"sforall2_cons";


(* ----------------------------------------------------------- *)
(*                        stakewhile                           *)
(* ----------------------------------------------------------- *)


bind_thm ("stakewhile_unfold", fix_prover2 thy stakewhile_def 
   "stakewhile = (LAM P tr. case tr of  \
 \                         nil   => nil \
 \                       | x##xs => (If P`x then x##(stakewhile`P`xs) else nil fi))");

goal thy "stakewhile`P`nil=nil"; 
by (stac stakewhile_unfold 1);
by (Simp_tac 1);
qed"stakewhile_nil";

goal thy "stakewhile`P`UU=UU"; 
by (stac stakewhile_unfold 1);
by (Simp_tac 1);
qed"stakewhile_UU";

goal thy 
"!!x.x~=UU ==> stakewhile`P`(x##xs) =   \
\             (If P`x then x##(stakewhile`P`xs) else nil fi)";
br trans 1;
by (stac stakewhile_unfold 1);
by (Asm_full_simp_tac 1);
br refl 1;
qed"stakewhile_cons";

(* ----------------------------------------------------------- *)
(*                        sdropwhile                           *)
(* ----------------------------------------------------------- *)


bind_thm ("sdropwhile_unfold", fix_prover2 thy sdropwhile_def 
   "sdropwhile = (LAM P tr. case tr of  \
 \                         nil   => nil \
 \                       | x##xs => (If P`x then sdropwhile`P`xs else tr fi))");

goal thy "sdropwhile`P`nil=nil"; 
by (stac sdropwhile_unfold 1);
by (Simp_tac 1);
qed"sdropwhile_nil";

goal thy "sdropwhile`P`UU=UU"; 
by (stac sdropwhile_unfold 1);
by (Simp_tac 1);
qed"sdropwhile_UU";

goal thy 
"!!x.x~=UU ==> sdropwhile`P`(x##xs) =   \
\             (If P`x then sdropwhile`P`xs else x##xs fi)";
br trans 1;
by (stac sdropwhile_unfold 1);
by (Asm_full_simp_tac 1);
br refl 1;
qed"sdropwhile_cons";


(* ----------------------------------------------------------- *)
(*                        slast                                 *)
(* ----------------------------------------------------------- *)


bind_thm ("slast_unfold", fix_prover2 thy slast_def 
   "slast = (LAM tr. case tr of  \
 \                         nil   => UU \
 \                       | x##xs => (If is_nil`xs then x else slast`xs fi))");


goal thy "slast`nil=UU"; 
by (stac slast_unfold 1);
by (Simp_tac 1);
qed"slast_nil";

goal thy "slast`UU=UU"; 
by (stac slast_unfold 1);
by (Simp_tac 1);
qed"slast_UU";

goal thy 
"!!x.x~=UU ==> slast`(x##xs)= (If is_nil`xs then x else slast`xs fi)";
br trans 1;
by (stac slast_unfold 1);
by (Asm_full_simp_tac 1);
br refl 1;
qed"slast_cons";


(* ----------------------------------------------------------- *)
(*                        sconc                                 *)
(* ----------------------------------------------------------- *)

bind_thm ("sconc_unfold", fix_prover2 thy sconc_def 
   "sconc = (LAM t1 t2. case t1 of  \
 \                         nil   => t2 \
 \                       | x##xs => x ## (xs @@ t2))");


goal thy "nil @@ y = y"; 
by (stac sconc_unfold 1);
by (Simp_tac 1);
qed"sconc_nil";

goal thy "UU @@ y=UU"; 
by (stac sconc_unfold 1);
by (Simp_tac 1);
qed"sconc_UU";

goal thy "(x##xs) @@ y=x##(xs @@ y)";
br trans 1;
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

goal thy "sflat`nil=nil"; 
by (stac sflat_unfold 1);
by (Simp_tac 1);
qed"sflat_nil";

goal thy "sflat`UU=UU"; 
by (stac sflat_unfold 1);
by (Simp_tac 1);
qed"sflat_UU";

goal thy "sflat`(x##xs)= x@@(sflat`xs)"; 
br trans 1;
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

goal thy "szip`nil`y=nil"; 
by (stac szip_unfold 1);
by (Simp_tac 1);
qed"szip_nil";

goal thy "szip`UU`y=UU"; 
by (stac szip_unfold 1);
by (Simp_tac 1);
qed"szip_UU1";

goal thy "!!x. x~=nil ==> szip`x`UU=UU"; 
by (stac szip_unfold 1);
by (Asm_full_simp_tac 1);
by (res_inst_tac [("x","x")] seq.cases 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"szip_UU2";

goal thy "!!x.x~=UU ==> szip`(x##xs)`nil=UU";
br trans 1;
by (stac szip_unfold 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"szip_cons_nil";

goal thy "!!x.[| x~=UU; y~=UU|] ==> szip`(x##xs)`(y##ys) = <x,y>##szip`xs`ys";
br trans 1;
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

goal thy 
 "!!x. [|x~=UU;y~=UU|]==> (x##xs=y##ys) = (x=y & xs=ys)";
by (rtac iffI 1);
by (etac (hd seq.injects) 1);
auto();
qed"scons_inject_eq";

goal thy "!!x. nil<<x ==> nil=x";
by (res_inst_tac [("x","x")] seq.cases 1);
by (hyp_subst_tac 1);
by (etac antisym_less 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
qed"nil_less_is_nil";

(* ------------------------------------------------------------------------------------- *)

section "sfilter, sforall, sconc";


goal thy  "(if b then tr1 else tr2) @@ tr \
        \= (if b then tr1 @@ tr else tr2 @@ tr)";
by (res_inst_tac [("P","b"),("Q","b")] impCE 1);
by (fast_tac HOL_cs 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"if_and_sconc";

Addsimps [if_and_sconc];


goal thy "sfilter`P`(x @@ y) = (sfilter`P`x @@ sfilter`P`y)";

by (res_inst_tac[("x","x")] seq.ind 1);
(* adm *)
by (Simp_tac 1);
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (asm_full_simp_tac (!simpset setloop split_If_tac) 1);
qed"sfiltersconc";

goal thy "sforall P (stakewhile`P`x)";
by (simp_tac (!simpset addsimps [sforall_def]) 1);
by (res_inst_tac[("x","x")] seq.ind 1);
(* adm *)
by (simp_tac (!simpset addsimps [adm_trick_1]) 1);
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (asm_full_simp_tac (!simpset setloop split_If_tac) 1);
qed"sforallPstakewhileP";

goal thy "sforall P (sfilter`P`x)";
by (simp_tac (!simpset addsimps [sforall_def]) 1);
by (res_inst_tac[("x","x")] seq.ind 1);
(* adm *)
(* FIX should be refined in _one_ tactic *)
by (simp_tac (!simpset addsimps [adm_trick_1]) 1);
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (asm_full_simp_tac (!simpset setloop split_If_tac) 1);
qed"forallPsfilterP";



(* ------------------------------------------------------------------------------------- *)

section "Finite";

(* ----------------------------------------------------  *)
(* Proofs of rewrite rules for Finite:                  *)
(* 1. Finite(nil),   (by definition)                    *)
(* 2. ~Finite(UU),                                      *)
(* 3. a~=UU==> Finite(a##x)=Finite(x)                  *)
(* ----------------------------------------------------  *)

goal thy "Finite x --> x~=UU";
br impI 1;
be sfinite.induct 1;
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed"Finite_UU_a";

goal thy "~(Finite UU)";
by (cut_inst_tac [("x","UU")]Finite_UU_a  1);
by (fast_tac HOL_cs 1);
qed"Finite_UU";

goal thy "Finite x --> a~=UU --> x=a##xs --> Finite xs";
by (strip_tac 1);
be sfinite.elim 1;
by (fast_tac (HOL_cs addss !simpset) 1);
by (fast_tac (HOL_cs addSDs seq.injects) 1);
qed"Finite_cons_a";

goal thy "!!x.a~=UU ==>(Finite (a##x)) = (Finite x)";
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
"(!!n.P(seq_take n`s)) ==>  seq_finite(s) -->P(s)"
 (fn prems =>
        [
        (strip_tac 1),
        (etac exE 1),
        (etac subst 1),
        (resolve_tac prems 1)
        ]);


goal  thy 
"!!P.[|P(UU);P(nil);\
\  !! x s1.[|x~=UU;P(s1)|] ==> P(x##s1)\
\  |] ==> seq_finite(s) --> P(s)";
by (rtac seq_finite_ind_lemma 1);
be seq.finite_ind 1;
 ba 1;
by (Asm_full_simp_tac 1);
qed"seq_finite_ind";




(*
(* -----------------------------------------------------------------
   Fr"uhere Herleitung des endlichen Induktionsprinzips 
   aus dem seq_finite Induktionsprinzip.
   Problem bei admissibility von Finite-->seq_finite!
   Deshalb Finite jetzt induktiv und nicht mehr rekursiv definiert! 
   ------------------------------------------------------------------ *)

goal thy "seq_finite nil";
by (simp_tac (!simpset addsimps [seq.sfinite_def]) 1);
by (res_inst_tac [("x","Suc 0")] exI 1);
by (simp_tac (!simpset addsimps seq.rews) 1);
qed"seq_finite_nil";

goal thy "seq_finite UU";
by (simp_tac (!simpset addsimps [seq.sfinite_def]) 1);
qed"seq_finite_UU";

Addsimps[seq_finite_nil,seq_finite_UU];

goal HOL.thy "(B-->A) --> (A--> (B-->C))--> (B--> C)";
by (fast_tac HOL_cs 1);
qed"logic_lemma";


goal thy "!!P.[| P nil; \
\                !!a t. [|a~=UU;Finite t; P t|] ==> P (a##t)|]\
\            ==> Finite x --> P x";

by (rtac (logic_lemma RS mp RS mp) 1);
by (rtac trf_impl_tf 1);
by (rtac seq_finite_ind 1);
by (simp_tac (!simpset addsimps [Finite_def]) 1);
by (simp_tac (!simpset addsimps [Finite_def]) 1);
by (asm_full_simp_tac (!simpset addsimps [Finite_def]) 1);
qed"Finite_ind";


goal thy "Finite tr --> seq_finite tr";
by (rtac seq.ind 1);
(* adm *)
(* hier grosses Problem !!!!!!!!!!!!!!! *)

by (simp_tac (!simpset addsimps [Finite_def]) 2);
by (simp_tac (!simpset addsimps [Finite_def]) 2);

(* main case *)
by (asm_full_simp_tac (!simpset addsimps [Finite_def,seq.sfinite_def]) 2);
by (rtac impI 2);
by (rotate_tac 2 2);
by (Asm_full_simp_tac 2);
by (etac exE 2);
by (res_inst_tac [("x","Suc n")] exI 2);
by (asm_full_simp_tac (!simpset addsimps seq.rews) 2);
qed"tf_is_trf";

*)

