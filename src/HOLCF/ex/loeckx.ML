(* Elegant proof for continuity of fixed-point operator *)
(* Loeckx & Sieber S.88                                 *)

val prems = goalw Fix.thy [Ifix_def]
"Ifix(F)=lub(range(%i.%G.iterate(i,G,UU)))(F)";
by (rtac (thelub_fun RS ssubst) 1);
by (rtac ch2ch_fun 1);
back();
by (rtac refl 2);
by (rtac is_chainI 1);
by (strip_tac 1);
by (rtac (less_fun RS iffD2) 1);
by (strip_tac 1);
by (rtac (less_fun RS iffD2) 1);
by (strip_tac 1);
by (rtac (is_chain_iterate RS is_chainE RS spec) 1);
val loeckx_sieber = result();

(* 

Idea: %i.%G.iterate(i,G,UU)) is a chain of continuous functions and
      Ifix is the lub of this chain. Hence Ifix is continuous.

----- The proof  in HOLCF ----------------------- 

Since we already proved the theorem

val contX_lubcfun = prove_goal Cfun2.thy 
	"is_chain(F) ==> contX(% x.lub(range(% j.F(j)[x])))"


we suffices to prove:

Ifix  = (%f.lub(range(%j.(LAM f. iterate(j, f, UU))[f])))

and 

contX(%f.lub(range(%j.(LAM f. iterate(j, f, UU))[f])))

Note that if we use the term 

%i.%G.iterate(i,G,UU)) instead of (%j.(LAM f. iterate(j, f, UU)))

we cannot use the theorem contX_lubcfun    

*)

val prems = goal Fix.thy  "contX(Ifix)";
by (res_inst_tac [("t","Ifix"),("s","(%f.lub(range(%j.(LAM f. iterate(j, f, UU))[f])))")] ssubst 1);
by (rtac ext 1);
by (rewrite_goals_tac [Ifix_def] );
by (subgoal_tac " range(% i.iterate(i, f, UU)) = range(%j.(LAM f. iterate(j, f, UU))[f])" 1);
by (etac arg_cong 1);
by (subgoal_tac " (% i.iterate(i, f, UU)) = (%j.(LAM f. iterate(j, f, UU))[f])" 1);
by (etac arg_cong 1);
by (rtac ext 1);
by (rtac (beta_cfun RS ssubst) 1);
by (rtac  contX2contX_CF1L 1);
by (rtac contX_iterate 1);
by (rtac refl 1);
by (rtac contX_lubcfun 1);
by (rtac is_chainI 1);
by (strip_tac 1);
by (rtac less_cfun2 1);
by (rtac (beta_cfun RS ssubst) 1);
by (rtac  contX2contX_CF1L 1);
by (rtac contX_iterate 1);
by (rtac (beta_cfun RS ssubst) 1);
by (rtac  contX2contX_CF1L 1);
by (rtac contX_iterate 1);
by (rtac (is_chain_iterate RS is_chainE RS spec) 1);
val contX_Ifix2 = result();

(* the proof in little steps *)

val prems = goal Fix.thy  
"(% i.iterate(i, f, UU)) = (%j.(LAM f. iterate(j, f, UU))[f])";
by (rtac ext 1);
by (rtac (beta_cfun RS ssubst) 1);
by (rtac  contX2contX_CF1L 1);
by (rtac contX_iterate 1);
by (rtac refl 1);
val fix_lemma1 = result();

val prems = goal Fix.thy  
" Ifix = (%f.lub(range(%j.(LAM f.iterate(j,f,UU))[f])))";
by (rtac ext 1);
by (rewrite_goals_tac [Ifix_def] ); 
by (rtac (fix_lemma1 RS ssubst) 1);
by (rtac refl 1);
val fix_lemma2 = result();

(*
- contX_lubcfun;
val it = "is_chain(?F) ==> contX(%x. lub(range(%j. ?F(j)[x])))" : thm

*)

val prems = goal Fix.thy "contX(Ifix)";
by (rtac ( fix_lemma2  RS ssubst) 1);
by (rtac contX_lubcfun 1);
by (rtac is_chainI 1);
by (strip_tac 1);
by (rtac less_cfun2 1);
by (rtac (beta_cfun RS ssubst) 1);
by (rtac  contX2contX_CF1L 1);
by (rtac contX_iterate 1);
by (rtac (beta_cfun RS ssubst) 1);
by (rtac  contX2contX_CF1L 1);
by (rtac contX_iterate 1);
by (rtac (is_chain_iterate RS is_chainE RS spec) 1);
val contX_Ifix2 = result();








