(* $Id$ *)
(* Elegant proof for continuity of fixed-point operator *)
(* Loeckx & Sieber S.88                                 *)

Goalw [Ifix_def] "Ifix F= lub (range (%i.%G. iterate i G UU)) F";
by (stac thelub_fun 1);
by (rtac refl 2);
by (blast_tac (claset() addIs [ch2ch_fun, chainI, less_fun RS iffD2,
                               chain_iterate RS chainE]) 1); 
qed "loeckx_sieber";

(* 

Idea: (%i.%G.iterate i G UU) is a chain of continuous functions and
      Ifix is the lub of this chain. Hence Ifix is continuous.

----- The proof  in HOLCF ----------------------- 

Since we already proved the theorem

val cont_lubcfun = prove_goal Cfun2.thy 
        "chain ?F ==> cont (%x. lub (range (%j. ?F j$x)))"


it suffices to prove:

Ifix  = (%f.lub (range (%j. (LAM f. iterate j f UU)$f)))

and 

cont (%f.lub (range (%j. (LAM f. iterate j f UU)$f)))

Note that if we use the term 

%i.%G.iterate i G UU instead of (%j.(LAM f. iterate j f UU))

we cannot use the theorem cont_lubcfun    

*)

Goal "cont(Ifix)";
by (res_inst_tac 
 [("t","Ifix"),("s","(%f. lub(range(%j.(LAM f. iterate j f UU)$f)))")]
  ssubst 1);
by (rtac ext 1);
by (rewtac Ifix_def );
by (subgoal_tac 
  "range(% i. iterate i f UU) = range(%j.(LAM f. iterate j f UU)$f)" 1);
by (etac arg_cong 1);
by (subgoal_tac 
        "(% i. iterate i f UU) = (%j.(LAM f. iterate j f UU)$f)" 1);
by (etac arg_cong 1);
by (rtac ext 1);
by (stac beta_cfun 1);
by (rtac  cont2cont_CF1L 1);
by (rtac cont_iterate 1);
by (rtac refl 1);
by (rtac cont_lubcfun 1);
by (rtac chainI 1);
by (strip_tac 1);
by (rtac less_cfun2 1);
by (stac beta_cfun 1);
by (rtac  cont2cont_CF1L 1);
by (rtac cont_iterate 1);
by (stac beta_cfun 1);
by (rtac  cont2cont_CF1L 1);
by (rtac cont_iterate 1);
by (rtac (chain_iterate RS chainE) 1);
qed "cont_Ifix2'";

(* the proof in little steps *)

Goal "(% i. iterate i f UU) = (%j.(LAM f. iterate j f UU)$f)";
by (rtac ext 1);
by (simp_tac (simpset() addsimps [beta_cfun, cont2cont_CF1L, cont_iterate]) 1);
qed "fix_lemma1";

Goal "Ifix = (%f. lub(range(%j.(LAM f. iterate j f UU)$f)))";
by (rtac ext 1);
by (simp_tac (simpset() addsimps [Ifix_def, fix_lemma1]) 1);
qed "fix_lemma2";

(*
- cont_lubcfun;
val it = "chain ?F ==> cont (%x. lub (range (%j. ?F j$x)))" : thm   

*)

Goal "cont Ifix";
by (stac fix_lemma2 1);
by (rtac cont_lubcfun 1);
by (rtac chainI 1);
by (rtac less_cfun2 1);
by (stac beta_cfun 1);
by (rtac  cont2cont_CF1L 1);
by (rtac cont_iterate 1);
by (stac beta_cfun 1);
by (rtac  cont2cont_CF1L 1);
by (rtac cont_iterate 1);
by (rtac (chain_iterate RS chainE) 1);
qed "cont_Ifix2''";

