(*  Title:      HOLCF/Cont.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Results about continuity and monotonicity
*)

(* ------------------------------------------------------------------------ *)
(* access to definition                                                     *)
(* ------------------------------------------------------------------------ *)

Goalw [contlub]
        "! Y. chain(Y) --> f(lub(range(Y))) = lub(range(%i. f(Y(i))))==>\
\        contlub(f)";
by (atac 1);
qed "contlubI";

Goalw [contlub]
        " contlub(f)==>\
\         ! Y. chain(Y) --> f(lub(range(Y))) = lub(range(%i. f(Y(i))))";
by (atac 1);
qed "contlubE";


Goalw [cont]
 "! Y. chain(Y) --> range(% i. f(Y(i))) <<| f(lub(range(Y))) ==> cont(f)";
by (atac 1);
qed "contI";

Goalw [cont]
 "cont(f) ==> ! Y. chain(Y) --> range(% i. f(Y(i))) <<| f(lub(range(Y)))";
by (atac 1);
qed "contE";


Goalw [monofun]
        "! x y. x << y --> f(x) << f(y) ==> monofun(f)";
by (atac 1);
qed "monofunI";

Goalw [monofun]
        "monofun(f) ==> ! x y. x << y --> f(x) << f(y)";
by (atac 1);
qed "monofunE";

(* ------------------------------------------------------------------------ *)
(* the main purpose of cont.thy is to show:                                 *)
(*              monofun(f) & contlub(f)  <==> cont(f)                      *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* monotone functions map chains to chains                                  *)
(* ------------------------------------------------------------------------ *)

Goal 
        "[| monofun(f); chain(Y) |] ==> chain(%i. f(Y(i)))";
by (rtac chainI 1);
by (etac (monofunE RS spec RS spec RS mp) 1);
by (etac (chainE) 1);
qed "ch2ch_monofun";

(* ------------------------------------------------------------------------ *)
(* monotone functions map upper bound to upper bounds                       *)
(* ------------------------------------------------------------------------ *)

Goal 
 "[| monofun(f); range(Y) <| u|]  ==> range(%i. f(Y(i))) <| f(u)";
by (rtac ub_rangeI 1);
by (etac (monofunE RS spec RS spec RS mp) 1);
by (etac (ub_rangeD) 1);
qed "ub2ub_monofun";

(* ------------------------------------------------------------------------ *)
(* left to right: monofun(f) & contlub(f)  ==> cont(f)                     *)
(* ------------------------------------------------------------------------ *)

Goalw [cont]
        "[|monofun(f);contlub(f)|] ==> cont(f)";
by (strip_tac 1);
by (rtac thelubE 1);
by (etac ch2ch_monofun 1);
by (atac 1);
by (etac (contlubE RS spec RS mp RS sym) 1);
by (atac 1);
qed "monocontlub2cont";

(* ------------------------------------------------------------------------ *)
(* first a lemma about binary chains                                        *)
(* ------------------------------------------------------------------------ *)

Goal "[| cont(f); x << y |]  \
\     ==> range(%i::nat. f(if i = 0 then x else y)) <<| f(y)";
by (rtac subst 1);
by (etac (contE RS spec RS mp) 2);
by (etac bin_chain 2);
by (res_inst_tac [("y","y")] arg_cong 1);
by (etac (lub_bin_chain RS thelubI) 1);
qed "binchain_cont";

(* ------------------------------------------------------------------------ *)
(* right to left: cont(f) ==> monofun(f) & contlub(f)                      *)
(* part1:         cont(f) ==> monofun(f                                    *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun] "cont(f) ==> monofun(f)";
by (strip_tac 1);
by (dtac (binchain_cont RS is_ub_lub) 1);
by (auto_tac (claset(), simpset() addsplits [split_if_asm]));
qed "cont2mono";

(* ------------------------------------------------------------------------ *)
(* right to left: cont(f) ==> monofun(f) & contlub(f)                      *)
(* part2:         cont(f) ==>              contlub(f)                      *)
(* ------------------------------------------------------------------------ *)

Goalw [contlub] "cont(f) ==> contlub(f)";
by (strip_tac 1);
by (rtac (thelubI RS sym) 1);
by (etac (contE RS spec RS mp) 1);
by (atac 1);
qed "cont2contlub";

(* ------------------------------------------------------------------------ *)
(* monotone functions map finite chains to finite chains                    *)
(* ------------------------------------------------------------------------ *)

Goalw [finite_chain_def]
  "[| monofun f; finite_chain Y |] ==> finite_chain (%n. f (Y n))";
by (force_tac (claset()  addSEs [ch2ch_monofun],
	       simpset() addsimps [max_in_chain_def]) 1);
qed "monofun_finch2finch";

(* ------------------------------------------------------------------------ *)
(* The same holds for continuous functions                                  *)
(* ------------------------------------------------------------------------ *)

bind_thm ("cont_finch2finch", cont2mono RS monofun_finch2finch);
(* [| cont ?f; finite_chain ?Y |] ==> finite_chain (%n. ?f (?Y n)) *)


(* ------------------------------------------------------------------------ *)
(* The following results are about a curried function that is monotone      *)
(* in both arguments                                                        *)
(* ------------------------------------------------------------------------ *)

Goal 
"[|monofun(MF2); chain(F)|] ==> chain(%i. MF2 (F i) x)";
by (etac (ch2ch_monofun RS ch2ch_fun) 1);
by (atac 1);
qed "ch2ch_MF2L";


Goal 
"[|monofun(MF2(f)); chain(Y)|] ==> chain(%i. MF2 f (Y i))";
by (etac ch2ch_monofun 1);
by (atac 1);
qed "ch2ch_MF2R";

Goal 
"[|monofun(MF2); !f. monofun(MF2(f)); chain(F); chain(Y)|] ==> \
\  chain(%i. MF2(F(i))(Y(i)))";
by (rtac chainI 1);
by (rtac trans_less 1);
by (etac (ch2ch_MF2L RS chainE) 1);
by (atac 1);
by ((rtac (monofunE RS spec RS spec RS mp) 1) THEN (etac spec 1));
by (etac (chainE) 1);
qed "ch2ch_MF2LR";


Goal 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo));\
\  !f. monofun(MF2(f)::('b::po=>'c::cpo));\
\       chain(F);chain(Y)|] ==> \
\       chain(%j. lub(range(%i. MF2 (F j) (Y i))))";
by (rtac (lub_mono RS chainI) 1);
by ((rtac ch2ch_MF2R 1) THEN (etac spec 1));
by (atac 1);
by ((rtac ch2ch_MF2R 1) THEN (etac spec 1));
by (atac 1);
by (strip_tac 1);
by (rtac (chainE) 1);
by (etac ch2ch_MF2L 1);
by (atac 1);
qed "ch2ch_lubMF2R";


Goal 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo));\
\  !f. monofun(MF2(f)::('b::po=>'c::cpo));\
\       chain(F);chain(Y)|] ==> \
\       chain(%i. lub(range(%j. MF2 (F j) (Y i))))";
by (rtac (lub_mono RS chainI) 1);
by (etac ch2ch_MF2L 1);
by (atac 1);
by (etac ch2ch_MF2L 1);
by (atac 1);
by (strip_tac 1);
by (rtac (chainE) 1);
by ((rtac ch2ch_MF2R 1) THEN (etac spec 1));
by (atac 1);
qed "ch2ch_lubMF2L";


Goal 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo));\
\  !f. monofun(MF2(f)::('b::po=>'c::cpo));\
\       chain(F)|] ==> \
\       monofun(% x. lub(range(% j. MF2 (F j) (x))))";
by (rtac monofunI 1);
by (strip_tac 1);
by (rtac lub_mono 1);
by (etac ch2ch_MF2L 1);
by (atac 1);
by (etac ch2ch_MF2L 1);
by (atac 1);
by (strip_tac 1);
by ((rtac (monofunE RS spec RS spec RS mp) 1) THEN (etac spec 1));
by (atac 1);
qed "lub_MF2_mono";

Goal 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo));\
\  !f. monofun(MF2(f)::('b::po=>'c::cpo));\
\       chain(F); chain(Y)|] ==> \
\               lub(range(%j. lub(range(%i. MF2(F j) (Y i))))) =\
\               lub(range(%i. lub(range(%j. MF2(F j) (Y i)))))";
by (rtac antisym_less 1);
by (rtac (ub_rangeI RSN (2,is_lub_thelub)) 1);
by (etac ch2ch_lubMF2R 1);
by (REPEAT (atac 1));
by (strip_tac 1);
by (rtac lub_mono 1);
by ((rtac ch2ch_MF2R 1) THEN (etac spec 1));
by (atac 1);
by (etac ch2ch_lubMF2L 1);
by (REPEAT (atac 1));
by (strip_tac 1);
by (rtac is_ub_thelub 1);
by (etac ch2ch_MF2L 1);
by (atac 1);
by (rtac (ub_rangeI RSN (2,is_lub_thelub)) 1);
by (etac ch2ch_lubMF2L 1);
by (REPEAT (atac 1));
by (strip_tac 1);
by (rtac lub_mono 1);
by (etac ch2ch_MF2L 1);
by (atac 1);
by (etac ch2ch_lubMF2R 1);
by (REPEAT (atac 1));
by (strip_tac 1);
by (rtac is_ub_thelub 1);
by ((rtac ch2ch_MF2R 1) THEN (etac spec 1));
by (atac 1);
qed "ex_lubMF2";


Goal 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo));\
\  !f. monofun(MF2(f)::('b::po=>'c::cpo));\
\  chain(FY);chain(TY)|] ==>\
\ lub(range(%i. lub(range(%j. MF2(FY(j))(TY(i)))))) =\
\ lub(range(%i. MF2(FY(i))(TY(i))))";
by (rtac antisym_less 1);
by (rtac (ub_rangeI RSN (2,is_lub_thelub)) 1);
by (etac ch2ch_lubMF2L 1);
by (REPEAT (atac 1));
by (strip_tac 1 );
by (rtac lub_mono3 1);
by (etac ch2ch_MF2L 1);
by (REPEAT (atac 1));
by (etac ch2ch_MF2LR 1);
by (REPEAT (atac 1));
by (rtac allI 1);
by (res_inst_tac [("m","i"),("n","ia")] nat_less_cases 1);
by (res_inst_tac [("x","ia")] exI 1);
by (rtac (chain_mono) 1);
by (etac allE 1);
by (etac ch2ch_MF2R 1);
by (REPEAT (atac 1));
by (hyp_subst_tac 1);
by (res_inst_tac [("x","ia")] exI 1);
by (rtac refl_less 1);
by (res_inst_tac [("x","i")] exI 1);
by (rtac (chain_mono) 1);
by (etac ch2ch_MF2L 1);
by (REPEAT (atac 1));
by (rtac lub_mono 1);
by (etac ch2ch_MF2LR 1);
by (REPEAT(atac 1));
by (etac ch2ch_lubMF2L 1);
by (REPEAT (atac 1));
by (strip_tac 1 );
by (rtac is_ub_thelub 1);
by (etac ch2ch_MF2L 1);
by (atac 1);
qed "diag_lubMF2_1";

Goal 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo));\
\  !f. monofun(MF2(f)::('b::po=>'c::cpo));\
\  chain(FY);chain(TY)|] ==>\
\ lub(range(%j. lub(range(%i. MF2(FY(j))(TY(i)))))) =\
\ lub(range(%i. MF2(FY(i))(TY(i))))";
by (rtac trans 1);
by (rtac ex_lubMF2 1);
by (REPEAT (atac 1));
by (etac diag_lubMF2_1 1);
by (REPEAT (atac 1));
qed "diag_lubMF2_2";


(* ------------------------------------------------------------------------ *)
(* The following results are about a curried function that is continuous    *)
(* in both arguments                                                        *)
(* ------------------------------------------------------------------------ *)

val [prem1,prem2,prem3,prem4] = goal thy 
"[| cont(CF2); !f. cont(CF2(f)); chain(FY); chain(TY)|] ==>\
\ CF2(lub(range(FY)))(lub(range(TY))) = lub(range(%i. CF2(FY(i))(TY(i))))";
by (cut_facts_tac [prem1,prem2,prem3, prem4] 1);
by (stac (prem1 RS cont2contlub RS contlubE RS spec RS mp) 1);
by (assume_tac 1);
by (stac thelub_fun 1);
by (rtac (prem1 RS (cont2mono RS ch2ch_monofun)) 1);
by (assume_tac 1);
by (rtac trans 1);
by (rtac ((prem2 RS spec RS cont2contlub) RS contlubE RS spec RS mp RS ext RS arg_cong RS arg_cong) 1);
by (rtac prem4 1);
by (blast_tac (claset() addIs [diag_lubMF2_2, cont2mono]) 1);
qed "contlub_CF2";

(* ------------------------------------------------------------------------ *)
(* The following results are about application for functions in 'a=>'b      *)
(* ------------------------------------------------------------------------ *)

Goal "f1 << f2 ==> f1(x) << f2(x)";
by (etac (less_fun RS iffD1 RS spec) 1);
qed "monofun_fun_fun";

Goal "[|monofun(f); x1 << x2|] ==> f(x1) << f(x2)";
by (etac (monofunE RS spec RS spec RS mp) 1);
by (atac 1);
qed "monofun_fun_arg";

Goal "[|monofun(f1); monofun(f2); f1 << f2; x1 << x2|] ==> f1(x1) << f2(x2)";
by (rtac trans_less 1);
by (etac monofun_fun_arg 1);
by (atac 1);
by (etac monofun_fun_fun 1);
qed "monofun_fun";


(* ------------------------------------------------------------------------ *)
(* The following results are about the propagation of monotonicity and      *)
(* continuity                                                               *)
(* ------------------------------------------------------------------------ *)

Goal "[|monofun(c1)|] ==> monofun(%x. c1 x y)";
by (rtac monofunI 1);
by (strip_tac 1);
by (etac (monofun_fun_arg RS monofun_fun_fun) 1);
by (atac 1);
qed "mono2mono_MF1L";

Goal "[|cont(c1)|] ==> cont(%x. c1 x y)";
by (rtac monocontlub2cont 1);
by (etac (cont2mono RS mono2mono_MF1L) 1);
by (rtac contlubI 1);
by (strip_tac 1);
by (ftac asm_rl 1);
by (etac (cont2contlub RS contlubE RS spec RS mp RS ssubst) 1);
by (atac 1);
by (stac thelub_fun 1);
by (rtac ch2ch_monofun 1);
by (etac cont2mono 1);
by (atac 1);
by (rtac refl 1);
qed "cont2cont_CF1L";

(*********  Note "(%x.%y.c1 x y) = c1" ***********)

Goal "!y. monofun(%x. c1 x y) ==> monofun(c1)";
by (rtac monofunI 1);
by (strip_tac 1);
by (rtac (less_fun RS iffD2) 1);
by (blast_tac (claset() addDs [monofunE]) 1);
qed "mono2mono_MF1L_rev";

Goal "!y. cont(%x. c1 x y) ==> cont(c1)";
by (rtac monocontlub2cont 1);
by (rtac (cont2mono RS allI RS mono2mono_MF1L_rev ) 1);
by (etac spec 1);
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac ext 1);
by (stac thelub_fun 1);
by (rtac (cont2mono RS allI RS mono2mono_MF1L_rev RS ch2ch_monofun) 1);
by (etac spec 1);
by (atac 1);
by (blast_tac (claset() addDs [ cont2contlub RS contlubE]) 1);
qed "cont2cont_CF1L_rev";

(* ------------------------------------------------------------------------ *)
(* What D.A.Schmidt calls continuity of abstraction                         *)
(* never used here                                                          *)
(* ------------------------------------------------------------------------ *)

Goal
"[|chain(Y::nat=>'a);!y. cont(%x.(c::'a::cpo=>'b::cpo=>'c::cpo) x y)|] ==>\
\ (%y. lub(range(%i. c (Y i) y))) = (lub(range(%i.%y. c (Y i) y)))";
by (rtac trans 1);
by (rtac (cont2contlub RS contlubE RS spec RS mp) 2);
by (atac 3);
by (etac cont2cont_CF1L_rev 2);
by (rtac ext 1);
by (rtac (cont2contlub RS contlubE RS spec RS mp RS sym) 1);
by (etac spec 1);
by (atac 1);
qed "contlub_abstraction";

Goal "[|monofun(ft);!x. monofun(ft(x));monofun(tt)|] ==>\
\        monofun(%x.(ft(x))(tt(x)))";
by (rtac monofunI 1);
by (strip_tac 1);
by (res_inst_tac [("f1.0","ft(x)"),("f2.0","ft(y)")] monofun_fun 1);
by (etac spec 1);
by (etac spec 1);
by (etac (monofunE RS spec RS spec RS mp) 1);
by (atac 1);
by (etac (monofunE RS spec RS spec RS mp) 1);
by (atac 1);
qed "mono2mono_app";


Goal "[|cont(ft);!x. cont(ft(x));cont(tt)|] ==> contlub(%x.(ft(x))(tt(x)))";
by (rtac contlubI 1);
by (strip_tac 1);
by (res_inst_tac [("f3","tt")] (contlubE RS spec RS mp RS ssubst) 1);
by (etac cont2contlub 1);
by (atac 1);
by (rtac contlub_CF2 1);
by (REPEAT (atac 1));
by (etac (cont2mono RS ch2ch_monofun) 1);
by (atac 1);
qed "cont2contlub_app";


Goal "[|cont(ft); !x. cont(ft(x)); cont(tt)|] ==> cont(%x.(ft(x))(tt(x)))";
by (blast_tac (claset() addIs [monocontlub2cont, mono2mono_app, cont2mono,
			       cont2contlub_app]) 1);
qed "cont2cont_app";


bind_thm ("cont2cont_app2", allI RSN (2,cont2cont_app));
(*  [| cont ?ft; !!x. cont (?ft x); cont ?tt |] ==> *)
(*        cont (%x. ?ft x (?tt x))                    *)


(* ------------------------------------------------------------------------ *)
(* The identity function is continuous                                      *)
(* ------------------------------------------------------------------------ *)

Goal "cont(% x. x)";
by (rtac contI 1);
by (strip_tac 1);
by (etac thelubE 1);
by (rtac refl 1);
qed "cont_id";

(* ------------------------------------------------------------------------ *)
(* constant functions are continuous                                        *)
(* ------------------------------------------------------------------------ *)

Goalw [cont] "cont(%x. c)";
by (strip_tac 1);
by (blast_tac (claset() addIs [is_lubI, ub_rangeI] addDs [ub_rangeD]) 1);
qed "cont_const";


Goal "[|cont(f); cont(t) |] ==> cont(%x. f(t(x)))";
by (best_tac (claset() addIs [ cont2cont_app2, cont_const]) 1);
qed "cont2cont_app3";

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Cfun                                          *)
(* ------------------------------------------------------------------------ *)

Goal "?x:Collect cont";
by (rtac CollectI 1);
by (rtac cont_const 1);
qed "CfunI";

(* ------------------------------------------------------------------------ *)
(* some properties of flat                                                  *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun] "f UU = UU ==> monofun (f::'a::flat=>'b::pcpo)";
by (strip_tac 1);
by (dtac (ax_flat RS spec RS spec RS mp) 1);
by (fast_tac ((HOL_cs addss (simpset() addsimps [minimal]))) 1);
qed "flatdom2monofun";


Goal "monofun f ==> cont(f::'a::chfin=>'b::pcpo)";
by (rtac monocontlub2cont 1);
by ( atac 1);
by (rtac contlubI 1);
by (strip_tac 1);
by (ftac chfin2finch 1);
by (rtac antisym_less 1);
by ( force_tac (HOL_cs addIs [is_ub_thelub,ch2ch_monofun],
               HOL_ss addsimps [finite_chain_def,maxinch_is_thelub]) 1);
by (dtac (monofun_finch2finch COMP swap_prems_rl) 1);
by ( atac 1);
by (asm_full_simp_tac (HOL_ss addsimps [finite_chain_def]) 1);
by (etac conjE 1);
by (etac exE 1);
by (asm_full_simp_tac (HOL_ss addsimps [maxinch_is_thelub]) 1);
by (etac (monofunE RS spec RS spec RS mp) 1);
by (etac is_ub_thelub 1);
qed "chfindom_monofun2cont";

bind_thm ("flatdom_strict2cont",flatdom2monofun RS chfindom_monofun2cont);
(* f UU = UU ==> cont (f::'a=>'b::pcpo)" *)
