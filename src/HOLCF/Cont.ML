(*  Title:      HOLCF/cont.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for cont.thy 
*)

open Cont;

(* ------------------------------------------------------------------------ *)
(* access to definition                                                     *)
(* ------------------------------------------------------------------------ *)

qed_goalw "contlubI" Cont.thy [contlub]
        "! Y. is_chain(Y) --> f(lub(range(Y))) = lub(range(%i. f(Y(i))))==>\
\        contlub(f)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);

qed_goalw "contlubE" Cont.thy [contlub]
        " contlub(f)==>\
\         ! Y. is_chain(Y) --> f(lub(range(Y))) = lub(range(%i. f(Y(i))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);


qed_goalw "contI" Cont.thy [cont]
 "! Y. is_chain(Y) --> range(% i.f(Y(i))) <<| f(lub(range(Y))) ==> cont(f)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);

qed_goalw "contE" Cont.thy [cont]
 "cont(f) ==> ! Y. is_chain(Y) --> range(% i.f(Y(i))) <<| f(lub(range(Y)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);


qed_goalw "monofunI" Cont.thy [monofun]
        "! x y. x << y --> f(x) << f(y) ==> monofun(f)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);

qed_goalw "monofunE" Cont.thy [monofun]
        "monofun(f) ==> ! x y. x << y --> f(x) << f(y)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the main purpose of cont.thy is to show:                                 *)
(*              monofun(f) & contlub(f)  <==> cont(f)                      *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* monotone functions map chains to chains                                  *)
(* ------------------------------------------------------------------------ *)

qed_goal "ch2ch_monofun" Cont.thy 
        "[| monofun(f); is_chain(Y) |] ==> is_chain(%i. f(Y(i)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_chainI 1),
        (rtac allI 1),
        (etac (monofunE RS spec RS spec RS mp) 1),
        (etac (is_chainE RS spec) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* monotone functions map upper bound to upper bounds                       *)
(* ------------------------------------------------------------------------ *)

qed_goal "ub2ub_monofun" Cont.thy 
 "[| monofun(f); range(Y) <| u|]  ==> range(%i.f(Y(i))) <| f(u)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (etac (monofunE RS spec RS spec RS mp) 1),
        (etac (ub_rangeE RS spec) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* left to right: monofun(f) & contlub(f)  ==> cont(f)                     *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monocontlub2cont" Cont.thy [cont]
        "[|monofun(f);contlub(f)|] ==> cont(f)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (rtac thelubE 1),
        (etac ch2ch_monofun 1),
        (atac 1),
        (etac (contlubE RS spec RS mp RS sym) 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* first a lemma about binary chains                                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "binchain_cont" Cont.thy
"[| cont(f); x << y |]  ==> range(%i. f(if i = 0 then x else y)) <<| f(y)"
(fn prems => 
        [
        (cut_facts_tac prems 1),
        (rtac subst 1), 
        (etac (contE RS spec RS mp) 2),
        (etac bin_chain 2),
        (res_inst_tac [("y","y")] arg_cong 1),
        (etac (lub_bin_chain RS thelubI) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* right to left: cont(f) ==> monofun(f) & contlub(f)                      *)
(* part1:         cont(f) ==> monofun(f                                    *)
(* ------------------------------------------------------------------------ *)

qed_goalw "cont2mono" Cont.thy [monofun]
        "cont(f) ==> monofun(f)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (res_inst_tac [("s","if 0 = 0 then x else y")] subst 1),
        (rtac (binchain_cont RS is_ub_lub) 2),
        (atac 2),
        (atac 2),
        (Simp_tac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* right to left: cont(f) ==> monofun(f) & contlub(f)                      *)
(* part2:         cont(f) ==>              contlub(f)                      *)
(* ------------------------------------------------------------------------ *)

qed_goalw "cont2contlub" Cont.thy [contlub]
        "cont(f) ==> contlub(f)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (rtac (thelubI RS sym) 1),
        (etac (contE RS spec RS mp) 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* The following results are about a curried function that is monotone      *)
(* in both arguments                                                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "ch2ch_MF2L" Cont.thy 
"[|monofun(MF2); is_chain(F)|] ==> is_chain(%i. MF2 (F i) x)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac (ch2ch_monofun RS ch2ch_fun) 1),
        (atac 1)
        ]);


qed_goal "ch2ch_MF2R" Cont.thy 
"[|monofun(MF2(f)); is_chain(Y)|] ==> is_chain(%i. MF2 f (Y i))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac ch2ch_monofun 1),
        (atac 1)
        ]);

qed_goal "ch2ch_MF2LR" Cont.thy 
"[|monofun(MF2); !f.monofun(MF2(f)); is_chain(F); is_chain(Y)|] ==> \
\  is_chain(%i. MF2(F(i))(Y(i)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_chainI 1),
        (strip_tac 1 ),
        (rtac trans_less 1),
        (etac (ch2ch_MF2L RS is_chainE RS spec) 1),
        (atac 1),
        ((rtac (monofunE RS spec RS spec RS mp) 1) THEN (etac spec 1)),
        (etac (is_chainE RS spec) 1)
        ]);


qed_goal "ch2ch_lubMF2R" Cont.thy 
"[|monofun(MF2::('a::po=>'b::po=>'c::pcpo));\
\  !f.monofun(MF2(f)::('b::po=>'c::pcpo));\
\       is_chain(F);is_chain(Y)|] ==> \
\       is_chain(%j. lub(range(%i. MF2 (F j) (Y i))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (lub_mono RS allI RS is_chainI) 1),
        ((rtac ch2ch_MF2R 1) THEN (etac spec 1)),
        (atac 1),
        ((rtac ch2ch_MF2R 1) THEN (etac spec 1)),
        (atac 1),
        (strip_tac 1),
        (rtac (is_chainE RS spec) 1),
        (etac ch2ch_MF2L 1),
        (atac 1)
        ]);


qed_goal "ch2ch_lubMF2L" Cont.thy 
"[|monofun(MF2::('a::po=>'b::po=>'c::pcpo));\
\  !f.monofun(MF2(f)::('b::po=>'c::pcpo));\
\       is_chain(F);is_chain(Y)|] ==> \
\       is_chain(%i. lub(range(%j. MF2 (F j) (Y i))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (lub_mono RS allI RS is_chainI) 1),
        (etac ch2ch_MF2L 1),
        (atac 1),
        (etac ch2ch_MF2L 1),
        (atac 1),
        (strip_tac 1),
        (rtac (is_chainE RS spec) 1),
        ((rtac ch2ch_MF2R 1) THEN (etac spec 1)),
        (atac 1)
        ]);


qed_goal "lub_MF2_mono" Cont.thy 
"[|monofun(MF2::('a::po=>'b::po=>'c::pcpo));\
\  !f.monofun(MF2(f)::('b::po=>'c::pcpo));\
\       is_chain(F)|] ==> \
\       monofun(% x.lub(range(% j.MF2 (F j) (x))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac monofunI 1),
        (strip_tac 1),
        (rtac lub_mono 1),
        (etac ch2ch_MF2L 1),
        (atac 1),
        (etac ch2ch_MF2L 1),
        (atac 1),
        (strip_tac 1),
        ((rtac (monofunE RS spec RS spec RS mp) 1) THEN (etac spec 1)),
        (atac 1)
        ]);

qed_goal "ex_lubMF2" Cont.thy 
"[|monofun(MF2::('a::po=>'b::po=>'c::pcpo));\
\  !f.monofun(MF2(f)::('b::po=>'c::pcpo));\
\       is_chain(F); is_chain(Y)|] ==> \
\               lub(range(%j. lub(range(%i. MF2(F j) (Y i))))) =\
\               lub(range(%i. lub(range(%j. MF2(F j) (Y i)))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac antisym_less 1),
        (rtac (ub_rangeI RSN (2,is_lub_thelub)) 1),
        (etac ch2ch_lubMF2R 1),
        (REPEAT (atac 1)),
        (strip_tac 1),
        (rtac lub_mono 1),
        ((rtac ch2ch_MF2R 1) THEN (etac spec 1)),
        (atac 1),
        (etac ch2ch_lubMF2L 1),
        (REPEAT (atac 1)),
        (strip_tac 1),
        (rtac is_ub_thelub 1),
        (etac ch2ch_MF2L 1),
        (atac 1),
        (rtac (ub_rangeI RSN (2,is_lub_thelub)) 1),
        (etac ch2ch_lubMF2L 1),
        (REPEAT (atac 1)),
        (strip_tac 1),
        (rtac lub_mono 1),
        (etac ch2ch_MF2L 1),
        (atac 1),
        (etac ch2ch_lubMF2R 1),
        (REPEAT (atac 1)),
        (strip_tac 1),
        (rtac is_ub_thelub 1),
        ((rtac ch2ch_MF2R 1) THEN (etac spec 1)),
        (atac 1)
        ]);


qed_goal "diag_lubMF2_1" Cont.thy 
"[|monofun(MF2::('a::po=>'b::po=>'c::pcpo));\
\  !f.monofun(MF2(f)::('b::po=>'c::pcpo));\
\  is_chain(FY);is_chain(TY)|] ==>\
\ lub(range(%i. lub(range(%j. MF2(FY(j))(TY(i)))))) =\
\ lub(range(%i. MF2(FY(i))(TY(i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac antisym_less 1),
        (rtac (ub_rangeI RSN (2,is_lub_thelub)) 1),
        (etac ch2ch_lubMF2L 1),
        (REPEAT (atac 1)),
        (strip_tac 1 ),
        (rtac lub_mono3 1),
        (etac ch2ch_MF2L 1),
        (REPEAT (atac 1)),
        (etac ch2ch_MF2LR 1),
        (REPEAT (atac 1)),
        (rtac allI 1),
        (res_inst_tac [("m","i"),("n","ia")] nat_less_cases 1),
        (res_inst_tac [("x","ia")] exI 1),
        (rtac (chain_mono RS mp) 1),
        (etac allE 1),
        (etac ch2ch_MF2R 1),
        (REPEAT (atac 1)),
        (hyp_subst_tac 1),
        (res_inst_tac [("x","ia")] exI 1),
        (rtac refl_less 1),
        (res_inst_tac [("x","i")] exI 1),
        (rtac (chain_mono RS mp) 1),
        (etac ch2ch_MF2L 1),
        (REPEAT (atac 1)),
        (rtac lub_mono 1),
        (etac ch2ch_MF2LR 1),
        (REPEAT(atac 1)),
        (etac ch2ch_lubMF2L 1),
        (REPEAT (atac 1)),
        (strip_tac 1 ),
        (rtac is_ub_thelub 1),
        (etac ch2ch_MF2L 1),
        (atac 1)
        ]);

qed_goal "diag_lubMF2_2" Cont.thy 
"[|monofun(MF2::('a::po=>'b::po=>'c::pcpo));\
\  !f.monofun(MF2(f)::('b::po=>'c::pcpo));\
\  is_chain(FY);is_chain(TY)|] ==>\
\ lub(range(%j. lub(range(%i. MF2(FY(j))(TY(i)))))) =\
\ lub(range(%i. MF2(FY(i))(TY(i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans 1),
        (rtac ex_lubMF2 1),
        (REPEAT (atac 1)),
        (etac diag_lubMF2_1 1),
        (REPEAT (atac 1))
        ]);




(* ------------------------------------------------------------------------ *)
(* The following results are about a curried function that is continuous    *)
(* in both arguments                                                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_CF2" Cont.thy 
"[|cont(CF2);!f.cont(CF2(f));is_chain(FY);is_chain(TY)|] ==>\
\ CF2(lub(range(FY)))(lub(range(TY))) = lub(range(%i.CF2(FY(i))(TY(i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac ((hd prems) RS cont2contlub RS contlubE RS spec RS mp) 1),
        (atac 1),
        (stac thelub_fun 1),
        (rtac ((hd prems) RS cont2mono RS ch2ch_monofun) 1),
        (atac 1),
        (rtac trans 1),
        (rtac (((hd (tl prems)) RS spec RS cont2contlub) RS contlubE RS                spec RS mp RS ext RS arg_cong RS arg_cong) 1),
        (atac 1),
        (rtac diag_lubMF2_2 1),
        (etac cont2mono 1),
        (rtac allI 1),
        (etac allE 1),
        (etac cont2mono 1),
        (REPEAT (atac 1))
        ]);

(* ------------------------------------------------------------------------ *)
(* The following results are about application for functions in 'a=>'b      *)
(* ------------------------------------------------------------------------ *)

qed_goal "monofun_fun_fun" Cont.thy 
        "f1 << f2 ==> f1(x) << f2(x)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac (less_fun RS iffD1 RS spec) 1)
        ]);

qed_goal "monofun_fun_arg" Cont.thy 
        "[|monofun(f); x1 << x2|] ==> f(x1) << f(x2)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac (monofunE RS spec RS spec RS mp) 1),
        (atac 1)
        ]);

qed_goal "monofun_fun" Cont.thy 
"[|monofun(f1); monofun(f2); f1 << f2; x1 << x2|] ==> f1(x1) << f2(x2)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans_less 1),
        (etac monofun_fun_arg 1),
        (atac 1),
        (etac monofun_fun_fun 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* The following results are about the propagation of monotonicity and      *)
(* continuity                                                               *)
(* ------------------------------------------------------------------------ *)

qed_goal "mono2mono_MF1L" Cont.thy 
        "[|monofun(c1)|] ==> monofun(%x. c1 x y)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac monofunI 1),
        (strip_tac 1),
        (etac (monofun_fun_arg RS monofun_fun_fun) 1),
        (atac 1)
        ]);

qed_goal "cont2cont_CF1L" Cont.thy 
        "[|cont(c1)|] ==> cont(%x. c1 x y)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac monocontlub2cont 1),
        (etac (cont2mono RS mono2mono_MF1L) 1),
        (rtac contlubI 1),
        (strip_tac 1),
        (rtac ((hd prems) RS cont2contlub RS 
                contlubE RS spec RS mp RS ssubst) 1),
        (atac 1),
        (stac thelub_fun 1),
        (rtac ch2ch_monofun 1),
        (etac cont2mono 1),
        (atac 1),
        (rtac refl 1)
        ]);

(*********  Note "(%x.%y.c1 x y) = c1" ***********)

qed_goal "mono2mono_MF1L_rev" Cont.thy
        "!y.monofun(%x.c1 x y) ==> monofun(c1)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac monofunI 1),
        (strip_tac 1),
        (rtac (less_fun RS iffD2) 1),
        (strip_tac 1),
        (rtac ((hd prems) RS spec RS monofunE RS spec RS spec RS mp) 1),
        (atac 1)
        ]);

qed_goal "cont2cont_CF1L_rev" Cont.thy
        "!y.cont(%x.c1 x y) ==> cont(c1)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac monocontlub2cont 1),
        (rtac (cont2mono RS allI RS mono2mono_MF1L_rev ) 1),
        (etac spec 1),
        (rtac contlubI 1),
        (strip_tac 1),
        (rtac ext 1),
        (stac thelub_fun 1),
        (rtac (cont2mono RS allI RS mono2mono_MF1L_rev RS ch2ch_monofun) 1),
        (etac spec 1),
        (atac 1),
        (rtac 
        ((hd prems) RS spec RS cont2contlub RS contlubE RS spec RS mp) 1),
        (atac 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* What D.A.Schmidt calls continuity of abstraction                         *)
(* never used here                                                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_abstraction" Cont.thy
"[|is_chain(Y::nat=>'a);!y.cont(%x.(c::'a=>'b=>'c) x y)|] ==>\
\ (%y.lub(range(%i.c (Y i) y))) = (lub(range(%i.%y.c (Y i) y)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans 1),
        (rtac (cont2contlub RS contlubE RS spec RS mp) 2),
        (atac 3),
        (etac cont2cont_CF1L_rev 2),
        (rtac ext 1), 
        (rtac (cont2contlub RS contlubE RS spec RS mp RS sym) 1),
        (etac spec 1),
        (atac 1)
        ]);


qed_goal "mono2mono_app" Cont.thy 
"[|monofun(ft);!x.monofun(ft(x));monofun(tt)|] ==>\
\        monofun(%x.(ft(x))(tt(x)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac monofunI 1),
        (strip_tac 1),
        (res_inst_tac [("f1.0","ft(x)"),("f2.0","ft(y)")] monofun_fun 1),
        (etac spec 1),
        (etac spec 1),
        (etac (monofunE RS spec RS spec RS mp) 1),
        (atac 1),
        (etac (monofunE RS spec RS spec RS mp) 1),
        (atac 1)
        ]);


qed_goal "cont2contlub_app" Cont.thy 
"[|cont(ft);!x.cont(ft(x));cont(tt)|] ==> contlub(%x.(ft(x))(tt(x)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac contlubI 1),
        (strip_tac 1),
        (res_inst_tac [("f3","tt")] (contlubE RS spec RS mp RS ssubst) 1),
        (etac cont2contlub 1),
        (atac 1),
        (rtac contlub_CF2 1),
        (REPEAT (atac 1)),
        (etac (cont2mono RS ch2ch_monofun) 1),
        (atac 1)
        ]);


qed_goal "cont2cont_app" Cont.thy 
"[|cont(ft);!x.cont(ft(x));cont(tt)|] ==>\
\        cont(%x.(ft(x))(tt(x)))"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac mono2mono_app 1),
        (rtac cont2mono 1),
        (resolve_tac prems 1),
        (strip_tac 1),
        (rtac cont2mono 1),
        (cut_facts_tac prems 1),
        (etac spec 1),
        (rtac cont2mono 1),
        (resolve_tac prems 1),
        (rtac cont2contlub_app 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1)
        ]);


bind_thm ("cont2cont_app2", allI RSN (2,cont2cont_app));
(*  [| cont ?ft; !!x. cont (?ft x); cont ?tt |] ==> *)
(*        cont (%x. ?ft x (?tt x))                    *)


(* ------------------------------------------------------------------------ *)
(* The identity function is continuous                                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont_id" Cont.thy "cont(% x.x)"
 (fn prems =>
        [
        (rtac contI 1),
        (strip_tac 1),
        (etac thelubE 1),
        (rtac refl 1)
        ]);



(* ------------------------------------------------------------------------ *)
(* constant functions are continuous                                        *)
(* ------------------------------------------------------------------------ *)

qed_goalw "cont_const" Cont.thy [cont] "cont(%x.c)"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (strip_tac 1),
        (rtac refl_less 1),
        (strip_tac 1),
        (dtac ub_rangeE 1),
        (etac spec 1)
        ]);


qed_goal "cont2cont_app3" Cont.thy 
 "[|cont(f);cont(t) |] ==> cont(%x. f(t(x)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac cont2cont_app2 1),
        (rtac cont_const 1),
        (atac 1),
        (atac 1)
        ]);

