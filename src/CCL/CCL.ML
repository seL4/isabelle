(*  Title:      CCL/ccl
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For ccl.thy.
*)

open CCL;

val ccl_data_defs = [apply_def,fix_def];

val CCL_ss = set_ss addsimps [po_refl RS P_iff_T];

(*** Congruence Rules ***)

(*similar to AP_THM in Gordon's HOL*)
qed_goal "fun_cong" CCL.thy "(f::'a=>'b) = g ==> f(x)=g(x)"
  (fn [prem] => [rtac (prem RS subst) 1, rtac refl 1]);

(*similar to AP_TERM in Gordon's HOL and FOL's subst_context*)
qed_goal "arg_cong" CCL.thy "x=y ==> f(x)=f(y)"
 (fn [prem] => [rtac (prem RS subst) 1, rtac refl 1]);

goal CCL.thy  "(ALL x. f(x) = g(x)) --> (%x. f(x)) = (%x. g(x))";
by (simp_tac (CCL_ss addsimps [eq_iff]) 1);
by (fast_tac (set_cs addIs [po_abstractn]) 1);
bind_thm("abstractn", standard (allI RS (result() RS mp)));

fun type_of_terms (Const("Trueprop",_) $ 
                   (Const("op =",(Type ("fun", [t,_]))) $ _ $ _)) = t;

fun abs_prems thm = 
   let fun do_abs n thm (Type ("fun", [_,t])) = do_abs n (abstractn RSN (n,thm)) t
         | do_abs n thm _                     = thm
       fun do_prems n      [] thm = thm
         | do_prems n (x::xs) thm = do_prems (n+1) xs (do_abs n thm (type_of_terms x));
   in do_prems 1 (prems_of thm) thm
   end;

val caseBs = [caseBtrue,caseBfalse,caseBpair,caseBlam,caseBbot];

(*** Termination and Divergence ***)

goalw CCL.thy [Trm_def,Dvg_def] "Trm(t) <-> ~ t = bot";
by (rtac iff_refl 1);
qed "Trm_iff";

goalw CCL.thy [Trm_def,Dvg_def] "Dvg(t) <-> t = bot";
by (rtac iff_refl 1);
qed "Dvg_iff";

(*** Constructors are injective ***)

val prems = goal CCL.thy
    "[| x=a;  y=b;  x=y |] ==> a=b";
by  (REPEAT (SOMEGOAL (ares_tac (prems@[box_equals]))));
qed "eq_lemma";

fun mk_inj_rl thy rews s = 
      let fun mk_inj_lemmas r = ([arg_cong] RL [(r RS (r RS eq_lemma))]);
          val inj_lemmas = flat (map mk_inj_lemmas rews);
          val tac = REPEAT (ares_tac [iffI,allI,conjI] 1 ORELSE
                            eresolve_tac inj_lemmas 1 ORELSE
                            asm_simp_tac (CCL_ss addsimps rews) 1)
      in prove_goal thy s (fn _ => [tac])
      end;

val ccl_injs = map (mk_inj_rl CCL.thy caseBs)
               ["<a,b> = <a',b'> <-> (a=a' & b=b')",
                "(lam x. b(x) = lam x. b'(x)) <-> ((ALL z. b(z)=b'(z)))"];

val pair_inject = ((hd ccl_injs) RS iffD1) RS conjE;

(*** Constructors are distinct ***)

local
  fun pairs_of f x [] = []
    | pairs_of f x (y::ys) = (f x y) :: (f y x) :: (pairs_of f x ys);

  fun mk_combs ff [] = []
    | mk_combs ff (x::xs) = (pairs_of ff x xs) @ mk_combs ff xs;

(* Doesn't handle binder types correctly *)
  fun saturate thy sy name = 
       let fun arg_str 0 a s = s
         | arg_str 1 a s = "(" ^ a ^ "a" ^ s ^ ")"
         | arg_str n a s = arg_str (n-1) a ("," ^ a ^ (chr((ord "a")+n-1)) ^ s);
           val sg = sign_of thy;
           val T = case Sign.const_type sg sy of
                            None => error(sy^" not declared") | Some(T) => T;
           val arity = length (fst (strip_type T));
       in sy ^ (arg_str arity name "") end;

  fun mk_thm_str thy a b = "~ " ^ (saturate thy a "a") ^ " = " ^ (saturate thy b "b");

  val lemma = prove_goal CCL.thy "t=t' --> case(t,b,c,d,e) = case(t',b,c,d,e)"
                   (fn _ => [simp_tac CCL_ss 1]) RS mp;
  fun mk_lemma (ra,rb) = [lemma] RL [ra RS (rb RS eq_lemma)] RL 
                           [distinctness RS notE,sym RS (distinctness RS notE)];
in
  fun mk_lemmas rls = flat (map mk_lemma (mk_combs pair rls));
  fun mk_dstnct_rls thy xs = mk_combs (mk_thm_str thy) xs;
end;


val caseB_lemmas = mk_lemmas caseBs;

val ccl_dstncts = 
        let fun mk_raw_dstnct_thm rls s = 
                  prove_goal CCL.thy s (fn _=> [rtac notI 1,eresolve_tac rls 1])
        in map (mk_raw_dstnct_thm caseB_lemmas) 
                (mk_dstnct_rls CCL.thy ["bot","true","false","pair","lambda"]) end;

fun mk_dstnct_thms thy defs inj_rls xs = 
          let fun mk_dstnct_thm rls s = prove_goalw thy defs s 
                               (fn _ => [simp_tac (CCL_ss addsimps (rls@inj_rls)) 1])
          in map (mk_dstnct_thm ccl_dstncts) (mk_dstnct_rls thy xs) end;

fun mkall_dstnct_thms thy defs i_rls xss = flat (map (mk_dstnct_thms thy defs i_rls) xss);

(*** Rewriting and Proving ***)

fun XH_to_I rl = rl RS iffD2;
fun XH_to_D rl = rl RS iffD1;
val XH_to_E = make_elim o XH_to_D;
val XH_to_Is = map XH_to_I;
val XH_to_Ds = map XH_to_D;
val XH_to_Es = map XH_to_E;

val ccl_rews = caseBs @ ccl_injs @ ccl_dstncts;
val ccl_ss = CCL_ss addsimps ccl_rews;

val ccl_cs = set_cs addSEs (pair_inject::(ccl_dstncts RL [notE])) 
                    addSDs (XH_to_Ds ccl_injs);

(****** Facts from gfp Definition of [= and = ******)

val major::prems = goal Set.thy "[| A=B;  a:B <-> P |] ==> a:A <-> P";
by (resolve_tac (prems RL [major RS ssubst]) 1);
qed "XHlemma1";

goal CCL.thy "(P(t,t') <-> Q) --> (<t,t'> : {p. EX t t'. p=<t,t'> &  P(t,t')} <-> Q)";
by (fast_tac ccl_cs 1);
bind_thm("XHlemma2", result() RS mp);

(*** Pre-Order ***)

goalw CCL.thy [POgen_def,SIM_def]  "mono(%X. POgen(X))";
by (rtac monoI 1);
by (safe_tac ccl_cs);
by (REPEAT_SOME (resolve_tac [exI,conjI,refl]));
by (ALLGOALS (simp_tac ccl_ss));
by (ALLGOALS (fast_tac set_cs));
qed "POgen_mono";

goalw CCL.thy [POgen_def,SIM_def]
  "<t,t'> : POgen(R) <-> t= bot | (t=true & t'=true)  | (t=false & t'=false) | \
\                    (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & <a,a'> : R & <b,b'> : R) | \
\                    (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x. <f(x),f'(x)> : R))";
by (rtac (iff_refl RS XHlemma2) 1);
qed "POgenXH";

goal CCL.thy
  "t [= t' <-> t=bot | (t=true & t'=true) | (t=false & t'=false) | \
\                    (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & a [= a' & b [= b') | \
\                    (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x. f(x) [= f'(x)))";
by (simp_tac (ccl_ss addsimps [PO_iff]) 1);
br (rewrite_rule [POgen_def,SIM_def] 
                 (POgen_mono RS (PO_def RS def_gfp_Tarski) RS XHlemma1)) 1;
by (rtac (iff_refl RS XHlemma2) 1);
qed "poXH";

goal CCL.thy "bot [= b";
by (rtac (poXH RS iffD2) 1);
by (simp_tac ccl_ss 1);
qed "po_bot";

goal CCL.thy "a [= bot --> a=bot";
by (rtac impI 1);
by (dtac (poXH RS iffD1) 1);
by (etac rev_mp 1);
by (simp_tac ccl_ss 1);
bind_thm("bot_poleast", result() RS mp);

goal CCL.thy "<a,b> [= <a',b'> <->  a [= a' & b [= b'";
by (rtac (poXH RS iff_trans) 1);
by (simp_tac ccl_ss 1);
by (fast_tac ccl_cs 1);
qed "po_pair";

goal CCL.thy "lam x. f(x) [= lam x. f'(x) <-> (ALL x. f(x) [= f'(x))";
by (rtac (poXH RS iff_trans) 1);
by (simp_tac ccl_ss 1);
by (REPEAT (ares_tac [iffI,allI] 1 ORELSE eresolve_tac [exE,conjE] 1));
by (asm_simp_tac ccl_ss 1);
by (fast_tac ccl_cs 1);
qed "po_lam";

val ccl_porews = [po_bot,po_pair,po_lam];

val [p1,p2,p3,p4,p5] = goal CCL.thy
    "[| t [= t';  a [= a';  b [= b';  !!x y. c(x,y) [= c'(x,y); \
\       !!u. d(u) [= d'(u) |] ==> case(t,a,b,c,d) [= case(t',a',b',c',d')";
by (rtac (p1 RS po_cong RS po_trans) 1);
by (rtac (p2 RS po_cong RS po_trans) 1);
by (rtac (p3 RS po_cong RS po_trans) 1);
by (rtac (p4 RS po_abstractn RS po_abstractn RS po_cong RS po_trans) 1);
by (res_inst_tac [("f1","%d. case(t',a',b',c',d)")] 
               (p5 RS po_abstractn RS po_cong RS po_trans) 1);
by (rtac po_refl 1);
qed "case_pocong";

val [p1,p2] = goalw CCL.thy ccl_data_defs
    "[| f [= f';  a [= a' |] ==> f ` a [= f' ` a'";
by (REPEAT (ares_tac [po_refl,case_pocong,p1,p2 RS po_cong] 1));
qed "apply_pocong";


val prems = goal CCL.thy "~ lam x. b(x) [= bot";
by (rtac notI 1);
by (dtac bot_poleast 1);
by (etac (distinctness RS notE) 1);
qed "npo_lam_bot";

val eq1::eq2::prems = goal CCL.thy
    "[| x=a;  y=b;  x[=y |] ==> a[=b";
by (rtac (eq1 RS subst) 1);
by (rtac (eq2 RS subst) 1);
by (resolve_tac prems 1);
qed "po_lemma";

goal CCL.thy "~ <a,b> [= lam x. f(x)";
by (rtac notI 1);
by (rtac (npo_lam_bot RS notE) 1);
by (etac (case_pocong RS (caseBlam RS (caseBpair RS po_lemma))) 1);
by (REPEAT (resolve_tac [po_refl,npo_lam_bot] 1));
qed "npo_pair_lam";

goal CCL.thy "~ lam x. f(x) [= <a,b>";
by (rtac notI 1);
by (rtac (npo_lam_bot RS notE) 1);
by (etac (case_pocong RS (caseBpair RS (caseBlam RS po_lemma))) 1);
by (REPEAT (resolve_tac [po_refl,npo_lam_bot] 1));
qed "npo_lam_pair";

fun mk_thm s = prove_goal CCL.thy s (fn _ => 
                          [rtac notI 1,dtac case_pocong 1,etac rev_mp 5,
                           ALLGOALS (simp_tac ccl_ss),
                           REPEAT (resolve_tac [po_refl,npo_lam_bot] 1)]);

val npo_rls = [npo_pair_lam,npo_lam_pair] @ map mk_thm
            ["~ true [= false",          "~ false [= true",
             "~ true [= <a,b>",          "~ <a,b> [= true",
             "~ true [= lam x. f(x)","~ lam x. f(x) [= true",
            "~ false [= <a,b>",          "~ <a,b> [= false",
            "~ false [= lam x. f(x)","~ lam x. f(x) [= false"];

(* Coinduction for [= *)

val prems = goal CCL.thy "[|  <t,u> : R;  R <= POgen(R) |] ==> t [= u";
by (rtac (PO_def RS def_coinduct RS (PO_iff RS iffD2)) 1);
by (REPEAT (ares_tac prems 1));
qed "po_coinduct";

fun po_coinduct_tac s i = res_inst_tac [("R",s)] po_coinduct i;

(*************** EQUALITY *******************)

goalw CCL.thy [EQgen_def,SIM_def]  "mono(%X. EQgen(X))";
by (rtac monoI 1);
by (safe_tac set_cs);
by (REPEAT_SOME (resolve_tac [exI,conjI,refl]));
by (ALLGOALS (simp_tac ccl_ss));
by (ALLGOALS (fast_tac set_cs));
qed "EQgen_mono";

goalw CCL.thy [EQgen_def,SIM_def]
  "<t,t'> : EQgen(R) <-> (t=bot & t'=bot)  | (t=true & t'=true)  | \
\                                            (t=false & t'=false) | \
\                (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & <a,a'> : R & <b,b'> : R) | \
\                (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x.<f(x),f'(x)> : R))";
by (rtac (iff_refl RS XHlemma2) 1);
qed "EQgenXH";

goal CCL.thy
  "t=t' <-> (t=bot & t'=bot)  | (t=true & t'=true)  | (t=false & t'=false) | \
\                    (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & a=a' & b=b') | \
\                    (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x. f(x)=f'(x)))";
by (subgoal_tac
  "<t,t'> : EQ <-> (t=bot & t'=bot)  | (t=true & t'=true) | (t=false & t'=false) | \
\             (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & <a,a'> : EQ & <b,b'> : EQ) | \
\             (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x. <f(x),f'(x)> : EQ))" 1);
by (etac rev_mp 1);
by (simp_tac (CCL_ss addsimps [EQ_iff RS iff_sym]) 1);
br (rewrite_rule [EQgen_def,SIM_def]
                 (EQgen_mono RS (EQ_def RS def_gfp_Tarski) RS XHlemma1)) 1;
by (rtac (iff_refl RS XHlemma2) 1);
qed "eqXH";

val prems = goal CCL.thy "[|  <t,u> : R;  R <= EQgen(R) |] ==> t = u";
by (rtac (EQ_def RS def_coinduct RS (EQ_iff RS iffD2)) 1);
by (REPEAT (ares_tac prems 1));
qed "eq_coinduct";

val prems = goal CCL.thy 
    "[|  <t,u> : R;  R <= EQgen(lfp(%x. EQgen(x) Un R Un EQ)) |] ==> t = u";
by (rtac (EQ_def RS def_coinduct3 RS (EQ_iff RS iffD2)) 1);
by (REPEAT (ares_tac (EQgen_mono::prems) 1));
qed "eq_coinduct3";

fun eq_coinduct_tac s i = res_inst_tac [("R",s)] eq_coinduct i;
fun eq_coinduct3_tac s i = res_inst_tac [("R",s)] eq_coinduct3 i;

(*** Untyped Case Analysis and Other Facts ***)

goalw CCL.thy [apply_def]  "(EX f. t=lam x. f(x)) --> t = lam x.(t ` x)";
by (safe_tac ccl_cs);
by (simp_tac ccl_ss 1);
bind_thm("cond_eta", result() RS mp);

goal CCL.thy "(t=bot) | (t=true) | (t=false) | (EX a b. t=<a,b>) | (EX f. t=lam x. f(x))";
by (cut_facts_tac [refl RS (eqXH RS iffD1)] 1);
by (fast_tac set_cs 1);
qed "exhaustion";

val prems = goal CCL.thy 
    "[| P(bot);  P(true);  P(false);  !!x y. P(<x,y>);  !!b. P(lam x. b(x)) |] ==> P(t)";
by (cut_facts_tac [exhaustion] 1);
by (REPEAT_SOME (ares_tac prems ORELSE' eresolve_tac [disjE,exE,ssubst]));
qed "term_case";

fun term_case_tac a i = res_inst_tac [("t",a)] term_case i;
