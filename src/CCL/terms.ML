(*  Title: 	CCL/terms
    ID:         $Id$
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For terms.thy.
*)

open Term;

val simp_can_defs = [one_def,inl_def,inr_def];
val simp_ncan_defs = [if_def,when_def,split_def,fst_def,snd_def,thd_def];
val simp_defs = simp_can_defs @ simp_ncan_defs;

val ind_can_defs = [zero_def,succ_def,nil_def,cons_def];
val ind_ncan_defs = [ncase_def,nrec_def,lcase_def,lrec_def];
val ind_defs = ind_can_defs @ ind_ncan_defs;

val data_defs = simp_defs @ ind_defs @ [napply_def];
val genrec_defs = [letrec_def,letrec2_def,letrec3_def];

val term_congs = ccl_mk_congs Term.thy 
    ["inl","inr","succ","op .","split","if","when","ncase","nrec","lcase","lrec",
     "fst","snd","thd","let","letrec","letrec2","letrec3","napply"];

(*** Beta Rules, including strictness ***)

goalw Term.thy [let_def] "~ t=bot--> let x be t in f(x) = f(t)";
by (res_inst_tac [("t","t")] term_case 1);
by (ALLGOALS(SIMP_TAC(CCL_ss addrews [caseBtrue,caseBfalse,caseBpair,caseBlam])));
val letB = result() RS mp;

goalw Term.thy [let_def] "let x be bot in f(x) = bot";
br caseBbot 1;
val letBabot = result();

goalw Term.thy [let_def] "let x be t in bot = bot";
brs ([caseBbot] RL [term_case]) 1;
by (ALLGOALS(SIMP_TAC(CCL_ss addrews [caseBtrue,caseBfalse,caseBpair,caseBlam])));
val letBbbot = result();

goalw Term.thy [apply_def] "(lam x.b(x)) ` a = b(a)";
by (ALLGOALS(SIMP_TAC(CCL_ss addrews [caseBtrue,caseBfalse,caseBpair,caseBlam])));
val applyB = result();

goalw Term.thy [apply_def] "bot ` a = bot";
br caseBbot 1;
val applyBbot = result();

goalw Term.thy [fix_def] "fix(f) = f(fix(f))";
by (resolve_tac [applyB RS ssubst] 1 THEN resolve_tac [refl] 1);
val fixB = result();

goalw Term.thy [letrec_def]
      "letrec g x be h(x,g) in g(a) = h(a,%y.letrec g x be h(x,g) in g(y))";
by (resolve_tac [fixB RS ssubst] 1 THEN 
    resolve_tac [applyB RS ssubst] 1 THEN resolve_tac [refl] 1);
val letrecB = result();

val rawBs = caseBs @ [applyB,applyBbot,letrecB];

fun raw_mk_beta_rl defs s = prove_goalw Term.thy defs s
           (fn _ => [SIMP_TAC (CCL_ss addrews rawBs  addcongs term_congs) 1]);
fun mk_beta_rl s = raw_mk_beta_rl data_defs s;

val ifBtrue    = mk_beta_rl "if true then t else u = t";
val ifBfalse   = mk_beta_rl "if false then t else u = u";
val ifBbot     = mk_beta_rl "if bot then t else u = bot";

val whenBinl   = mk_beta_rl "when(inl(a),t,u) = t(a)";
val whenBinr   = mk_beta_rl "when(inr(a),t,u) = u(a)";
val whenBbot   = mk_beta_rl "when(bot,t,u) = bot";

val splitB     = mk_beta_rl "split(<a,b>,h) = h(a,b)";
val splitBbot  = mk_beta_rl "split(bot,h) = bot";
val fstB       = mk_beta_rl "fst(<a,b>) = a";
val fstBbot    = mk_beta_rl "fst(bot) = bot";
val sndB       = mk_beta_rl "snd(<a,b>) = b";
val sndBbot    = mk_beta_rl "snd(bot) = bot";
val thdB       = mk_beta_rl "thd(<a,<b,c>>) = c";
val thdBbot    = mk_beta_rl "thd(bot) = bot";

val ncaseBzero = mk_beta_rl "ncase(zero,t,u) = t";
val ncaseBsucc = mk_beta_rl "ncase(succ(n),t,u) = u(n)";
val ncaseBbot  = mk_beta_rl "ncase(bot,t,u) = bot";
val nrecBzero  = mk_beta_rl "nrec(zero,t,u) = t";
val nrecBsucc  = mk_beta_rl "nrec(succ(n),t,u) = u(n,nrec(n,t,u))";
val nrecBbot   = mk_beta_rl "nrec(bot,t,u) = bot";

val lcaseBnil  = mk_beta_rl "lcase([],t,u) = t";
val lcaseBcons = mk_beta_rl "lcase(x.xs,t,u) = u(x,xs)";
val lcaseBbot  = mk_beta_rl "lcase(bot,t,u) = bot";
val lrecBnil   = mk_beta_rl "lrec([],t,u) = t";
val lrecBcons  = mk_beta_rl "lrec(x.xs,t,u) = u(x,xs,lrec(xs,t,u))";
val lrecBbot   = mk_beta_rl "lrec(bot,t,u) = bot";

val letrec2B = raw_mk_beta_rl (data_defs @ [letrec2_def])
       "letrec g x y be h(x,y,g) in g(p,q) = \
\                     h(p,q,%u v.letrec g x y be h(x,y,g) in g(u,v))";
val letrec3B = raw_mk_beta_rl (data_defs @ [letrec3_def])
       "letrec g x y z be h(x,y,z,g) in g(p,q,r) = \
\                     h(p,q,r,%u v w.letrec g x y z be h(x,y,z,g) in g(u,v,w))";

val napplyBzero   = mk_beta_rl "f^zero`a = a";
val napplyBsucc   = mk_beta_rl "f^succ(n)`a = f(f^n`a)";

val termBs = [letB,applyB,applyBbot,splitB,splitBbot,
              fstB,fstBbot,sndB,sndBbot,thdB,thdBbot,
              ifBtrue,ifBfalse,ifBbot,whenBinl,whenBinr,whenBbot,
              ncaseBzero,ncaseBsucc,ncaseBbot,nrecBzero,nrecBsucc,nrecBbot,
              lcaseBnil,lcaseBcons,lcaseBbot,lrecBnil,lrecBcons,lrecBbot,
              napplyBzero,napplyBsucc];

(*** Constructors are injective ***)

val term_injs = map (mk_inj_rl Term.thy 
                             [applyB,splitB,whenBinl,whenBinr,ncaseBsucc,lcaseBcons] 
                             (ccl_congs @ term_congs))
               ["(inl(a) = inl(a')) <-> (a=a')",
                "(inr(a) = inr(a')) <-> (a=a')",
                "(succ(a) = succ(a')) <-> (a=a')",
                "(a.b = a'.b') <-> (a=a' & b=b')"];

(*** Constructors are distinct ***)

val term_dstncts = mkall_dstnct_thms Term.thy data_defs (ccl_injs @ term_injs)
                    [["bot","inl","inr"],["bot","zero","succ"],["bot","nil","op ."]];

(*** Rules for pre-order [= ***)

local
  fun mk_thm s = prove_goalw Term.thy data_defs s (fn _ => 
                  [SIMP_TAC (ccl_ss addrews (ccl_porews)) 1]);
in
  val term_porews = map mk_thm ["inl(a) [= inl(a') <-> a [= a'",
                                "inr(b) [= inr(b') <-> b [= b'",
                                "succ(n) [= succ(n') <-> n [= n'",
                                "x.xs [= x'.xs' <-> x [= x'  & xs [= xs'"];
end;

(*** Rewriting and Proving ***)

val term_rews = termBs @ term_injs @ term_dstncts @ ccl_porews @ term_porews;
val term_ss = ccl_ss addrews term_rews addcongs term_congs;

val term_cs = ccl_cs addSEs (term_dstncts RL [notE]) addSDs (XH_to_Ds term_injs);
