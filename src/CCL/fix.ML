(*  Title: 	CCL/fix
    ID:         $Id$
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For fix.thy.
*)

open Fix;

(*** Fixed Point Induction ***)

val [base,step,incl] = goalw Fix.thy [INCL_def]
    "[| P(bot);  !!x.P(x) ==> P(f(x));  INCL(P) |] ==> P(fix(f))";
br (incl RS spec RS mp) 1;
by (rtac (Nat_ind RS ballI) 1 THEN atac 1);
by (ALLGOALS (simp_tac term_ss));
by (REPEAT (ares_tac [base,step] 1));
val fix_ind = result();

(*** Inclusive Predicates ***)

val prems = goalw Fix.thy [INCL_def]
     "INCL(P) <-> (ALL f. (ALL n:Nat. P(f ^ n ` bot)) --> P(fix(f)))";
br iff_refl 1;
val inclXH = result();

val prems = goal Fix.thy
     "[| !!f.ALL n:Nat.P(f^n`bot) ==> P(fix(f)) |] ==> INCL(%x.P(x))";
by (fast_tac (term_cs addIs (prems @ [XH_to_I inclXH])) 1);
val inclI = result();

val incl::prems = goal Fix.thy
     "[| INCL(P);  !!n.n:Nat ==> P(f^n`bot) |] ==> P(fix(f))";
by (fast_tac (term_cs addIs ([ballI RS (incl RS (XH_to_D inclXH) RS spec RS mp)] 
                       @ prems)) 1);
val inclD = result();

val incl::prems = goal Fix.thy
     "[| INCL(P);  (ALL n:Nat.P(f^n`bot))-->P(fix(f)) ==> R |] ==> R";
by (fast_tac (term_cs addIs ([incl RS inclD] @ prems)) 1);
val inclE = result();


(*** Lemmas for Inclusive Predicates ***)

goal Fix.thy "INCL(%x.~ a(x) [= t)";
br inclI 1;
bd bspec 1;
br zeroT 1;
be contrapos 1;
br po_trans 1;
ba 2;
br (napplyBzero RS ssubst) 1;
by (rtac po_cong 1 THEN rtac po_bot 1);
val npo_INCL = result();

val prems = goal Fix.thy "[| INCL(P);  INCL(Q) |] ==> INCL(%x.P(x) & Q(x))";
by (fast_tac (set_cs addSIs ([inclI] @ (prems RL [inclD]))) 1);;
val conj_INCL = result();

val prems = goal Fix.thy "[| !!a.INCL(P(a)) |] ==> INCL(%x.ALL a.P(a,x))";
by (fast_tac (set_cs addSIs ([inclI] @ (prems RL [inclD]))) 1);;
val all_INCL = result();

val prems = goal Fix.thy "[| !!a.a:A ==> INCL(P(a)) |] ==> INCL(%x.ALL a:A.P(a,x))";
by (fast_tac (set_cs addSIs ([inclI] @ (prems RL [inclD]))) 1);;
val ball_INCL = result();

goal Fix.thy "INCL(%x.a(x) = b(x)::'a::prog)";
by (simp_tac (term_ss addsimps [eq_iff]) 1);
by (REPEAT (resolve_tac [conj_INCL,po_INCL] 1));
val eq_INCL = result();

(*** Derivation of Reachability Condition ***)

(* Fixed points of idgen *)

goal Fix.thy "idgen(fix(idgen)) = fix(idgen)";
br (fixB RS sym) 1;
val fix_idgenfp = result();

goalw Fix.thy [idgen_def] "idgen(lam x.x) = lam x.x";
by (simp_tac term_ss 1);
br (term_case RS allI) 1;
by (ALLGOALS (simp_tac term_ss));
val id_idgenfp = result();

(* All fixed points are lam-expressions *)

val [prem] = goal Fix.thy "idgen(d) = d ==> d = lam x.?f(x)";
br (prem RS subst) 1;
bw idgen_def;
br refl 1;
val idgenfp_lam = result();

(* Lemmas for rewriting fixed points of idgen *)

val prems = goalw Fix.thy [idgen_def] 
    "[| a = b;  a ` t = u |] ==> b ` t = u";
by (simp_tac (term_ss addsimps (prems RL [sym])) 1);
val l_lemma= result();

val idgen_lemmas =
    let fun mk_thm s = prove_goalw Fix.thy [idgen_def] s
           (fn [prem] => [rtac (prem RS l_lemma) 1,simp_tac term_ss 1])
    in map mk_thm
          [    "idgen(d) = d ==> d ` bot = bot",
               "idgen(d) = d ==> d ` true = true",
               "idgen(d) = d ==> d ` false = false",
               "idgen(d) = d ==> d ` <a,b> = <d ` a,d ` b>",
               "idgen(d) = d ==> d ` (lam x.f(x)) = lam x.d ` f(x)"]
    end;

(* Proof of Reachability law - show that fix and lam x.x both give LEAST fixed points 
                               of idgen and hence are they same *)

val [p1,p2,p3] = goal CCL.thy
    "[| ALL x.t ` x [= u ` x;  EX f.t=lam x.f(x);  EX f.u=lam x.f(x) |] ==> t [= u";
br (p2 RS cond_eta RS ssubst) 1;
br (p3 RS cond_eta RS ssubst) 1;
br (p1 RS (po_lam RS iffD2)) 1;
val po_eta = result();

val [prem] = goalw Fix.thy [idgen_def] "idgen(d) = d ==> d = lam x.?f(x)";
br (prem RS subst) 1;
br refl 1;
val po_eta_lemma = result();

val [prem] = goal Fix.thy
    "idgen(d) = d ==> \
\      {p.EX a b.p=<a,b> & (EX t.a=fix(idgen) ` t & b = d ` t)} <=   \
\      POgen({p.EX a b.p=<a,b> & (EX t.a=fix(idgen) ` t  & b = d ` t)})";
by (REPEAT (step_tac term_cs 1));
by (term_case_tac "t" 1);
by (ALLGOALS (simp_tac (term_ss addsimps (POgenXH::([prem,fix_idgenfp] RL idgen_lemmas)))));
by (ALLGOALS (fast_tac set_cs));
val lemma1 = result();

val [prem] = goal Fix.thy
    "idgen(d) = d ==> fix(idgen) [= d";
br (allI RS po_eta) 1;
br (lemma1 RSN(2,po_coinduct)) 1;
by (ALLGOALS (fast_tac (term_cs addIs [prem,po_eta_lemma,fix_idgenfp])));
val fix_least_idgen = result();

val [prem] = goal Fix.thy
    "idgen(d) = d ==> \
\      {p.EX a b.p=<a,b> & b = d ` a} <= POgen({p.EX a b.p=<a,b> & b = d ` a})";
by (REPEAT (step_tac term_cs 1));
by (term_case_tac "a" 1);
by (ALLGOALS (simp_tac (term_ss addsimps (POgenXH::([prem] RL idgen_lemmas)))));
by (ALLGOALS (fast_tac set_cs));
val lemma2 = result();

val [prem] = goal Fix.thy
    "idgen(d) = d ==> lam x.x [= d";
br (allI RS po_eta) 1;
br (lemma2 RSN(2,po_coinduct)) 1;
by (simp_tac term_ss 1);
by (ALLGOALS (fast_tac (term_cs addIs [prem,po_eta_lemma,fix_idgenfp])));
val id_least_idgen = result();

goal Fix.thy  "fix(idgen) = lam x.x";
by (fast_tac (term_cs addIs [eq_iff RS iffD2,
                             id_idgenfp RS fix_least_idgen,
                             fix_idgenfp RS id_least_idgen]) 1);
val reachability = result();

(********)

val [prem] = goal Fix.thy "f = lam x.x ==> f`t = t";
br (prem RS sym RS subst) 1;
br applyB 1;
val id_apply = result();

val prems = goal Fix.thy
     "[| P(bot);  P(true);  P(false);  \
\        !!x y.[| P(x);  P(y) |] ==> P(<x,y>);  \
\        !!u.(!!x.P(u(x))) ==> P(lam x.u(x));  INCL(P) |] ==> \
\     P(t)";
br (reachability RS id_apply RS subst) 1;
by (res_inst_tac [("x","t")] spec 1);
br fix_ind 1;
bw idgen_def;
by (REPEAT_SOME (ares_tac [allI]));
br (applyBbot RS ssubst) 1;
brs prems 1;
br (applyB RS ssubst )1;
by (res_inst_tac [("t","xa")] term_case 1);
by (ALLGOALS (simp_tac term_ss));
by (ALLGOALS (fast_tac (term_cs addIs ([all_INCL,INCL_subst] @ prems))));
val term_ind = result();

