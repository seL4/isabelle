(*  Title:      HOL/Subst/unifier.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For unifier.thy.
Properties of unifiers.
Cases for partial correctness of algorithm and conditions for termination.
*)

open Unifier;

val unify_defs =
    [Idem_def,Unifier_def,MoreGeneral_def,MGUnifier_def,MGIUnifier_def];

(**** Unifiers ****)

goalw Unifier.thy [Unifier_def] "Unifier s t u = (t <| s = u <| s)";
by (rtac refl 1);
qed "Unifier_iff";

goal Unifier.thy
    "Unifier s (Comb t u) (Comb v w) --> Unifier s t v & Unifier s u w";
by (simp_tac (subst_ss addsimps [Unifier_iff]) 1);
val Unifier_Comb  = store_thm("Unifier_Comb", result() RS mp RS conjE);

goal Unifier.thy
  "~v : vars_of(t) --> ~v : vars_of(u) -->Unifier s t u --> \
\  Unifier ((v,r)#s) t u";
by (simp_tac (subst_ss addsimps [Unifier_iff,repl_invariance]) 1);
val Cons_Unifier  = store_thm("Cons_Unifier", result() RS mp RS mp RS mp);

(**** Most General Unifiers ****)

goalw Unifier.thy [MoreGeneral_def]  "r >> s = (EX q. s =s= r <> q)";
by (rtac refl 1);
qed "MoreGen_iff";

goal Unifier.thy  "[] >> s";
by (simp_tac (subst_ss addsimps [MoreGen_iff]) 1);
by (fast_tac (set_cs addIs [refl RS subst_refl]) 1);
qed "MoreGen_Nil";

goalw Unifier.thy unify_defs
    "MGUnifier s t u = (ALL r.Unifier r t u = s >> r)";
by (REPEAT (ares_tac [iffI,allI] 1 ORELSE 
            eresolve_tac [conjE,allE,mp,exE,ssubst_subst2] 1));
by (asm_simp_tac (subst_ss addsimps [subst_comp]) 1);
by (fast_tac (set_cs addIs [comp_Nil RS sym RS subst_refl]) 1);
qed "MGU_iff";

val [prem] = goal Unifier.thy
     "~ Var(v) <: t ==> MGUnifier [(v,t)] (Var v) t";
by (simp_tac (subst_ss addsimps [MGU_iff,MoreGen_iff,Unifier_iff]) 1);
by (REPEAT_SOME (step_tac set_cs));
by (etac subst 1);
by (etac ssubst_subst2 2);
by (rtac (Cons_trivial RS subst_sym) 1);
by (simp_tac (subst_ss addsimps [prem RS Var_not_occs,Var_subst]) 1);
qed "MGUnifier_Var";

(**** Most General Idempotent Unifiers ****)

goal Unifier.thy "r <> r =s= r --> s =s= r <> q --> r <> s =s= s";
by (simp_tac (subst_ss addsimps [subst_eq_iff,subst_comp]) 1);
val MGIU_iff_lemma  = store_thm("MGIU_iff_lemma", result() RS mp RS mp);

goalw Unifier.thy unify_defs
 "MGIUnifier s t u = \
\  (Idem(s) & Unifier s t u & (ALL r.Unifier r t u --> s<>r=s=r))";
by (fast_tac (set_cs addEs [subst_sym,MGIU_iff_lemma]) 1);
qed "MGIU_iff";

(**** Idempotence ****)

goalw Unifier.thy unify_defs "Idem(s) = (s <> s =s= s)";
by (rtac refl 1);
qed "raw_Idem_iff";

goal Unifier.thy "Idem(s) = (sdom(s) Int srange(s) = {})";
by (simp_tac (subst_ss addsimps [raw_Idem_iff,subst_eq_iff,subst_comp,
                                invariance,dom_range_disjoint])1);
qed "Idem_iff";

goal Unifier.thy "Idem([])";
by (simp_tac (subst_ss addsimps [raw_Idem_iff,refl RS subst_refl]) 1);
qed "Idem_Nil";

goal Unifier.thy "~ (Var(v) <: t) --> Idem([(v,t)])";
by (simp_tac (subst_ss addsimps [Var_subst,vars_iff_occseq,Idem_iff,srange_iff]
                       setloop (split_tac [expand_if])) 1);
by (fast_tac set_cs 1);
val Var_Idem  = store_thm("Var_Idem", result() RS mp);

val [prem] = goalw Unifier.thy [Idem_def]
     "Idem(r) ==>  Unifier s (t <| r) (u <| r) --> Unifier (r <> s) (t <| r) (u <| r)";
by (simp_tac (subst_ss addsimps 
              [Unifier_iff,subst_comp,prem RS comp_subst_subst]) 1);
val Unifier_Idem_subst  = store_thm("Unifier_Idem_subst", result() RS mp);

val [prem] = goal Unifier.thy 
     "r <> s =s= s ==>  Unifier s t u --> Unifier s (t <| r) (u <| r)";
by (simp_tac (subst_ss addsimps 
              [Unifier_iff,subst_comp,prem RS comp_subst_subst]) 1);
val Unifier_comp_subst  = store_thm("Unifier_comp_subst", result() RS mp);

(*** The domain of a MGIU is a subset of the variables in the terms ***)
(***      NB this and one for range are only needed for termination ***)

val [prem] = goal Unifier.thy
    "~ vars_of(Var(x) <| r) = vars_of(Var(x) <| s) ==> ~r =s= s";
by (rtac (prem RS contrapos) 1);
by (fast_tac (set_cs addEs [subst_subst2]) 1);
qed "lemma_lemma";

val prems = goal Unifier.thy 
    "x : sdom(s) -->  ~x : srange(s) --> \
\   ~vars_of(Var(x) <| s<> (x,Var(x))#s) = \
\      vars_of(Var(x) <| (x,Var(x))#s)";
by (simp_tac (subst_ss addsimps [not_equal_iff]) 1);
by (REPEAT (resolve_tac [impI,disjI2] 1));
by(res_inst_tac [("x","x")] exI 1);
by (rtac conjI 1);
by (asm_simp_tac (subst_ss addsimps [Var_elim,subst_comp,repl_invariance]) 1);
by (asm_simp_tac (subst_ss addsimps [Var_subst]) 1);
val MGIU_sdom_lemma = store_thm("MGIU_sdom_lemma", result() RS mp RS mp RS lemma_lemma RS notE);

goal Unifier.thy "MGIUnifier s t u --> sdom(s) <= vars_of(t) Un vars_of(u)";
by (subgoal_tac "! P Q.(P | Q) = (~( ~P & ~Q))" 1);
by (asm_simp_tac (subst_ss addsimps [MGIU_iff,Idem_iff,subset_iff]) 1);
by (safe_tac set_cs);
by (eresolve_tac ([spec] RL [impE]) 1);
by (rtac Cons_Unifier 1);
by (ALLGOALS (fast_tac (set_cs addIs [Cons_Unifier,MGIU_sdom_lemma])));
val MGIU_sdom  = store_thm("MGIU_sdom", result() RS mp);

(*** The range of a MGIU is a subset of the variables in the terms ***)

val prems = goal HOL.thy  "P = Q ==> (~P) = (~Q)";
by (simp_tac (subst_ss addsimps prems) 1);
qed "not_cong";

val prems = goal Unifier.thy 
   "~w=x --> x : vars_of(Var(w) <| s) --> w : sdom(s) --> ~w : srange(s) --> \
\   ~vars_of(Var(w) <| s<> (x,Var(w))#s) = \
\   vars_of(Var(w) <| (x,Var(w))#s)";
by (simp_tac (subst_ss addsimps [not_equal_iff]) 1);
by (REPEAT (resolve_tac [impI,disjI1] 1));
by(res_inst_tac [("x","w")] exI 1);
by (ALLGOALS (asm_simp_tac (subst_ss addsimps  [Var_elim,subst_comp,
                vars_var_iff RS not_cong RS iffD2 RS repl_invariance]) ));
by (fast_tac (set_cs addIs [Var_in_subst]) 1);
val MGIU_srange_lemma  = store_thm("MGIU_srange_lemma", result() RS mp RS mp RS mp RS mp RS lemma_lemma RS notE);

goal Unifier.thy "MGIUnifier s t u --> srange(s) <= vars_of(t) Un vars_of(u)";
by (subgoal_tac "! P Q.(P | Q) = (~( ~P & ~Q))" 1);
by (asm_simp_tac (subst_ss addsimps [MGIU_iff,srange_iff,subset_iff]) 1);
by (simp_tac (subst_ss addsimps [Idem_iff]) 1);
by (safe_tac set_cs);
by (eresolve_tac ([spec] RL [impE]) 1);
by (rtac Cons_Unifier 1);
by (imp_excluded_middle_tac "w=ta" 4);
by (fast_tac (set_cs addEs [MGIU_srange_lemma]) 5);
by (ALLGOALS (fast_tac (set_cs addIs [Var_elim2])));
val MGIU_srange = store_thm("MGIU_srange", result() RS mp);

(*************** Correctness of a simple unification algorithm ***************)
(*                                                                           *)
(*  fun unify Const(m) Const(n) = if m=n then Nil else Fail                  *)
(*    | unify Const(m) _        = Fail                                       *)
(*    | unify Var(v)   t        = if Var(v)<:t then Fail else (v,t)#Nil      *)
(*    | unify Comb(t,u) Const(n) = Fail                                      *)
(*    | unify Comb(t,u) Var(v)  = if Var(v) <: Comb(t,u) then Fail           *)
(*                                               else (v,Comb(t,u)#Nil       *)
(*    | unify Comb(t,u) Comb(v,w) = let s = unify t v                        *)
(*                                  in if s=Fail then Fail                   *)
(*                                               else unify (u<|s) (w<|s);   *)

(**** Cases for the partial correctness of the algorithm ****)

goalw Unifier.thy unify_defs "MGIUnifier s t u = MGIUnifier s u t";
by (safe_tac (HOL_cs addSEs ([sym]@([spec] RL [mp]))));
qed "Unify_comm";

goal Unifier.thy "MGIUnifier [] (Const n) (Const n)";
by (simp_tac (subst_ss addsimps
              [MGIU_iff,MGU_iff,Unifier_iff,subst_eq_iff,Idem_Nil]) 1);
qed "Unify1";

goal Unifier.thy "~m=n --> (ALL l.~Unifier l (Const m) (Const n))";
by (simp_tac (subst_ss addsimps[Unifier_iff]) 1);
val Unify2 = store_thm("Unify2", result() RS mp);

val [prem] = goalw Unifier.thy [MGIUnifier_def] 
 "~Var(v) <: t ==> MGIUnifier [(v,t)] (Var v) t";
by (fast_tac (HOL_cs addSIs [prem RS MGUnifier_Var,prem RS Var_Idem]) 1);
qed "Unify3";

val [prem] = goal Unifier.thy "Var(v) <: t ==> (ALL l.~Unifier l (Var v) t)";
by (simp_tac (subst_ss addsimps
              [Unifier_iff,prem RS subst_mono RS occs_irrefl2]) 1);
qed "Unify4";

goal Unifier.thy "ALL l.~Unifier l (Const m) (Comb t u)";
by (simp_tac (subst_ss addsimps [Unifier_iff]) 1);
qed "Unify5";

goal Unifier.thy
    "(ALL l.~Unifier l t v) --> (ALL l.~Unifier l (Comb t u) (Comb v w))";
by (simp_tac (subst_ss addsimps [Unifier_iff]) 1);
val Unify6 = store_thm("Unify6", result() RS mp);

goal Unifier.thy "MGIUnifier s t v --> (ALL l.~Unifier l (u <| s) (w <| s)) \
\                                --> (ALL l.~Unifier l (Comb t u) (Comb v w))";
by (simp_tac (subst_ss addsimps [MGIU_iff]) 1);
by (fast_tac (set_cs addIs [Unifier_comp_subst] addSEs [Unifier_Comb]) 1);
val Unify7 = store_thm("Unify7", result() RS mp RS mp);

val [p1,p2,p3] = goal Unifier.thy
     "[| Idem(r); Unifier s (t <| r) (u <| r); \
\     (! q.Unifier q (t <| r) (u <| r) --> s <> q =s= q) |] ==> \
\     Idem(r <> s)";
by (cut_facts_tac [p1,
                   p2 RS (p1 RS Unifier_Idem_subst RS (p3 RS spec RS mp))] 1);
by (REPEAT_SOME (etac rev_mp));
by (simp_tac (subst_ss addsimps [raw_Idem_iff,subst_eq_iff,subst_comp]) 1);
qed "Unify8_lemma1";

val [p1,p2,p3,p4] = goal Unifier.thy
   "[| Unifier q t v; Unifier q u w; (! q.Unifier q t v --> r <> q =s= q); \
\      (! q.Unifier q (u <| r) (w <| r) --> s <> q =s= q) |] ==> \
\   r <> s <> q =s= q";
val pp = p1 RS (p3 RS spec RS mp);
by (cut_facts_tac [pp,
                   p2 RS (pp RS Unifier_comp_subst) RS (p4 RS spec RS mp)] 1);
by (REPEAT_SOME (etac rev_mp));
by (simp_tac (subst_ss addsimps [subst_eq_iff,subst_comp]) 1);
qed "Unify8_lemma2";

goal Unifier.thy  "MGIUnifier r t v -->  MGIUnifier s (u <| r) (w <| r) --> \
\                MGIUnifier (r <> s) (Comb t u) (Comb v w)";
by (simp_tac (subst_ss addsimps [MGIU_iff,subst_comp,comp_assoc]) 1);
by (safe_tac HOL_cs);
by (REPEAT (etac rev_mp 2));
by (simp_tac (subst_ss addsimps 
              [Unifier_iff,MGIU_iff,subst_comp,comp_assoc]) 2);
by (ALLGOALS (fast_tac (set_cs addEs 
                        [Unifier_Comb,Unify8_lemma1,Unify8_lemma2])));
qed "Unify8";


(********************** Termination of the algorithm *************************)
(*                                                                           *)
(*UWFD is a well-founded relation that orders the 2 recursive calls in unify *)
(*                   NB well-foundedness of UWFD isn't proved                *)


goalw Unifier.thy [UWFD_def]  "UWFD t t' (Comb t u) (Comb t' u')";
by (simp_tac subst_ss 1);
by (fast_tac set_cs 1);
qed "UnifyWFD1";

val [prem] = goal Unifier.thy 
     "MGIUnifier s t t' ==> vars_of(u <| s) Un vars_of(u' <| s) <= \
\                           vars_of (Comb t u) Un vars_of (Comb t' u')";
by (subgoal_tac "vars_of(u <| s) Un vars_of(u' <| s) <= \
\                srange(s) Un vars_of(u) Un srange(s) Un vars_of(u')" 1);
by (etac subset_trans 1);
by (ALLGOALS (simp_tac (subst_ss addsimps [Var_intro,subset_iff])));
by (ALLGOALS (fast_tac (set_cs addDs 
                        [Var_intro,prem RS MGIU_srange RS subsetD])));
qed "UWFD2_lemma1";

val [major,minor] = goal Unifier.thy 
     "[| MGIUnifier s t t';  ~ u <| s = u |] ==> \
\     ~ vars_of(u <| s) Un vars_of(u' <| s) =  \
\         (vars_of(t) Un vars_of(u)) Un (vars_of(t') Un vars_of(u'))";
by (cut_facts_tac 
    [major RS (MGIU_iff RS iffD1) RS conjunct1 RS (Idem_iff RS iffD1)] 1);
by (rtac (minor RS subst_not_empty RS exE) 1);
by (rtac (make_elim ((major RS MGIU_sdom) RS subsetD)) 1 THEN assume_tac 1);
by (rtac (disjI2 RS (not_equal_iff RS iffD2)) 1);
by (REPEAT (etac rev_mp 1));
by (asm_simp_tac subst_ss 1);
by (fast_tac (set_cs addIs [Var_elim2]) 1);
qed "UWFD2_lemma2";

val [prem] = goalw Unifier.thy [UWFD_def]  
  "MGIUnifier s t t' ==> UWFD (u <| s) (u' <| s) (Comb t u) (Comb t' u')";
by (cut_facts_tac 
    [prem RS UWFD2_lemma1 RS (subseteq_iff_subset_eq RS iffD1)] 1);
by (imp_excluded_middle_tac "u <| s = u" 1);
by (simp_tac (subst_ss delsimps (ssubset_iff :: utlemmas_rews)
                       addsimps [occs_Comb2]) 1);
by (rtac impI 1 THEN etac subst 1 THEN assume_tac 1);
by (rtac impI 1);
by (rtac (conjI RS (ssubset_iff RS iffD2) RS disjI1) 1);
by (asm_simp_tac (subst_ss delsimps (ssubset_iff :: utlemmas_rews) addsimps [subseteq_iff_subset_eq]) 1);
by (asm_simp_tac subst_ss 1);
by (fast_tac (set_cs addDs [prem RS UWFD2_lemma2]) 1);
qed "UnifyWFD2";
