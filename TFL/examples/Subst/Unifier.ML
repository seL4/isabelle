(*  Title:      HOL/Subst/unifier.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For Unifier.thy.
Properties of unifiers.
*)

open Unifier;

val unify_defs = [Unifier_def,MoreGeneral_def,MGUnifier_def];

val rews = subst_rews@al_rews@setplus_rews;

(*---------------------------------------------------------------------------
 * Unifiers 
 *---------------------------------------------------------------------------*)

goalw Unifier.thy [Unifier_def] "Unifier s t u = (t <| s = u <| s)";
by (rtac refl 1);
val Unifier_iff = result();

goal Unifier.thy
    "Unifier s (Comb t u) (Comb v w) --> Unifier s t v & Unifier s u w";
by (simp_tac (!simpset addsimps [Unifier_iff]) 1);
val Unifier_Comb  = result() RS mp RS conjE;

goal Unifier.thy
  "~v : vars_of(t) --> ~v : vars_of(u) --> Unifier s t u --> \
\  Unifier ((v,r)#s) t u";
by (simp_tac (!simpset addsimps [Unifier_iff,repl_invariance]) 1);
val Cons_Unifier  = result() RS mp RS mp RS mp;


(*---------------------------------------------------------------------------
 * Most General Unifiers 
 *---------------------------------------------------------------------------*)

goalw Unifier.thy unify_defs "MGUnifier s t u = MGUnifier s u t";
by (safe_tac (HOL_cs addSEs ([sym]@([spec] RL [mp]))));
val mgu_sym = result();


goalw Unifier.thy [MoreGeneral_def]  "r >> s = (EX q. s =s= r <> q)";
by (rtac refl 1);
val MoreGen_iff = result();


goal Unifier.thy  "[] >> s";
by (simp_tac (!simpset addsimps (MoreGen_iff::subst_rews)) 1);
by (fast_tac (set_cs addIs [refl RS subst_refl]) 1);
val MoreGen_Nil = result();


goalw Unifier.thy unify_defs
    "MGUnifier s t u = (ALL r. Unifier r t u = s >> r)";
by (REPEAT (ares_tac [iffI,allI] 1 ORELSE 
            eresolve_tac [conjE,allE,mp,exE,ssubst_subst2] 1));
by (asm_simp_tac (!simpset addsimps [subst_comp]) 1);
by (fast_tac (set_cs addIs [comp_Nil RS sym RS subst_refl]) 1);
val MGU_iff = result();


val [prem] = goal Unifier.thy
     "~ Var(v) <: t ==> MGUnifier [(v,t)] (Var v) t";
by(simp_tac(HOL_ss addsimps([MGU_iff,MoreGen_iff,Unifier_iff]@rews))1);
by (REPEAT_SOME (step_tac set_cs));
by (etac subst 1);
by (etac ssubst_subst2 2);
by (rtac (Cons_trivial RS subst_sym) 1);
by (simp_tac (!simpset addsimps ((prem RS Var_not_occs)::rews)) 1);
val MGUnifier_Var = result();



(*---------------------------------------------------------------------------
 * Idempotence.
 *---------------------------------------------------------------------------*)

goalw Unifier.thy [Idem_def] "Idem([])";
by (simp_tac (!simpset addsimps (refl RS subst_refl)::rews) 1);
qed "Idem_Nil";

goalw Unifier.thy [Idem_def] "Idem(s) = (sdom(s) Int srange(s) = {})";
by (simp_tac (!simpset addsimps [subst_eq_iff,subst_comp,
                                 invariance,dom_range_disjoint])1);
qed "Idem_iff";

val rews = subst_rews@al_rews@setplus_rews;
goal Unifier.thy "~ (Var(v) <: t) --> Idem([(v,t)])";
by (simp_tac (!simpset addsimps (vars_iff_occseq::Idem_iff::srange_iff::rews)
                        setloop (split_tac [expand_if])) 1);
by (fast_tac set_cs 1);
val Var_Idem  = store_thm("Var_Idem", result() RS mp);


val [prem] = goalw Unifier.thy [Idem_def]
"Idem(r) ==>  Unifier s (t<|r) (u<|r) --> Unifier (r <> s) (t <| r) (u <| r)";
by (simp_tac (!simpset addsimps 
              [Unifier_iff,subst_comp,prem RS comp_subst_subst]) 1);
val Unifier_Idem_subst  = store_thm("Unifier_Idem_subst", result() RS mp);

val [p1,p2,p3] = goal Unifier.thy
     "[| Idem(r); Unifier s (t <| r) (u <| r); \
\        (!q. Unifier q (t <| r) (u <| r) --> s <> q =s= q) \
\     |] ==> Idem(r <> s)";

by (cut_facts_tac [p1,
                   p2 RS (p1 RS Unifier_Idem_subst RS (p3 RS spec RS mp))] 1);
by (REPEAT_SOME (etac rev_mp));
by (simp_tac (!simpset addsimps [Idem_def,subst_eq_iff,subst_comp]) 1);
qed "Idem_comp";

