(*  Title:      HOL/Subst/Unifier.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For Unifier.thy.
Properties of unifiers.
*)

open Unifier;

val unify_defs = [Unifier_def, MoreGeneral_def, MGUnifier_def];

(*---------------------------------------------------------------------------
 * Unifiers 
 *---------------------------------------------------------------------------*)

goal Unifier.thy
    "Unifier s (Comb t u) (Comb v w) = (Unifier s t v & Unifier s u w)";
by (simp_tac (!simpset addsimps [Unifier_def]) 1);
qed "Unifier_Comb";

AddIffs [Unifier_Comb];

goal Unifier.thy
  "!!v. [| v ~: vars_of t; v ~: vars_of u; Unifier s t u |] ==> \
\       Unifier ((v,r)#s) t u";
by (asm_full_simp_tac (!simpset addsimps [Unifier_def, repl_invariance]) 1);
qed "Cons_Unifier";


(*---------------------------------------------------------------------------
 * Most General Unifiers 
 *---------------------------------------------------------------------------*)

goalw Unifier.thy unify_defs "MGUnifier s t u = MGUnifier s u t";
by (blast_tac (!claset addIs [sym]) 1);
qed "mgu_sym";


goal Unifier.thy  "[] >> s";
by (simp_tac (!simpset addsimps [MoreGeneral_def]) 1);
by (Blast_tac 1);
qed "MoreGen_Nil";

AddIffs [MoreGen_Nil];

goalw Unifier.thy unify_defs
    "MGUnifier s t u = (ALL r. Unifier r t u = s >> r)";
by (auto_tac (!claset addIs [ssubst_subst2, subst_comp_Nil], !simpset));
qed "MGU_iff";


goal Unifier.thy
     "!!v. ~ Var v <: t ==> MGUnifier [(v,t)] (Var v) t";
by (simp_tac(!simpset addsimps [MGU_iff, Unifier_def, MoreGeneral_def]
	              delsimps [subst_Var]) 1);
by (Step_tac 1);
br exI 1;
by (etac subst 1 THEN rtac (Cons_trivial RS subst_sym) 1);
by (etac ssubst_subst2 1);
by (asm_simp_tac (!simpset addsimps [Var_not_occs]) 1);
qed "MGUnifier_Var";

AddSIs [MGUnifier_Var];


(*---------------------------------------------------------------------------
 * Idempotence.
 *---------------------------------------------------------------------------*)

goalw Unifier.thy [Idem_def] "Idem([])";
by (Simp_tac 1);
qed "Idem_Nil";

AddIffs [Idem_Nil];

goalw Unifier.thy [Idem_def] "Idem(s) = (sdom(s) Int srange(s) = {})";
by (simp_tac (!simpset addsimps [subst_eq_iff, invariance, 
				 dom_range_disjoint]) 1);
qed "Idem_iff";

goal Unifier.thy "~ (Var(v) <: t) --> Idem([(v,t)])";
by (simp_tac (!simpset addsimps [vars_iff_occseq, Idem_iff, srange_iff, 
				 empty_iff_all_not]
                       setloop (split_tac [expand_if])) 1);
by (Blast_tac 1);
qed_spec_mp "Var_Idem";

AddSIs [Var_Idem];

goalw Unifier.thy [Idem_def]
  "!!r. [| Idem(r); Unifier s (t<|r) (u<|r) |]       \
\       ==> Unifier (r <> s) (t <| r) (u <| r)";
by (asm_full_simp_tac (!simpset addsimps [Unifier_def, comp_subst_subst]) 1);
qed "Unifier_Idem_subst";

val [idemr,unifier,minor] = goal Unifier.thy
     "[| Idem(r);  Unifier s (t <| r) (u <| r); \
\        !!q. Unifier q (t <| r) (u <| r) ==> s <> q =$= q \
\     |] ==> Idem(r <> s)";
by (cut_facts_tac [idemr,
                   unifier RS (idemr RS Unifier_Idem_subst RS minor)] 1);
by (asm_full_simp_tac (!simpset addsimps [Idem_def, subst_eq_iff]) 1);
qed "Idem_comp";
