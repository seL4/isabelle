(*  Title: 	HOL/IMP/Equiv.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

goal Equiv.thy "!n. (<a,s> -a-> n) = (n = A a s)";
by (aexp.induct_tac "a" 1);                		  (* struct. ind. *)
by (ALLGOALS(simp_tac (HOL_ss addsimps A_simps)));	  (* rewr. Den.   *)
by (TRYALL (fast_tac (set_cs addSIs (evala.intrs@prems)
                             addSEs evala_elim_cases)));
bind_thm("aexp_iff", result() RS spec);

goal Equiv.thy "!w. (<b,s> -b-> w) = (w = B b s)";
by (bexp.induct_tac "b" 1);
by (ALLGOALS(asm_simp_tac (HOL_ss addcongs [conj_cong]
              addsimps (aexp_iff::B_simps@evalb_simps))));
bind_thm("bexp_iff", result() RS spec);

val bexp1 = bexp_iff RS iffD1;
val bexp2 = bexp_iff RS iffD2;

val BfstI = read_instantiate_sg (sign_of Equiv.thy)
              [("P","%x.B ?b x")] (fst_conv RS ssubst);
val BfstD = read_instantiate_sg (sign_of Equiv.thy)
              [("P","%x.B ?b x")] (fst_conv RS subst);

goal Equiv.thy "!!c. <c,s> -c-> t ==> (s,t) : C(c)";

(* start with rule induction *)
be (evalc.mutual_induct RS spec RS spec RS spec RSN (2,rev_mp)) 1;
by (rewrite_tac (Gamma_def::C_simps));
  (* simplification with HOL_ss again too agressive *)
(* skip *)
by (fast_tac comp_cs 1);
(* assign *)
by (asm_full_simp_tac (prod_ss addsimps [aexp_iff]) 1);
(* comp *)
by (fast_tac comp_cs 1);
(* if *)
by(fast_tac (set_cs addSIs [BfstI] addSDs [BfstD,bexp1]) 1);
by(fast_tac (set_cs addSIs [BfstI] addSDs [BfstD,bexp1]) 1);
(* while *)
by (rtac (rewrite_rule [Gamma_def] (Gamma_mono RS lfp_Tarski RS ssubst)) 1);
by (fast_tac (comp_cs addSIs [bexp1,BfstI] addSDs [BfstD,bexp1]) 1);
by (rtac (rewrite_rule [Gamma_def] (Gamma_mono RS lfp_Tarski RS ssubst)) 1);
by (fast_tac (comp_cs addSIs [bexp1,BfstI] addSDs [BfstD,bexp1]) 1);

qed "com1";


val com_ss = prod_ss addsimps (aexp_iff::bexp_iff::evalc.intrs);

goal Equiv.thy "!io:C(c). <c,fst(io)> -c-> snd(io)";
by (com.induct_tac "c" 1);
by (rewrite_tac C_simps);
by (safe_tac comp_cs);
by (ALLGOALS (asm_full_simp_tac com_ss));

(* comp *)
by (REPEAT (EVERY [(dtac bspec 1),(atac 1)]));
by (asm_full_simp_tac com_ss 1);

(* while *)
by (etac (Gamma_mono RSN (2,induct)) 1);
by (rewrite_goals_tac [Gamma_def]);  
by (safe_tac comp_cs);
by (EVERY1 [dtac bspec, atac]);
by (ALLGOALS (asm_full_simp_tac com_ss));

qed "com2";


(**** Proof of Equivalence ****)

val com_iff_cs = set_cs addEs [com2 RS bspec] addDs [com1];

goal Equiv.thy "C(c) = {io . <c,fst(io)> -c-> snd(io)}";
by (rtac equalityI 1);
(* => *)
by (fast_tac com_iff_cs 1);
(* <= *)
by (REPEAT (step_tac com_iff_cs 1));
by (asm_full_simp_tac (prod_ss addsimps [surjective_pairing RS sym])1);
qed "com_equivalence";
