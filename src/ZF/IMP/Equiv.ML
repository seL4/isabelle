(*  Title: 	ZF/IMP/Equiv.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

val prems = goal Equiv.thy "[| a: aexp; sigma: loc -> nat |] ==> \
\ <a,sigma> -a-> n <-> n = A(a,sigma) ";
by (res_inst_tac [("x","n")] spec 1);                       (* quantify n *)
by (res_inst_tac [("x","a")] aexp.induct 1);                (* struct. ind. *)
by (resolve_tac prems 1);                                   (* type prem. *)
by (safe_tac ZF_cs);                        		    (* allI,-->,<-- *)
by (rewrite_goals_tac A_rewrite_rules);			    (* rewr. Den.   *)
by (TRYALL (fast_tac (ZF_cs addSIs (evala.intrs@prems)) )); (* <== *)
by (TRYALL (fast_tac (ZF_cs addSEs aexp_elim_cases)));      (* ==> *)
val aexp_iff = result();


val aexp_rew_rules_cs = ZF_cs addIs  op_type_intrs@[aexp_iff RS iffD1 RS sym];

val aexp1 = prove_goal Equiv.thy		    (* elim the prems *)
        "<a,sigma> -a-> n ==> A(a,sigma) = n"	    (* destruction rule *)
     (fn prems => [(fast_tac (aexp_rew_rules_cs addSIs prems) 1)]);

val aexp2 = aexp_iff RS iffD2;


val bexp_elim_cases = 
   [
    evalb.mk_cases bexp.con_defs "<true,sigma> -b-> x",
    evalb.mk_cases bexp.con_defs "<false,sigma> -b-> x",
    evalb.mk_cases bexp.con_defs "<ROp(f,a0,a1),sigma> -b-> x",
    evalb.mk_cases bexp.con_defs "<noti(b),sigma> -b-> x",
    evalb.mk_cases bexp.con_defs "<b0 andi b1,sigma> -b-> x",
    evalb.mk_cases bexp.con_defs "<b0 ori b1,sigma> -b-> x"
   ];


val prems = goal Equiv.thy "[| b: bexp; sigma: loc -> nat |] ==> \
\ <b,sigma> -b-> w <-> w = B(b,sigma) ";

by (res_inst_tac [("x","w")] spec 1);			(* quantify w *)
by (res_inst_tac [("x","b")] bexp.induct 1);		(* struct. ind. *)
by (resolve_tac prems 1);				(* type prem. *)
by (safe_tac ZF_cs);                                  	(* allI,-->,<-- *)
by (rewrite_goals_tac B_rewrite_rules);			(* rewr. Den.   *)
by (TRYALL (fast_tac 					(* <== *)
            (ZF_cs addSIs (evalb.intrs@prems@[aexp2])) ));
by (TRYALL (fast_tac ((ZF_cs addSDs [aexp1]) addSEs bexp_elim_cases)));
								(* ==> *)
val bexp_iff = result();


val bexp_rew_rules_cs = ZF_cs addIs  op_type_intrs@[bexp_iff RS iffD1 RS sym];

val bexp1 = prove_goal Equiv.thy
        "<b,sigma> -b-> w ==> B(b,sigma) = w"
     (fn prems => [(fast_tac (bexp_rew_rules_cs addSIs prems) 1)]);

val bexp2 = prove_goal Equiv.thy 
    "[| B(b,sigma) = w; b : bexp; sigma : loc -> nat |] ==> <b,sigma> -b-> w"
    (fn prems => 
    [(cut_facts_tac prems 1), 
     (fast_tac (ZF_cs addIs ([bexp_iff RS iffD2])) 1)]);



val prems = goal Equiv.thy
	"<c,sigma> -c-> sigma' ==> <sigma,sigma'> : C(c)";
by (cut_facts_tac prems 1);

(* start with rule induction *)
be (evalc.mutual_induct RS spec RS spec RS spec RSN (2,rev_mp)) 1;

by (rewrite_tac (Gamma_def::C_rewrite_rules));
(* skip *)
by (fast_tac comp_cs 1);

(* assign *)
by (asm_full_simp_tac (ZF_ss addsimps [aexp1,assign_type] @
                                      op_type_intrs) 1);
(* comp *)
by (fast_tac comp_cs 1);

(* if *)
by (fast_tac (ZF_cs addSIs [bexp1] addIs  [(fst_conv RS ssubst)]) 1);
by (fast_tac (ZF_cs addSIs [bexp1] addIs  [(fst_conv RS ssubst)]) 1);

(* while *)
by (etac (rewrite_rule [Gamma_def] (Gamma_bnd_mono RS lfp_Tarski RS ssubst)) 1);
by (fast_tac (comp_cs addSIs [bexp1,idI]@evalb_type_intrs
                      addIs  [(fst_conv RS ssubst)]) 1);

by (etac (rewrite_rule [Gamma_def] (Gamma_bnd_mono RS lfp_Tarski RS ssubst)) 1);
by (fast_tac (comp_cs addSIs [bexp1,compI]@evalb_type_intrs
                      addIs  [(fst_conv RS ssubst)]) 1);

val com1 = result();


val com_cs = ZF_cs addSIs [aexp2,bexp2,B_type,A_type]
                   addIs evalc.intrs
                   addSEs [idE,compE]
                   addEs [C_type,C_type_fst];

val [prem] = goal Equiv.thy
    "c : com ==> ALL x. x:C(c) --> <c,fst(x)> -c-> snd(x)";
br (prem RS com.induct) 1;
by (rewrite_tac C_rewrite_rules);
by (safe_tac com_cs);
by (ALLGOALS (asm_full_simp_tac ZF_ss));

(* skip *)
by (fast_tac com_cs 1);

(* assign *)
by (fast_tac com_cs 1);

(* comp *)
by (REPEAT (EVERY [(etac allE 1),(etac impE 1),(atac 1)]));
by (asm_full_simp_tac ZF_ss 1);
by (fast_tac com_cs 1);

(* while *)
by (EVERY [(forward_tac [Gamma_bnd_mono] 1),(etac induct 1),(atac 1)]);
by (rewrite_goals_tac [Gamma_def]);  
by (safe_tac com_cs);
by (EVERY [(etac allE 1),(etac impE 1),(atac 1)]);
by (ALLGOALS (asm_full_simp_tac ZF_ss));

(* while, if *)
by (ALLGOALS (fast_tac com_cs));
val com2 = result();


(**** Proof of Equivalence ****)

val com_iff_cs = ZF_cs addIs [C_subset RS subsetD]
                       addEs [com2 RS spec RS impE]
                       addDs [com1];

goal Equiv.thy
    "ALL c:com. C(c) = {io:(loc->nat)*(loc->nat). <c,fst(io)> -c-> snd(io)}";
by (rtac ballI 1);
by (rtac equalityI 1);
(* => *)
by (fast_tac com_iff_cs 1);
(* <= *)
by (REPEAT (step_tac com_iff_cs 1));
by (asm_full_simp_tac ZF_ss 1);
val com_equivalence = result();
