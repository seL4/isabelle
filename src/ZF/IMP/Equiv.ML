(*  Title:      ZF/IMP/Equiv.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

val prems = goal Equiv.thy "[| a: aexp; sigma: loc -> nat |] ==> \
\ <a,sigma> -a-> n <-> A(a,sigma) = n";
by (res_inst_tac [("x","n")] spec 1);                       (* quantify n *)
by (res_inst_tac [("x","a")] aexp.induct 1);                (* struct. ind. *)
by (resolve_tac prems 1);                                   (* type prem. *)
by (rewrite_goals_tac A_rewrite_rules);                     (* rewr. Den.   *)
by (TRYALL (fast_tac (claset() addSIs (evala.intrs@prems)
                              addSEs aexp_elim_cases)));
qed "aexp_iff";


val aexp1 = prove_goal Equiv.thy
        "[| <a,sigma> -a-> n; a: aexp; sigma: loc -> nat |] \
        \ ==> A(a,sigma) = n"       (* destruction rule *)
     (fn prems => [(fast_tac (claset() addSIs ((aexp_iff RS iffD1)::prems)) 1)]);
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
\ <b,sigma> -b-> w <-> B(b,sigma) = w";
by (res_inst_tac [("x","w")] spec 1);                   (* quantify w *)
by (res_inst_tac [("x","b")] bexp.induct 1);            (* struct. ind. *)
by (resolve_tac prems 1);                               (* type prem. *)
by (rewrite_goals_tac B_rewrite_rules);                 (* rewr. Den.   *)
by (TRYALL (fast_tac (claset() addSIs (evalb.intrs@prems@[aexp2])
                            addSDs [aexp1] addSEs bexp_elim_cases)));
qed "bexp_iff";

val bexp1 = prove_goal Equiv.thy
        "[| <b,sigma> -b-> w; b: bexp; sigma: loc -> nat |]\
        \ ==> B(b,sigma) = w"
     (fn prems => [(fast_tac (claset() addSIs ((bexp_iff RS iffD1)::prems)) 1)]);
val bexp2 = bexp_iff RS iffD2;

goal Equiv.thy "!!c. <c,sigma> -c-> sigma' ==> <sigma,sigma'> : C(c)";

(* start with rule induction *)
by (etac evalc.induct 1);

by (rewrite_tac (Gamma_def::C_rewrite_rules));
(* skip *)
by (Fast_tac 1);

(* assign *)
by (asm_full_simp_tac (simpset() addsimps [aexp1,assign_type] @ op_type_intrs) 1);

(* comp *)
by (Fast_tac 1);

(* if *)
by (asm_simp_tac (simpset() addsimps [bexp1]) 1);
by (asm_simp_tac (simpset() addsimps [bexp1]) 1);

(* while *)
by (etac (rewrite_rule [Gamma_def]
          (Gamma_bnd_mono RS lfp_Tarski RS ssubst)) 1);
by (asm_simp_tac (simpset() addsimps [bexp1]) 1);
by (fast_tac (claset() addSIs [bexp1,idI]@evalb_type_intrs) 1);

by (etac (rewrite_rule [Gamma_def]
          (Gamma_bnd_mono RS lfp_Tarski RS ssubst)) 1);
by (asm_simp_tac (simpset() addsimps [bexp1]) 1);
by (fast_tac (claset() addSIs [bexp1,compI]@evalb_type_intrs) 1);

val com1 = result();


AddSIs [aexp2,bexp2,B_type,A_type];
AddIs evalc.intrs;
AddEs [C_type,C_type_fst];

val [prem] = goal Equiv.thy
    "c : com ==> ALL x:C(c). <c,fst(x)> -c-> snd(x)";
by (rtac (prem RS com.induct) 1);
by (rewrite_tac C_rewrite_rules);
by (safe_tac (claset()));
by (ALLGOALS Asm_full_simp_tac);

(* skip *)
by (Fast_tac 1);

(* assign *)
by (Fast_tac 1);

(* comp *)
by (REPEAT (EVERY [(dtac bspec 1),(atac 1)]));
by (Asm_full_simp_tac 1);
by (Fast_tac 1);

(* while *)
by (EVERY1 [forward_tac [Gamma_bnd_mono], etac induct, atac]);
by (rewtac Gamma_def);  
by (safe_tac (claset()));
by (EVERY1 [dtac bspec, atac]);
by (ALLGOALS Asm_full_simp_tac);

(* while, if *)
by (ALLGOALS Fast_tac);
val com2 = result();


(**** Proof of Equivalence ****)

goal Equiv.thy
    "ALL c:com. C(c) = {io:(loc->nat)*(loc->nat). <c,fst(io)> -c-> snd(io)}";
by (fast_tac (claset() addIs [C_subset RS subsetD]
	              addEs [com2 RS bspec]
		      addDs [com1]
		      addss (simpset())) 1);
val com_equivalence = result();
