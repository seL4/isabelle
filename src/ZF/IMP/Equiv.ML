(*  Title:      ZF/IMP/Equiv.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

Goal "[| a: aexp; sigma: loc -> nat |] ==> \
\        <a,sigma> -a-> n <-> A(a,sigma) = n";
by (res_inst_tac [("x","n")] spec 1);                       (* quantify n *)
by (etac aexp.induct 1);
by (ALLGOALS (fast_tac (claset() addSIs evala.intrs
                                 addSEs aexp_elim_cases 
                                 addss (simpset()))));
qed "aexp_iff";


val aexp1 = aexp_iff RS iffD1;
val aexp2 = aexp_iff RS iffD2;


val bexp_elim_cases = 
   [
    evalb.mk_cases "<true,sigma> -b-> x",
    evalb.mk_cases "<false,sigma> -b-> x",
    evalb.mk_cases "<ROp(f,a0,a1),sigma> -b-> x",
    evalb.mk_cases "<noti(b),sigma> -b-> x",
    evalb.mk_cases "<b0 andi b1,sigma> -b-> x",
    evalb.mk_cases "<b0 ori b1,sigma> -b-> x"
   ];


Goal "[| b: bexp; sigma: loc -> nat |] ==> \
\        <b,sigma> -b-> w <-> B(b,sigma) = w";
by (res_inst_tac [("x","w")] spec 1);
by (etac bexp.induct 1);
by (ALLGOALS (fast_tac (claset() addSIs evalb.intrs
                                 addSEs bexp_elim_cases 
                                 addss (simpset() addsimps [aexp_iff]))));
qed "bexp_iff";

val bexp1 = bexp_iff RS iffD1;
val bexp2 = bexp_iff RS iffD2;


Goal "<c,sigma> -c-> sigma' ==> <sigma,sigma'> : C(c)";
by (etac evalc.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [bexp1])));
(* skip *)
by (Fast_tac 1);
(* assign *)
by (asm_full_simp_tac (simpset() addsimps 
		       [aexp1, update_type] @ op_type_intrs) 1);
(* comp *)
by (Fast_tac 1);
(* while *)
by (etac (Gamma_bnd_mono RS lfp_unfold RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [Gamma_def, bexp1]) 1);
by (blast_tac (claset() addSIs [bexp1]@evalb_type_intrs) 1);
(* recursive case of while *)
by (etac (Gamma_bnd_mono RS lfp_unfold RS ssubst) 1);
by (asm_full_simp_tac (simpset() addsimps [Gamma_def, bexp1]) 1);
by (blast_tac (claset() addSIs [bexp1]@evalb_type_intrs) 1);
val com1 = result();


AddSIs [aexp2,bexp2,B_type,A_type];
AddIs  evalc.intrs;


Goal "c : com ==> ALL x:C(c). <c,fst(x)> -c-> snd(x)";
by (etac com.induct 1);
(* comp *)
by (Force_tac 3); 
(* assign *)
by (Force_tac 2); 
(* skip *)
by (Force_tac 1); 
(* while *)
by Safe_tac;
by (ALLGOALS Asm_full_simp_tac);
by (EVERY1 [ftac Gamma_bnd_mono , etac induct, atac]);
by (rewtac Gamma_def);  
by Safe_tac;
by (EVERY1 [dtac bspec, atac]);
by (ALLGOALS Asm_full_simp_tac);
(* while, if *)
by (ALLGOALS Blast_tac);
val com2 = result();


(**** Proof of Equivalence ****)

Goal "ALL c:com. C(c) = {io:(loc->nat)*(loc->nat). <c,fst(io)> -c-> snd(io)}";
by (fast_tac (claset() addIs [C_subset RS subsetD]
		       addEs [com2 RS bspec]
		       addDs [com1]
		       addss (simpset())) 1);
val com_equivalence = result();
