(*  Title: 	ZF/IMP/Evalc.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

structure Evalc = Inductive_Fun    
 (
  val thy = Evalc0.thy;
  val thy_name = "Evalc"
  val rec_doms = [("evalc","com * (loc -> nat) * (loc -> nat)")];
  val sintrs =
      [
	"[| sigma: loc -> nat |] ==> <skip,sigma> -c-> sigma",
       	"[| m: nat; x: loc; a:aexp; <a,sigma> -a-> m |] ==> \
\          <X(x) := a,sigma> -c-> sigma[m/x]" , 
       "[| <c0,sigma> -c-> sigma2; <c1,sigma2> -c-> sigma1 |] ==> \
\          <c0 ; c1, sigma> -c-> sigma1",
       "[| b:bexp; c1:com; sigma:loc->nat;\
\          <b,sigma> -b-> 1; <c0,sigma> -c-> sigma1 |] ==> \
\       <ifc b then c0 else c1, sigma> -c-> sigma1 ",
       "[| b:bexp; c0:com; sigma:loc->nat;\
\          <b,sigma> -b-> 0; <c1,sigma> -c-> sigma1 |] ==> \
\       <ifc b then c0 else c1, sigma> -c-> sigma1 ",
       "[| b:bexp; c:com; <b, sigma> -b-> 0 |] ==> \
\          <while b do c,sigma> -c-> sigma ",
       "[| b:bexp; c:com; <b,sigma> -b-> 1; <c,sigma> -c-> sigma2; \
\          <while b do c, sigma2> -c-> sigma1 |] ==> \
\          <while b do c, sigma> -c-> sigma1 "];

  val monos = [];
  val con_defs = [assign_def];
  val type_intrs = Bexp.intrs@Com.intrs@[if_type,lam_type,apply_type];
  val type_elims = [make_elim(Evala.dom_subset RS subsetD),
		    make_elim(Evalb.dom_subset RS subsetD) ]);
