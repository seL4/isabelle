(*  Title: 	ZF/IMP/Evalb.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

structure Evalb = Inductive_Fun
 (
  val thy = Evalb0.thy;
  val thy_name = "Evalb"
  val rec_doms = [("evalb","bexp * (loc -> nat) * bool")];
  val sintrs = 
      [
	"[| sigma:loc -> nat |] ==> <true,sigma> -b-> 1",
       	"[| sigma:loc -> nat |] ==> <false,sigma> -b-> 0",
       	"[| <a0,sigma> -a-> n0; <a1,sigma> -a-> n1; f: (nat*nat)->bool |] \
\	    ==> <ROp(f,a0,a1),sigma> -b-> f`<n0,n1> ",
       	"[| <b,sigma> -b-> w |] \
\	    ==> <noti(b),sigma> -b-> not(w)", 
       	"[| <b0,sigma> -b-> w0; <b1,sigma> -b-> w1 |] \
\	    ==> <b0 andi b1,sigma> -b-> (w0 and w1)",
       	"[| <b0,sigma> -b-> w0; <b1,sigma> -b-> w1 |] \
\	    ==> <b0 ori b1,sigma> -b-> (w0 or w1)"
      ];

  val monos = [];
  val con_defs = [];
  val type_intrs = Bexp.intrs@[apply_funtype,and_type,or_type,
		   bool_1I,bool_0I,not_type];
  val type_elims = [make_elim(Evala.dom_subset RS subsetD) ];
 );
