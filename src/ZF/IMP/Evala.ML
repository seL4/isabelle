(*  Title: 	ZF/IMP/Evala.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

structure Evala = Inductive_Fun
 (
  val thy = Evala0.thy;
  val thy_name="Evala";
  val rec_doms = [("evala","aexp * (loc -> nat) * nat")];
  val sintrs = 
      [
	"[| n:nat ; sigma:loc->nat |] ==> <N(n),sigma> -a-> n",
       	"[| x:loc;  sigma:loc->nat |] ==> <X(x),sigma> -a-> sigma`x",
       	"[| <e,sigma> -a-> n; f: nat -> nat |] \
\           ==> <Op1(f,e),sigma> -a-> f`n" ,
       	"[| <e0,sigma> -a-> n0; <e1,sigma>  -a-> n1; \
\           f: (nat * nat) -> nat  |] \
\           ==> <Op2(f,e0,e1),sigma> -a-> f`<n0,n1>"  ];

  val monos = [];
  val con_defs = [];
  val type_intrs = Aexp.intrs@[SigmaI,apply_funtype];
  val type_elims = [SigmaE2]
 );
