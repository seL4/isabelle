(*  Title: 	ZF/ex/comb.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson
    Copyright   1993  University of Cambridge

Datatype definition of combinators S and K

J. Camilleri and T. F. Melham.
Reasoning with Inductively Defined Relations in the HOL Theorem Prover.
Report 265, University of Cambridge Computer Laboratory, 1992.
*)


(*Example of a datatype with mixfix syntax for some constructors*)
structure Comb = Datatype_Fun
 (val thy = Univ.thy;
  val rec_specs = 
      [("comb", "univ(0)",
	  [(["K","S"],	"i", NoSyn),
	   (["#"],	"[i,i]=>i", Infixl 90)])];
  val rec_styp = "i";
  val sintrs = 
	  ["K : comb",
	   "S : comb",
	   "[| p: comb;  q: comb |] ==> p#q : comb"];
  val monos = [];
  val type_intrs = datatype_intrs;
  val type_elims = []);

val [K_comb,S_comb,Ap_comb] = Comb.intrs;

val Ap_E = Comb.mk_cases Comb.con_defs "p#q : comb";

