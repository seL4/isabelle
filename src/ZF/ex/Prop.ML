(*  Title: 	ZF/ex/prop.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson
    Copyright   1993  University of Cambridge

Datatype definition of propositional logic formulae and inductive definition
of the propositional tautologies.
*)

(*Example of a datatype with mixfix syntax for some constructors*)
structure Prop = Datatype_Fun
 (val thy = Univ.thy;
  val thy_name = "Prop";
  val rec_specs = 
      [("prop", "univ(0)",
	  [(["Fls"],	"i",NoSyn),
	   (["Var"],	"i=>i", Mixfix ("#_", [100], 100)),
	   (["=>"],	"[i,i]=>i", Infixr 90)])];
  val rec_styp = "i";
  val sintrs = 
	  ["Fls : prop",
	   "n: nat ==> #n : prop",
	   "[| p: prop;  q: prop |] ==> p=>q : prop"];
  val monos = [];
  val type_intrs = datatype_intrs;
  val type_elims = []);

val [FlsI,VarI,ImpI] = Prop.intrs;


(** Type-checking rules **)

val ImpE = Prop.mk_cases Prop.con_defs "p=>q : prop";

writeln"Reached end of file.";
