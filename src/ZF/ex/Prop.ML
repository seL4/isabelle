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
  val rec_specs = 
      [("prop", "univ(0)",
	  [(["Fls"],	"i"),
	   (["Var"],	"i=>i"),
	   (["op =>"],	"[i,i]=>i")])];
  val rec_styp = "i";
  val ext = Some (Syntax.simple_sext
		    [Mixfix("#_", "i => i", "Var", [100], 100),
		     Infixr("=>", "[i,i] => i", 90)]);
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
