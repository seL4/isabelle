(*  Title: 	ZF/ex/bin.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Datatype of binary integers
*)

(*Example of a datatype with an infix constructor*)
structure Bin = Datatype_Fun
 (val thy = Univ.thy;
  val rec_specs = 
      [("bin", "univ(0)",
	  [(["Plus", "Minus"],	"i"),
	   (["op $$"],		"[i,i]=>i")])];
  val rec_styp = "i";
  val ext = Some (Syntax.simple_sext [Infixl("$$", "[i,i] => i", 60)]);
  val sintrs = 
	  ["Plus : bin",
	   "Minus : bin",
	   "[| w: bin;  b: bool |] ==> w$$b : bin"];
  val monos = [];
  val type_intrs = datatype_intrs @ [bool_into_univ];
  val type_elims = []);

(*Perform induction on l, then prove the major premise using prems. *)
fun bin_ind_tac a prems i = 
    EVERY [res_inst_tac [("x",a)] Bin.induct i,
	   rename_last_tac a ["1"] (i+3),
	   ares_tac prems i];

