(*  Title: 	ZF/ex/enum
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Example of a BIG enumeration type

Can go up to at least 100 constructors, but it takes nearly 7 minutes...
*)


(*An enumeration type with 60 contructors!  -- takes about 150 seconds!*)
fun mk_ids a 0 = []
  | mk_ids a n = a :: mk_ids (bump_string a) (n-1);

val consts = mk_ids "con1" 60;

structure Enum = Datatype_Fun
 (val thy = Univ.thy;
  val rec_specs = 
      [("enum", "univ(0)",
	  [(consts, "i", NoSyn)])];
  val rec_styp = "i";
  val sintrs = map (fn const => const ^ " : enum") consts;
  val monos = [];
  val type_intrs = datatype_intrs
  val type_elims = []);

goal Enum.thy "con59 ~= con60";
by (simp_tac (ZF_ss addsimps Enum.free_iffs) 1);
result();

