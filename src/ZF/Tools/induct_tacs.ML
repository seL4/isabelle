(*  Title:      HOL/Tools/induct_tacs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Induction and exhaustion tactics for Isabelle/ZF
*)


signature DATATYPE_TACTICS =
sig
  val induct_tac : string -> int -> tactic
  val exhaust_tac : string -> int -> tactic
end;


structure DatatypeTactics : DATATYPE_TACTICS =
struct

fun datatype_info_sg sign name =
  (case Symtab.lookup (DatatypesData.get_sg sign, name) of
    Some info => info
  | None => error ("Unknown datatype " ^ quote name));


(*Given a variable, find the inductive set associated it in the assumptions*)
fun find_tname var Bi =
  let fun mk_pair (Const("op :",_) $ Free (v,_) $ A) = 
             (v, #1 (dest_Const (head_of A)))
	| mk_pair _ = raise Match
      val pairs = mapfilter (try (mk_pair o FOLogic.dest_Trueprop))
	  (#2 (strip_context Bi))
  in case assoc (pairs, var) of
       None => error ("Cannot determine datatype of " ^ quote var)
     | Some t => t
  end;

(** generic exhaustion and induction tactic for datatypes 
    Differences from HOL: 
      (1) no checking if the induction var occurs in premises, since it always
          appears in one of them, and it's hard to check for other occurrences
      (2) exhaustion works for VARIABLES in the premises, not general terms
**)

fun exhaust_induct_tac exh var i state =
  let
    val (_, _, Bi, _) = dest_state (state, i)
    val {sign, ...} = rep_thm state
    val tn = find_tname var Bi
    val rule = 
	if exh then #exhaustion (datatype_info_sg sign tn)
	       else #induct  (datatype_info_sg sign tn)
    val (Const("op :",_) $ Var(ixn,_) $ _) = 
	FOLogic.dest_Trueprop (hd (prems_of rule))
    val ind_vname = Syntax.string_of_vname ixn
    val vname' = (*delete leading question mark*)
	String.substring (ind_vname, 1, size ind_vname-1)
  in
    eres_inst_tac [(vname',var)] rule i state
  end;

val exhaust_tac = exhaust_induct_tac true;
val induct_tac = exhaust_induct_tac false;

end;


open DatatypeTactics;
