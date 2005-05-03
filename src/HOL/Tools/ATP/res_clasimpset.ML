(*  ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

signature RES_CLASIMP =
  sig
     val write_out_clasimp :string -> (ResClause.clause * Thm.thm) Array.array * int
  end;

structure ResClasimp : RES_CLASIMP =
struct

fun has_name th = not((Thm.name_of_thm th)= "")

fun has_name_pair (a,b) = not_equal a "";

fun stick []  = []
|   stick (x::xs)  = x@(stick xs )

(* changed, now it also finds out the name of the theorem. *)
(* convert a theorem into CNF and then into Clause.clause format. *)
fun clausify_axiom_pairs thm =
    let val isa_clauses = ResAxioms.cnf_axiom thm (*"isa_clauses" are already "standard"ed. *)
        val isa_clauses' = ResAxioms.rm_Eps [] isa_clauses
        val thm_name = Thm.name_of_thm thm
	val clauses_n = length isa_clauses
	fun make_axiom_clauses _ [] []= []
	  | make_axiom_clauses i (cls::clss) (cls'::clss')= ((ResClause.make_axiom_clause cls (thm_name,i)),cls') :: make_axiom_clauses (i+1) clss clss'
    in
	make_axiom_clauses 0 isa_clauses' isa_clauses		
    end;


fun clausify_rules_pairs [] err_list = ([],err_list)
  | clausify_rules_pairs (thm::thms) err_list =
    let val (ts,es) = clausify_rules_pairs thms err_list
    in
	((clausify_axiom_pairs thm)::ts,es) handle  _ => (ts,(thm::es))
    end;

fun write_out_clasimp filename = let
					val claset_rules = ResAxioms.claset_rules_of_thy (the_context());
					val named_claset = List.filter has_name claset_rules;
					val claset_cls_thms = #1( clausify_rules_pairs named_claset []);

					val simpset_rules = ResAxioms.simpset_rules_of_thy (the_context());
					val named_simpset = map #2(List.filter has_name_pair simpset_rules);
					val simpset_cls_thms = #1 (clausify_rules_pairs named_simpset []);

					val cls_thms = (claset_cls_thms@simpset_cls_thms);
					val cls_thms_list = stick cls_thms;

                                        (*********************************************************)
                                  	(* create array and put clausename, number pairs into it *)
                                   	(*********************************************************)
					val num_of_clauses =  0;
                                     	val clause_arr = Array.fromList cls_thms_list;
              
                                   	val  num_of_clauses= (List.length cls_thms_list);

                                        (*************************************************)
					(* Write out clauses as tptp strings to filename *)
 					(*************************************************)
                                        val clauses = map #1(cls_thms_list);
          				val cls_tptp_strs = map ResClause.tptp_clause clauses;
                                        (* list of lists of tptp string clauses *)
                                        val stick_clasrls =   stick cls_tptp_strs;
    					val out = TextIO.openOut filename;
                                    	val _=   ResLib.writeln_strs out stick_clasrls;
                                    	val _= TextIO.flushOut out;
					val _= TextIO.closeOut out
                     		  in
					(clause_arr, num_of_clauses)
				  end;


end;
