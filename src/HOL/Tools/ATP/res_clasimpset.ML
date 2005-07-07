
(*  ID:         $Id$

    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)


structure ReduceAxiomsN =
(* Author: Jia Meng, Cambridge University Computer Laboratory
   Remove irrelevant axioms used for a proof of a goal, with with iteration control*)

struct

fun add_term_consts_rm ncs (Const(c, _)) cs = 
    if (c mem ncs) then cs else (c ins_string cs)
  | add_term_consts_rm ncs (t $ u) cs = add_term_consts_rm ncs t (add_term_consts_rm ncs u cs)
  | add_term_consts_rm ncs (Abs(_,_,t)) cs = add_term_consts_rm ncs t cs
  | add_term_consts_rm ncs _ cs = cs;


fun term_consts_rm ncs t = add_term_consts_rm ncs t [];


fun thm_consts_rm ncs thm = term_consts_rm ncs (prop_of thm);


fun consts_of_thm (n,thm) = thm_consts_rm ["Trueprop","==>","all","Ex","op &", "op |", "Not", "All", "op -->", "op =", "==", "True", "False"] thm;




fun consts_of_term term = term_consts_rm ["Trueprop","==>","all","Ex","op &", "op |", "Not", "All", "op -->", "op =", "==", "True", "False"] term;

fun make_pairs [] _ = []
  | make_pairs (x::xs) y = (x,y)::(make_pairs xs y);



fun const_thm_list_aux [] cthms = cthms
  | const_thm_list_aux (thm::thms) cthms =
    let val consts = consts_of_thm thm
	val cthms' = make_pairs consts thm 
    in
	const_thm_list_aux thms (cthms' @ cthms)
    end;


fun const_thm_list thms = const_thm_list_aux thms [];

fun make_thm_table thms  = 
    let val consts_thms = const_thm_list thms
    in
	Symtab.make_multi consts_thms
    end;


fun consts_in_goal goal = consts_of_term goal;

fun axioms_having_consts_aux [] tab thms = thms
  | axioms_having_consts_aux (c::cs) tab thms =
    let val thms1 = Symtab.lookup(tab,c)
	val thms2 = 
	    case thms1 of (SOME x) => x
			| NONE => []
    in
	axioms_having_consts_aux cs tab (thms2 union thms)
    end;


fun axioms_having_consts cs tab = axioms_having_consts_aux cs tab [];


fun relevant_axioms goal thmTab n =  
    let val consts = consts_in_goal goal
	fun relevant_axioms_aux1 cs k =
	    let val thms1 = axioms_having_consts cs thmTab
		val cs1 = ResLib.flat_noDup (map consts_of_thm thms1)
	    in
		if ((cs1 subset cs) orelse (n <= k)) then (k,thms1) 
		else (relevant_axioms_aux1 (cs1 union cs) (k+1))
	    end

	fun relevant_axioms_aux2 cs k =
	    let val thms1 = axioms_having_consts cs thmTab
		val cs1 = ResLib.flat_noDup (map consts_of_thm thms1)
	    in
		if (cs1 subset cs)  then (k,thms1) 
		else (relevant_axioms_aux2 (cs1 union cs) (k+1))
	    end

    in
	if n <= 0 then (relevant_axioms_aux2 consts 1) else (relevant_axioms_aux1 consts 1)
    end;



fun relevant_filter n goal thms = #2 (relevant_axioms goal (make_thm_table thms) n);


(* find the thms from thy that contain relevant constants, n is the iteration number *)
fun find_axioms_n thy goal n =
    let val clasetR = ResAxioms.claset_rules_of_thy thy
	val simpsetR = ResAxioms.simpset_rules_of_thy thy	  
	val table = make_thm_table (clasetR @ simpsetR)	
    in
	relevant_axioms goal table n
    end;


fun find_axioms_n_c thy goal n =
    let val current_thms = PureThy.thms_of thy
	val table = make_thm_table current_thms
    in
	relevant_axioms goal table n

    end;

end;


signature RES_CLASIMP = 
  sig
     val write_out_clasimp : string -> theory -> term -> 
                             (ResClause.clause * thm) Array.array * int
val write_out_clasimp_small :string -> theory -> (ResClause.clause * thm) Array.array * int
  end;

structure ResClasimp : RES_CLASIMP =
struct

fun has_name th = ((Thm.name_of_thm th)  <>  "")

fun has_name_pair (a,b) = (a <> "");


(* changed, now it also finds out the name of the theorem. *)
(* convert a theorem into CNF and then into Clause.clause format. *)

(* outputs a list of (thm,clause) pairs *)


(* for tracing: encloses each string element in brackets. *)
fun concat_with_stop [] = ""
  | concat_with_stop [x] =  x
  | concat_with_stop (x::xs) = x^ "." ^ concat_with_stop xs;

fun remove_symb str = 
    if String.isPrefix  "List.op @." str
    then  ((String.substring(str,0,5)) ^ (String.extract (str, 10, NONE)))
    else str;

fun remove_spaces str = 
    let val strlist = String.tokens Char.isSpace str
	val spaceless = concat strlist
	val strlist' = String.tokens Char.isPunct spaceless
    in
	concat_with_stop strlist'
    end

fun remove_symb_pair (str, thm) = (remove_symb str, thm);

fun remove_spaces_pair (str, thm) = (remove_spaces str, thm);


(*Insert th into the result provided the name is not "".*)
fun add_nonempty ((name,th), ths) = if name="" then ths else th::ths;

fun posinlist x [] n = "not in list"
|   posinlist x (y::ys) n = if (x=y) 
			    then
 				string_of_int n
			    else posinlist x (ys) (n+1)


fun pairup [] [] = []
|   pairup (x::xs) (y::ys) = (x,y)::(pairup xs ys)

fun multi x 0 xlist = xlist
   |multi x n xlist = multi x (n -1 ) (x::xlist);

fun clause_numbering ((clause, theorem), cls) = 
    let val num_of_cls = length cls
	val numbers = 0 upto (num_of_cls -1)
	val multi_name = multi (clause, theorem)  num_of_cls []
    in 
	(multi_name)
    end;

(*Write out the claset and simpset rules of the supplied theory.
  FIXME: argument "goal" is a hack to allow relevance filtering.*)
fun write_out_clasimp filename thy goal = 
    let val claset_rules = ReduceAxiomsN.relevant_filter 1 goal 
                              (ResAxioms.claset_rules_of_thy thy);
	val named_claset = List.filter has_name_pair claset_rules;
	val claset_names = map remove_spaces_pair (named_claset)
	val claset_cls_thms = #1 (ResAxioms.clausify_rules_pairs named_claset []);

	val simpset_rules = ReduceAxiomsN.relevant_filter 1 goal 
	                       (ResAxioms.simpset_rules_of_thy thy);
	val named_simpset = 
	      map remove_spaces_pair (List.filter has_name_pair simpset_rules)
	val simpset_cls_thms = #1 (ResAxioms.clausify_rules_pairs named_simpset []);

	val cls_thms = (claset_cls_thms@simpset_cls_thms);
	val cls_thms_list = List.concat cls_thms;
        (* length 1429 *)
	(*************************************************)
	(* Write out clauses as tptp strings to filename *)
	(*************************************************)
	val clauses = map #1(cls_thms_list);
	val cls_tptp_strs = map ResClause.tptp_clause clauses;
        val alllist = pairup cls_thms_list cls_tptp_strs
        val whole_list = List.concat (map clause_numbering alllist);
 
        (*********************************************************)
	(* create array and put clausename, number pairs into it *)
	(*********************************************************)
	val num_of_clauses =  0;
	val clause_arr = Array.fromList whole_list;
	val num_of_clauses = List.length whole_list;

	(* list of lists of tptp string clauses *)
	val stick_clasrls =   List.concat cls_tptp_strs;
        (* length 1581*)
	val out = TextIO.openOut filename;
	val _=   ResLib.writeln_strs out stick_clasrls;
	val _= TextIO.flushOut out;
	val _= TextIO.closeOut out
  in
	(clause_arr, num_of_clauses)
  end;





(*Write out the claset and simpset rules of the supplied theory. Only include the first 50 rules*)
fun write_out_clasimp_small filename thy = 
    let val claset_rules = ResAxioms.claset_rules_of_thy thy;
	val named_claset = List.filter has_name_pair claset_rules;
	val claset_names = map remove_spaces_pair (named_claset)
	val claset_cls_thms = #1 (ResAxioms.clausify_rules_pairs named_claset []);

	val simpset_rules = ResAxioms.simpset_rules_of_thy thy;
	val named_simpset = 
	      map remove_spaces_pair (List.filter has_name_pair simpset_rules)
	val simpset_cls_thms = #1 (ResAxioms.clausify_rules_pairs named_simpset []);

	val cls_thms = (claset_cls_thms@simpset_cls_thms);
	val cls_thms_list = List.concat cls_thms;
        (* length 1429 *)
	(*************************************************)
	(* Write out clauses as tptp strings to filename *)
	(*************************************************)
	val clauses = map #1(cls_thms_list);
	val cls_tptp_strs = map ResClause.tptp_clause clauses;
        val alllist = pairup cls_thms_list cls_tptp_strs
        val whole_list = List.concat (map clause_numbering alllist);
        val mini_list = List.take ( whole_list,50)
        (*********************************************************)
	(* create array and put clausename, number pairs into it *)
	(*********************************************************)
	val num_of_clauses =  0;
	val clause_arr = Array.fromList mini_list;
	val num_of_clauses = List.length mini_list;

	(* list of lists of tptp string clauses *)
	val stick_clasrls =   List.concat cls_tptp_strs;
        (* length 1581*)
	val out = TextIO.openOut filename;
	val _=   ResLib.writeln_strs out (List.take (stick_clasrls,50));
	val _= TextIO.flushOut out;
	val _= TextIO.closeOut out
  in
	(clause_arr, num_of_clauses)
  end;



end;


	
