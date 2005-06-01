
(*  ID:         $Id$

    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

signature RES_CLASIMP = 
  sig
     val write_out_clasimp :string -> theory -> (ResClause.clause * thm) Array.array * int
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

(*Write out the claset and simpset rules of the supplied theory.*)
fun write_out_clasimp filename thy = 
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

end;


	
