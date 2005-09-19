(*  ID:      $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)


structure ReduceAxiomsN =
(* Author: Jia Meng, Cambridge University Computer Laboratory
   Remove irrelevant axioms used for a proof of a goal, with with iteration control
   
   Initial version. Needs elaboration. *)

struct

fun add_term_consts_rm ncs (Const(c, _)) cs = 
    if (c mem ncs) then cs else (c ins_string cs)
  | add_term_consts_rm ncs (t $ u) cs =
      add_term_consts_rm ncs t (add_term_consts_rm ncs u cs)
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
    let val thms1 = Symtab.lookup tab c
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
		if ((cs1 subset cs) orelse n <= k) then (k,thms1) 
		else (relevant_axioms_aux1 (cs1 union cs) (k+1))
	    end

    in  relevant_axioms_aux1 consts 1  end;


fun relevant_filter n goal thms = 
    if n<=0 then thms 
    else #2 (relevant_axioms goal (make_thm_table thms) n);


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
  val relevant : int ref
  val use_simpset: bool ref
  val use_nameless: bool ref
  val get_clasimp_lemmas : 
         Proof.context -> term -> 
         (ResClause.clause * thm) Array.array * ResClause.clause list 
  end;

structure ResClasimp : RES_CLASIMP =
struct
val use_simpset = ref false;   (*Performance is much better without simprules*)
val use_nameless = ref false;  (*Because most are useless [iff] rules*)

val relevant = ref 0;  (*Relevance filtering is off by default*)

(*The "name" of a theorem is its statement, if nothing else is available.*)
val plain_string_of_thm =
    setmp show_question_marks false 
      (setmp print_mode [] 
	(Pretty.setmp_margin 999 string_of_thm));
	
fun fake_thm_name th = 
    Context.theory_name (theory_of_thm th) ^ "." ^ 
    ResLib.trim_ends (plain_string_of_thm th);

fun put_name_pair ("",th) = if !use_nameless then (fake_thm_name th, th)
                            else ("HOL.TrueI",TrueI)
  | put_name_pair (a,th)  = (a,th);

(* changed, now it also finds out the name of the theorem. *)
(* convert a theorem into CNF and then into Clause.clause format. *)

(* outputs a list of (thm,clause) pairs *)

fun multi x 0 xlist = xlist
   |multi x n xlist = multi x (n-1) (x::xlist);

fun clause_numbering ((clause, theorem), num_of_cls) = 
    let val numbers = 0 upto (num_of_cls - 1)
    in 
	multi (clause, theorem) num_of_cls []
    end;
    

(*Write out the claset and simpset rules of the supplied theory.
  FIXME: argument "goal" is a hack to allow relevance filtering.
  To reduce the number of clauses produced, set ResClasimp.relevant:=1*)
fun get_clasimp_lemmas ctxt goal = 
    let val claset_rules = 
              map put_name_pair
	        (ReduceAxiomsN.relevant_filter (!relevant) goal 
		  (ResAxioms.claset_rules_of_ctxt ctxt));
	val claset_cls_thms = #1 (ResAxioms.clausify_rules_pairs claset_rules []);

	val simpset_rules =
	      ReduceAxiomsN.relevant_filter (!relevant) goal 
                (ResAxioms.simpset_rules_of_ctxt ctxt);
	val named_simpset = map put_name_pair simpset_rules
	val simpset_cls_thms = #1 (ResAxioms.clausify_rules_pairs named_simpset []);

	val cls_thms = if !use_simpset then (claset_cls_thms@simpset_cls_thms) 
	               else claset_cls_thms;
	val cls_thms_list = List.concat cls_thms;
	(*************************************************)
	(* Identify the set of clauses to be written out *)
	(*************************************************)
	val clauses = map #1(cls_thms_list);
	val cls_nums = map ResClause.num_of_clauses clauses;
        val whole_list = List.concat 
              (map clause_numbering (ListPair.zip (cls_thms_list, cls_nums)));
 
        (*********************************************************)
	(* create array and put clausename, number pairs into it *)
	(*********************************************************)
	val clause_arr = Array.fromList whole_list;
  in
	(clause_arr, clauses)
  end;


end;


	
