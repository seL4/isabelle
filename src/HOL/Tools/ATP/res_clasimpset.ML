(*  ID:      $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

structure ReduceAxiomsN =
(* Author: Jia Meng, Cambridge University Computer Laboratory
   Remove irrelevant axioms used for a proof of a goal, with with iteration control
   Initial version. Needs elaboration. *)

struct

fun add_term_consts_rm ncs (Const(c, _)) cs = if (c mem ncs) then cs else (c ins_string cs)
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
    in const_thm_list_aux thms (cthms' @ cthms) end;

fun const_thm_list thms = const_thm_list_aux thms [];

fun make_thm_table thms = Symtab.make_multi (const_thm_list thms);

fun consts_in_goal goal = consts_of_term goal;

fun axioms_having_consts_aux [] tab thms = thms
  | axioms_having_consts_aux (c::cs) tab thms =
    let val thms2 = Option.getOpt (Symtab.lookup tab c, [])
    in axioms_having_consts_aux cs tab (thms2 union thms) end;

fun axioms_having_consts cs tab = axioms_having_consts_aux cs tab [];

fun relevant_axioms goal thmTab n =  
    let fun relevant_axioms_aux1 cs k =
	    let val thms1 = axioms_having_consts cs thmTab
		val cs1 = foldl (op union_string) [] (map consts_of_thm thms1)
	    in
		if (cs1 subset cs) orelse n <= k then (k,thms1) 
		else relevant_axioms_aux1 (cs1 union cs) (k+1)
	    end
    in  relevant_axioms_aux1 (consts_in_goal goal) 1  end;

fun relevant_filter n goal thms = 
    if n<=0 then thms 
    else #2 (relevant_axioms goal (make_thm_table thms) n);

(* find the thms from thy that contain relevant constants, n is the iteration number *)
fun find_axioms_n thy goal n =
    let val clasetR = ResAxioms.claset_rules_of_thy thy
	val simpsetR = ResAxioms.simpset_rules_of_thy thy	  
	val table = make_thm_table (clasetR @ simpsetR)	
    in relevant_axioms goal table n end;

fun find_axioms_n_c thy goal n =
    let val current_thms = PureThy.thms_of thy
	val table = make_thm_table current_thms
    in relevant_axioms goal table n end;

end;


signature RES_CLASIMP = 
  sig
  val blacklist : string list ref (*Theorems forbidden in the output*)
  val relevant : int ref
  val use_simpset: bool ref
  val get_clasimp_lemmas : 
         Proof.context -> term -> 
         (ResClause.clause * thm) Array.array * ResClause.clause list 
  end;

structure ResClasimp : RES_CLASIMP =
struct
val use_simpset = ref false;   (*Performance is much better without simprules*)

(*In general, these produce clauses that are prolific (match too many equality or
  membership literals) and relate to seldom-used facts. Some duplicate other rules.*)
val blacklist = ref
  ["Finite_Set.Max_ge",
   "Finite_Set.Max_le_iff",
   "Finite_Set.Max_less_iff",
   "Finite_Set.Min_le",
   "Finite_Set.Min_ge_iff",
   "Finite_Set.Min_gr_iff",
   "Finite_Set.min_max.below_inf_sup_Inf_Sup.inf_Sup_absorb",
   "Finite_Set.min_max.below_inf_sup_Inf_Sup.sup_Inf_absorb",
   (*The next four are duplicates of the properties of min and max, from Orderings.*)
   "Finite_Set.max.f_below_strict_below.below_f_conv",
   "Finite_Set.max.f_below_strict_below.strict_below_f_conv",
   "Finite_Set.min.f_below_strict_below.strict_below_f_conv",
   "Finite_Set.min.f_below_strict_below.below_f_conv",
   "Infinite_Set.atmost_one_unique",
   "List.in_listsD",
   "List.in_listsI",
   "List.listsE",
   "List.lists.Cons",
   "Relation.ImageI",
   "Relation.diagI",
   "Set.Diff_insert0",
   "Set.Inter_UNIV_conv_1",
   "Set.Inter_UNIV_conv_2",
   "Set.Inter_iff",              (*We already have InterI, InterE*)
   "Set.Union_iff",              (*We already have UnionI, UnionE*)
   "Datatype.not_None_eq_iff2",
   "Datatype.not_Some_eq",
   "Datatype.not_Some_eq_D",
   "Set.disjoint_insert_1",
   "Set.disjoint_insert_2",
   "Set.insert_disjoint_1",
   "Set.insert_disjoint_2",
   "Set.singletonD",
   "Set.singletonI",
   "Sum_Type.InlI",
   "Sum_Type.InrI",
   "Set.singleton_insert_inj_eq",
   "Set.singleton_insert_inj_eq'"];

(*These are the defining properties of min and max, but as they are prolific they
  could be included above.
   "Orderings.max_less_iff_conj",
   "Orderings.min_less_iff_conj",
   "Orderings.min_max.below_inf.below_inf_conv",
   "Orderings.min_max.below_sup.above_sup_conv",
*)

val relevant = ref 0;  (*Relevance filtering is off by default*)

(*The "name" of a theorem is its statement, if nothing else is available.*)
val plain_string_of_thm =
    setmp show_question_marks false 
      (setmp print_mode [] 
	(Pretty.setmp_margin 999 string_of_thm));
	
(*Returns the first substring enclosed in quotation marks, typically omitting 
  the [.] of meta-level assumptions.*)
val firstquoted = hd o (String.tokens (fn c => c = #"\""))
	
fun fake_thm_name th = 
    Context.theory_name (theory_of_thm th) ^ "." ^ firstquoted (plain_string_of_thm th);

fun put_name_pair ("",th) = (fake_thm_name th, th)
  | put_name_pair (a,th)  = (a,th);

(* outputs a list of (thm,clause) pairs *)

fun multi x 0 xlist = xlist
   |multi x n xlist = multi x (n-1) (x::xlist);

fun clause_numbering ((clause, theorem), num_of_cls) = 
    let val numbers = 0 upto (num_of_cls - 1)
    in 
	multi (clause, theorem) num_of_cls []
    end;
    
(*Hashing to detect duplicate and variant clauses, e.g. from the [iff] attribute
Some primes from http://primes.utm.edu/:
*)

exception HASH_CLAUSE and HASH_STRING;

(*Catches (for deletion) theorems automatically generated from other theorems*)
fun insert_suffixed_names ht x = 
     (Polyhash.insert ht (x^"_iff1", ()); 
      Polyhash.insert ht (x^"_iff2", ()); 
      Polyhash.insert ht (x^"_dest", ())); 

fun make_banned_test xs = 
  let val ht = Polyhash.mkTable (Polyhash.hash_string, op =)
                                (6000, HASH_STRING)
      fun banned s = isSome (Polyhash.peek ht s)
  in  app (fn x => Polyhash.insert ht (x,())) (!blacklist);
      app (insert_suffixed_names ht) (!blacklist @ xs); 
      banned
  end;

(*Create a hash table for clauses, of the given size*)
fun mk_clause_table n =
      Polyhash.mkTable (ResClause.hash_clause, ResClause.clause_eq)
                       (n, HASH_CLAUSE);

(*Use a hash table to eliminate duplicates from xs*)
fun make_unique ht xs = 
      (app (ignore o Polyhash.peekInsert ht) xs;  Polyhash.listItems ht);

(*Write out the claset and simpset rules of the supplied theory.
  FIXME: argument "goal" is a hack to allow relevance filtering.
  To reduce the number of clauses produced, set ResClasimp.relevant:=1*)
fun get_clasimp_lemmas ctxt goal = 
  let val claset_thms =
	    map put_name_pair
	      (ReduceAxiomsN.relevant_filter (!relevant) goal 
		(ResAxioms.claset_rules_of_ctxt ctxt))
      val simpset_thms = 
	    if !use_simpset then 
		  map put_name_pair 
		    (ReduceAxiomsN.relevant_filter (!relevant) goal
		      (ResAxioms.simpset_rules_of_ctxt ctxt))
	    else []
      val banned = make_banned_test (map #1 (claset_thms@simpset_thms))
      fun ok (a,_) = not (banned a)
      val claset_cls_thms = ResAxioms.clausify_rules_pairs (filter ok claset_thms)
      val simpset_cls_thms = ResAxioms.clausify_rules_pairs (filter ok simpset_thms)
      val cls_thms_list = make_unique (mk_clause_table 2200) 
                                      (List.concat (simpset_cls_thms@claset_cls_thms))
      (* Identify the set of clauses to be written out *)
      val clauses = map #1(cls_thms_list);
      val cls_nums = map ResClause.num_of_clauses clauses;
      (*Note: in every case, cls_num = 1.  I think that only conjecture clauses
	can have any other value.*)
      val whole_list = List.concat 
	    (map clause_numbering (ListPair.zip (cls_thms_list, cls_nums)));
      
  in  (* create array of put clausename, number pairs into it *)
      (Array.fromList whole_list, clauses)
  end;


end;


	
