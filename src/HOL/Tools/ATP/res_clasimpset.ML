(*  ID:      $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

signature RES_CLASIMP = 
  sig
  val blacklist : string list ref (*Theorems forbidden in the output*)
  val theory_blacklist : string list ref (*entire blacklisted theories*)
  val relevant : int ref
  val use_simpset: bool ref
  val get_clasimp_lemmas : 
         Proof.context -> term list -> 
         (ResClause.clause * thm) Array.array * ResClause.clause list 
  end;

structure ResClasimp : RES_CLASIMP =
struct
val use_simpset = ref false;   (*Performance is much better without simprules*)

(*In general, these produce clauses that are prolific (match too many equality or
  membership literals) and relate to seldom-used facts. Some duplicate other rules.
  FIXME: this blacklist needs to be maintained using theory data and added to using
  an attribute.*)
val blacklist = ref
  ["Datatype.not_None_eq_iff2",
   "Datatype.not_Some_eq_D",
   "Datatype.not_Some_eq",
   "Datatype.option.size_1",
   "Datatype.option.size_2",
   "Datatype.prod.size",
   "Datatype.sum.size_1",
   "Datatype.sum.size_2",
   "Datatype.unit.size",
   "Divides.dvd_0_left_iff",
   "Finite_Set.card_0_eq",
   "Finite_Set.card_infinite",
   "Finite_Set.Max_ge",
   "Finite_Set.Max_in",
   "Finite_Set.Max_le_iff",
   "Finite_Set.Max_less_iff",
   "Finite_Set.max.f_below_strict_below.below_f_conv", (*duplicates in Orderings.*)
   "Finite_Set.max.f_below_strict_below.strict_below_f_conv", (*duplicates in Orderings.*)
   "Finite_Set.Min_ge_iff",
   "Finite_Set.Min_gr_iff",
   "Finite_Set.Min_in",
   "Finite_Set.Min_le",
   "Finite_Set.min_max.below_inf_sup_Inf_Sup.inf_Sup_absorb", 
   "Finite_Set.min_max.below_inf_sup_Inf_Sup.sup_Inf_absorb", 
   "Finite_Set.min.f_below_strict_below.below_f_conv",        (*duplicates in Orderings.*)
   "Finite_Set.min.f_below_strict_below.strict_below_f_conv", (*duplicates in Orderings.*)
   "Infinite_Set.atmost_one_unique",
   "IntArith.zabs_less_one_iff",
   "IntDef.Integ.Abs_Integ_inject",
   "IntDef.Integ.Abs_Integ_inverse",
   "IntDiv.zdvd_0_left",
   "IntDiv.zero_less_zpower_abs_iff",
   "List.append_eq_append_conv",
   "List.Cons_in_lex",
   "List.in_listsD",
   "List.in_listsI",
   "List.lists.Cons",
   "List.listsE",
   "List.take_eq_Nil",
   "Nat.less_one",
   "Nat.less_one", (*not directional? obscure*)
   "Nat.not_gr0",
   "Nat.one_eq_mult_iff", (*duplicate by symmetry*)
   "NatArith.of_nat_0_eq_iff",
   "NatArith.of_nat_eq_0_iff",
   "NatArith.of_nat_le_0_iff",
   "NatSimprocs.divide_le_0_iff_number_of",  (*seldom used; often prolific*)
   "NatSimprocs.divide_le_0_iff_number_of",  (*too many clauses*)
   "NatSimprocs.divide_less_0_iff_number_of",
   "NatSimprocs.divide_less_0_iff_number_of",   (*too many clauses*)
   "NatSimprocs.equation_minus_iff_1",  (*not directional*)
   "NatSimprocs.equation_minus_iff_number_of", (*not directional*)
   "NatSimprocs.le_minus_iff_1", (*not directional*)
   "NatSimprocs.le_minus_iff_number_of",  (*not directional*)
   "NatSimprocs.less_minus_iff_1", (*not directional*)
   "NatSimprocs.less_minus_iff_number_of", (*not directional*)
   "NatSimprocs.minus_equation_iff_number_of", (*not directional*)
   "NatSimprocs.minus_le_iff_1", (*not directional*)
   "NatSimprocs.minus_le_iff_number_of", (*not directional*)
   "NatSimprocs.minus_less_iff_1", (*not directional*)
   "NatSimprocs.mult_le_cancel_left_number_of", (*excessive case analysis*)
   "NatSimprocs.mult_le_cancel_right_number_of", (*excessive case analysis*)
   "NatSimprocs.mult_less_cancel_left_number_of", (*excessive case analysis*)
   "NatSimprocs.mult_less_cancel_right_number_of", (*excessive case analysis*)
   "NatSimprocs.zero_le_divide_iff_number_of",
   "NatSimprocs.zero_le_divide_iff_number_of", (*excessive case analysis*)
   "NatSimprocs.zero_less_divide_iff_number_of",
   "NatSimprocs.zero_less_divide_iff_number_of", (*excessive case analysis*)
   "OrderedGroup.abs_0_eq",
   "OrderedGroup.abs_0_eq", (*duplicate by symmetry*)
   "OrderedGroup.diff_eq_0_iff_eq", (*prolific?*)
   "OrderedGroup.join_0_eq_0",
   "OrderedGroup.meet_0_eq_0",
   "OrderedGroup.pprt_eq_0",   (*obscure*)
   "OrderedGroup.pprt_eq_id",   (*obscure*)
   "OrderedGroup.pprt_mono",   (*obscure*)
   "Parity.even_nat_power",   (*obscure, somewhat prolilfic*)
   "Parity.power_eq_0_iff_number_of",
   "Parity.power_eq_0_iff_number_of",
   "Parity.power_le_zero_eq_number_of",
   "Parity.power_le_zero_eq_number_of",   (*obscure and prolific*)
   "Parity.power_less_zero_eq_number_of",
   "Parity.zero_le_power_eq_number_of",   (*obscure and prolific*)
   "Parity.zero_less_power_eq_number_of",   (*obscure and prolific*)
   "Power.zero_less_power_abs_iff",
   "Relation.diagI",
   "Relation.ImageI",
   "Ring_and_Field.divide_cancel_left", (*fields are seldom used & often prolific*)
   "Ring_and_Field.divide_cancel_right",
   "Ring_and_Field.divide_divide_eq_left",
   "Ring_and_Field.divide_divide_eq_right",
   "Ring_and_Field.divide_eq_0_iff",
   "Ring_and_Field.divide_eq_1_iff",
   "Ring_and_Field.divide_eq_eq_1",
   "Ring_and_Field.divide_le_0_1_iff",
   "Ring_and_Field.divide_le_eq_1_neg",
   "Ring_and_Field.divide_le_eq_1_neg",  (*obscure and prolific*)
   "Ring_and_Field.divide_le_eq_1_pos",
   "Ring_and_Field.divide_le_eq_1_pos",  (*obscure and prolific*)
   "Ring_and_Field.divide_less_0_1_iff",
   "Ring_and_Field.divide_less_eq_1_neg",  (*obscure and prolific*)
   "Ring_and_Field.divide_less_eq_1_pos",
   "Ring_and_Field.divide_less_eq_1_pos",  (*obscure and prolific*)
   "Ring_and_Field.eq_divide_eq_1",
   "Ring_and_Field.eq_divide_eq_1", (*duplicate by symmetry*)
   "Ring_and_Field.field_mult_cancel_left",
   "Ring_and_Field.field_mult_cancel_right",
   "Ring_and_Field.inverse_le_iff_le_neg",
   "Ring_and_Field.inverse_le_iff_le",
   "Ring_and_Field.inverse_less_iff_less_neg",
   "Ring_and_Field.inverse_less_iff_less",
   "Ring_and_Field.le_divide_eq_1_neg",
   "Ring_and_Field.le_divide_eq_1_neg", (*obscure and prolific*)
   "Ring_and_Field.le_divide_eq_1_pos",
   "Ring_and_Field.le_divide_eq_1_pos", (*obscure and prolific*)
   "Ring_and_Field.less_divide_eq_1_neg",
   "Ring_and_Field.less_divide_eq_1_neg", (*obscure and prolific*)
   "Ring_and_Field.less_divide_eq_1_pos",
   "Ring_and_Field.less_divide_eq_1_pos", (*obscure and prolific*)
   "Ring_and_Field.one_eq_divide_iff",  (*duplicate by symmetry*)
   "Set.Diff_eq_empty_iff", (*redundant with paramodulation*)
   "Set.Diff_insert0",
   "Set.disjoint_insert_1",
   "Set.disjoint_insert_2",
   "Set.empty_Union_conv", (*redundant with paramodulation*)
   "Set.insert_disjoint_1",
   "Set.insert_disjoint_2",
   "Set.Int_UNIV", (*redundant with paramodulation*)
   "Set.Inter_iff",              (*We already have InterI, InterE*)
   "Set.Inter_UNIV_conv_1",
   "Set.Inter_UNIV_conv_2",
   "Set.psubsetE",    (*too prolific and obscure*)
   "Set.psubsetI",
   "Set.singleton_insert_inj_eq'",
   "Set.singleton_insert_inj_eq",
   "Set.singletonD",  (*these two duplicate some "insert" lemmas*)
   "Set.singletonI",
   "Set.Un_empty", (*redundant with paramodulation*)
   "Set.Union_empty_conv", (*redundant with paramodulation*)
   "Set.Union_iff",              (*We already have UnionI, UnionE*)
   "SetInterval.atLeastAtMost_iff", (*obscure and prolific*)
   "SetInterval.atLeastLessThan_iff", (*obscure and prolific*)
   "SetInterval.greaterThanAtMost_iff", (*obscure and prolific*)
   "SetInterval.greaterThanLessThan_iff", (*obscure and prolific*)
   "SetInterval.ivl_subset", (*excessive case analysis*)
   "Sum_Type.InlI",
   "Sum_Type.InrI"];
   
(*These might be prolific but are probably OK, and min and max are basic.
   "Orderings.max_less_iff_conj", 
   "Orderings.min_less_iff_conj",
   "Orderings.min_max.below_inf.below_inf_conv",
   "Orderings.min_max.below_sup.above_sup_conv",
Very prolific and somewhat obscure:
   "Set.InterD",
   "Set.UnionI",
*)

val theory_blacklist = ref
  ["Datatype_Universe.",    (*unnecessary in virtually all proofs*)
   "Equiv_Relations."]  


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
    
(*Hashing to detect duplicate and variant clauses, e.g. from the [iff] attribute*)

exception HASH_CLAUSE and HASH_STRING;

(*Catches (for deletion) theorems automatically generated from other theorems*)
fun insert_suffixed_names ht x = 
     (Polyhash.insert ht (x^"_iff1", ()); 
      Polyhash.insert ht (x^"_iff2", ()); 
      Polyhash.insert ht (x^"_dest", ())); 

fun banned_theory s = exists (fn thy => String.isPrefix thy s) (!theory_blacklist);

fun make_banned_test xs = 
  let val ht = Polyhash.mkTable (Polyhash.hash_string, op =)
                                (6000, HASH_STRING)
      fun banned s = isSome (Polyhash.peek ht s) orelse banned_theory s
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
fun get_clasimp_lemmas ctxt goals = 
  let val claset_thms =
	  map put_name_pair (ResAxioms.claset_rules_of_ctxt ctxt)
      val simpset_thms = 
	    if !use_simpset then 
		map put_name_pair (ResAxioms.simpset_rules_of_ctxt ctxt)
	    else []
      val banned = make_banned_test (map #1 (claset_thms@simpset_thms))
      fun ok (a,_) = not (banned a)
      val claset_cls_thms = ResAxioms.clausify_rules_pairs (filter ok claset_thms)
      val simpset_cls_thms = ResAxioms.clausify_rules_pairs (filter ok simpset_thms)
 

     val cls_thms_list = make_unique (mk_clause_table 2200) 
                                      (List.concat (simpset_cls_thms@claset_cls_thms))

     val relevant_cls_thms_list = ReduceAxiomsN.relevance_filter cls_thms_list goals
      (* Identify the set of clauses to be written out *)
      val clauses = map #1(relevant_cls_thms_list);
      val cls_nums = map ResClause.num_of_clauses clauses;
      (*Note: in every case, cls_num = 1.  I think that only conjecture clauses
	can have any other value.*)
      val whole_list = List.concat 
	    (map clause_numbering (ListPair.zip (relevant_cls_thms_list, cls_nums)));
      
  in  (* create array of put clausename, number pairs into it *)
      (Array.fromList whole_list, clauses)
  end;


end;


	
