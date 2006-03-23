(*  ID:      $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

signature RES_CLASIMP = 
  sig
  val blacklist : string list ref (*Theorems forbidden in the output*)
  val whitelist : thm list ref    (*Theorems required in the output*)
  val use_simpset: bool ref
  val get_clasimp_atp_lemmas : 
      Proof.context ->
      Term.term list ->
      (string * Thm.thm) list ->
      (bool * bool * bool) -> bool -> string Array.array * (Term.term * (string * int)) list
  end;
  
structure ResClasimp : RES_CLASIMP =
struct
val use_simpset = ref false;   (*Performance is much better without simprules*)

(*The rule subsetI is frequently omitted by the relevance filter.*)
val whitelist = ref [subsetI]; 

(*In general, these produce clauses that are prolific (match too many equality or
  membership literals) and relate to seldom-used facts. Some duplicate other rules.
  FIXME: this blacklist needs to be maintained using theory data and added to using
  an attribute.*)
val blacklist = ref
  ["Datatype.not_None_eq",    (*Says everything is None or Some. Probably prolific.*)
   "Datatype.not_Some_eq_D",  (*Says everything is None or Some. Probably prolific.*)
   "Datatype.not_Some_eq",    (*Says everything is None or Some. Probably prolific.*)
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
   "List.hd_Cons_tl",   (*Says everything is [] or Cons. Probably prolific.*)
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

(*Hashing to detect duplicate and variant clauses, e.g. from the [iff] attribute*)

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


(*** a hash function from Term.term to int, and also a hash table ***)
val xor_words = List.foldl Word.xorb 0w0;

fun hashw_term ((Const(c,_)), w) = Polyhash.hashw_string (c,w)
  | hashw_term ((Free(_,_)), w) = w
  | hashw_term ((Var(_,_)), w) = w
  | hashw_term ((Bound _), w) = w
  | hashw_term ((Abs(_,_,t)), w) = hashw_term (t, w)
  | hashw_term ((P$Q), w) = hashw_term (Q, (hashw_term (P, w)));

fun hashw_pred (P,w) = 
    let val (p,args) = strip_comb P
    in
	List.foldl hashw_term w (p::args)
    end;

fun hash_literal (Const("Not",_)$P) = Word.notb(hashw_pred(P,0w0))
  | hash_literal P = hashw_pred(P,0w0);


fun get_literals (Const("Trueprop",_)$P) lits = get_literals P lits
  | get_literals (Const("op |",_)$P$Q) lits = get_literals Q (get_literals P lits)
  | get_literals lit lits = (lit::lits);


fun hash_term term = Word.toIntX (xor_words (map hash_literal (get_literals term [])));


(*Create a hash table for clauses, of the given size*)
fun mk_clause_table n =
      Polyhash.mkTable (hash_term, Term.aconv)
                       (n, HASH_CLAUSE);

(*Use a hash table to eliminate duplicates from xs*)
fun make_unique ht xs = 
      (app (ignore o Polyhash.peekInsert ht) xs;  Polyhash.listItems ht);

fun mem_tm tm [] = false
  | mem_tm tm ((tm',name)::tms_names) = Term.aconv (tm,tm') orelse mem_tm tm tms_names;

fun insert_tms [] tms_names = tms_names
  | insert_tms ((tm,name)::tms_names) tms_names' =
      if mem_tm tm tms_names' then insert_tms tms_names tms_names' 
      else insert_tms tms_names ((tm,name)::tms_names');

fun display_thms [] = ()
  | display_thms ((name,thm)::nthms) = 
      let val nthm = name ^ ": " ^ (string_of_thm thm)
      in Output.debug nthm; display_thms nthms  end;
 
(*Write out the claset, simpset and atpset rules of the supplied theory.*)
(* also write supplied user rules, they are not relevance filtered *)
fun get_clasimp_atp_lemmas ctxt goals user_thms (use_claset, use_simpset', use_atpset) run_filter =
    let val claset_thms =
	    if use_claset then
		map put_name_pair (ResAxioms.claset_rules_of_ctxt ctxt)
	    else []
      val simpset_thms = 
	    if (!use_simpset andalso use_simpset') then (* temporary, may merge two use_simpset later *)  
		map put_name_pair (ResAxioms.simpset_rules_of_ctxt ctxt)
	    else []
      val atpset_thms =
	  if use_atpset then
	      map put_name_pair (ResAxioms.atpset_rules_of_ctxt ctxt)
	  else []
      val _ = if !Output.show_debug_msgs then (Output.debug "ATP theorems: "; display_thms atpset_thms) else ()
      val user_rules = 
	  case user_thms of  (*use whitelist if there are no user-supplied rules*)
	       [] => map (put_name_pair o ResAxioms.pairname) (!whitelist)
	     | _  => map put_name_pair user_thms
      val banned = make_banned_test (map #1 (user_rules@atpset_thms@claset_thms@simpset_thms))
      fun ok (a,_) = not (banned a) 	   
      val claset_cls_tms = 
            if run_filter then ResAxioms.clausify_rules_pairs_abs (filter ok claset_thms)
            else ResAxioms.clausify_rules_pairs_abs claset_thms
      val simpset_cls_tms = 
      	    if run_filter then ResAxioms.clausify_rules_pairs_abs (filter ok simpset_thms)
	    else ResAxioms.clausify_rules_pairs_abs simpset_thms
      val atpset_cls_tms = 
      	    if run_filter then ResAxioms.clausify_rules_pairs_abs (filter ok atpset_thms)
	    else ResAxioms.clausify_rules_pairs_abs atpset_thms
      val user_cls_tms = ResAxioms.clausify_rules_pairs_abs user_rules (* no filter here, because user supplied rules *)
      val cls_tms_list = make_unique (mk_clause_table 2200) 
                           (List.concat (user_cls_tms@atpset_cls_tms@simpset_cls_tms@claset_cls_tms))
      val relevant_cls_tms_list =
	  if run_filter 
	  then ReduceAxiomsN.relevance_filter (ProofContext.theory_of ctxt) cls_tms_list goals
	  else cls_tms_list
      val all_relevant_cls_tms_list = insert_tms (List.concat user_cls_tms) relevant_cls_tms_list (*ensure all user supplied rules are output*)	  
    in
	(Array.fromList (map fst (map snd all_relevant_cls_tms_list)), all_relevant_cls_tms_list)
end;


	
end;