(*  Author: Jia Meng, Cambridge University Computer Laboratory, NICTA
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

signature RES_ATP =
sig
  val prover: string ref
  val custom_spass: string list ref
  val destdir: string ref
  val helper_path: string -> string -> string
  val problem_name: string ref
  val time_limit: int ref
   
  datatype mode = Auto | Fol | Hol
  val linkup_logic_mode : mode ref
  val write_subgoal_file: bool -> mode -> Proof.context -> thm list -> thm list -> int -> string
  val vampire_time: int ref
  val eprover_time: int ref
  val spass_time: int ref
  val run_vampire: int -> unit
  val run_eprover: int -> unit
  val run_spass: int -> unit
  val vampireLimit: unit -> int
  val eproverLimit: unit -> int
  val spassLimit: unit -> int
  val atp_method: (ProofContext.context -> thm list -> int -> Tactical.tactic) ->
		  Method.src -> ProofContext.context -> Method.method
  val cond_rm_tmp: string -> unit
  val keep_atp_input: bool ref
  val fol_keep_types: bool ref
  val hol_full_types: unit -> unit
  val hol_partial_types: unit -> unit
  val hol_const_types_only: unit -> unit
  val hol_no_types: unit -> unit
  val hol_typ_level: unit -> ResHolClause.type_level
  val run_relevance_filter: bool ref
  val run_blacklist_filter: bool ref
  val invoke_atp_ml : ProofContext.context * thm -> unit
  val add_claset : unit -> unit
  val add_simpset : unit -> unit
  val add_clasimp : unit -> unit
  val add_atpset : unit -> unit
  val rm_claset : unit -> unit
  val rm_simpset : unit -> unit
  val rm_atpset : unit -> unit
  val rm_clasimp : unit -> unit
end;

structure ResAtp : RES_ATP =
struct

(********************************************************************)
(* some settings for both background automatic ATP calling procedure*)
(* and also explicit ATP invocation methods                         *)
(********************************************************************)

(*** background linkup ***)
val call_atp = ref false; 
val hook_count = ref 0;
val time_limit = ref 30;
val prover = ref "E";   (* use E as the default prover *)
val custom_spass =   (*specialized options for SPASS*)
      ref ["-Auto=0","-FullRed=0","-IORe","-IOFc","-RTaut","-RFSub","-RBSub"];
val destdir = ref "";   (*Empty means write files to /tmp*)
val problem_name = ref "prob";

(*Return the path to a "helper" like SPASS or tptp2X, first checking that
  it exists.  FIXME: modify to use Path primitives and move to some central place.*)  
fun helper_path evar base =
  case getenv evar of
      "" => error  ("Isabelle environment variable " ^ evar ^ " not defined")
    | home => 
        let val path = home ^ "/" ^ base
        in  if File.exists (File.unpack_platform_path path) then path 
	    else error ("Could not find the file " ^ path)
	end;  

fun probfile_nosuffix _ = 
  if !destdir = "" then File.platform_path (File.tmp_path (Path.basic (!problem_name)))
  else if File.exists (File.unpack_platform_path (!destdir))
  then !destdir ^ "/" ^ !problem_name
  else error ("No such directory: " ^ !destdir);

fun prob_pathname n = probfile_nosuffix n ^ "_" ^ Int.toString n;


(*** ATP methods ***)
val vampire_time = ref 60;
val eprover_time = ref 60;
val spass_time = ref 60;

fun run_vampire time =  
    if (time >0) then vampire_time:= time
    else vampire_time:=60;

fun run_eprover time = 
    if (time > 0) then eprover_time:= time
    else eprover_time:=60;

fun run_spass time = 
    if (time > 0) then spass_time:=time
    else spass_time:=60;


fun vampireLimit () = !vampire_time;
fun eproverLimit () = !eprover_time;
fun spassLimit () = !spass_time;

val keep_atp_input = ref false;
val fol_keep_types = ResClause.keep_types;
val hol_full_types = ResHolClause.full_types;
val hol_partial_types = ResHolClause.partial_types;
val hol_const_types_only = ResHolClause.const_types_only;
val hol_no_types = ResHolClause.no_types;
fun hol_typ_level () = ResHolClause.find_typ_level ();
fun is_typed_hol () = 
    let val tp_level = hol_typ_level()
    in
	not (tp_level = ResHolClause.T_NONE)
    end;
val include_combS = ResHolClause.include_combS;
val include_min_comb = ResHolClause.include_min_comb;

fun atp_input_file () =
    let val file = !problem_name 
    in
	if !destdir = "" then File.platform_path (File.tmp_path (Path.basic file))
	else if File.exists (File.unpack_platform_path (!destdir))
	then !destdir ^ "/" ^ file
	else error ("No such directory: " ^ !destdir)
    end;

val include_simpset = ref false;
val include_claset = ref false; 
val include_atpset = ref true;
val add_simpset = (fn () => include_simpset:=true);
val add_claset = (fn () => include_claset:=true);
val add_clasimp = (fn () => (include_simpset:=true;include_claset:=true));
val add_atpset = (fn () => include_atpset:=true);
val rm_simpset = (fn () => include_simpset:=false);
val rm_claset = (fn () => include_claset:=false);
val rm_clasimp = (fn () => (include_simpset:=false;include_claset:=false));
val rm_atpset = (fn () => include_atpset:=false);


(**** relevance filter ****)
val run_relevance_filter = ref true;
val run_blacklist_filter = ref true;

(******************************************************************)
(* detect whether a given problem (clauses) is FOL/HOL/HOLC/HOLCS *)
(******************************************************************)

datatype logic = FOL | HOL | HOLC | HOLCS;

fun string_of_logic FOL = "FOL"
  | string_of_logic HOL = "HOL"
  | string_of_logic HOLC = "HOLC"
  | string_of_logic HOLCS = "HOLCS";


fun is_fol_logic FOL = true
  | is_fol_logic  _ = false


(*HOLCS will not occur here*)
fun upgrade_lg HOLC _ = HOLC
  | upgrade_lg HOL HOLC = HOLC
  | upgrade_lg HOL _ = HOL
  | upgrade_lg FOL lg = lg; 

(* check types *)
fun has_bool_hfn (Type("bool",_)) = true
  | has_bool_hfn (Type("fun",_)) = true
  | has_bool_hfn (Type(_, Ts)) = exists has_bool_hfn Ts
  | has_bool_hfn _ = false;

fun is_hol_fn tp =
    let val (targs,tr) = strip_type tp
    in
	exists (has_bool_hfn) (tr::targs)
    end;

fun is_hol_pred tp =
    let val (targs,tr) = strip_type tp
    in
	exists (has_bool_hfn) targs
    end;

exception FN_LG of term;

fun fn_lg (t as Const(f,tp)) (lg,seen) = 
    if is_hol_fn tp then (upgrade_lg HOL lg, t ins seen) else (lg, t ins seen) 
  | fn_lg (t as Free(f,tp)) (lg,seen) = 
    if is_hol_fn tp then (upgrade_lg HOL lg, t ins seen) else (lg, t ins seen) 
  | fn_lg (t as Var(f,tp)) (lg,seen) =
    if is_hol_fn tp then (upgrade_lg HOL lg,t ins seen) else (lg,t ins seen)
  | fn_lg (t as Abs(_,_,_)) (lg,seen) = (upgrade_lg HOLC lg,t ins seen)
  | fn_lg f _ = raise FN_LG(f); 


fun term_lg [] (lg,seen) = (lg,seen)
  | term_lg (tm::tms) (FOL,seen) =
    let val (f,args) = strip_comb tm
	val (lg',seen') = if f mem seen then (FOL,seen) 
			  else fn_lg f (FOL,seen)
	val _ =
          if is_fol_logic lg' then ()
          else Output.debug ("Found a HOL term: " ^ Display.raw_string_of_term f)
	 in
	     term_lg (args@tms) (lg',seen')
    end
  | term_lg _ (lg,seen) = (lg,seen)

exception PRED_LG of term;

fun pred_lg (t as Const(P,tp)) (lg,seen)= 
    if is_hol_pred tp then (upgrade_lg HOL lg, t ins seen) else (lg,t ins seen) 
  | pred_lg (t as Free(P,tp)) (lg,seen) =
    if is_hol_pred tp then (upgrade_lg HOL lg, t ins seen) else (lg,t ins seen)
  | pred_lg (t as Var(_,_)) (lg,seen) = (upgrade_lg HOL lg, t ins seen)
  | pred_lg P _ = raise PRED_LG(P);


fun lit_lg (Const("Not",_) $ P) (lg,seen) = lit_lg P (lg,seen)
  | lit_lg P (lg,seen) =
    let val (pred,args) = strip_comb P
	val (lg',seen') = if pred mem seen then (lg,seen) 
			  else pred_lg pred (lg,seen)
	val _ =
          if is_fol_logic lg' then ()
          else Output.debug ("Found a HOL predicate: " ^ Display.raw_string_of_term pred)
    in
	term_lg args (lg',seen')
    end;

fun lits_lg [] (lg,seen) = (lg,seen)
  | lits_lg (lit::lits) (FOL,seen) =
    let val (lg,seen') = lit_lg lit (FOL,seen)
	val _ =
          if is_fol_logic lg then ()
          else Output.debug ("Found a HOL literal: " ^ Display.raw_string_of_term lit)
    in
	lits_lg lits (lg,seen')
    end
  | lits_lg lits (lg,seen) = (lg,seen);


fun dest_disj_aux (Const ("op |", _) $ t $ t') disjs = 
    dest_disj_aux t (dest_disj_aux t' disjs)
  | dest_disj_aux t disjs = t::disjs;

fun dest_disj t = dest_disj_aux t [];

fun logic_of_clause tm (lg,seen) =
    let val tm' = HOLogic.dest_Trueprop tm
	val disjs = dest_disj tm'
    in
	lits_lg disjs (lg,seen)
    end;

fun logic_of_clauses [] (lg,seen) = (lg,seen)
  | logic_of_clauses (cls::clss) (FOL,seen) =
    let val (lg,seen') = logic_of_clause cls (FOL,seen)
	val _ =
          if is_fol_logic lg then ()
          else Output.debug ("Found a HOL clause: " ^ Display.raw_string_of_term cls)
    in
	logic_of_clauses clss (lg,seen')
    end
  | logic_of_clauses (cls::clss) (lg,seen) = (lg,seen);

fun problem_logic_goals_aux [] (lg,seen) = lg
  | problem_logic_goals_aux (subgoal::subgoals) (lg,seen) = 
    problem_logic_goals_aux subgoals (logic_of_clauses subgoal (lg,seen));
    
fun problem_logic_goals subgoals = problem_logic_goals_aux subgoals (FOL,[]);

(***************************************************************)
(* Retrieving and filtering lemmas                             *)
(***************************************************************)

(*** white list and black list of lemmas ***)

(*The rule subsetI is frequently omitted by the relevance filter.*)
val whitelist = ref [subsetI]; 

(*In general, these produce clauses that are prolific (match too many equality or
  membership literals) and relate to seldom-used facts. Some duplicate other rules.
  FIXME: this blacklist needs to be maintained using theory data and added to using
  an attribute.*)
val blacklist = ref
  ["Datatype.prod.size",
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
   "IntDef.Integ.Abs_Integ_inject",
   "IntDef.Integ.Abs_Integ_inverse",
   "IntDiv.zdvd_0_left",
   "List.append_eq_append_conv",
   "List.hd_Cons_tl",   (*Says everything is [] or Cons. Probably prolific.*)
   "List.in_listsD",
   "List.in_listsI",
   "List.lists.Cons",
   "List.listsE",
   "Nat.less_one", (*not directional? obscure*)
   "Nat.not_gr0",
   "Nat.one_eq_mult_iff", (*duplicate by symmetry*)
   "NatArith.of_nat_0_eq_iff",
   "NatArith.of_nat_eq_0_iff",
   "NatArith.of_nat_le_0_iff",
   "NatSimprocs.divide_le_0_iff_number_of",  (*too many clauses*)
   "NatSimprocs.divide_less_0_iff_number_of",
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
   "NatSimprocs.zero_le_divide_iff_number_of", (*excessive case analysis*)
   "NatSimprocs.zero_less_divide_iff_number_of",
   "OrderedGroup.abs_0_eq", (*duplicate by symmetry*)
   "OrderedGroup.diff_eq_0_iff_eq", (*prolific?*)
   "OrderedGroup.join_0_eq_0",
   "OrderedGroup.meet_0_eq_0",
   "OrderedGroup.pprt_eq_0",   (*obscure*)
   "OrderedGroup.pprt_eq_id",   (*obscure*)
   "OrderedGroup.pprt_mono",   (*obscure*)
   "Parity.even_nat_power",   (*obscure, somewhat prolilfic*)
   "Parity.power_eq_0_iff_number_of",
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
   "Ring_and_Field.divide_le_eq_1_neg",  (*obscure and prolific*)
   "Ring_and_Field.divide_le_eq_1_pos",  (*obscure and prolific*)
   "Ring_and_Field.divide_less_0_1_iff",
   "Ring_and_Field.divide_less_eq_1_neg",  (*obscure and prolific*)
   "Ring_and_Field.divide_less_eq_1_pos",  (*obscure and prolific*)
   "Ring_and_Field.eq_divide_eq_1", (*duplicate by symmetry*)
   "Ring_and_Field.field_mult_cancel_left",
   "Ring_and_Field.field_mult_cancel_right",
   "Ring_and_Field.inverse_le_iff_le_neg",
   "Ring_and_Field.inverse_le_iff_le",
   "Ring_and_Field.inverse_less_iff_less_neg",
   "Ring_and_Field.inverse_less_iff_less",
   "Ring_and_Field.le_divide_eq_1_neg", (*obscure and prolific*)
   "Ring_and_Field.le_divide_eq_1_pos", (*obscure and prolific*)
   "Ring_and_Field.less_divide_eq_1_neg", (*obscure and prolific*)
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
   "SetInterval.ivl_subset"];  (*excessive case analysis*)


(*These might be prolific but are probably OK, and min and max are basic.
   "Orderings.max_less_iff_conj", 
   "Orderings.min_less_iff_conj",
   "Orderings.min_max.below_inf.below_inf_conv",
   "Orderings.min_max.below_sup.above_sup_conv",
Very prolific and somewhat obscure:
   "Set.InterD",
   "Set.UnionI",
*)

(*** retrieve lemmas from clasimpset and atpset, may filter them ***)

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

(** a hash function from Term.term to int, and also a hash table **)
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

fun hash_thm  thm = hash_term (prop_of thm);

fun equal_thm (thm1,thm2) = Term.aconv(prop_of thm1, prop_of thm2);
(*Create a hash table for clauses, of the given size*)
fun mk_clause_table n =
      Polyhash.mkTable (hash_thm, equal_thm)
                       (n, HASH_CLAUSE);

(*Use a hash table to eliminate duplicates from xs*)
fun make_unique ht xs = 
      (app (ignore o Polyhash.peekInsert ht) xs;  Polyhash.listItems ht);

fun mem_thm thm [] = false
  | mem_thm thm ((thm',name)::thms_names) = equal_thm (thm,thm') orelse mem_thm thm thms_names;

fun insert_thms [] thms_names = thms_names
  | insert_thms ((thm,name)::thms_names) thms_names' =
      if mem_thm thm thms_names' then insert_thms thms_names thms_names' 
      else insert_thms thms_names ((thm,name)::thms_names');

fun display_thms [] = ()
  | display_thms ((name,thm)::nthms) = 
      let val nthm = name ^ ": " ^ (string_of_thm thm)
      in Output.debug nthm; display_thms nthms  end;
 

(* get lemmas from claset, simpset, atpset and extra supplied rules *)
fun get_clasimp_atp_lemmas ctxt user_thms = 
    let val claset_thms =
	    if !include_claset then
		map put_name_pair (ResAxioms.claset_rules_of_ctxt ctxt)
	    else []
	val simpset_thms = 
	    if !include_simpset then 
		map put_name_pair (ResAxioms.simpset_rules_of_ctxt ctxt)
	    else []
	val atpset_thms =
	    if !include_atpset then
		map put_name_pair (ResAxioms.atpset_rules_of_ctxt ctxt)
	    else []
	val _ = if !Output.show_debug_msgs then (Output.debug "ATP theorems: "; display_thms atpset_thms) else ()		 
	val user_rules = 
	    case user_thms of  (*use whitelist if there are no user-supplied rules*)
		[] => map (put_name_pair o ResAxioms.pairname) (!whitelist)
	      | _  => map put_name_pair user_thms
    in
	(claset_thms, simpset_thms, atpset_thms, user_rules)
    end;

(* remove lemmas that are banned from the backlist *)
fun blacklist_filter thms = 
    if !run_blacklist_filter then 
	let val banned = make_banned_test (map #1 thms)
	    fun ok (a,_) = not (banned a)
	in
	    filter ok thms
	end
    else
	thms;

(* filter axiom clauses, but keep supplied clauses and clauses in whitelist *)
fun get_relevant_clauses ctxt cls_thms white_cls goals =
    let val cls_thms_list = make_unique (mk_clause_table 2200) (List.concat (white_cls@cls_thms))
	val relevant_cls_thms_list = if !run_relevance_filter then ReduceAxiomsN.relevance_filter (ProofContext.theory_of ctxt) cls_thms_list goals else cls_thms_list
    in
        insert_thms (List.concat white_cls) relevant_cls_thms_list 
    end;

(***************************************************************)
(* ATP invocation methods setup                                *)
(***************************************************************)


(**** prover-specific format: TPTP ****)


fun cnf_hyps_thms ctxt = 
    let val ths = ProofContext.prems_of ctxt
    in fold (fold (insert Thm.eq_thm) o ResAxioms.skolem_thm) ths [] end;


(**** write to files ****)

datatype mode = Auto | Fol | Hol;

val linkup_logic_mode = ref Auto;

fun tptp_writer logic goals filename (axioms,classrels,arities) =
    if is_fol_logic logic 
    then ResClause.tptp_write_file goals filename (axioms, classrels, arities)
    else ResHolClause.tptp_write_file goals filename (axioms, classrels, arities);

fun dfg_writer logic goals filename (axioms,classrels,arities) =
    if is_fol_logic logic 
    then ResClause.dfg_write_file goals filename (axioms, classrels, arities)
    else ResHolClause.dfg_write_file goals filename (axioms, classrels, arities);

fun write_subgoal_file dfg mode ctxt conjectures user_thms n =
    let val conj_cls = make_clauses conjectures 
	val hyp_cls = cnf_hyps_thms ctxt
	val goal_cls = conj_cls@hyp_cls
	val (cla_thms,simp_thms,atp_thms,user_rules) = get_clasimp_atp_lemmas ctxt (map ResAxioms.pairname user_thms)
	val rm_black_cls = blacklist_filter (cla_thms@simp_thms@atp_thms) 
	val cla_simp_atp_clauses = ResAxioms.cnf_rules_pairs rm_black_cls
	val user_cls = ResAxioms.cnf_rules_pairs user_rules
	val axclauses_as_thms = get_relevant_clauses ctxt cla_simp_atp_clauses user_cls (map prop_of goal_cls)
	val thy = ProofContext.theory_of ctxt
	val prob_logic = case mode of Auto => problem_logic_goals [map prop_of goal_cls]
				    | Fol => FOL
				    | Hol => HOL
	val keep_types = if is_fol_logic prob_logic then !fol_keep_types else is_typed_hol ()
	val classrel_clauses = if keep_types then ResClause.classrel_clauses_thy thy else []
	val arity_clauses = if keep_types then ResClause.arity_clause_thy thy else []
        val writer = if dfg then dfg_writer else tptp_writer 
	val file = atp_input_file()
    in
	(writer prob_logic goal_cls file (axclauses_as_thms,classrel_clauses,arity_clauses);
	 Output.debug ("Writing to " ^ file);
	 file)
    end;


(**** remove tmp files ****)
fun cond_rm_tmp file = 
    if !keep_atp_input then Output.debug "ATP input kept..." 
    else if !destdir <> "" then Output.debug ("ATP input kept in directory " ^ (!destdir))
    else (Output.debug "deleting ATP inputs..."; OS.FileSys.remove file);


(****** setup ATPs as Isabelle methods ******)
fun atp_meth' tac ths ctxt = 
    Method.SIMPLE_METHOD' HEADGOAL
    (tac ctxt ths);

fun atp_meth tac ths ctxt = 
    let val thy = ProofContext.theory_of ctxt
	val _ = ResClause.init thy
	val _ = ResHolClause.init thy
    in
	atp_meth' tac ths ctxt
    end;

fun atp_method tac = Method.thms_ctxt_args (atp_meth tac);

(***************************************************************)
(* automatic ATP invocation                                    *)
(***************************************************************)

(* call prover with settings and problem file for the current subgoal *)
fun watcher_call_provers sign sg_terms (childin, childout, pid) =
  let
    fun make_atp_list [] n = []
      | make_atp_list (sg_term::xs) n =
          let
            val probfile = prob_pathname n
            val time = Int.toString (!time_limit)
          in
            Output.debug ("problem file in watcher_call_provers is " ^ probfile);
            (*options are separated by Watcher.setting_sep, currently #"%"*)
            if !prover = "spass"
            then
              let val spass = helper_path "SPASS_HOME" "SPASS"
                  val sopts =
   "-Auto%-SOS=1%-PGiven=0%-PProblem=0%-Splits=0%-FullRed=0%-DocProof%-TimeLimit=" ^ time
              in 
                  ("spass", spass, sopts, probfile) :: make_atp_list xs (n+1)
              end
            else if !prover = "vampire"
	    then 
              let val vampire = helper_path "VAMPIRE_HOME" "vampire"
                  val casc = if !time_limit > 70 then "--mode casc%" else ""
                  val vopts = casc ^ "-m 100000%-t " ^ time
              in
                  ("vampire", vampire, vopts, probfile) :: make_atp_list xs (n+1)
              end
      	     else if !prover = "E"
      	     then
	       let val Eprover = helper_path "E_HOME" "eproof"
	       in
		  ("E", Eprover, 
		     "--tptp-in%-l5%-xAuto%-tAuto%--silent%--cpu-limit=" ^ time, probfile) ::
		   make_atp_list xs (n+1)
	       end
	     else error ("Invalid prover name: " ^ !prover)
          end

    val atp_list = make_atp_list sg_terms 1
  in
    Watcher.callResProvers(childout,atp_list);
    Output.debug "Sent commands to watcher!"
  end

(*We write out problem files for each subgoal. Argument pf generates filenames,
  and allows the suppression of the suffix "_1" in problem-generation mode.
  FIXME: does not cope with &&, and it isn't easy because one could have multiple
  subgoals, each involving &&.*)
fun write_problem_files pf (ctxt,th)  =
  let val goals = Thm.prems_of th
      val _ = Output.debug ("number of subgoals = " ^ Int.toString (length goals))
      val (cla_thms,simp_thms,atp_thms,white_thms) = get_clasimp_atp_lemmas ctxt []
      val rm_blacklist_cls = blacklist_filter (cla_thms@simp_thms@atp_thms)
      val cla_simp_atp_clauses = ResAxioms.cnf_rules_pairs rm_blacklist_cls
      val axclauses = get_relevant_clauses ctxt cla_simp_atp_clauses (ResAxioms.cnf_rules_pairs white_thms) goals 
      val _ = Output.debug ("claset, simprules and atprules total clauses = " ^ 
                     Int.toString (length axclauses))
      val thy = ProofContext.theory_of ctxt
      fun get_neg_subgoals n =
	  if n=0 then []
	  else
	      let val st = Seq.hd (EVERY'
				       [rtac ccontr, ObjectLogic.atomize_tac, skolemize_tac] n th)
		  val negs = Option.valOf (metahyps_thms n st)
		  val negs_clauses = make_clauses negs
	      in
		  negs_clauses::(get_neg_subgoals (n - 1))
	      end
      val neg_subgoals = get_neg_subgoals (length goals) 
      val goals_logic = case !linkup_logic_mode of Auto => problem_logic_goals (map (map prop_of) neg_subgoals)
						 | Fol => FOL
						 | Hol => HOL
      val keep_types = if is_fol_logic goals_logic then !ResClause.keep_types else is_typed_hol ()
      val classrel_clauses = if keep_types then ResClause.classrel_clauses_thy thy else []
      val _ = Output.debug ("classrel clauses = " ^ Int.toString (length classrel_clauses))
      val arity_clauses = if keep_types then ResClause.arity_clause_thy thy else []
      val _ = Output.debug ("arity clauses = " ^ Int.toString (length arity_clauses))
      val writer = if !prover = "spass" then dfg_writer else tptp_writer 
      fun write_all [] _ = []
	| write_all (subgoal::subgoals) k =
	  (writer goals_logic subgoal (pf k) (axclauses,classrel_clauses,arity_clauses); pf k):: (write_all subgoals (k - 1))
      val thm_names = Array.fromList (map (#1 o #2) axclauses)
  in
      (write_all neg_subgoals (length goals), thm_names)
  end;

val last_watcher_pid = ref (NONE : (TextIO.instream * TextIO.outstream * 
                                    Posix.Process.pid * string list) option);

fun kill_last_watcher () =
    (case !last_watcher_pid of 
         NONE => ()
       | SOME (_, _, pid, files) => 
	  (Output.debug ("Killing old watcher, pid = " ^ string_of_pid pid);
	   Watcher.killWatcher pid;  
	   ignore (map (try OS.FileSys.remove) files)))
     handle OS.SysErr _ => Output.debug "Attempt to kill watcher failed";

(*writes out the current clasimpset to a tptp file;
  turns off xsymbol at start of function, restoring it at end    *)
val isar_atp = setmp print_mode [] 
 (fn (ctxt, th) =>
  if Thm.no_prems th then ()
  else
    let
      val _ = kill_last_watcher()
      val (files,thm_names) = write_problem_files prob_pathname (ctxt,th)
      val (childin, childout, pid) = Watcher.createWatcher (th, thm_names)
    in
      last_watcher_pid := SOME (childin, childout, pid, files);
      Output.debug ("problem files: " ^ space_implode ", " files); 
      Output.debug ("pid: " ^ string_of_pid pid);
      watcher_call_provers (sign_of_thm th) (Thm.prems_of th) (childin, childout, pid)
    end);

val isar_atp_writeonly = setmp print_mode [] 
      (fn (ctxt,th) =>
       if Thm.no_prems th then ()
       else 
         let val pf = if Thm.nprems_of th = 1 then probfile_nosuffix 
         	      else prob_pathname
         in ignore (write_problem_files pf (ctxt,th)) end);


(** the Isar toplevel hook **)

fun invoke_atp_ml (ctxt, goal) =
  let val thy = ProofContext.theory_of ctxt;
  in
    Output.debug ("subgoals in isar_atp:\n" ^ 
		  Pretty.string_of (ProofContext.pretty_term ctxt
		    (Logic.mk_conjunction_list (Thm.prems_of goal))));
    Output.debug ("current theory: " ^ Context.theory_name thy);
    hook_count := !hook_count +1;
    Output.debug ("in hook for time: " ^ Int.toString (!hook_count));
    ResClause.init thy;
    ResHolClause.init thy;
    if !destdir = "" andalso !time_limit > 0 then isar_atp (ctxt, goal)
    else isar_atp_writeonly (ctxt, goal)
  end;

val invoke_atp = Toplevel.no_timing o Toplevel.unknown_proof o Toplevel.keep
 (fn state =>
  let val (ctxt, (_, goal)) = Proof.get_goal (Toplevel.proof_of state)
  in  invoke_atp_ml (ctxt, goal)  end);

val call_atpP =
  OuterSyntax.command 
    "ProofGeneral.call_atp" 
    "call automatic theorem provers" 
    OuterKeyword.diag
    (Scan.succeed invoke_atp);

val _ = OuterSyntax.add_parsers [call_atpP];

end;
