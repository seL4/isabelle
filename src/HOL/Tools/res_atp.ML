(*  Author: Jia Meng, Cambridge University Computer Laboratory, NICTA
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

(*Currently unused, during debugging*)
signature RES_ATP =
sig
  val prover: string ref
  val custom_spass: string list ref
  val destdir: string ref
  val helper_path: string -> string -> string
  val problem_name: string ref
  val time_limit: int ref
  val set_prover: string -> unit

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
  val atp_method: (Proof.context -> thm list -> int -> tactic) ->
    Method.src -> Proof.context -> Proof.method
  val cond_rm_tmp: string -> unit
  val hol_full_types: unit -> unit
  val hol_partial_types: unit -> unit
  val hol_const_types_only: unit -> unit
  val hol_no_types: unit -> unit
  val hol_typ_level: unit -> ResHolClause.type_level
  val include_all: bool ref
  val run_relevance_filter: bool ref
  val run_blacklist_filter: bool ref
  val blacklist: string list ref
  val add_all : unit -> unit
  val add_claset : unit -> unit
  val add_simpset : unit -> unit
  val add_clasimp : unit -> unit
  val add_atpset : unit -> unit
  val rm_all : unit -> unit
  val rm_claset : unit -> unit
  val rm_simpset : unit -> unit
  val rm_atpset : unit -> unit
  val rm_clasimp : unit -> unit
  val is_fol_thms : thm list -> bool
end;

structure ResAtp =
struct

fun timestamp s = Output.debug (fn () => ("At " ^ Time.toString (Time.now()) ^ ": " ^ s));

(********************************************************************)
(* some settings for both background automatic ATP calling procedure*)
(* and also explicit ATP invocation methods                         *)
(********************************************************************)

(*** background linkup ***)
val call_atp = ref false;
val hook_count = ref 0;
val time_limit = ref 60;
val prover = ref "";

fun set_prover atp =
  case String.map Char.toLower atp of
      "e" =>
          (ReduceAxiomsN.max_new := 100;
           ReduceAxiomsN.theory_const := false;
           prover := "E")
    | "spass" =>
          (ReduceAxiomsN.max_new := 40;
           ReduceAxiomsN.theory_const := true;
           prover := "spass")
    | "vampire" =>
          (ReduceAxiomsN.max_new := 60;
           ReduceAxiomsN.theory_const := false;
           prover := "vampire")
    | _ => error ("No such prover: " ^ atp);

val _ = set_prover "E"; (* use E as the default prover *)

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
        in  if File.exists (File.explode_platform_path path) then path
            else error ("Could not find the file " ^ path)
        end;

fun probfile_nosuffix _ =
  if !destdir = "" then File.platform_path (File.tmp_path (Path.basic (!problem_name)))
  else if File.exists (File.explode_platform_path (!destdir))
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

fun atp_input_file () =
    let val file = !problem_name
    in
        if !destdir = "" then File.platform_path (File.tmp_path (Path.basic file))
        else if File.exists (File.explode_platform_path (!destdir))
        then !destdir ^ "/" ^ file
        else error ("No such directory: " ^ !destdir)
    end;

val include_all = ref true;
val include_simpset = ref false;
val include_claset = ref false;
val include_atpset = ref true;

(*Tests show that follow_defs gives VERY poor results with "include_all"*)
fun add_all() = (include_all:=true; ReduceAxiomsN.follow_defs := false);
fun rm_all() = include_all:=false;

fun add_simpset() = include_simpset:=true;
fun rm_simpset() = include_simpset:=false;

fun add_claset() = include_claset:=true;
fun rm_claset() = include_claset:=false;

fun add_clasimp() = (include_simpset:=true;include_claset:=true);
fun rm_clasimp() = (include_simpset:=false;include_claset:=false);

fun add_atpset() = include_atpset:=true;
fun rm_atpset() = include_atpset:=false;


(**** relevance filter ****)
val run_relevance_filter = ReduceAxiomsN.run_relevance_filter;
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
    if is_hol_fn tp then (upgrade_lg HOL lg, insert (op =) t seen) else (lg, insert (op =) t seen)
  | fn_lg (t as Free(f,tp)) (lg,seen) =
    if is_hol_fn tp then (upgrade_lg HOL lg, insert (op =) t seen) else (lg, insert (op =) t seen)
  | fn_lg (t as Var(f,tp)) (lg,seen) =
    if is_hol_fn tp then (upgrade_lg HOL lg,insert (op =) t seen) else (lg,insert (op =) t seen)
  | fn_lg (t as Abs(_,_,_)) (lg,seen) = (upgrade_lg HOLC lg,insert (op =) t seen)
  | fn_lg f _ = raise FN_LG(f);


fun term_lg [] (lg,seen) = (lg,seen)
  | term_lg (tm::tms) (FOL,seen) =
      let val (f,args) = strip_comb tm
          val (lg',seen') = if f mem seen then (FOL,seen)
                            else fn_lg f (FOL,seen)
      in
        if is_fol_logic lg' then ()
        else Output.debug (fn () => ("Found a HOL term: " ^ Display.raw_string_of_term f));
        term_lg (args@tms) (lg',seen')
      end
  | term_lg _ (lg,seen) = (lg,seen)

exception PRED_LG of term;

fun pred_lg (t as Const(P,tp)) (lg,seen)=
      if is_hol_pred tp then (upgrade_lg HOL lg, insert (op =) t seen)
      else (lg,insert (op =) t seen)
  | pred_lg (t as Free(P,tp)) (lg,seen) =
      if is_hol_pred tp then (upgrade_lg HOL lg, insert (op =) t seen)
      else (lg,insert (op =) t seen)
  | pred_lg (t as Var(_,_)) (lg,seen) = (upgrade_lg HOL lg, insert (op =) t seen)
  | pred_lg P _ = raise PRED_LG(P);


fun lit_lg (Const("Not",_) $ P) (lg,seen) = lit_lg P (lg,seen)
  | lit_lg P (lg,seen) =
      let val (pred,args) = strip_comb P
          val (lg',seen') = if pred mem seen then (lg,seen)
                            else pred_lg pred (lg,seen)
      in
        if is_fol_logic lg' then ()
        else Output.debug (fn () => ("Found a HOL predicate: " ^ Display.raw_string_of_term pred));
        term_lg args (lg',seen')
      end;

fun lits_lg [] (lg,seen) = (lg,seen)
  | lits_lg (lit::lits) (FOL,seen) =
      let val (lg,seen') = lit_lg lit (FOL,seen)
      in
        if is_fol_logic lg then ()
        else Output.debug (fn () => ("Found a HOL literal: " ^ Display.raw_string_of_term lit));
        lits_lg lits (lg,seen')
      end
  | lits_lg lits (lg,seen) = (lg,seen);

fun dest_disj_aux (Const("Trueprop",_) $ t) disjs = dest_disj_aux t disjs
  | dest_disj_aux (Const ("op |", _) $ t $ t') disjs = dest_disj_aux t (dest_disj_aux t' disjs)
  | dest_disj_aux t disjs = t::disjs;

fun dest_disj t = dest_disj_aux t [];

fun logic_of_clause tm = lits_lg (dest_disj tm);

fun logic_of_clauses [] (lg,seen) = (lg,seen)
  | logic_of_clauses (cls::clss) (FOL,seen) =
    let val (lg,seen') = logic_of_clause cls (FOL,seen)
        val _ =
          if is_fol_logic lg then ()
          else Output.debug (fn () => ("Found a HOL clause: " ^ Display.raw_string_of_term cls))
    in
        logic_of_clauses clss (lg,seen')
    end
  | logic_of_clauses (cls::clss) (lg,seen) = (lg,seen);

fun problem_logic_goals_aux [] (lg,seen) = lg
  | problem_logic_goals_aux (subgoal::subgoals) (lg,seen) =
    problem_logic_goals_aux subgoals (logic_of_clauses subgoal (lg,seen));

fun problem_logic_goals subgoals = problem_logic_goals_aux subgoals (FOL,[]);

fun is_fol_thms ths = ((fst(logic_of_clauses (map prop_of ths) (FOL,[]))) = FOL);

(***************************************************************)
(* Retrieving and filtering lemmas                             *)
(***************************************************************)

(*** white list and black list of lemmas ***)

(*The rule subsetI is frequently omitted by the relevance filter.*)
val whitelist = ref [subsetI];

(*Names of theorems (not theorem lists! See multi_blacklist below) to be banned.

  These theorems typically produce clauses that are prolific (match too many equality or
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
   "Finite_Set.min.f_below_strict_below.below_f_conv",        (*duplicates in Orderings.*)
   "Finite_Set.min.f_below_strict_below.strict_below_f_conv", (*duplicates in Orderings.*)
   "Fun.vimage_image_eq",   (*involves an existential quantifier*)
   "HOL.split_if_asm",     (*splitting theorem*)
   "HOL.split_if",         (*splitting theorem*)
   "HOL.All_def",          (*far worse than useless!!*)
   "IntDef.abs_split",
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
   "Nat.of_nat_0_eq_iff",
   "Nat.of_nat_eq_0_iff",
   "Nat.of_nat_le_0_iff",
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
   "Orderings.split_max",      (*splitting theorem*)
   "Orderings.split_min",      (*splitting theorem*)
   "Power.zero_less_power_abs_iff",
   "Product_Type.split_eta_SetCompr",   (*involves an existential quantifier*)
   "Product_Type.split_paired_Ball_Sigma",     (*splitting theorem*)
   "Product_Type.split_paired_Bex_Sigma",      (*splitting theorem*)
   "Product_Type.split_split_asm",             (*splitting theorem*)
   "Product_Type.split_split",                 (*splitting theorem*)
   "Product_Type.unit_abs_eta_conv",
   "Product_Type.unit_induct",
   "Relation.diagI",
   "Relation.Domain_def",   (*involves an existential quantifier*)
   "Relation.Image_def",   (*involves an existential quantifier*)
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
   "Set.Collect_bex_eq",   (*involves an existential quantifier*)
   "Set.Collect_ex_eq",   (*involves an existential quantifier*)
   "Set.Diff_eq_empty_iff", (*redundant with paramodulation*)
   "Set.Diff_insert0",
   "Set.empty_Union_conv",   (*redundant with paramodulation*)
   "Set.full_SetCompr_eq",   (*involves an existential quantifier*)
   "Set.image_Collect",      (*involves Collect and a boolean variable...*)
   "Set.image_def",          (*involves an existential quantifier*)
   "Set.Int_UNIV",  (*redundant with paramodulation*)
   "Set.Inter_iff", (*We already have InterI, InterE*)
   "Set.psubsetE",    (*too prolific and obscure*)
   "Set.psubsetI",
   "Set.singleton_insert_inj_eq'",
   "Set.singleton_insert_inj_eq",
   "Set.singletonD",  (*these two duplicate some "insert" lemmas*)
   "Set.singletonI",
   "Set.Un_empty", (*redundant with paramodulation*)
   "Set.UNION_def",   (*involves an existential quantifier*)
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

(*Hashing to detect duplicate and variant clauses, e.g. from the [iff] attribute*)

exception HASH_CLAUSE and HASH_STRING;

(*Reject theorems with names like "List.filter.filter_list_def" or
  "Accessible_Part.acc.defs", as these are definitions arising from packages.*)
fun is_package_def a =
  let val names = NameSpace.explode a
  in
     length names > 2 andalso
     not (hd names = "local") andalso
     String.isSuffix "_def" a  orelse  String.isSuffix "_defs" a
  end;

fun make_banned_test xs =
  let val ht = Polyhash.mkTable (Polyhash.hash_string, op =) (6000, HASH_STRING)
      fun banned s = isSome (Polyhash.peek ht s) orelse is_package_def s
  in  app (fn x => Polyhash.insert ht (x,())) (!blacklist);
      banned
  end;

(** a hash function from Term.term to int, and also a hash table **)
val xor_words = List.foldl Word.xorb 0w0;

fun hashw_term ((Const(c,_)), w) = Polyhash.hashw_string (c,w)
  | hashw_term ((Free(a,_)), w) = Polyhash.hashw_string (a,w)
  | hashw_term ((Var(_,_)), w) = w
  | hashw_term ((Bound i), w) = Polyhash.hashw_int(i,w)
  | hashw_term ((Abs(_,_,t)), w) = hashw_term (t, w)
  | hashw_term ((P$Q), w) = hashw_term (Q, (hashw_term (P, w)));

fun hash_literal (Const("Not",_)$P) = Word.notb(hashw_term(P,0w0))
  | hash_literal P = hashw_term(P,0w0);

fun hash_term t = Word.toIntX (xor_words (map hash_literal (dest_disj t)));

fun equal_thm (thm1,thm2) = Term.aconv(prop_of thm1, prop_of thm2);

(*Create a hash table for clauses, of the given size*)
fun mk_clause_table n =
      Polyhash.mkTable (hash_term o prop_of, equal_thm)
                       (n, HASH_CLAUSE);

(*Use a hash table to eliminate duplicates from xs. Argument is a list of
  (thm * (string * int)) tuples. The theorems are hashed into the table. *)
fun make_unique xs =
  let val ht = mk_clause_table 7000
  in
      Output.debug (fn () => ("make_unique gets " ^ Int.toString (length xs) ^ " clauses"));
      app (ignore o Polyhash.peekInsert ht) xs;
      Polyhash.listItems ht
  end;

(*Remove existing axiom clauses from the conjecture clauses, as this can dramatically
  boost an ATP's performance (for some reason)*)
fun subtract_cls c_clauses ax_clauses =
  let val ht = mk_clause_table 2200
      fun known x = isSome (Polyhash.peek ht x)
  in
      app (ignore o Polyhash.peekInsert ht) ax_clauses;
      filter (not o known) c_clauses
  end;

(*Filter axiom clauses, but keep supplied clauses and clauses in whitelist.
  Duplicates are removed later.*)
fun get_relevant_clauses thy cls_thms white_cls goals =
  white_cls @ (ReduceAxiomsN.relevance_filter thy cls_thms goals);

fun all_valid_thms ctxt =
  PureThy.thms_containing (ProofContext.theory_of ctxt) ([], []) @
  filter (ProofContext.valid_thms ctxt)
    (FactIndex.find (ProofContext.fact_index_of ctxt) ([], []));

fun multi_name a (th, (n,pairs)) =
  (n+1, (a ^ "(" ^ Int.toString n ^ ")", th) :: pairs)

fun add_multi_names_aux ((a, []), pairs) = pairs
  | add_multi_names_aux ((a, [th]), pairs) = (a,th)::pairs
  | add_multi_names_aux ((a, ths), pairs) = #2 (foldl (multi_name a) (1,pairs) ths);

val multi_blacklist =
  ["Set.ball_simps", "Set.bex_simps",  (*quantifier rewriting: useless*)
   "Set.disjoint_insert", "Set.insert_disjoint", "Set.Inter_UNIV_conv"];

val multi_base_blacklist =
  ["defs","select_defs","update_defs","induct","inducts","split","splits","split_asm"];

(*Ignore blacklisted theorem lists*)
fun add_multi_names ((a, ths), pairs) =
  if a mem_string multi_blacklist orelse (Sign.base_name a) mem_string multi_base_blacklist
  then pairs
  else add_multi_names_aux ((a, ths), pairs);

fun is_multi (a, ths) = length ths > 1 orelse String.isSuffix ".axioms" a;

(*The single theorems go BEFORE the multiple ones*)
fun name_thm_pairs ctxt =
  let val (mults,singles) = List.partition is_multi (all_valid_thms ctxt)
  in  foldl add_multi_names (foldl add_multi_names [] mults) singles  end;

fun check_named ("",th) = (warning ("No name for theorem " ^ string_of_thm th); false)
  | check_named (_,th) = true;

fun display_thm (name,th) = Output.debug (fn () => name ^ ": " ^ string_of_thm th);

(* get lemmas from claset, simpset, atpset and extra supplied rules *)
fun get_clasimp_atp_lemmas ctxt user_thms =
  let val included_thms =
        if !include_all
        then (tap (fn ths => Output.debug
                     (fn () => ("Including all " ^ Int.toString (length ths) ^ " theorems")))
                  (name_thm_pairs ctxt))
        else
        let val claset_thms =
                if !include_claset then ResAxioms.claset_rules_of ctxt
                else []
            val simpset_thms =
                if !include_simpset then ResAxioms.simpset_rules_of ctxt
                else []
            val atpset_thms =
                if !include_atpset then ResAxioms.atpset_rules_of ctxt
                else []
            val _ = (Output.debug (fn () => "ATP theorems: ");  app display_thm atpset_thms)
        in  claset_thms @ simpset_thms @ atpset_thms  end
      val user_rules = filter check_named
                         (map (ResAxioms.pairname)
                           (if null user_thms then !whitelist else user_thms))
  in
      (filter check_named included_thms, user_rules)
  end;

(*Remove lemmas that are banned from the backlist. Also remove duplicates. *)
fun blacklist_filter ths =
  if !run_blacklist_filter then
      let val banned = make_banned_test (map #1 ths)
          fun ok (a,_) = not (banned a)
          val (good,bad) = List.partition ok ths
      in
        Output.debug (fn () => "blacklist filter gets " ^ Int.toString (length ths) ^ " theorems");
        Output.debug (fn () => "filtered: " ^ space_implode ", " (map #1 bad));
        Output.debug (fn () => "...and returns " ^ Int.toString (length good));
        good 
      end
  else ths;

(***************************************************************)
(* Type Classes Present in the Axiom or Conjecture Clauses     *)
(***************************************************************)

fun setinsert (x,s) = Symtab.update (x,()) s;

fun add_classes (sorts, cset) = foldl setinsert cset (List.concat sorts);

(*Remove this trivial type class*)
fun delete_type cset = Symtab.delete_safe "HOL.type" cset;

fun tvar_classes_of_terms ts =
  let val sorts_list = map (map #2 o term_tvars) ts
  in  Symtab.keys (delete_type (foldl add_classes Symtab.empty sorts_list))  end;

fun tfree_classes_of_terms ts =
  let val sorts_list = map (map #2 o term_tfrees) ts
  in  Symtab.keys (delete_type (foldl add_classes Symtab.empty sorts_list))  end;

(*fold type constructors*)
fun fold_type_consts f (Type (a, Ts)) x = fold (fold_type_consts f) Ts (f (a,x))
  | fold_type_consts f T x = x;

val add_type_consts_in_type = fold_type_consts setinsert;

(*Type constructors used to instantiate overloaded constants are the only ones needed.*)
fun add_type_consts_in_term thy =
  let val const_typargs = Sign.const_typargs thy
      fun add_tcs (Const cT) x = fold add_type_consts_in_type (const_typargs cT) x
        | add_tcs (Abs (_, T, u)) x = add_tcs u x
        | add_tcs (t $ u) x = add_tcs t (add_tcs u x)
        | add_tcs _ x = x
  in  add_tcs  end

fun type_consts_of_terms thy ts =
  Symtab.keys (fold (add_type_consts_in_term thy) ts Symtab.empty);


(***************************************************************)
(* ATP invocation methods setup                                *)
(***************************************************************)

fun cnf_hyps_thms ctxt =
    let val ths = Assumption.prems_of ctxt
    in fold (fold (insert Thm.eq_thm) o ResAxioms.skolem_thm) ths [] end;

(*Translation mode can be auto-detected, or forced to be first-order or higher-order*)
datatype mode = Auto | Fol | Hol;

val linkup_logic_mode = ref Auto;

(*Ensures that no higher-order theorems "leak out"*)
fun restrict_to_logic logic cls =
  if is_fol_logic logic then filter (Meson.is_fol_term o prop_of o fst) cls
                        else cls;

(**** Predicates to detect unwanted clauses (prolific or likely to cause unsoundness) ****)

(** Too general means, positive equality literal with a variable X as one operand,
  when X does not occur properly in the other operand. This rules out clearly
  inconsistent clauses such as V=a|V=b, though it by no means guarantees soundness. **)

fun occurs ix =
    let fun occ(Var (jx,_)) = (ix=jx)
          | occ(t1$t2)      = occ t1 orelse occ t2
          | occ(Abs(_,_,t)) = occ t
          | occ _           = false
    in occ end;

fun is_recordtype T = not (null (RecordPackage.dest_recTs T));

(*Unwanted equalities include
  (1) those between a variable that does not properly occur in the second operand,
  (2) those between a variable and a record, since these seem to be prolific "cases" thms
*)
fun too_general_eqterms (Var (ix,T), t) = not (occurs ix t) orelse is_recordtype T
  | too_general_eqterms _ = false;

fun too_general_equality (Const ("op =", _) $ x $ y) =
      too_general_eqterms (x,y) orelse too_general_eqterms(y,x)
  | too_general_equality _ = false;

(* tautologous? *)
fun is_taut (Const ("Trueprop", _) $ Const ("True", _)) = true
  | is_taut _ = false;

(*True if the term contains a variable whose (atomic) type is in the given list.*)
fun has_typed_var tycons =
  let fun var_tycon (Var (_, Type(a,_))) = a mem_string tycons
        | var_tycon _ = false
  in  exists var_tycon o term_vars  end;

(*Clauses are forbidden to contain variables of these types. The typical reason is that
  they lead to unsoundness. Note that "unit" satisfies numerous equations like ?X=().
  The resulting clause will have no type constraint, yielding false proofs. Even "bool"
  leads to many unsound proofs, though (obviously) only for higher-order problems.*)
val unwanted_types = ref ["Product_Type.unit","bool"];

fun unwanted t =
    is_taut t orelse has_typed_var (!unwanted_types) t orelse
    forall too_general_equality (dest_disj t);

(*Clauses containing variables of type "unit" or "bool" are unlikely to be useful and
  likely to lead to unsound proofs.*)
fun remove_unwanted_clauses cls = filter (not o unwanted o prop_of o fst) cls;

fun tptp_writer logic goals filename (axioms,classrels,arities) user_lemmas =
    if is_fol_logic logic
    then ResClause.tptp_write_file goals filename (axioms, classrels, arities)
    else ResHolClause.tptp_write_file goals filename (axioms, classrels, arities) user_lemmas;

fun dfg_writer logic goals filename (axioms,classrels,arities) user_lemmas =
    if is_fol_logic logic
    then ResClause.dfg_write_file goals filename (axioms, classrels, arities)
    else ResHolClause.dfg_write_file goals filename (axioms, classrels, arities) user_lemmas;

(*Called by the oracle-based methods declared in res_atp_methods.ML*)
fun write_subgoal_file dfg mode ctxt conjectures user_thms n =
    let val conj_cls = make_clauses conjectures
                         |> ResAxioms.assume_abstract_list |> Meson.finish_cnf
        val hyp_cls = cnf_hyps_thms ctxt
        val goal_cls = conj_cls@hyp_cls
        val goal_tms = map prop_of goal_cls
        val logic = case mode of
                            Auto => problem_logic_goals [goal_tms]
                          | Fol => FOL
                          | Hol => HOL
        val (included_thms,user_rules) = get_clasimp_atp_lemmas ctxt user_thms
        val cla_simp_atp_clauses = included_thms |> blacklist_filter
                                     |> ResAxioms.cnf_rules_pairs |> make_unique
                                     |> restrict_to_logic logic
                                     |> remove_unwanted_clauses
        val user_cls = ResAxioms.cnf_rules_pairs user_rules
        val thy = ProofContext.theory_of ctxt
        val axclauses = make_unique (get_relevant_clauses thy cla_simp_atp_clauses user_cls goal_tms)
        val subs = tfree_classes_of_terms goal_tms
        and axtms = map (prop_of o #1) axclauses
        val supers = tvar_classes_of_terms axtms
        and tycons = type_consts_of_terms thy (goal_tms@axtms)
        (*TFrees in conjecture clauses; TVars in axiom clauses*)
        val classrel_clauses = ResClause.make_classrel_clauses thy subs supers
        val arity_clauses = ResClause.arity_clause_thy thy tycons supers
        val writer = if dfg then dfg_writer else tptp_writer
        and file = atp_input_file()
        and user_lemmas_names = map #1 user_rules
    in
        writer logic goal_cls file (axclauses,classrel_clauses,arity_clauses) user_lemmas_names;
        Output.debug (fn () => "Writing to " ^ file);
        file
    end;


(**** remove tmp files ****)
fun cond_rm_tmp file =
    if !Output.debugging orelse !destdir <> ""
    then Output.debug (fn () => "ATP input kept...")
    else OS.FileSys.remove file;


(****** setup ATPs as Isabelle methods ******)

fun atp_meth tac ths ctxt =
    let val thy = ProofContext.theory_of ctxt
        val _ = ResClause.init thy
        val _ = ResHolClause.init thy
    in Method.SIMPLE_METHOD' (tac ctxt ths) end;

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
            Output.debug (fn () => "problem file in watcher_call_provers is " ^ probfile);
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
                  val vopts = "--mode casc%-t " ^ time  (*what about -m 100000?*)
              in
                  ("vampire", vampire, vopts, probfile) :: make_atp_list xs (n+1)
              end
             else if !prover = "E"
             then
               let val Eprover = helper_path "E_HOME" "eproof"
               in
                  ("E", Eprover,
                     "--tstp-in%--tstp-out%-l5%-xAutoDev%-tAutoDev%--silent%--cpu-limit=" ^ time, probfile) ::
                   make_atp_list xs (n+1)
               end
             else error ("Invalid prover name: " ^ !prover)
          end

    val atp_list = make_atp_list sg_terms 1
  in
    Watcher.callResProvers(childout,atp_list);
    Output.debug (fn () => "Sent commands to watcher!")
  end

(*For debugging the generated set of theorem names*)
fun trace_vector fname =
  let val path = File.explode_platform_path (fname ^ "_thm_names")
  in  Vector.app (File.append path o (fn s => s ^ "\n"))  end;

(*We write out problem files for each subgoal. Argument probfile generates filenames,
  and allows the suppression of the suffix "_1" in problem-generation mode.
  FIXME: does not cope with &&, and it isn't easy because one could have multiple
  subgoals, each involving &&.*)
fun write_problem_files probfile (ctxt,th)  =
  let val goals = Thm.prems_of th
      val _ = Output.debug (fn () => "number of subgoals = " ^ Int.toString (length goals))
      val thy = ProofContext.theory_of ctxt
      fun get_neg_subgoals [] _ = []
        | get_neg_subgoals (gl::gls) n = #1 (ResAxioms.neg_conjecture_clauses th n) :: 
                                         get_neg_subgoals gls (n+1)
      val goal_cls = get_neg_subgoals goals 1
      val logic = case !linkup_logic_mode of
                Auto => problem_logic_goals (map ((map prop_of)) goal_cls)
              | Fol => FOL
              | Hol => HOL
      val (included_thms,white_thms) = get_clasimp_atp_lemmas ctxt []
      val included_cls = included_thms |> blacklist_filter
                                       |> ResAxioms.cnf_rules_pairs |> make_unique
                                       |> restrict_to_logic logic
                                       |> remove_unwanted_clauses
      val _ = Output.debug (fn () => "included clauses = " ^ Int.toString(length included_cls))
      val white_cls = ResAxioms.cnf_rules_pairs white_thms
      (*clauses relevant to goal gl*)
      val axcls_list = map (fn ngcls => get_relevant_clauses thy included_cls white_cls (map prop_of ngcls)) goal_cls
      val _ = app (fn axcls => Output.debug (fn () => "filtered clauses = " ^ Int.toString(length axcls)))
                  axcls_list
      val writer = if !prover = "spass" then dfg_writer else tptp_writer
      fun write_all [] [] _ = []
        | write_all (ccls::ccls_list) (axcls::axcls_list) k =
            let val fname = probfile k
                val _ = Output.debug (fn () => "About to write file " ^ fname)
                val axcls = make_unique axcls
                val _ = Output.debug (fn () => "Conjecture Clauses (before duplicate removal)")
                val _ = app (fn th => Output.debug (fn _ => string_of_thm th)) ccls
                val ccls = subtract_cls ccls axcls
                val _ = Output.debug (fn () => "Conjecture Clauses (AFTER duplicate removal)")
                val _ = app (fn th => Output.debug (fn _ => string_of_thm th)) ccls
                val ccltms = map prop_of ccls
                and axtms = map (prop_of o #1) axcls
                val subs = tfree_classes_of_terms ccltms
                and supers = tvar_classes_of_terms axtms
                and tycons = type_consts_of_terms thy (ccltms@axtms)
                (*TFrees in conjecture clauses; TVars in axiom clauses*)
                val classrel_clauses = ResClause.make_classrel_clauses thy subs supers
                val _ = Output.debug (fn () => "classrel clauses = " ^ Int.toString (length classrel_clauses))
                val arity_clauses = ResClause.arity_clause_thy thy tycons supers
                val _ = Output.debug (fn () => "arity clauses = " ^ Int.toString (length arity_clauses))
                val clnames = writer logic ccls fname (axcls,classrel_clauses,arity_clauses) []
                val thm_names = Vector.fromList clnames
                val _ = if !Output.debugging then trace_vector fname thm_names else ()
            in  (thm_names,fname) :: write_all ccls_list axcls_list (k+1)  end
      val (thm_names_list, filenames) = ListPair.unzip (write_all goal_cls axcls_list 1)
  in
      (filenames, thm_names_list)
  end;

val last_watcher_pid = ref (NONE : (TextIO.instream * TextIO.outstream *
                                    Posix.Process.pid * string list) option);

fun kill_last_watcher () =
    (case !last_watcher_pid of
         NONE => ()
       | SOME (_, _, pid, files) =>
          (Output.debug (fn () => "Killing old watcher, pid = " ^ string_of_pid pid);
           Watcher.killWatcher pid;
           ignore (map (try cond_rm_tmp) files)))
     handle OS.SysErr _ => Output.debug (fn () => "Attempt to kill watcher failed");

(*writes out the current problems and calls ATPs*)
fun isar_atp (ctxt, th) =
  if Thm.no_prems th then ()
  else
    let
      val _ = kill_last_watcher()
      val (files,thm_names_list) = write_problem_files prob_pathname (ctxt,th)
      val (childin, childout, pid) = Watcher.createWatcher (ctxt, th, thm_names_list)
    in
      last_watcher_pid := SOME (childin, childout, pid, files);
      Output.debug (fn () => "problem files: " ^ space_implode ", " files);
      Output.debug (fn () => "pid: " ^ string_of_pid pid);
      watcher_call_provers (sign_of_thm th) (Thm.prems_of th) (childin, childout, pid)
    end;

(*For ML scripts, and primarily, for debugging*)
fun callatp () =
  let val th = topthm()
      val ctxt = ProofContext.init (theory_of_thm th)
  in  isar_atp (ctxt, th)  end;

val isar_atp_writeonly = setmp print_mode []
      (fn (ctxt,th) =>
       if Thm.no_prems th then ()
       else
         let val probfile = if Thm.nprems_of th = 1 then probfile_nosuffix
                            else prob_pathname
         in ignore (write_problem_files probfile (ctxt,th)) end);


(** the Isar toplevel hook **)

fun invoke_atp_ml (ctxt, goal) =
  let val thy = ProofContext.theory_of ctxt;
  in
    Output.debug (fn () => "subgoals in isar_atp:\n" ^
                  Pretty.string_of (ProofContext.pretty_term ctxt
                    (Logic.mk_conjunction_list (Thm.prems_of goal))));
    Output.debug (fn () => "current theory: " ^ Context.theory_name thy);
    inc hook_count;
    Output.debug (fn () => "in hook for time: " ^ Int.toString (!hook_count));
    ResClause.init thy;
    ResHolClause.init thy;
    if !time_limit > 0 then isar_atp (ctxt, goal)
    else (warning ("Writing problem file only: " ^ !problem_name); 
          isar_atp_writeonly (ctxt, goal))
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
