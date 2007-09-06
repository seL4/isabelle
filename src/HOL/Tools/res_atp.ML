(*  Author: Jia Meng, Cambridge University Computer Laboratory, NICTA
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

signature RES_ATP =
sig
  val prover: ResReconstruct.atp ref
  val destdir: string ref
  val helper_path: string -> string -> string
  val problem_name: string ref
  val time_limit: int ref
  val set_prover: string -> unit

  datatype mode = Auto | Fol | Hol
  val linkup_logic_mode : mode ref
  val write_subgoal_file: bool -> mode -> Proof.context -> thm list -> thm list -> int -> string
  val cond_rm_tmp: string -> unit
  val include_all: bool ref
  val run_relevance_filter: bool ref
  val run_blacklist_filter: bool ref
  val theory_const : bool ref
  val pass_mark    : real ref
  val convergence  : real ref
  val max_new      : int ref
  val follow_defs  : bool ref
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
  val tvar_classes_of_terms : term list -> string list
  val tfree_classes_of_terms : term list -> string list
  val type_consts_of_terms : theory -> term list -> string list
end;

structure ResAtp: RES_ATP =
struct

structure Recon = ResReconstruct;

fun timestamp s = Output.debug (fn () => ("At " ^ Time.toString (Time.now()) ^ ": " ^ s));

(********************************************************************)
(* some settings for both background automatic ATP calling procedure*)
(* and also explicit ATP invocation methods                         *)
(********************************************************************)

(*** background linkup ***)
val run_blacklist_filter = ref true;
val time_limit = ref 60;
val prover = ref Recon.E;

(*** relevance filter parameters ***)
val run_relevance_filter = ref true;
val theory_const = ref true;
val pass_mark = ref 0.5;
val convergence = ref 3.2;    (*Higher numbers allow longer inference chains*)
val max_new = ref 60;         (*Limits how many clauses can be picked up per stage*)
val follow_defs = ref false;  (*Follow definitions. Makes problems bigger.*)

fun set_prover atp =
  case String.map Char.toLower atp of
      "e" =>
          (max_new := 100;
           theory_const := false;
           prover := Recon.E)
    | "spass" =>
          (max_new := 40;
           theory_const := true;
           prover := Recon.SPASS)
    | "vampire" =>
          (max_new := 60;
           theory_const := false;
           prover := Recon.Vampire)
    | _ => error ("No such prover: " ^ atp);

val _ = set_prover "E"; (* use E as the default prover *)

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
fun add_all() = (include_all:=true; follow_defs := false);
fun rm_all() = include_all:=false;

fun add_simpset() = include_simpset:=true;
fun rm_simpset() = include_simpset:=false;

fun add_claset() = include_claset:=true;
fun rm_claset() = include_claset:=false;

fun add_clasimp() = (include_simpset:=true;include_claset:=true);
fun rm_clasimp() = (include_simpset:=false;include_claset:=false);

fun add_atpset() = include_atpset:=true;
fun rm_atpset() = include_atpset:=false;


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
(* Relevance Filtering                                         *)
(***************************************************************)

(*A surprising number of theorems contain only a few significant constants.
  These include all induction rules, and other general theorems. Filtering
  theorems in clause form reveals these complexities in the form of Skolem 
  functions. If we were instead to filter theorems in their natural form,
  some other method of measuring theorem complexity would become necessary.*)

fun log_weight2 (x:real) = 1.0 + 2.0/Math.ln (x+1.0);

(*The default seems best in practice. A constant function of one ignores
  the constant frequencies.*)
val weight_fn = ref log_weight2;


(*Including equality in this list might be expected to stop rules like subset_antisym from
  being chosen, but for some reason filtering works better with them listed. The
  logical signs All, Ex, &, and --> are omitted because any remaining occurrrences
  must be within comprehensions.*)
val standard_consts = ["Trueprop","==>","all","==","op |","Not","op ="];


(*** constants with types ***)

(*An abstraction of Isabelle types*)
datatype const_typ =  CTVar | CType of string * const_typ list

(*Is the second type an instance of the first one?*)
fun match_type (CType(con1,args1)) (CType(con2,args2)) = 
      con1=con2 andalso match_types args1 args2
  | match_type CTVar _ = true
  | match_type _ CTVar = false
and match_types [] [] = true
  | match_types (a1::as1) (a2::as2) = match_type a1 a2 andalso match_types as1 as2;

(*Is there a unifiable constant?*)
fun uni_mem gctab (c,c_typ) =
  case Symtab.lookup gctab c of
      NONE => false
    | SOME ctyps_list => exists (match_types c_typ) ctyps_list;
  
(*Maps a "real" type to a const_typ*)
fun const_typ_of (Type (c,typs)) = CType (c, map const_typ_of typs) 
  | const_typ_of (TFree _) = CTVar
  | const_typ_of (TVar _) = CTVar

(*Pairs a constant with the list of its type instantiations (using const_typ)*)
fun const_with_typ thy (c,typ) = 
    let val tvars = Sign.const_typargs thy (c,typ)
    in (c, map const_typ_of tvars) end
    handle TYPE _ => (c,[]);   (*Variable (locale constant): monomorphic*)   

(*Add a const/type pair to the table, but a [] entry means a standard connective,
  which we ignore.*)
fun add_const_typ_table ((c,ctyps), tab) =
  Symtab.map_default (c, [ctyps]) (fn [] => [] | ctyps_list => insert (op =) ctyps ctyps_list) 
    tab;

(*Free variables are included, as well as constants, to handle locales*)
fun add_term_consts_typs_rm thy (Const(c, typ), tab) =
      add_const_typ_table (const_with_typ thy (c,typ), tab) 
  | add_term_consts_typs_rm thy (Free(c, typ), tab) =
      add_const_typ_table (const_with_typ thy (c,typ), tab) 
  | add_term_consts_typs_rm thy (t $ u, tab) =
      add_term_consts_typs_rm thy (t, add_term_consts_typs_rm thy (u, tab))
  | add_term_consts_typs_rm thy (Abs(_,_,t), tab) = add_term_consts_typs_rm thy (t, tab)
  | add_term_consts_typs_rm thy (_, tab) = tab;

(*The empty list here indicates that the constant is being ignored*)
fun add_standard_const (s,tab) = Symtab.update (s,[]) tab;

val null_const_tab : const_typ list list Symtab.table = 
    foldl add_standard_const Symtab.empty standard_consts;

fun get_goal_consts_typs thy = foldl (add_term_consts_typs_rm thy) null_const_tab;

(*Inserts a dummy "constant" referring to the theory name, so that relevance
  takes the given theory into account.*)
fun const_prop_of th =
 if !theory_const then
  let val name = Context.theory_name (theory_of_thm th)
      val t = Const (name ^ ". 1", HOLogic.boolT)
  in  t $ prop_of th  end
 else prop_of th;

(**** Constant / Type Frequencies ****)

(*A two-dimensional symbol table counts frequencies of constants. It's keyed first by
  constant name and second by its list of type instantiations. For the latter, we need
  a linear ordering on type const_typ list.*)
  
local

fun cons_nr CTVar = 0
  | cons_nr (CType _) = 1;

in

fun const_typ_ord TU =
  case TU of
    (CType (a, Ts), CType (b, Us)) =>
      (case fast_string_ord(a,b) of EQUAL => dict_ord const_typ_ord (Ts,Us) | ord => ord)
  | (T, U) => int_ord (cons_nr T, cons_nr U);

end;

structure CTtab = TableFun(type key = const_typ list val ord = dict_ord const_typ_ord);

fun count_axiom_consts thy ((thm,_), tab) = 
  let fun count_const (a, T, tab) =
	let val (c, cts) = const_with_typ thy (a,T)
	in  (*Two-dimensional table update. Constant maps to types maps to count.*)
	    Symtab.map_default (c, CTtab.empty) 
	                       (CTtab.map_default (cts,0) (fn n => n+1)) tab
	end
      fun count_term_consts (Const(a,T), tab) = count_const(a,T,tab)
	| count_term_consts (Free(a,T), tab) = count_const(a,T,tab)
	| count_term_consts (t $ u, tab) =
	    count_term_consts (t, count_term_consts (u, tab))
	| count_term_consts (Abs(_,_,t), tab) = count_term_consts (t, tab)
	| count_term_consts (_, tab) = tab
  in  count_term_consts (const_prop_of thm, tab)  end;


(**** Actual Filtering Code ****)

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun const_frequency ctab (c, cts) =
  let val pairs = CTtab.dest (the (Symtab.lookup ctab c))
      fun add ((cts',m), n) = if match_types cts cts' then m+n else n
  in  List.foldl add 0 pairs  end;

(*Add in a constant's weight, as determined by its frequency.*)
fun add_ct_weight ctab ((c,T), w) =
  w + !weight_fn (real (const_frequency ctab (c,T)));

(*Relevant constants are weighted according to frequency, 
  but irrelevant constants are simply counted. Otherwise, Skolem functions,
  which are rare, would harm a clause's chances of being picked.*)
fun clause_weight ctab gctyps consts_typs =
    let val rel = filter (uni_mem gctyps) consts_typs
        val rel_weight = List.foldl (add_ct_weight ctab) 0.0 rel
    in
	rel_weight / (rel_weight + real (length consts_typs - length rel))
    end;
    
(*Multiplies out to a list of pairs: 'a * 'b list -> ('a * 'b) list -> ('a * 'b) list*)
fun add_expand_pairs (x,ys) xys = foldl (fn (y,acc) => (x,y)::acc) xys ys;

fun consts_typs_of_term thy t = 
  let val tab = add_term_consts_typs_rm thy (t, null_const_tab)
  in  Symtab.fold add_expand_pairs tab []  end;

fun pair_consts_typs_axiom thy (thm,name) =
    ((thm,name), (consts_typs_of_term thy (const_prop_of thm)));

exception ConstFree;
fun dest_ConstFree (Const aT) = aT
  | dest_ConstFree (Free aT) = aT
  | dest_ConstFree _ = raise ConstFree;

(*Look for definitions of the form f ?x1 ... ?xn = t, but not reversed.*)
fun defines thy (thm,(name,n)) gctypes =
    let val tm = prop_of thm
	fun defs lhs rhs =
            let val (rator,args) = strip_comb lhs
		val ct = const_with_typ thy (dest_ConstFree rator)
            in  forall is_Var args andalso uni_mem gctypes ct andalso
                Term.add_vars rhs [] subset Term.add_vars lhs []
            end
	    handle ConstFree => false
    in    
	case tm of Const ("Trueprop",_) $ (Const("op =",_) $ lhs $ rhs) => 
		   defs lhs rhs andalso
		   (Output.debug (fn () => "Definition found: " ^ name ^ "_" ^ Int.toString n); true)
		 | _ => false
    end;

type annotd_cls = (thm * (string * int)) * ((string * const_typ list) list);
       
(*For a reverse sort, putting the largest values first.*)
fun compare_pairs ((_,w1),(_,w2)) = Real.compare (w2,w1);

(*Limit the number of new clauses, to prevent runaway acceptance.*)
fun take_best (newpairs : (annotd_cls*real) list) =
  let val nnew = length newpairs
  in
    if nnew <= !max_new then (map #1 newpairs, [])
    else 
      let val cls = sort compare_pairs newpairs
          val accepted = List.take (cls, !max_new)
      in
        Output.debug (fn () => ("Number of candidates, " ^ Int.toString nnew ^ 
		       ", exceeds the limit of " ^ Int.toString (!max_new)));
        Output.debug (fn () => ("Effective pass mark: " ^ Real.toString (#2 (List.last accepted))));
        Output.debug (fn () => "Actually passed: " ^
          space_implode ", " (map (fn (((_,(name,_)),_),_) => name) accepted));

	(map #1 accepted, map #1 (List.drop (cls, !max_new)))
      end
  end;

fun relevant_clauses thy ctab p rel_consts =
  let fun relevant ([],_) [] = [] : (thm * (string * int)) list  (*Nothing added this iteration*)
	| relevant (newpairs,rejects) [] =
	    let val (newrels,more_rejects) = take_best newpairs
		val new_consts = List.concat (map #2 newrels)
		val rel_consts' = foldl add_const_typ_table rel_consts new_consts
		val newp = p + (1.0-p) / !convergence
	    in
              Output.debug (fn () => ("relevant this iteration: " ^ Int.toString (length newrels)));
	       (map #1 newrels) @ 
	       (relevant_clauses thy ctab newp rel_consts' (more_rejects@rejects))
	    end
	| relevant (newrels,rejects) ((ax as (clsthm as (_,(name,n)),consts_typs)) :: axs) =
	    let val weight = clause_weight ctab rel_consts consts_typs
	    in
	      if p <= weight orelse (!follow_defs andalso defines thy clsthm rel_consts)
	      then (Output.debug (fn () => (name ^ " clause " ^ Int.toString n ^ 
	                                    " passes: " ^ Real.toString weight));
	            relevant ((ax,weight)::newrels, rejects) axs)
	      else relevant (newrels, ax::rejects) axs
	    end
    in  Output.debug (fn () => ("relevant_clauses, current pass mark = " ^ Real.toString p));
        relevant ([],[]) 
    end;
	
fun relevance_filter thy axioms goals = 
 if !run_relevance_filter andalso !pass_mark >= 0.1
 then
  let val _ = Output.debug (fn () => "Start of relevance filtering");
      val const_tab = List.foldl (count_axiom_consts thy) Symtab.empty axioms
      val goal_const_tab = get_goal_consts_typs thy goals
      val _ = Output.debug (fn () => ("Initial constants: " ^
                                 space_implode ", " (Symtab.keys goal_const_tab)));
      val rels = relevant_clauses thy const_tab (!pass_mark) 
                   goal_const_tab  (map (pair_consts_typs_axiom thy) axioms)
  in
      Output.debug (fn () => ("Total relevant: " ^ Int.toString (length rels)));
      rels
  end
 else axioms;

(***************************************************************)
(* Retrieving and filtering lemmas                             *)
(***************************************************************)

(*** white list and black list of lemmas ***)

(*The rule subsetI is frequently omitted by the relevance filter. This could be theory data
  or identified with ATPset (which however is too big currently)*)
val whitelist = [subsetI];

(*** retrieve lemmas from clasimpset and atpset, may filter them ***)

(*Hashing to detect duplicate and variant clauses, e.g. from the [iff] attribute*)

fun setinsert (x,s) = Symtab.update (x,()) s;

(*Reject theorems with names like "List.filter.filter_list_def" or
  "Accessible_Part.acc.defs", as these are definitions arising from packages.*)
fun is_package_def a =
  let val names = NameSpace.explode a
  in
     length names > 2 andalso
     not (hd names = "local") andalso
     String.isSuffix "_def" a  orelse  String.isSuffix "_defs" a
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

exception HASH_CLAUSE;

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

fun all_valid_thms ctxt =
  let
    fun blacklisted s = !run_blacklist_filter andalso is_package_def s

    fun extern_valid space (name, ths) =
      let
        val is_valid = ProofContext.valid_thms ctxt;
        val xname = NameSpace.extern space name;
      in
        if blacklisted name then I
        else if is_valid (xname, ths) then cons (xname, ths)
        else if is_valid (name, ths) then cons (name, ths)
        else I
      end;
    val thy = ProofContext.theory_of ctxt;
    val all_thys = thy :: Theory.ancestors_of thy;

    fun dest_valid (space, tab) = Symtab.fold (extern_valid space) tab [];
  in
    maps (dest_valid o PureThy.theorems_of) all_thys @
    fold (extern_valid (#1 (ProofContext.theorems_of ctxt)))
      (FactIndex.find (ProofContext.fact_index_of ctxt) ([], [])) []
  end;

fun multi_name a (th, (n,pairs)) =
  (n+1, (a ^ "(" ^ Int.toString n ^ ")", th) :: pairs)

fun add_single_names ((a, []), pairs) = pairs
  | add_single_names ((a, [th]), pairs) = (a,th)::pairs
  | add_single_names ((a, ths), pairs) = #2 (foldl (multi_name a) (1,pairs) ths);

val multi_base_blacklist =
  ["defs","select_defs","update_defs","induct","inducts","split","splits","split_asm"];

(*Ignore blacklisted basenames*)
fun add_multi_names ((a, ths), pairs) =
  if (Sign.base_name a) mem_string multi_base_blacklist  then pairs
  else add_single_names ((a, ths), pairs);

fun is_multi (a, ths) = length ths > 1 orelse String.isSuffix ".axioms" a;

(*The single theorems go BEFORE the multiple ones. Blacklist is applied to all.*)
fun name_thm_pairs ctxt =
  let val (mults,singles) = List.partition is_multi (all_valid_thms ctxt)
      val ht = mk_clause_table 900   (*ht for blacklisted theorems*)
      fun blacklisted x = !run_blacklist_filter andalso isSome (Polyhash.peek ht x)
  in
      app (fn th => ignore (Polyhash.peekInsert ht (th,()))) (ResBlacklist.get ctxt);
      filter (not o blacklisted o #2)
        (foldl add_single_names (foldl add_multi_names [] mults) singles)
  end;

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
                         (map ResAxioms.pairname
                           (if null user_thms then whitelist else user_thms))
  in
      (filter check_named included_thms, user_rules)
  end;

(***************************************************************)
(* Type Classes Present in the Axiom or Conjecture Clauses     *)
(***************************************************************)

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
fun restrict_to_logic thy logic cls =
  if is_fol_logic logic then filter (Meson.is_fol_term thy o prop_of o fst) cls
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
val unwanted_types = ["Product_Type.unit","bool"];

fun unwanted t =
    is_taut t orelse has_typed_var unwanted_types t orelse
    forall too_general_equality (dest_disj t);

(*Clauses containing variables of type "unit" or "bool" are unlikely to be useful and
  likely to lead to unsound proofs.*)
fun remove_unwanted_clauses cls = filter (not o unwanted o prop_of o fst) cls;

fun tptp_writer thy logic = ResHolClause.tptp_write_file thy (logic=FOL);

fun dfg_writer thy logic = ResHolClause.dfg_write_file thy (logic=FOL);

(*Called by the oracle-based methods declared in res_atp_methods.ML*)
fun write_subgoal_file dfg mode ctxt conjectures user_thms n =
    let val conj_cls = Meson.make_clauses conjectures
                         |> ResAxioms.assume_abstract_list "subgoal" |> Meson.finish_cnf
        val hyp_cls = cnf_hyps_thms ctxt
        val goal_cls = conj_cls@hyp_cls
        val goal_tms = map prop_of goal_cls
        val thy = ProofContext.theory_of ctxt
        val logic = case mode of
                            Auto => problem_logic_goals [goal_tms]
                          | Fol => FOL
                          | Hol => HOL
        val (included_thms,user_rules) = get_clasimp_atp_lemmas ctxt user_thms
        val cla_simp_atp_clauses = included_thms
                                     |> ResAxioms.cnf_rules_pairs |> make_unique
                                     |> restrict_to_logic thy logic
                                     |> remove_unwanted_clauses
        val user_cls = ResAxioms.cnf_rules_pairs user_rules
        val axclauses = make_unique (user_cls @ relevance_filter thy cla_simp_atp_clauses goal_tms)
        val subs = tfree_classes_of_terms goal_tms
        and axtms = map (prop_of o #1) axclauses
        val supers = tvar_classes_of_terms axtms
        and tycons = type_consts_of_terms thy (goal_tms@axtms)
        (*TFrees in conjecture clauses; TVars in axiom clauses*)
        val (supers',arity_clauses) = ResClause.make_arity_clauses thy tycons supers
        val classrel_clauses = ResClause.make_classrel_clauses thy subs supers'
        val writer = if dfg then dfg_writer else tptp_writer
        and file = atp_input_file()
        and user_lemmas_names = map #1 user_rules
    in
        writer thy logic goal_cls file (axclauses,classrel_clauses,arity_clauses) user_lemmas_names;
        Output.debug (fn () => "Writing to " ^ file);
        file
    end;


(**** remove tmp files ****)
fun cond_rm_tmp file =
    if !Output.debugging orelse !destdir <> ""
    then Output.debug (fn () => "ATP input kept...")
    else OS.FileSys.remove file;


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
            case !prover of
                Recon.SPASS =>
		  let val spass = helper_path "SPASS_HOME" "SPASS"
		      val sopts =
       "-Auto%-SOS=1%-PGiven=0%-PProblem=0%-Splits=0%-FullRed=0%-DocProof%-TimeLimit=" ^ time
		  in
		      ("spass", spass, sopts, probfile) :: make_atp_list xs (n+1)
		  end
              | Recon.Vampire =>
		  let val vampire = helper_path "VAMPIRE_HOME" "vampire"
		      val vopts = "--output_syntax tptp%--mode casc%-t " ^ time
		  in
		      ("vampire", vampire, vopts, probfile) :: make_atp_list xs (n+1)
		  end
              | Recon.E =>
		  let val eproof = helper_path "E_HOME" "eproof"
                      val eopts = "--tstp-in%--tstp-out%-l5%-xAutoDev%-tAutoDev%--silent%--cpu-limit=" ^ time
		  in
		     ("E", eproof, eopts, probfile) :: make_atp_list xs (n+1)
		  end
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
fun write_problem_files probfile (ctxt, chain_ths, th) =
  let val goals = Thm.prems_of th
      val _ = Output.debug (fn () => "number of subgoals = " ^ Int.toString (length goals))
      val thy = ProofContext.theory_of ctxt
      fun get_neg_subgoals [] _ = []
        | get_neg_subgoals (gl::gls) n = #1 (ResAxioms.neg_conjecture_clauses th n) ::
                                         get_neg_subgoals gls (n+1)
      val goal_cls = get_neg_subgoals goals 1
      val logic = case !linkup_logic_mode of
                Auto => problem_logic_goals (map (map prop_of) goal_cls)
              | Fol => FOL
              | Hol => HOL
      val (included_thms,white_thms) = get_clasimp_atp_lemmas ctxt chain_ths
      val included_cls = included_thms |> ResAxioms.cnf_rules_pairs |> make_unique
                                       |> restrict_to_logic thy logic
                                       |> remove_unwanted_clauses
      val _ = Output.debug (fn () => "included clauses = " ^ Int.toString(length included_cls))
      val white_cls = ResAxioms.cnf_rules_pairs white_thms
      (*clauses relevant to goal gl*)
      val axcls_list = map (fn ngcls => white_cls @ relevance_filter thy included_cls (map prop_of ngcls)) goal_cls
      val _ = app (fn axcls => Output.debug (fn () => "filtered clauses = " ^ Int.toString(length axcls)))
                  axcls_list
      val writer = if !prover = Recon.SPASS then dfg_writer else tptp_writer
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
                val (supers',arity_clauses) = ResClause.make_arity_clauses thy tycons supers
                val _ = Output.debug (fn () => "arity clauses = " ^ Int.toString (length arity_clauses))
                val classrel_clauses = ResClause.make_classrel_clauses thy subs supers'
                val _ = Output.debug (fn () => "classrel clauses = " ^ Int.toString (length classrel_clauses))
                val clnames = writer thy logic ccls fname (axcls,classrel_clauses,arity_clauses) []
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
fun isar_atp (ctxt, chain_ths, th) =
  if Thm.no_prems th then ()
  else
    let
      val _ = kill_last_watcher()
      val (files,thm_names_list) = write_problem_files prob_pathname (ctxt, chain_ths, th)
      val (childin, childout, pid) = Watcher.createWatcher (ctxt, th, thm_names_list)
    in
      last_watcher_pid := SOME (childin, childout, pid, files);
      Output.debug (fn () => "problem files: " ^ space_implode ", " files);
      Output.debug (fn () => "pid: " ^ string_of_pid pid);
      watcher_call_provers (Thm.theory_of_thm th) (Thm.prems_of th) (childin, childout, pid)
    end;

(*For ML scripts, and primarily, for debugging*)
fun callatp () =
  let val th = topthm()
      val ctxt = ProofContext.init (theory_of_thm th)
  in  isar_atp (ctxt, [], th)  end;

val isar_atp_writeonly = setmp print_mode []
      (fn (ctxt, chain_ths, th) =>
       if Thm.no_prems th then ()
       else
         let val probfile = if Thm.nprems_of th = 1 then probfile_nosuffix
                            else prob_pathname
         in ignore (write_problem_files probfile (ctxt, chain_ths, th)) end);


(** the Isar toplevel command **)

fun sledgehammer state =
  let
    val (ctxt, (chain_ths, goal)) = Proof.get_goal (Toplevel.proof_of state);
    val thy = ProofContext.theory_of ctxt;
  in
    Output.debug (fn () => "subgoals in isar_atp:\n" ^
                  Pretty.string_of (ProofContext.pretty_term ctxt
                    (Logic.mk_conjunction_list (Thm.prems_of goal))));
    Output.debug (fn () => "current theory: " ^ Context.theory_name thy);
    app (fn th => Output.debug (fn _ => "chained: " ^ string_of_thm th)) chain_ths;
    if !time_limit > 0 then isar_atp (ctxt, chain_ths, goal)
    else (warning ("Writing problem file only: " ^ !problem_name);
          isar_atp_writeonly (ctxt, chain_ths, goal))
  end;

val _ = OuterSyntax.add_parsers
  [OuterSyntax.command "sledgehammer" "call automatic theorem provers" OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_proof o Toplevel.keep sledgehammer))];

end;
