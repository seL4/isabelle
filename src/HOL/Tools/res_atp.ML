(*  Author: Jia Meng, Cambridge University Computer Laboratory, NICTA *)

signature RES_ATP =
sig
  datatype mode = Auto | Fol | Hol
  val tvar_classes_of_terms : term list -> string list
  val tfree_classes_of_terms : term list -> string list
  val type_consts_of_terms : theory -> term list -> string list
  val get_relevant : int -> bool -> Proof.context * (thm list * 'a) -> thm list ->
    (thm * (string * int)) list
  val prepare_clauses : bool -> thm list -> thm list ->
    (thm * (ResHolClause.axiom_name * ResHolClause.clause_id)) list ->
    (thm * (ResHolClause.axiom_name * ResHolClause.clause_id)) list -> theory ->
    ResHolClause.axiom_name vector *
      (ResHolClause.clause list * ResHolClause.clause list * ResHolClause.clause list *
      ResHolClause.clause list * ResClause.classrelClause list * ResClause.arityClause list)
end;

structure ResAtp: RES_ATP =
struct


(********************************************************************)
(* some settings for both background automatic ATP calling procedure*)
(* and also explicit ATP invocation methods                         *)
(********************************************************************)

(*Translation mode can be auto-detected, or forced to be first-order or higher-order*)
datatype mode = Auto | Fol | Hol;

val linkup_logic_mode = Auto;

(*** background linkup ***)
val run_blacklist_filter = true;

(*** relevance filter parameters ***)
val run_relevance_filter = true;
val pass_mark = 0.5;
val convergence = 3.2;    (*Higher numbers allow longer inference chains*)
val follow_defs = false;  (*Follow definitions. Makes problems bigger.*)
val include_all = true;
val include_atpset = true;
  
(***************************************************************)
(* Relevance Filtering                                         *)
(***************************************************************)

fun strip_Trueprop (Const("Trueprop",_) $ t) = t
  | strip_Trueprop t = t;

(*A surprising number of theorems contain only a few significant constants.
  These include all induction rules, and other general theorems. Filtering
  theorems in clause form reveals these complexities in the form of Skolem 
  functions. If we were instead to filter theorems in their natural form,
  some other method of measuring theorem complexity would become necessary.*)

fun log_weight2 (x:real) = 1.0 + 2.0/Math.ln (x+1.0);

(*The default seems best in practice. A constant function of one ignores
  the constant frequencies.*)
val weight_fn = log_weight2;


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
    List.foldl add_standard_const Symtab.empty standard_consts;

fun get_goal_consts_typs thy = List.foldl (add_term_consts_typs_rm thy) null_const_tab;

(*Inserts a dummy "constant" referring to the theory name, so that relevance
  takes the given theory into account.*)
fun const_prop_of theory_const th =
 if theory_const then
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

structure CTtab = Table(type key = const_typ list val ord = dict_ord const_typ_ord);

fun count_axiom_consts theory_const thy ((thm,_), tab) = 
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
  in  count_term_consts (const_prop_of theory_const thm, tab)  end;


(**** Actual Filtering Code ****)

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun const_frequency ctab (c, cts) =
  let val pairs = CTtab.dest (the (Symtab.lookup ctab c))
      fun add ((cts',m), n) = if match_types cts cts' then m+n else n
  in  List.foldl add 0 pairs  end;

(*Add in a constant's weight, as determined by its frequency.*)
fun add_ct_weight ctab ((c,T), w) =
  w + weight_fn (real (const_frequency ctab (c,T)));

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
fun add_expand_pairs (x,ys) xys = List.foldl (fn (y,acc) => (x,y)::acc) xys ys;

fun consts_typs_of_term thy t = 
  let val tab = add_term_consts_typs_rm thy (t, null_const_tab)
  in  Symtab.fold add_expand_pairs tab []  end;

fun pair_consts_typs_axiom theory_const thy (thm,name) =
    ((thm,name), (consts_typs_of_term thy (const_prop_of theory_const thm)));

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
		   defs lhs rhs 
		 | _ => false
    end;

type annotd_cls = (thm * (string * int)) * ((string * const_typ list) list);
       
(*For a reverse sort, putting the largest values first.*)
fun compare_pairs ((_,w1),(_,w2)) = Real.compare (w2,w1);

(*Limit the number of new clauses, to prevent runaway acceptance.*)
fun take_best max_new (newpairs : (annotd_cls*real) list) =
  let val nnew = length newpairs
  in
    if nnew <= max_new then (map #1 newpairs, [])
    else 
      let val cls = sort compare_pairs newpairs
          val accepted = List.take (cls, max_new)
      in
        ResAxioms.trace_msg (fn () => ("Number of candidates, " ^ Int.toString nnew ^ 
		       ", exceeds the limit of " ^ Int.toString (max_new)));
        ResAxioms.trace_msg (fn () => ("Effective pass mark: " ^ Real.toString (#2 (List.last accepted))));
        ResAxioms.trace_msg (fn () => "Actually passed: " ^
          space_implode ", " (map (fn (((_,(name,_)),_),_) => name) accepted));

	(map #1 accepted, map #1 (List.drop (cls, max_new)))
      end
  end;

fun relevant_clauses max_new thy ctab p rel_consts =
  let fun relevant ([],_) [] = [] : (thm * (string * int)) list  (*Nothing added this iteration*)
	| relevant (newpairs,rejects) [] =
	    let val (newrels,more_rejects) = take_best max_new newpairs
		val new_consts = maps #2 newrels
		val rel_consts' = List.foldl add_const_typ_table rel_consts new_consts
		val newp = p + (1.0-p) / convergence
	    in
              ResAxioms.trace_msg (fn () => ("relevant this iteration: " ^ Int.toString (length newrels)));
	       (map #1 newrels) @ 
	       (relevant_clauses max_new thy ctab newp rel_consts' (more_rejects@rejects))
	    end
	| relevant (newrels,rejects) ((ax as (clsthm as (_,(name,n)),consts_typs)) :: axs) =
	    let val weight = clause_weight ctab rel_consts consts_typs
	    in
	      if p <= weight orelse (follow_defs andalso defines thy clsthm rel_consts)
	      then (ResAxioms.trace_msg (fn () => (name ^ " clause " ^ Int.toString n ^ 
	                                    " passes: " ^ Real.toString weight));
	            relevant ((ax,weight)::newrels, rejects) axs)
	      else relevant (newrels, ax::rejects) axs
	    end
    in  ResAxioms.trace_msg (fn () => ("relevant_clauses, current pass mark = " ^ Real.toString p));
        relevant ([],[]) 
    end;
	
fun relevance_filter max_new theory_const thy axioms goals = 
 if run_relevance_filter andalso pass_mark >= 0.1
 then
  let val const_tab = List.foldl (count_axiom_consts theory_const thy) Symtab.empty axioms
      val goal_const_tab = get_goal_consts_typs thy goals
      val _ = ResAxioms.trace_msg (fn () => ("Initial constants: " ^
                                 space_implode ", " (Symtab.keys goal_const_tab)));
      val rels = relevant_clauses max_new thy const_tab (pass_mark) 
                   goal_const_tab  (map (pair_consts_typs_axiom theory_const thy) axioms)
  in
      ResAxioms.trace_msg (fn () => ("Total relevant: " ^ Int.toString (length rels)));
      rels
  end
 else axioms;

(***************************************************************)
(* Retrieving and filtering lemmas                             *)
(***************************************************************)

(*** white list and black list of lemmas ***)

(*The rule subsetI is frequently omitted by the relevance filter. This could be theory data
  or identified with ATPset (which however is too big currently)*)
val whitelist_fo = [subsetI];
(* ext has been a 'helper clause', always given to the atps.
  As such it was not passed to metis, but metis does not include ext (in contrast
  to the other helper_clauses *)
val whitelist_ho = [ResHolClause.ext];

(*** retrieve lemmas from clasimpset and atpset, may filter them ***)

(*Hashing to detect duplicate and variant clauses, e.g. from the [iff] attribute*)

fun setinsert (x,s) = Symtab.update (x,()) s;

(*Reject theorems with names like "List.filter.filter_list_def" or
  "Accessible_Part.acc.defs", as these are definitions arising from packages.*)
fun is_package_def a =
  let val names = Long_Name.explode a
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

fun hash_term t = Word.toIntX (xor_words (map hash_literal (HOLogic.disjuncts (strip_Trueprop t))));

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
      ResAxioms.trace_msg (fn () => ("make_unique gets " ^ Int.toString (length xs) ^ " clauses"));
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

fun valid_facts facts =
  Facts.fold_static (fn (name, ths) =>
    if run_blacklist_filter andalso is_package_def name then I
    else
      let val xname = Facts.extern facts name in
        if NameSpace.is_hidden xname then I
        else cons (xname, filter_out ResAxioms.bad_for_atp ths)
      end) facts [];

fun all_valid_thms ctxt =
  let
    val global_facts = PureThy.facts_of (ProofContext.theory_of ctxt);
    val local_facts = ProofContext.facts_of ctxt;
  in valid_facts global_facts @ valid_facts local_facts end;

fun multi_name a (th, (n,pairs)) =
  (n+1, (a ^ "(" ^ Int.toString n ^ ")", th) :: pairs)

fun add_single_names ((a, []), pairs) = pairs
  | add_single_names ((a, [th]), pairs) = (a,th)::pairs
  | add_single_names ((a, ths), pairs) = #2 (List.foldl (multi_name a) (1,pairs) ths);

(*Ignore blacklisted basenames*)
fun add_multi_names ((a, ths), pairs) =
  if (Long_Name.base_name a) mem_string ResAxioms.multi_base_blacklist  then pairs
  else add_single_names ((a, ths), pairs);

fun is_multi (a, ths) = length ths > 1 orelse String.isSuffix ".axioms" a;

(*The single theorems go BEFORE the multiple ones. Blacklist is applied to all.*)
fun name_thm_pairs ctxt =
  let val (mults,singles) = List.partition is_multi (all_valid_thms ctxt)
      val ht = mk_clause_table 900   (*ht for blacklisted theorems*)
      fun blacklisted x = run_blacklist_filter andalso isSome (Polyhash.peek ht x)
  in
      app (fn th => ignore (Polyhash.peekInsert ht (th,()))) (ResBlacklist.get ctxt);
      filter (not o blacklisted o #2)
        (List.foldl add_single_names (List.foldl add_multi_names [] mults) singles)
  end;

fun check_named ("", th) =
      (warning ("No name for theorem " ^ Display.string_of_thm_without_context th); false)
  | check_named (_, th) = true;

(* get lemmas from claset, simpset, atpset and extra supplied rules *)
fun get_clasimp_atp_lemmas ctxt =
  let val included_thms =
    if include_all
    then (tap (fn ths => ResAxioms.trace_msg
                 (fn () => ("Including all " ^ Int.toString (length ths) ^ " theorems")))
              (name_thm_pairs ctxt))
    else
    let val atpset_thms =
            if include_atpset then ResAxioms.atpset_rules_of ctxt
            else []
    in  atpset_thms  end
  in
    filter check_named included_thms
  end;

(***************************************************************)
(* Type Classes Present in the Axiom or Conjecture Clauses     *)
(***************************************************************)

fun add_classes (sorts, cset) = List.foldl setinsert cset (flat sorts);

(*Remove this trivial type class*)
fun delete_type cset = Symtab.delete_safe "HOL.type" cset;

fun tvar_classes_of_terms ts =
  let val sorts_list = map (map #2 o OldTerm.term_tvars) ts
  in  Symtab.keys (delete_type (List.foldl add_classes Symtab.empty sorts_list))  end;

fun tfree_classes_of_terms ts =
  let val sorts_list = map (map #2 o OldTerm.term_tfrees) ts
  in  Symtab.keys (delete_type (List.foldl add_classes Symtab.empty sorts_list))  end;

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

(*Ensures that no higher-order theorems "leak out"*)
fun restrict_to_logic thy true cls = filter (Meson.is_fol_term thy o prop_of o fst) cls
  | restrict_to_logic thy false cls = cls;

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

fun is_recordtype T = not (null (Record.dest_recTs T));

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

fun has_typed_var tycons = exists_subterm
  (fn Var (_, Type (a, _)) => member (op =) tycons a | _ => false);

(*Clauses are forbidden to contain variables of these types. The typical reason is that
  they lead to unsoundness. Note that "unit" satisfies numerous equations like ?X=().
  The resulting clause will have no type constraint, yielding false proofs. Even "bool"
  leads to many unsound proofs, though (obviously) only for higher-order problems.*)
val unwanted_types = ["Product_Type.unit","bool"];

fun unwanted t =
  is_taut t orelse has_typed_var unwanted_types t orelse
  forall too_general_equality (HOLogic.disjuncts (strip_Trueprop t));

(*Clauses containing variables of type "unit" or "bool" are unlikely to be useful and
  likely to lead to unsound proofs.*)
fun remove_unwanted_clauses cls = filter (not o unwanted o prop_of o fst) cls;

fun isFO thy goal_cls = case linkup_logic_mode of
      Auto => forall (Meson.is_fol_term thy) (map prop_of goal_cls)
    | Fol => true
    | Hol => false

fun ths_to_cls thy ths =
  ResAxioms.cnf_rules_pairs thy (filter check_named (map ResAxioms.pairname ths))

fun get_relevant max_new theory_const (ctxt, (chain_ths, th)) goal_cls =
  let
    val thy = ProofContext.theory_of ctxt
    val isFO = isFO thy goal_cls
    val included_thms = get_clasimp_atp_lemmas ctxt
    val included_cls = included_thms |> ResAxioms.cnf_rules_pairs thy |> make_unique
                                     |> restrict_to_logic thy isFO
                                     |> remove_unwanted_clauses
    val axcls = relevance_filter max_new theory_const thy included_cls (map prop_of goal_cls)
    (* add whitelist *)
    val white_cls = ths_to_cls thy (whitelist_fo @ (if isFO then [] else whitelist_ho))
  in
    white_cls @ axcls 
  end;

(* prepare for passing to writer,
   create additional clauses based on the information from extra_cls *)
fun prepare_clauses dfg goal_cls chain_ths axcls extra_cls thy =
  let
    (* add chain thms *)
    val chain_cls = ths_to_cls thy chain_ths
    val axcls = chain_cls @ axcls
    val extra_cls = chain_cls @ extra_cls
    val isFO = isFO thy goal_cls
    val ccls = subtract_cls goal_cls extra_cls
    val _ = app (fn th => ResAxioms.trace_msg (fn _ => Display.string_of_thm_global thy th)) ccls
    val ccltms = map prop_of ccls
    and axtms = map (prop_of o #1) extra_cls
    val subs = tfree_classes_of_terms ccltms
    and supers = tvar_classes_of_terms axtms
    and tycons = type_consts_of_terms thy (ccltms@axtms)
    (*TFrees in conjecture clauses; TVars in axiom clauses*)
    val conjectures = ResHolClause.make_conjecture_clauses dfg thy ccls
    val (_, extra_clauses) = ListPair.unzip (ResHolClause.make_axiom_clauses dfg thy extra_cls)
    val (clnames,axiom_clauses) = ListPair.unzip (ResHolClause.make_axiom_clauses dfg thy axcls)
    val helper_clauses = ResHolClause.get_helper_clauses dfg thy isFO (conjectures, extra_cls, [])
    val (supers',arity_clauses) = ResClause.make_arity_clauses_dfg dfg thy tycons supers
    val classrel_clauses = ResClause.make_classrel_clauses thy subs supers'
  in
    (Vector.fromList clnames,
      (conjectures, axiom_clauses, extra_clauses, helper_clauses, classrel_clauses, arity_clauses))
  end

end;

