(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact_filter.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory, NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

signature SLEDGEHAMMER_FACT_FILTER =
sig
  type cnf_thm = Sledgehammer_Fact_Preprocessor.cnf_thm
  type classrel_clause = Sledgehammer_FOL_Clause.classrel_clause
  type arity_clause = Sledgehammer_FOL_Clause.arity_clause
  type hol_clause = Sledgehammer_HOL_Clause.hol_clause

  type relevance_override =
    {add: Facts.ref list,
     del: Facts.ref list,
     only: bool}

  val name_thms_pair_from_ref :
    Proof.context -> thm list -> Facts.ref -> string * thm list
  val tvar_classes_of_terms : term list -> string list
  val tfree_classes_of_terms : term list -> string list
  val type_consts_of_terms : theory -> term list -> string list
  val is_quasi_fol_term : theory -> term -> bool
  val relevant_facts :
    bool -> bool -> real -> real -> bool -> int -> bool -> relevance_override
    -> Proof.context * (thm list * 'a) -> thm list -> cnf_thm list
  val prepare_clauses :
    bool -> thm list -> cnf_thm list -> cnf_thm list -> theory
    -> string vector
       * (hol_clause list * hol_clause list * hol_clause list
          * hol_clause list * classrel_clause list * arity_clause list)
end;

structure Sledgehammer_Fact_Filter : SLEDGEHAMMER_FACT_FILTER =
struct

open Sledgehammer_FOL_Clause
open Sledgehammer_Fact_Preprocessor
open Sledgehammer_HOL_Clause

type relevance_override =
  {add: Facts.ref list,
   del: Facts.ref list,
   only: bool}

(***************************************************************)
(* Relevance Filtering                                         *)
(***************************************************************)

fun strip_Trueprop (@{const Trueprop} $ t) = t
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
val standard_consts =
  [@{const_name Trueprop}, @{const_name "==>"}, @{const_name all},
   @{const_name "=="}, @{const_name "op |"}, @{const_name Not},
   @{const_name "op ="}];


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
  | add_term_consts_typs_rm _ (Const (@{const_name skolem_id}, _) $ _, tab) =
      tab
  | add_term_consts_typs_rm thy (t $ u, tab) =
      add_term_consts_typs_rm thy (t, add_term_consts_typs_rm thy (u, tab))
  | add_term_consts_typs_rm thy (Abs(_,_,t), tab) = add_term_consts_typs_rm thy (t, tab)
  | add_term_consts_typs_rm _ (_, tab) = tab;

(*The empty list here indicates that the constant is being ignored*)
fun add_standard_const (s,tab) = Symtab.update (s,[]) tab;

val null_const_tab : const_typ list list Symtab.table = 
    List.foldl add_standard_const Symtab.empty standard_consts;

fun get_goal_consts_typs thy = List.foldl (add_term_consts_typs_rm thy) null_const_tab;

(*Inserts a dummy "constant" referring to the theory name, so that relevance
  takes the given theory into account.*)
fun const_prop_of theory_relevant th =
 if theory_relevant then
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

fun count_axiom_consts theory_relevant thy ((thm,_), tab) = 
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
  in  count_term_consts (const_prop_of theory_relevant thm, tab)  end;


(**** Actual Filtering Code ****)

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun const_frequency ctab (c, cts) =
  CTtab.fold (fn (cts', m) => match_types cts cts' ? Integer.add m)
             (the (Symtab.lookup ctab c)) 0

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

fun pair_consts_typs_axiom theory_relevant thy (p as (thm, _)) =
  (p, (consts_typs_of_term thy (const_prop_of theory_relevant thm)));

exception ConstFree;
fun dest_ConstFree (Const aT) = aT
  | dest_ConstFree (Free aT) = aT
  | dest_ConstFree _ = raise ConstFree;

(*Look for definitions of the form f ?x1 ... ?xn = t, but not reversed.*)
fun defines thy thm gctypes =
    let val tm = prop_of thm
        fun defs lhs rhs =
            let val (rator,args) = strip_comb lhs
                val ct = const_with_typ thy (dest_ConstFree rator)
            in
              forall is_Var args andalso uni_mem gctypes ct andalso
                subset (op =) (Term.add_vars rhs [], Term.add_vars lhs [])
            end
            handle ConstFree => false
    in    
        case tm of
          @{const Trueprop} $ (Const (@{const_name "op ="}, _) $ lhs $ rhs) => 
            defs lhs rhs 
        | _ => false
    end;

type annotated_clause = cnf_thm * ((string * const_typ list) list)
       
(*For a reverse sort, putting the largest values first.*)
fun compare_pairs ((_, w1), (_, w2)) = Real.compare (w2, w1)

(*Limit the number of new clauses, to prevent runaway acceptance.*)
fun take_best max_new (newpairs : (annotated_clause * real) list) =
  let val nnew = length newpairs
  in
    if nnew <= max_new then (map #1 newpairs, [])
    else 
      let val cls = sort compare_pairs newpairs
          val accepted = List.take (cls, max_new)
      in
        trace_msg (fn () => ("Number of candidates, " ^ Int.toString nnew ^ 
                       ", exceeds the limit of " ^ Int.toString (max_new)));
        trace_msg (fn () => ("Effective pass mark: " ^ Real.toString (#2 (List.last accepted))));
        trace_msg (fn () => "Actually passed: " ^
          space_implode ", " (map (fn (((_,((name,_), _)),_),_) => name) accepted));

        (map #1 accepted, map #1 (List.drop (cls, max_new)))
      end
  end;

fun relevant_clauses ctxt relevance_convergence defs_relevant max_new
                     ({add, del, ...} : relevance_override) ctab =
  let
    val thy = ProofContext.theory_of ctxt
    val add_thms = maps (ProofContext.get_fact ctxt) add
    val del_thms = maps (ProofContext.get_fact ctxt) del
    fun iter threshold rel_consts =
      let
        fun relevant ([], _) [] = []  (* Nothing added this iteration *)
          | relevant (newpairs, rejects) [] =
            let
              val (newrels, more_rejects) = take_best max_new newpairs
              val new_consts = maps #2 newrels
              val rel_consts' = List.foldl add_const_typ_table rel_consts new_consts
              val threshold =
                threshold + (1.0 - threshold) / relevance_convergence
            in
              trace_msg (fn () => "relevant this iteration: " ^
                                  Int.toString (length newrels));
              map #1 newrels @ iter threshold rel_consts'
                  (more_rejects @ rejects)
            end
          | relevant (newrels, rejects)
                     ((ax as (clsthm as (thm, ((name, n), orig_th)),
                              consts_typs)) :: axs) =
            let
              val weight = if member Thm.eq_thm add_thms orig_th then 1.0
                           else if member Thm.eq_thm del_thms orig_th then 0.0
                           else clause_weight ctab rel_consts consts_typs
            in
              if weight >= threshold orelse
                 (defs_relevant andalso defines thy (#1 clsthm) rel_consts) then
                (trace_msg (fn () => name ^ " clause " ^ Int.toString n ^ 
                                     " passes: " ^ Real.toString weight);
                relevant ((ax, weight) :: newrels, rejects) axs)
              else
                relevant (newrels, ax :: rejects) axs
            end
        in
          trace_msg (fn () => "relevant_clauses, current threshold: " ^
                              Real.toString threshold);
          relevant ([], [])
        end
  in iter end
        
fun relevance_filter ctxt relevance_threshold relevance_convergence
                     defs_relevant max_new theory_relevant relevance_override
                     thy (axioms : cnf_thm list) goals = 
  if relevance_threshold > 0.0 then
    let
      val const_tab = List.foldl (count_axiom_consts theory_relevant thy)
                                 Symtab.empty axioms
      val goal_const_tab = get_goal_consts_typs thy goals
      val _ =
        trace_msg (fn () => "Initial constants: " ^
                            commas (Symtab.keys goal_const_tab))
      val relevant =
        relevant_clauses ctxt relevance_convergence defs_relevant max_new
                         relevance_override const_tab relevance_threshold
                         goal_const_tab
                         (map (pair_consts_typs_axiom theory_relevant thy)
                              axioms)
    in
      trace_msg (fn () => "Total relevant: " ^ Int.toString (length relevant));
      relevant
    end
  else
    axioms;

(***************************************************************)
(* Retrieving and filtering lemmas                             *)
(***************************************************************)

(*** retrieve lemmas and filter them ***)

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

fun mk_clause_table xs =
  fold (Termtab.update o `(prop_of o fst)) xs Termtab.empty

fun make_unique xs =
  Termtab.fold (cons o snd) (mk_clause_table xs) []

(* Remove existing axiom clauses from the conjecture clauses, as this can
   dramatically boost an ATP's performance (for some reason). *)
fun subtract_cls ax_clauses =
  filter_out (Termtab.defined (mk_clause_table ax_clauses) o prop_of)

fun all_name_thms_pairs respect_no_atp ctxt chained_ths =
  let
    val global_facts = PureThy.facts_of (ProofContext.theory_of ctxt);
    val local_facts = ProofContext.facts_of ctxt;
    val full_space =
      Name_Space.merge (Facts.space_of global_facts, Facts.space_of local_facts);

    fun valid_facts facts =
      (facts, []) |-> Facts.fold_static (fn (name, ths0) =>
        if Facts.is_concealed facts name orelse
           (respect_no_atp andalso is_package_def name) orelse
           member (op =) multi_base_blacklist (Long_Name.base_name name) then
          I
        else
          let
            fun check_thms a =
              (case try (ProofContext.get_thms ctxt) a of
                NONE => false
              | SOME ths1 => Thm.eq_thms (ths0, ths1));

            val name1 = Facts.extern facts name;
            val name2 = Name_Space.extern full_space name;
            val ths = filter_out is_theorem_bad_for_atps ths0;
          in
            case find_first check_thms [name1, name2, name] of
              NONE => I
            | SOME name' =>
              cons (name' |> forall (member Thm.eq_thm chained_ths) ths
                             ? prefix chained_prefix, ths)
          end)
  in valid_facts global_facts @ valid_facts local_facts end;

fun multi_name a th (n, pairs) =
  (n + 1, (a ^ "(" ^ Int.toString n ^ ")", th) :: pairs);

fun add_names (_, []) pairs = pairs
  | add_names (a, [th]) pairs = (a, th) :: pairs
  | add_names (a, ths) pairs = #2 (fold (multi_name a) ths (1, pairs))

fun is_multi (a, ths) = length ths > 1 orelse String.isSuffix ".axioms" a;

(* The single-name theorems go after the multiple-name ones, so that single
   names are preferred when both are available. *)
fun name_thm_pairs respect_no_atp ctxt name_thms_pairs =
  let
    val (mults, singles) = List.partition is_multi name_thms_pairs
    val ps = [] |> fold add_names singles |> fold add_names mults
  in ps |> respect_no_atp ? filter_out (No_ATPs.member ctxt o snd) end;

fun is_named ("", th) =
    (warning ("No name for theorem " ^
              Display.string_of_thm_without_context th); false)
  | is_named _ = true
fun checked_name_thm_pairs respect_no_atp ctxt =
  name_thm_pairs respect_no_atp ctxt
  #> tap (fn ps => trace_msg
                        (fn () => ("Considering " ^ Int.toString (length ps) ^
                                   " theorems")))
  #> filter is_named

fun name_thms_pair_from_ref ctxt chained_ths xref =
  let
    val ths = ProofContext.get_fact ctxt xref
    val name = Facts.string_of_ref xref
               |> forall (member Thm.eq_thm chained_ths) ths
                  ? prefix chained_prefix
  in (name, ths) end


(***************************************************************)
(* Type Classes Present in the Axiom or Conjecture Clauses     *)
(***************************************************************)

fun add_classes (sorts, cset) = List.foldl setinsert cset (flat sorts);

(*Remove this trivial type class*)
fun delete_type cset = Symtab.delete_safe (the_single @{sort HOL.type}) cset;

fun tvar_classes_of_terms ts =
  let val sorts_list = map (map #2 o OldTerm.term_tvars) ts
  in  Symtab.keys (delete_type (List.foldl add_classes Symtab.empty sorts_list))  end;

fun tfree_classes_of_terms ts =
  let val sorts_list = map (map #2 o OldTerm.term_tfrees) ts
  in  Symtab.keys (delete_type (List.foldl add_classes Symtab.empty sorts_list))  end;

(*fold type constructors*)
fun fold_type_consts f (Type (a, Ts)) x = fold (fold_type_consts f) Ts (f (a,x))
  | fold_type_consts _ _ x = x;

val add_type_consts_in_type = fold_type_consts setinsert;

(*Type constructors used to instantiate overloaded constants are the only ones needed.*)
fun add_type_consts_in_term thy =
  let val const_typargs = Sign.const_typargs thy
      fun add_tcs (Const cT) x = fold add_type_consts_in_type (const_typargs cT) x
        | add_tcs (Abs (_, _, u)) x = add_tcs u x
        | add_tcs (t $ u) x = add_tcs t (add_tcs u x)
        | add_tcs _ x = x
  in  add_tcs  end

fun type_consts_of_terms thy ts =
  Symtab.keys (fold (add_type_consts_in_term thy) ts Symtab.empty);


(***************************************************************)
(* ATP invocation methods setup                                *)
(***************************************************************)

fun is_quasi_fol_term thy =
  Meson.is_fol_term thy o snd o conceal_skolem_somes ~1 []

(*Ensures that no higher-order theorems "leak out"*)
fun restrict_to_logic thy true cls =
    filter (is_quasi_fol_term thy o prop_of o fst) cls
  | restrict_to_logic _ false cls = cls

(**** Predicates to detect unwanted clauses (prolific or likely to cause
      unsoundness) ****)

(** Too general means, positive equality literal with a variable X as one operand,
  when X does not occur properly in the other operand. This rules out clearly
  inconsistent clauses such as V=a|V=b, though it by no means guarantees soundness. **)

fun var_occurs_in_term ix =
  let
    fun aux (Var (jx, _)) = (ix = jx)
      | aux (t1 $ t2) = aux t1 orelse aux t2
      | aux (Abs (_, _, t)) = aux t
      | aux _ = false
  in aux end

fun is_record_type T = not (null (Record.dest_recTs T))

(*Unwanted equalities include
  (1) those between a variable that does not properly occur in the second operand,
  (2) those between a variable and a record, since these seem to be prolific "cases" thms
*)
fun too_general_eqterms (Var (ix,T), t) =
    not (var_occurs_in_term ix t) orelse is_record_type T
  | too_general_eqterms _ = false;

fun too_general_equality (Const (@{const_name "op ="}, _) $ x $ y) =
      too_general_eqterms (x,y) orelse too_general_eqterms(y,x)
  | too_general_equality _ = false;

fun has_typed_var tycons = exists_subterm
  (fn Var (_, Type (a, _)) => member (op =) tycons a | _ => false);

(* Clauses are forbidden to contain variables of these types. The typical reason
   is that they lead to unsoundness. Note that "unit" satisfies numerous
   equations like "?x = ()". The resulting clause will have no type constraint,
   yielding false proofs. Even "bool" leads to many unsound proofs, though only
   for higher-order problems. *)
val dangerous_types = [@{type_name unit}, @{type_name bool}];

(* Clauses containing variables of type "unit" or "bool" or of the form
   "?x = A | ?x = B | ?x = C" are likely to lead to unsound proofs if types are
   omitted. *)
fun is_dangerous_term _ @{prop True} = true
  | is_dangerous_term full_types t =
    not full_types andalso 
    (has_typed_var dangerous_types t orelse
     forall too_general_equality (HOLogic.disjuncts (strip_Trueprop t)))

fun remove_dangerous_clauses full_types add_thms =
  filter_out (fn (cnf_th, (_, orig_th)) =>
                 not (member Thm.eq_thm add_thms orig_th) andalso
                 is_dangerous_term full_types (prop_of cnf_th))

fun is_fol_goal thy = forall (Meson.is_fol_term thy) o map prop_of

fun relevant_facts full_types respect_no_atp relevance_threshold
                   relevance_convergence defs_relevant max_new theory_relevant
                   (relevance_override as {add, del, only})
                   (ctxt, (chained_ths, _)) goal_cls =
  if (only andalso null add) orelse relevance_threshold > 1.0 then
    []
  else
    let
      val thy = ProofContext.theory_of ctxt
      val has_override = not (null add) orelse not (null del)
      val is_FO = is_fol_goal thy goal_cls
      val axioms =
        checked_name_thm_pairs (respect_no_atp andalso not only) ctxt
            (if only then map (name_thms_pair_from_ref ctxt chained_ths) add
             else all_name_thms_pairs respect_no_atp ctxt chained_ths)
        |> cnf_rules_pairs thy
        |> not has_override ? make_unique
        |> not only ? restrict_to_logic thy is_FO
        |> (if only then
              I
            else
              remove_dangerous_clauses full_types
                                       (maps (ProofContext.get_fact ctxt) add))
    in
      relevance_filter ctxt relevance_threshold relevance_convergence
                       defs_relevant max_new theory_relevant relevance_override
                       thy axioms (map prop_of goal_cls)
      |> has_override ? make_unique
    end

(* prepare for passing to writer,
   create additional clauses based on the information from extra_cls *)
fun prepare_clauses full_types goal_cls axcls extra_cls thy =
  let
    val is_FO = is_fol_goal thy goal_cls
    val ccls = subtract_cls extra_cls goal_cls
    val _ = app (fn th => trace_msg (fn _ => Display.string_of_thm_global thy th)) ccls
    val ccltms = map prop_of ccls
    and axtms = map (prop_of o #1) extra_cls
    val subs = tfree_classes_of_terms ccltms
    and supers = tvar_classes_of_terms axtms
    and tycons = type_consts_of_terms thy (ccltms @ axtms)
    (*TFrees in conjecture clauses; TVars in axiom clauses*)
    val conjectures = make_conjecture_clauses thy ccls
    val (_, extra_clauses) = ListPair.unzip (make_axiom_clauses thy extra_cls)
    val (clnames, axiom_clauses) = ListPair.unzip (make_axiom_clauses thy axcls)
    val helper_clauses =
      get_helper_clauses thy is_FO full_types conjectures extra_cls
    val (supers', arity_clauses) = make_arity_clauses thy tycons supers
    val classrel_clauses = make_classrel_clauses thy subs supers'
  in
    (Vector.fromList clnames,
      (conjectures, axiom_clauses, extra_clauses, helper_clauses, classrel_clauses, arity_clauses))
  end

end;
