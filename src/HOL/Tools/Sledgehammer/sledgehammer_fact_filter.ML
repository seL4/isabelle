(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact_filter.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory, NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

signature SLEDGEHAMMER_FACT_FILTER =
sig
  type cnf_thm = Clausifier.cnf_thm

  type relevance_override =
    {add: Facts.ref list,
     del: Facts.ref list,
     only: bool}

  val use_natural_form : bool Unsynchronized.ref
  val relevant_facts :
    bool -> bool -> real -> real -> bool -> int -> bool -> relevance_override
    -> Proof.context * (thm list * 'a) -> thm list -> cnf_thm list
end;

structure Sledgehammer_Fact_Filter : SLEDGEHAMMER_FACT_FILTER =
struct

open Clausifier
open Sledgehammer_FOL_Clause
open Sledgehammer_HOL_Clause

(* Experimental feature: Filter theorems in natural form or in CNF? *)
val use_natural_form = Unsynchronized.ref false

type relevance_override =
  {add: Facts.ref list,
   del: Facts.ref list,
   only: bool}

(***************************************************************)
(* Relevance Filtering                                         *)
(***************************************************************)

fun strip_Trueprop (@{const Trueprop} $ t) = t
  | strip_Trueprop t = t;

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
fun uni_mem goal_const_tab (c, c_typ) =
  exists (match_types c_typ) (these (Symtab.lookup goal_const_tab c))

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
fun add_const_type_to_table (c, ctyps) =
  Symtab.map_default (c, [ctyps])
                     (fn [] => [] | ctypss => insert (op =) ctyps ctypss)

val fresh_prefix = "Sledgehammer.Fresh."

val flip = Option.map not

val boring_natural_consts = [@{const_name If}]
(* Including equality in this list might be expected to stop rules like
   subset_antisym from being chosen, but for some reason filtering works better
   with them listed. The logical signs All, Ex, &, and --> are omitted for CNF
   because any remaining occurrences must be within comprehensions. *)
val boring_cnf_consts =
  [@{const_name Trueprop}, @{const_name "==>"}, @{const_name all},
   @{const_name "=="}, @{const_name "op |"}, @{const_name Not},
   @{const_name "op ="}]

fun get_consts_typs thy pos ts =
  let
    (* Free variables are included, as well as constants, to handle locales.
       "skolem_id" is included to increase the complexity of theorems containing
       Skolem functions. In non-CNF form, "Ex" is included but each occurrence
       is considered fresh, to simulate the effect of Skolemization. *)
    fun do_term t =
      case t of
        Const x => add_const_type_to_table (const_with_typ thy x)
      | Free x => add_const_type_to_table (const_with_typ thy x)
      | (t as Const (@{const_name skolem_id}, _)) $ _ => do_term t
      | t1 $ t2 => do_term t1 #> do_term t2
      | Abs (_, _, t) =>
        (* Abstractions lead to combinators, so we add a penalty for them. *)
        add_const_type_to_table (gensym fresh_prefix, [])
        #> do_term t
      | _ => I
    fun do_quantifier sweet_pos pos body_t =
      do_formula pos body_t
      #> (if pos = SOME sweet_pos then I
          else add_const_type_to_table (gensym fresh_prefix, []))
    and do_equality T t1 t2 =
      fold (if T = @{typ bool} orelse T = @{typ prop} then do_formula NONE
            else do_term) [t1, t2]
    and do_formula pos t =
      case t of
        Const (@{const_name all}, _) $ Abs (_, _, body_t) =>
        do_quantifier false pos body_t
      | @{const "==>"} $ t1 $ t2 =>
        do_formula (flip pos) t1 #> do_formula pos t2
      | Const (@{const_name "=="}, Type (_, [T, _])) $ t1 $ t2 =>
        do_equality T t1 t2
      | @{const Trueprop} $ t1 => do_formula pos t1
      | @{const Not} $ t1 => do_formula (flip pos) t1
      | Const (@{const_name All}, _) $ Abs (_, _, body_t) =>
        do_quantifier false pos body_t
      | Const (@{const_name Ex}, _) $ Abs (_, _, body_t) =>
        do_quantifier true pos body_t
      | @{const "op &"} $ t1 $ t2 => fold (do_formula pos) [t1, t2]
      | @{const "op |"} $ t1 $ t2 => fold (do_formula pos) [t1, t2]
      | @{const "op -->"} $ t1 $ t2 =>
        do_formula (flip pos) t1 #> do_formula pos t2
      | Const (@{const_name "op ="}, Type (_, [T, _])) $ t1 $ t2 =>
        do_equality T t1 t2
      | (t0 as Const (_, @{typ bool})) $ t1 =>
        do_term t0 #> do_formula pos t1  (* theory constant *)
      | _ => do_term t
  in
    Symtab.empty
    |> (if !use_natural_form then
          fold (Symtab.update o rpair []) boring_natural_consts
          #> fold (do_formula pos) ts
        else
          fold (Symtab.update o rpair []) boring_cnf_consts
          #> fold do_term ts)
  end

(*Inserts a dummy "constant" referring to the theory name, so that relevance
  takes the given theory into account.*)
fun const_prop_of theory_relevant th =
  if theory_relevant then
    let
      val name = Context.theory_name (theory_of_thm th)
      val t = Const (name ^ ". 1", @{typ bool})
    in t $ prop_of th end
  else
    prop_of th

fun appropriate_prop_of theory_relevant (cnf_thm, (_, orig_thm)) =
  (if !use_natural_form then orig_thm else cnf_thm)
  |> const_prop_of theory_relevant

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

fun count_axiom_consts theory_relevant thy axiom =
  let
    fun do_const (a, T) =
      let val (c, cts) = const_with_typ thy (a,T) in
        (* Two-dimensional table update. Constant maps to types maps to
           count. *)
        CTtab.map_default (cts, 0) (Integer.add 1)
        |> Symtab.map_default (c, CTtab.empty)
      end
    fun do_term (Const x) = do_const x
      | do_term (Free x) = do_const x
      | do_term (Const (x as (@{const_name skolem_id}, _)) $ _) = do_const x
      | do_term (t $ u) = do_term t #> do_term u
      | do_term (Abs (_, _, t)) = do_term t
      | do_term _ = I
  in axiom |> appropriate_prop_of theory_relevant |> do_term end


(**** Actual Filtering Code ****)

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun const_frequency const_tab (c, cts) =
  CTtab.fold (fn (cts', m) => match_types cts cts' ? Integer.add m)
             (the (Symtab.lookup const_tab c)
              handle Option.Option => raise Fail ("Const: " ^ c)) 0

(*A surprising number of theorems contain only a few significant constants.
  These include all induction rules, and other general theorems. Filtering
  theorems in clause form reveals these complexities in the form of Skolem
  functions. If we were instead to filter theorems in their natural form,
  some other method of measuring theorem complexity would become necessary.*)

(* "log" seems best in practice. A constant function of one ignores the constant
   frequencies. *)
fun log_weight2 (x:real) = 1.0 + 2.0 / Math.ln (x + 1.0)

(* Computes a constant's weight, as determined by its frequency. *)
val ct_weight = log_weight2 o real oo const_frequency

(*Relevant constants are weighted according to frequency,
  but irrelevant constants are simply counted. Otherwise, Skolem functions,
  which are rare, would harm a clause's chances of being picked.*)
fun clause_weight const_tab gctyps consts_typs =
    let val rel = filter (uni_mem gctyps) consts_typs
        val rel_weight = fold (curry Real.+ o ct_weight const_tab) rel 0.0
    in
        rel_weight / (rel_weight + real (length consts_typs - length rel))
    end;

(*Multiplies out to a list of pairs: 'a * 'b list -> ('a * 'b) list -> ('a * 'b) list*)
fun add_expand_pairs (x,ys) xys = List.foldl (fn (y,acc) => (x,y)::acc) xys ys;

fun consts_typs_of_term thy t =
  Symtab.fold add_expand_pairs (get_consts_typs thy (SOME false) [t]) []

fun pair_consts_typs_axiom theory_relevant thy axiom =
  (axiom, axiom |> appropriate_prop_of theory_relevant
                |> consts_typs_of_term thy)

exception CONST_OR_FREE of unit

fun dest_Const_or_Free (Const x) = x
  | dest_Const_or_Free (Free x) = x
  | dest_Const_or_Free _ = raise CONST_OR_FREE ()

(*Look for definitions of the form f ?x1 ... ?xn = t, but not reversed.*)
fun defines thy thm gctypes =
    let val tm = prop_of thm
        fun defs lhs rhs =
            let val (rator,args) = strip_comb lhs
                val ct = const_with_typ thy (dest_Const_or_Free rator)
            in
              forall is_Var args andalso uni_mem gctypes ct andalso
                subset (op =) (Term.add_vars rhs [], Term.add_vars lhs [])
            end
            handle CONST_OR_FREE () => false
    in
        case tm of
          @{const Trueprop} $ (Const (@{const_name "op ="}, _) $ lhs $ rhs) =>
            defs lhs rhs
        | _ => false
    end;

type annotated_cnf_thm = cnf_thm * ((string * const_typ list) list)

(*For a reverse sort, putting the largest values first.*)
fun compare_pairs ((_, w1), (_, w2)) = Real.compare (w2, w1)

(*Limit the number of new clauses, to prevent runaway acceptance.*)
fun take_best max_new (newpairs : (annotated_cnf_thm * real) list) =
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
                     ({add, del, ...} : relevance_override) const_tab =
  let
    val thy = ProofContext.theory_of ctxt
    val add_thms = maps (ProofContext.get_fact ctxt) add
    val del_thms = maps (ProofContext.get_fact ctxt) del
    fun iter threshold rel_const_tab =
      let
        fun relevant ([], _) [] = []  (* Nothing added this iteration *)
          | relevant (newpairs, rejects) [] =
            let
              val (newrels, more_rejects) = take_best max_new newpairs
              val new_consts = maps #2 newrels
              val rel_const_tab =
                rel_const_tab |> fold add_const_type_to_table new_consts
              val threshold =
                threshold + (1.0 - threshold) / relevance_convergence
            in
              trace_msg (fn () => "relevant this iteration: " ^
                                  Int.toString (length newrels));
              map #1 newrels @ iter threshold rel_const_tab
                  (more_rejects @ rejects)
            end
          | relevant (newrels, rejects)
                     ((ax as (clsthm as (_, ((name, n), orig_th)),
                              consts_typs)) :: axs) =
            let
              val weight =
                if member Thm.eq_thm add_thms orig_th then 1.0
                else if member Thm.eq_thm del_thms orig_th then 0.0
                else clause_weight const_tab rel_const_tab consts_typs
            in
              if weight >= threshold orelse
                 (defs_relevant andalso
                  defines thy (#1 clsthm) rel_const_tab) then
                (trace_msg (fn () =>
                     name ^ " clause " ^ Int.toString n ^
                     " passes: " ^ Real.toString weight
                     (* ^ " consts: " ^ commas (map fst consts_typs) *));
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
  if relevance_threshold > 1.0 then
    []
  else if relevance_threshold < 0.0 then
    axioms
  else
    let
      val const_tab = fold (count_axiom_consts theory_relevant thy) axioms
                           Symtab.empty
      val goal_const_tab = get_consts_typs thy (SOME true) goals
      val relevance_threshold =
        if !use_natural_form then 0.9 * relevance_threshold (* experimental *)
        else relevance_threshold
      val _ =
        trace_msg (fn () => "Initial constants: " ^
                            commas (goal_const_tab
                                    |> Symtab.dest
                                    |> filter (curry (op <>) [] o snd)
                                    |> map fst))
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

(***************************************************************)
(* Retrieving and filtering lemmas                             *)
(***************************************************************)

(*** retrieve lemmas and filter them ***)

(*Reject theorems with names like "List.filter.filter_list_def" or
  "Accessible_Part.acc.defs", as these are definitions arising from packages.*)
fun is_package_def a =
  let val names = Long_Name.explode a
  in
     length names > 2 andalso
     not (hd names = "local") andalso
     String.isSuffix "_def" a  orelse  String.isSuffix "_defs" a
  end;

fun make_unique xs = Termtab.fold (cons o snd) (make_clause_table xs) []

val exists_sledgehammer_const =
  exists_Const (fn (s, _) => String.isPrefix sledgehammer_prefix s) o prop_of

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
            val ths = filter_out (is_theorem_bad_for_atps orf
                                  exists_sledgehammer_const) ths0
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

(***************************************************************)
(* ATP invocation methods setup                                *)
(***************************************************************)

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

fun relevant_facts full_types respect_no_atp relevance_threshold
                   relevance_convergence defs_relevant max_new theory_relevant
                   (relevance_override as {add, del, only})
                   (ctxt, (chained_ths, _)) goal_cls =
  let
    val thy = ProofContext.theory_of ctxt
    val add_thms = maps (ProofContext.get_fact ctxt) add
    val has_override = not (null add) orelse not (null del)
    val is_FO = forall (Meson.is_fol_term thy o prop_of) goal_cls
    val axioms =
      checked_name_thm_pairs (respect_no_atp andalso not only) ctxt
          (map (name_thms_pair_from_ref ctxt chained_ths) add @
           (if only then []
            else all_name_thms_pairs respect_no_atp ctxt chained_ths))
      |> cnf_rules_pairs thy
      |> not has_override ? make_unique
      |> filter (fn (cnf_thm, (_, orig_thm)) =>
                    member Thm.eq_thm add_thms orig_thm orelse
                    ((not is_FO orelse is_quasi_fol_theorem thy cnf_thm) andalso
                     not (is_dangerous_term full_types (prop_of cnf_thm))))
  in
    relevance_filter ctxt relevance_threshold relevance_convergence
                     defs_relevant max_new theory_relevant relevance_override
                     thy axioms (map prop_of goal_cls)
    |> has_override ? make_unique
    |> sort (prod_ord string_ord int_ord o pairself (fst o snd))
  end

end;
