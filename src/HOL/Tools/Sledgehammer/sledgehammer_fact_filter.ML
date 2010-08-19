(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact_filter.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

signature SLEDGEHAMMER_FACT_FILTER =
sig
  type relevance_override =
    {add: Facts.ref list,
     del: Facts.ref list,
     only: bool}

  val trace : bool Unsynchronized.ref
  val chained_prefix : string
  val name_thms_pair_from_ref :
    Proof.context -> thm list -> Facts.ref -> string * thm list
  val relevant_facts :
    bool -> real -> real -> bool -> int -> bool -> relevance_override
    -> Proof.context * (thm list * 'a) -> term list -> term
    -> (string * thm) list
end;

structure Sledgehammer_Fact_Filter : SLEDGEHAMMER_FACT_FILTER =
struct

val trace = Unsynchronized.ref false
fun trace_msg msg = if !trace then tracing (msg ()) else ()

val respect_no_atp = true

type relevance_override =
  {add: Facts.ref list,
   del: Facts.ref list,
   only: bool}

val sledgehammer_prefix = "Sledgehammer" ^ Long_Name.separator
(* Used to label theorems chained into the goal. *)
val chained_prefix = sledgehammer_prefix ^ "chained_"

fun name_thms_pair_from_ref ctxt chained_ths xref =
  let
    val ths = ProofContext.get_fact ctxt xref
    val name = Facts.string_of_ref xref
               |> forall (member Thm.eq_thm chained_ths) ths
                  ? prefix chained_prefix
  in (name, ths) end


(***************************************************************)
(* Relevance Filtering                                         *)
(***************************************************************)

fun strip_Trueprop_and_all (@{const Trueprop} $ t) =
    strip_Trueprop_and_all t
  | strip_Trueprop_and_all (Const (@{const_name all}, _) $ Abs (_, _, t)) =
    strip_Trueprop_and_all t
  | strip_Trueprop_and_all (Const (@{const_name All}, _) $ Abs (_, _, t)) =
    strip_Trueprop_and_all t
  | strip_Trueprop_and_all t = t

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
  let val tvars = Sign.const_typargs thy (c,typ) in
    (c, map const_typ_of tvars) end
  handle TYPE _ => (c, [])   (*Variable (locale constant): monomorphic*)

(*Add a const/type pair to the table, but a [] entry means a standard connective,
  which we ignore.*)
fun add_const_type_to_table (c, ctyps) =
  Symtab.map_default (c, [ctyps])
                     (fn [] => [] | ctypss => insert (op =) ctyps ctypss)

val fresh_prefix = "Sledgehammer.Fresh."
val flip = Option.map not
(* These are typically simplified away by "Meson.presimplify". *)
val boring_consts =
  [@{const_name If}, @{const_name Let} (* TODO: , @{const_name Set.member}, @{const_name Collect} *)]

fun get_consts_typs thy pos ts =
  let
    (* We include free variables, as well as constants, to handle locales. For
       each quantifiers that must necessarily be skolemized by the ATP, we
       introduce a fresh constant to simulate the effect of Skolemization. *)
    fun do_term t =
      case t of
        Const x => add_const_type_to_table (const_with_typ thy x)
      | Free (s, _) => add_const_type_to_table (s, [])
      | t1 $ t2 => do_term t1 #> do_term t2
      | Abs (_, _, t) =>
        (* Abstractions lead to combinators, so we add a penalty for them. *)
        add_const_type_to_table (gensym fresh_prefix, [])
        #> do_term t
      | _ => I
    fun do_quantifier will_surely_be_skolemized body_t =
      do_formula pos body_t
      #> (if will_surely_be_skolemized then
            add_const_type_to_table (gensym fresh_prefix, [])
          else
            I)
    and do_term_or_formula T =
      if T = @{typ bool} orelse T = @{typ prop} then do_formula NONE
      else do_term
    and do_formula pos t =
      case t of
        Const (@{const_name all}, _) $ Abs (_, _, body_t) =>
        do_quantifier (pos = SOME false) body_t
      | @{const "==>"} $ t1 $ t2 =>
        do_formula (flip pos) t1 #> do_formula pos t2
      | Const (@{const_name "=="}, Type (_, [T, _])) $ t1 $ t2 =>
        fold (do_term_or_formula T) [t1, t2]
      | @{const Trueprop} $ t1 => do_formula pos t1
      | @{const Not} $ t1 => do_formula (flip pos) t1
      | Const (@{const_name All}, _) $ Abs (_, _, body_t) =>
        do_quantifier (pos = SOME false) body_t
      | Const (@{const_name Ex}, _) $ Abs (_, _, body_t) =>
        do_quantifier (pos = SOME true) body_t
      | @{const "op &"} $ t1 $ t2 => fold (do_formula pos) [t1, t2]
      | @{const "op |"} $ t1 $ t2 => fold (do_formula pos) [t1, t2]
      | @{const "op -->"} $ t1 $ t2 =>
        do_formula (flip pos) t1 #> do_formula pos t2
      | Const (@{const_name "op ="}, Type (_, [T, _])) $ t1 $ t2 =>
        fold (do_term_or_formula T) [t1, t2]
      | Const (@{const_name If}, Type (_, [_, Type (_, [T, _])]))
        $ t1 $ t2 $ t3 =>
        do_formula NONE t1 #> fold (do_term_or_formula T) [t2, t3]
      | Const (@{const_name Ex1}, _) $ Abs (_, _, body_t) =>
        do_quantifier (is_some pos) body_t
      | Const (@{const_name Ball}, _) $ t1 $ Abs (_, _, body_t) =>
        do_quantifier (pos = SOME false)
                      (HOLogic.mk_imp (incr_boundvars 1 t1 $ Bound 0, body_t))
      | Const (@{const_name Bex}, _) $ t1 $ Abs (_, _, body_t) =>
        do_quantifier (pos = SOME true)
                      (HOLogic.mk_conj (incr_boundvars 1 t1 $ Bound 0, body_t))
      | (t0 as Const (_, @{typ bool})) $ t1 =>
        do_term t0 #> do_formula pos t1  (* theory constant *)
      | _ => do_term t
  in
    Symtab.empty |> fold (Symtab.update o rpair []) boring_consts
                 |> fold (do_formula pos) ts
  end

(*Inserts a dummy "constant" referring to the theory name, so that relevance
  takes the given theory into account.*)
fun theory_const_prop_of theory_relevant th =
  if theory_relevant then
    let
      val name = Context.theory_name (theory_of_thm th)
      val t = Const (name ^ ". 1", @{typ bool})
    in t $ prop_of th end
  else
    prop_of th

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

fun count_axiom_consts theory_relevant thy (_, th) =
  let
    fun do_const (a, T) =
      let val (c, cts) = const_with_typ thy (a, T) in
        (* Two-dimensional table update. Constant maps to types maps to
           count. *)
        CTtab.map_default (cts, 0) (Integer.add 1)
        |> Symtab.map_default (c, CTtab.empty)
      end
    fun do_term (Const x) = do_const x
      | do_term (Free x) = do_const x
      | do_term (t $ u) = do_term t #> do_term u
      | do_term (Abs (_, _, t)) = do_term t
      | do_term _ = I
  in th |> theory_const_prop_of theory_relevant |> do_term end


(**** Actual Filtering Code ****)

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun const_frequency const_tab (c, cts) =
  CTtab.fold (fn (cts', m) => match_types cts cts' ? Integer.add m)
             (the (Symtab.lookup const_tab c)
              handle Option.Option => raise Fail ("Const: " ^ c)) 0

(* A surprising number of theorems contain only a few significant constants.
   These include all induction rules, and other general theorems. *)

(* "log" seems best in practice. A constant function of one ignores the constant
   frequencies. *)
fun log_weight2 (x:real) = 1.0 + 2.0 / Math.ln (x + 1.0)

(* Computes a constant's weight, as determined by its frequency. *)
val ct_weight = log_weight2 o real oo const_frequency

(*Relevant constants are weighted according to frequency,
  but irrelevant constants are simply counted. Otherwise, Skolem functions,
  which are rare, would harm a formula's chances of being picked.*)
fun formula_weight const_tab gctyps consts_typs =
  let
    val rel = filter (uni_mem gctyps) consts_typs
    val rel_weight = fold (curry Real.+ o ct_weight const_tab) rel 0.0
    val res = rel_weight / (rel_weight + real (length consts_typs - length rel))
  in if Real.isFinite res then res else 0.0 end

(*Multiplies out to a list of pairs: 'a * 'b list -> ('a * 'b) list -> ('a * 'b) list*)
fun add_expand_pairs (x,ys) xys = List.foldl (fn (y,acc) => (x,y)::acc) xys ys;

fun consts_typs_of_term thy t =
  Symtab.fold add_expand_pairs (get_consts_typs thy (SOME true) [t]) []

fun pair_consts_typs_axiom theory_relevant thy axiom =
  (axiom, axiom |> snd |> theory_const_prop_of theory_relevant
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

type annotated_thm = (string * thm) * (string * const_typ list) list

(*For a reverse sort, putting the largest values first.*)
fun compare_pairs ((_, w1), (_, w2)) = Real.compare (w2, w1)

(* Limit the number of new facts, to prevent runaway acceptance. *)
fun take_best max_new (newpairs : (annotated_thm * real) list) =
  let val nnew = length newpairs in
    if nnew <= max_new then
      (map #1 newpairs, [])
    else
      let
        val newpairs = sort compare_pairs newpairs
        val accepted = List.take (newpairs, max_new)
      in
        trace_msg (fn () => ("Number of candidates, " ^ Int.toString nnew ^
                       ", exceeds the limit of " ^ Int.toString max_new));
        trace_msg (fn () => ("Effective pass mark: " ^ Real.toString (#2 (List.last accepted))));
        trace_msg (fn () => "Actually passed: " ^
          space_implode ", " (map (fst o fst o fst) accepted));
        (map #1 accepted, map #1 (List.drop (newpairs, max_new)))
      end
  end;

fun relevance_filter ctxt relevance_threshold relevance_convergence
                     defs_relevant max_new theory_relevant
                     ({add, del, ...} : relevance_override) axioms goal_ts =
  if relevance_threshold > 1.0 then
    []
  else if relevance_threshold < 0.0 then
    axioms
  else
    let
      val thy = ProofContext.theory_of ctxt
      val const_tab = fold (count_axiom_consts theory_relevant thy) axioms
                           Symtab.empty
      val goal_const_tab = get_consts_typs thy (SOME false) goal_ts
      val relevance_threshold = 0.8 * relevance_threshold (* FIXME *)
      val _ =
        trace_msg (fn () => "Initial constants: " ^
                            commas (goal_const_tab
                                    |> Symtab.dest
                                    |> filter (curry (op <>) [] o snd)
                                    |> map fst))
      val add_thms = maps (ProofContext.get_fact ctxt) add
      val del_thms = maps (ProofContext.get_fact ctxt) del
      fun iter threshold rel_const_tab =
        let
          fun relevant ([], rejects) [] =
              (* Nothing was added this iteration: Add "add:" facts. *)
              if null add_thms then
                []
              else
                map_filter (fn (p as (name, th), _) =>
                               if member Thm.eq_thm add_thms th then SOME p
                               else NONE) rejects
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
                       ((ax as ((name, th), consts_typs)) :: axs) =
              let
                val weight =
                  if member Thm.eq_thm del_thms th then 0.0
                  else formula_weight const_tab rel_const_tab consts_typs
              in
                if weight >= threshold orelse
                   (defs_relevant andalso defines thy th rel_const_tab) then
                  (trace_msg (fn () =>
                       name ^ " passes: " ^ Real.toString weight
                       (* ^ " consts: " ^ commas (map fst consts_typs) *));
                   relevant ((ax, weight) :: newrels, rejects) axs)
                else
                  relevant (newrels, ax :: rejects) axs
              end
          in
            trace_msg (fn () => "relevant_facts, current threshold: " ^
                                Real.toString threshold);
            relevant ([], [])
          end
      val relevant = iter relevance_threshold goal_const_tab
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

fun make_fact_table xs =
  fold (Termtab.update o `(prop_of o snd)) xs Termtab.empty
fun make_unique xs = Termtab.fold (cons o snd) (make_fact_table xs) []

(* FIXME: put other record thms here, or declare as "no_atp" *)
val multi_base_blacklist =
  ["defs", "select_defs", "update_defs", "induct", "inducts", "split", "splits",
   "split_asm", "cases", "ext_cases"]

val max_lambda_nesting = 3

fun term_has_too_many_lambdas max (t1 $ t2) =
    exists (term_has_too_many_lambdas max) [t1, t2]
  | term_has_too_many_lambdas max (Abs (_, _, t)) =
    max = 0 orelse term_has_too_many_lambdas (max - 1) t
  | term_has_too_many_lambdas _ _ = false

fun is_formula_type T = (T = HOLogic.boolT orelse T = propT)

(* Don't count nested lambdas at the level of formulas, since they are
   quantifiers. *)
fun formula_has_too_many_lambdas Ts (Abs (_, T, t)) =
    formula_has_too_many_lambdas (T :: Ts) t
  | formula_has_too_many_lambdas Ts t =
    if is_formula_type (fastype_of1 (Ts, t)) then
      exists (formula_has_too_many_lambdas Ts) (#2 (strip_comb t))
    else
      term_has_too_many_lambdas max_lambda_nesting t

(* The max apply depth of any "metis" call in "Metis_Examples" (on 31-10-2007)
   was 11. *)
val max_apply_depth = 15

fun apply_depth (f $ t) = Int.max (apply_depth f, apply_depth t + 1)
  | apply_depth (Abs (_, _, t)) = apply_depth t
  | apply_depth _ = 0

fun is_formula_too_complex t =
  apply_depth t > max_apply_depth orelse formula_has_too_many_lambdas [] t

val exists_sledgehammer_const =
  exists_Const (fn (s, _) => String.isPrefix sledgehammer_prefix s)

fun is_strange_thm th =
  case head_of (concl_of th) of
      Const (a, _) => (a <> @{const_name Trueprop} andalso
                       a <> @{const_name "=="})
    | _ => false

val type_has_top_sort =
  exists_subtype (fn TFree (_, []) => true | TVar (_, []) => true | _ => false)

fun is_theorem_bad_for_atps thm =
  let val t = prop_of thm in
    is_formula_too_complex t orelse exists_type type_has_top_sort t orelse
    exists_sledgehammer_const t orelse is_strange_thm thm
  end

fun all_name_thms_pairs ctxt chained_ths =
  let
    val global_facts = PureThy.facts_of (ProofContext.theory_of ctxt);
    val local_facts = ProofContext.facts_of ctxt;
    val full_space =
      Name_Space.merge (Facts.space_of global_facts, Facts.space_of local_facts);

    fun valid_facts facts =
      (facts, []) |-> Facts.fold_static (fn (name, ths0) =>
        if Facts.is_concealed facts name orelse
           (respect_no_atp andalso is_package_def name) orelse
           member (op =) multi_base_blacklist (Long_Name.base_name name) orelse
           String.isSuffix "_def_raw" (* FIXME: crude hack *) name then
          I
        else
          let
            fun check_thms a =
              (case try (ProofContext.get_thms ctxt) a of
                NONE => false
              | SOME ths1 => Thm.eq_thms (ths0, ths1));

            val name1 = Facts.extern facts name;
            val name2 = Name_Space.extern full_space name;
            val ths = filter_out is_theorem_bad_for_atps ths0
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
fun name_thm_pairs ctxt respect_no_atp name_thms_pairs =
  let
    val (mults, singles) = List.partition is_multi name_thms_pairs
    val ps = [] |> fold add_names singles |> fold add_names mults
  in ps |> respect_no_atp ? filter_out (No_ATPs.member ctxt o snd) end;

fun is_named ("", th) =
    (warning ("No name for theorem " ^
              Display.string_of_thm_without_context th); false)
  | is_named _ = true
fun checked_name_thm_pairs respect_no_atp ctxt =
  name_thm_pairs ctxt respect_no_atp
  #> tap (fn ps => trace_msg
                        (fn () => ("Considering " ^ Int.toString (length ps) ^
                                   " theorems")))
  #> filter is_named

(***************************************************************)
(* ATP invocation methods setup                                *)
(***************************************************************)

(**** Predicates to detect unwanted facts (prolific or likely to cause
      unsoundness) ****)

(* Too general means, positive equality literal with a variable X as one
   operand, when X does not occur properly in the other operand. This rules out
   clearly inconsistent facts such as X = a | X = b, though it by no means
   guarantees soundness. *)

(* Unwanted equalities are those between a (bound or schematic) variable that
   does not properly occur in the second operand. *)
fun too_general_eqterms (Var z) t =
    not (exists_subterm (fn Var z' => z = z' | _ => false) t)
  | too_general_eqterms (Bound j) t = not (loose_bvar1 (t, j))
  | too_general_eqterms _ _ = false

fun too_general_equality (Const (@{const_name "op ="}, _) $ t1 $ t2) =
    too_general_eqterms t1 t2 orelse too_general_eqterms t2 t1
  | too_general_equality _ = false

fun has_bound_or_var_of_type tycons =
  exists_subterm (fn Var (_, Type (s, _)) => member (op =) tycons s
                   | Abs (_, Type (s, _), _) => member (op =) tycons s
                   | _ => false)

(* Facts are forbidden to contain variables of these types. The typical reason
   is that they lead to unsoundness. Note that "unit" satisfies numerous
   equations like "?x = ()". The resulting clauses will have no type constraint,
   yielding false proofs. Even "bool" leads to many unsound proofs, though only
   for higher-order problems. *)
val dangerous_types = [@{type_name unit}, @{type_name bool}, @{type_name prop}];

(* Facts containing variables of type "unit" or "bool" or of the form
   "ALL x. x = A | x = B | x = C" are likely to lead to unsound proofs if types
   are omitted. *)
fun is_dangerous_term full_types t =
    not full_types andalso
    (has_bound_or_var_of_type dangerous_types t orelse
     forall too_general_equality (HOLogic.disjuncts (strip_Trueprop_and_all t)))

fun relevant_facts full_types relevance_threshold relevance_convergence
                   defs_relevant max_new theory_relevant
                   (relevance_override as {add, del, only})
                   (ctxt, (chained_ths, _)) hyp_ts concl_t =
  let
    val add_thms = maps (ProofContext.get_fact ctxt) add
    val axioms =
      checked_name_thm_pairs (respect_no_atp andalso not only) ctxt
          (map (name_thms_pair_from_ref ctxt chained_ths) add @
           (if only then [] else all_name_thms_pairs ctxt chained_ths))
      |> make_unique
      |> filter (fn (_, th) => member Thm.eq_thm add_thms th orelse
                               not (is_dangerous_term full_types (prop_of th)))
  in
    relevance_filter ctxt relevance_threshold relevance_convergence
                     defs_relevant max_new theory_relevant relevance_override
                     axioms (concl_t :: hyp_ts)
    |> sort_wrt fst
  end

end;
