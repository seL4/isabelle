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
  val name_thm_pairs_from_ref :
    Proof.context -> unit Symtab.table -> thm list -> Facts.ref
    -> ((unit -> string * bool) * (bool * thm)) list
  val relevant_facts :
    bool -> real * real -> int -> bool -> relevance_override
    -> Proof.context * (thm list * 'a) -> term list -> term
    -> ((string * bool) * thm) list
end;

structure Sledgehammer_Fact_Filter : SLEDGEHAMMER_FACT_FILTER =
struct

open Sledgehammer_Util

val trace = Unsynchronized.ref false
fun trace_msg msg = if !trace then tracing (msg ()) else ()

val respect_no_atp = true

type relevance_override =
  {add: Facts.ref list,
   del: Facts.ref list,
   only: bool}

val sledgehammer_prefix = "Sledgehammer" ^ Long_Name.separator

fun repair_name reserved multi j name =
  (name |> Symtab.defined reserved name ? quote) ^
  (if multi then "(" ^ Int.toString j ^ ")" else "")

fun name_thm_pairs_from_ref ctxt reserved chained_ths xref =
  let
    val ths = ProofContext.get_fact ctxt xref
    val name = Facts.string_of_ref xref
    val multi = length ths > 1
  in
    fold (fn th => fn (j, rest) =>
             (j + 1, (fn () => (repair_name reserved multi j name,
                                member Thm.eq_thm chained_ths th),
                      (multi, th)) :: rest))
         ths (1, [])
    |> snd
  end

(***************************************************************)
(* Relevance Filtering                                         *)
(***************************************************************)

(*** constants with types ***)

(*An abstraction of Isabelle types*)
datatype pseudotype = PVar | PType of string * pseudotype list

fun string_for_pseudotype PVar = "?"
  | string_for_pseudotype (PType (s, Ts)) =
    (case Ts of
       [] => ""
     | [T] => string_for_pseudotype T
     | Ts => string_for_pseudotypes Ts ^ " ") ^ s
and string_for_pseudotypes Ts =
  "(" ^ commas (map string_for_pseudotype Ts) ^ ")"

(*Is the second type an instance of the first one?*)
fun match_pseudotype (PType (a, T), PType (b, U)) =
    a = b andalso match_pseudotypes (T, U)
  | match_pseudotype (PVar, _) = true
  | match_pseudotype (_, PVar) = false
and match_pseudotypes ([], []) = true
  | match_pseudotypes (T :: Ts, U :: Us) =
    match_pseudotype (T, U) andalso match_pseudotypes (Ts, Us)

(*Is there a unifiable constant?*)
fun pseudoconst_mem f const_tab (c, c_typ) =
  exists (curry (match_pseudotypes o f) c_typ)
         (these (Symtab.lookup const_tab c))

fun pseudotype_for (Type (c,typs)) = PType (c, map pseudotype_for typs)
  | pseudotype_for (TFree _) = PVar
  | pseudotype_for (TVar _) = PVar
(* Pairs a constant with the list of its type instantiations. *)
fun pseudoconst_for thy (c, T) =
  (c, map pseudotype_for (Sign.const_typargs thy (c, T)))
  handle TYPE _ => (c, [])  (* Variable (locale constant): monomorphic *)

fun string_for_pseudoconst (s, []) = s
  | string_for_pseudoconst (s, Ts) = s ^ string_for_pseudotypes Ts
fun string_for_super_pseudoconst (s, [[]]) = s
  | string_for_super_pseudoconst (s, Tss) =
    s ^ "{" ^ commas (map string_for_pseudotypes Tss) ^ "}"

(*Add a const/type pair to the table, but a [] entry means a standard connective,
  which we ignore.*)
fun add_const_to_table (c, ctyps) =
  Symtab.map_default (c, [ctyps])
                     (fn [] => [] | ctypss => insert (op =) ctyps ctypss)

fun is_formula_type T = (T = HOLogic.boolT orelse T = propT)

val fresh_prefix = "Sledgehammer.skolem."
val flip = Option.map not
(* These are typically simplified away by "Meson.presimplify". *)
val boring_consts =
  [@{const_name False}, @{const_name True}, @{const_name If}, @{const_name Let}]

fun get_consts thy pos ts =
  let
    (* We include free variables, as well as constants, to handle locales. For
       each quantifiers that must necessarily be skolemized by the ATP, we
       introduce a fresh constant to simulate the effect of Skolemization. *)
    fun do_term t =
      case t of
        Const x => add_const_to_table (pseudoconst_for thy x)
      | Free (s, _) => add_const_to_table (s, [])
      | t1 $ t2 => fold do_term [t1, t2]
      | Abs (_, _, t') => do_term t'
      | _ => I
    fun do_quantifier will_surely_be_skolemized body_t =
      do_formula pos body_t
      #> (if will_surely_be_skolemized then
            add_const_to_table (gensym fresh_prefix, [])
          else
            I)
    and do_term_or_formula T =
      if is_formula_type T then do_formula NONE else do_term
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

(* A two-dimensional symbol table counts frequencies of constants. It's keyed
   first by constant name and second by its list of type instantiations. For the
   latter, we need a linear ordering on "pseudotype list". *)

fun pseudotype_ord p =
  case p of
    (PVar, PVar) => EQUAL
  | (PVar, PType _) => LESS
  | (PType _, PVar) => GREATER
  | (PType q1, PType q2) =>
    prod_ord fast_string_ord (dict_ord pseudotype_ord) (q1, q2)

structure CTtab =
  Table(type key = pseudotype list val ord = dict_ord pseudotype_ord)

fun count_axiom_consts theory_relevant thy (_, th) =
  let
    fun do_const (a, T) =
      let val (c, cts) = pseudoconst_for thy (a, T) in
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
fun pseudoconst_freq match const_tab (c, cts) =
  CTtab.fold (fn (cts', m) => match (cts, cts') ? Integer.add m)
             (the (Symtab.lookup const_tab c)) 0
  handle Option.Option => 0


(* A surprising number of theorems contain only a few significant constants.
   These include all induction rules, and other general theorems. *)

(* "log" seems best in practice. A constant function of one ignores the constant
   frequencies. *)
fun rel_log (x : real) = 1.0 + 2.0 / Math.ln (x + 1.0)
fun irrel_log (x : real) = Math.ln (x + 19.0) / 6.4

(* Computes a constant's weight, as determined by its frequency. *)
val rel_weight = rel_log o real oo pseudoconst_freq match_pseudotypes
val irrel_weight =
  irrel_log o real oo pseudoconst_freq (match_pseudotypes o swap)
(* fun irrel_weight _ _ = 1.0  FIXME: OLD CODE *)

fun axiom_weight const_tab relevant_consts axiom_consts =
  case axiom_consts |> List.partition (pseudoconst_mem I relevant_consts)
                    ||> filter_out (pseudoconst_mem swap relevant_consts) of
    ([], []) => 0.0
  | (_, []) => 1.0
  | (rel, irrel) =>
    let
      val rel_weight = fold (curry Real.+ o rel_weight const_tab) rel 0.0
      val irrel_weight = fold (curry Real.+ o irrel_weight const_tab) irrel 0.0
      val res = rel_weight / (rel_weight + irrel_weight)
    in if Real.isFinite res then res else 0.0 end

fun consts_of_term thy t =
  Symtab.fold (fn (x, ys) => fold (fn y => cons (x, y)) ys)
              (get_consts thy (SOME true) [t]) []

fun pair_consts_axiom theory_relevant thy axiom =
  (axiom, axiom |> snd |> theory_const_prop_of theory_relevant
                |> consts_of_term thy)

type annotated_thm =
  ((unit -> string * bool) * thm) * (string * pseudotype list) list

fun take_best max (candidates : (annotated_thm * real) list) =
  let
    val ((perfect, more_perfect), imperfect) =
      candidates |> List.partition (fn (_, w) => w > 0.99999) |>> chop (max - 1)
                 ||> sort (Real.compare o swap o pairself snd)
    val (accepts, rejects) =
      case more_perfect @ imperfect of
        [] => (perfect, [])
      | (q :: qs) => (q :: perfect, qs)
  in
    trace_msg (fn () => "Number of candidates: " ^
                        string_of_int (length candidates));
    trace_msg (fn () => "Effective threshold: " ^
                        Real.toString (#2 (hd accepts)));
    trace_msg (fn () => "Actually passed: " ^
        (accepts |> map (fn (((name, _), _), weight) =>
                            fst (name ()) ^ " [" ^ Real.toString weight ^ "]")
                 |> commas));
    (accepts, rejects)
  end

val threshold_divisor = 2.0
val ridiculous_threshold = 0.1

fun relevance_filter ctxt threshold0 decay max_relevant theory_relevant
                     ({add, del, ...} : relevance_override) axioms goal_ts =
  let
    val thy = ProofContext.theory_of ctxt
    val const_tab = fold (count_axiom_consts theory_relevant thy) axioms
                         Symtab.empty
    val add_thms = maps (ProofContext.get_fact ctxt) add
    val del_thms = maps (ProofContext.get_fact ctxt) del
    fun iter j max threshold rel_const_tab hopeless hopeful =
      let
        fun game_over rejects =
          if j = 0 andalso threshold >= ridiculous_threshold then
            (* First iteration? Try again. *)
            iter 0 max (threshold / threshold_divisor) rel_const_tab hopeless
                 hopeful
          else
            (* Add "add:" facts. *)
            if null add_thms then
              []
            else
              map_filter (fn ((p as (_, th), _), _) =>
                             if member Thm.eq_thm add_thms th then SOME p
                             else NONE) rejects
        fun relevant [] rejects [] hopeless =
            (* Nothing has been added this iteration. *)
            game_over (map (apsnd SOME) (rejects @ hopeless))
          | relevant candidates rejects [] hopeless =
            let
              val (accepts, more_rejects) = take_best max candidates
              val rel_const_tab' =
                rel_const_tab
                |> fold add_const_to_table (maps (snd o fst) accepts)
              fun is_dirty (c, _) =
                Symtab.lookup rel_const_tab' c <> Symtab.lookup rel_const_tab c
              val (hopeful_rejects, hopeless_rejects) =
                 (rejects @ hopeless, ([], []))
                 |-> fold (fn (ax as (_, consts), old_weight) =>
                              if exists is_dirty consts then
                                apfst (cons (ax, NONE))
                              else
                                apsnd (cons (ax, old_weight)))
                 |>> append (more_rejects
                             |> map (fn (ax as (_, consts), old_weight) =>
                                        (ax, if exists is_dirty consts then NONE
                                             else SOME old_weight)))
              val threshold = threshold + (1.0 - threshold) * decay
              val max = max - length accepts
            in
              trace_msg (fn () => "New or updated constants: " ^
                  commas (rel_const_tab' |> Symtab.dest
                          |> subtract (op =) (Symtab.dest rel_const_tab)
                          |> map string_for_super_pseudoconst));
              map (fst o fst) accepts @
              (if max = 0 then
                 game_over (hopeful_rejects @ map (apsnd SOME) hopeless_rejects)
               else
                 iter (j + 1) max threshold rel_const_tab' hopeless_rejects
                      hopeful_rejects)
            end
          | relevant candidates rejects
                     (((ax as ((name, th), axiom_consts)), cached_weight)
                      :: hopeful) hopeless =
            let
              val weight =
                case cached_weight of
                  SOME w => w
                | NONE => axiom_weight const_tab rel_const_tab axiom_consts
            in
              if weight >= threshold then
                relevant ((ax, weight) :: candidates) rejects hopeful hopeless
              else
                relevant candidates ((ax, weight) :: rejects) hopeful hopeless
            end
        in
          trace_msg (fn () =>
              "ITERATION " ^ string_of_int j ^ ": current threshold: " ^
              Real.toString threshold ^ ", constants: " ^
              commas (rel_const_tab |> Symtab.dest
                      |> filter (curry (op <>) [] o snd)
                      |> map string_for_super_pseudoconst));
          relevant [] [] hopeful hopeless
        end
  in
    axioms |> filter_out (member Thm.eq_thm del_thms o snd)
           |> map (rpair NONE o pair_consts_axiom theory_relevant thy)
           |> iter 0 max_relevant threshold0
                   (get_consts thy (SOME false) goal_ts) []
           |> tap (fn res => trace_msg (fn () =>
                                "Total relevant: " ^ Int.toString (length res)))
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
   "split_asm", "cases", "ext_cases", "eq.simps", "eq.refl", "nchotomy",
   "case_cong", "weak_case_cong"]
  |> map (prefix ".")

val max_lambda_nesting = 3

fun term_has_too_many_lambdas max (t1 $ t2) =
    exists (term_has_too_many_lambdas max) [t1, t2]
  | term_has_too_many_lambdas max (Abs (_, _, t)) =
    max = 0 orelse term_has_too_many_lambdas (max - 1) t
  | term_has_too_many_lambdas _ _ = false

(* Don't count nested lambdas at the level of formulas, since they are
   quantifiers. *)
fun formula_has_too_many_lambdas Ts (Abs (_, T, t)) =
    formula_has_too_many_lambdas (T :: Ts) t
  | formula_has_too_many_lambdas Ts t =
    if is_formula_type (fastype_of1 (Ts, t)) then
      exists (formula_has_too_many_lambdas Ts) (#2 (strip_comb t))
    else
      term_has_too_many_lambdas max_lambda_nesting t

(* The max apply depth of any "metis" call in "Metis_Examples" (on 2007-10-31)
   was 11. *)
val max_apply_depth = 15

fun apply_depth (f $ t) = Int.max (apply_depth f, apply_depth t + 1)
  | apply_depth (Abs (_, _, t)) = apply_depth t
  | apply_depth _ = 0

fun is_formula_too_complex t =
  apply_depth t > max_apply_depth orelse formula_has_too_many_lambdas [] t

val exists_sledgehammer_const =
  exists_Const (fn (s, _) => String.isPrefix sledgehammer_prefix s)

fun is_strange_theorem th =
  case head_of (concl_of th) of
      Const (a, _) => (a <> @{const_name Trueprop} andalso
                       a <> @{const_name "=="})
    | _ => false

val type_has_top_sort =
  exists_subtype (fn TFree (_, []) => true | TVar (_, []) => true | _ => false)

(**** Predicates to detect unwanted facts (prolific or likely to cause
      unsoundness) ****)

(* Too general means, positive equality literal with a variable X as one
   operand, when X does not occur properly in the other operand. This rules out
   clearly inconsistent facts such as X = a | X = b, though it by no means
   guarantees soundness. *)

(* Unwanted equalities are those between a (bound or schematic) variable that
   does not properly occur in the second operand. *)
val is_exhaustive_finite =
  let
    fun is_bad_equal (Var z) t =
        not (exists_subterm (fn Var z' => z = z' | _ => false) t)
      | is_bad_equal (Bound j) t = not (loose_bvar1 (t, j))
      | is_bad_equal _ _ = false
    fun do_equals t1 t2 = is_bad_equal t1 t2 orelse is_bad_equal t2 t1
    fun do_formula pos t =
      case (pos, t) of
        (_, @{const Trueprop} $ t1) => do_formula pos t1
      | (true, Const (@{const_name all}, _) $ Abs (_, _, t')) =>
        do_formula pos t'
      | (true, Const (@{const_name All}, _) $ Abs (_, _, t')) =>
        do_formula pos t'
      | (false, Const (@{const_name Ex}, _) $ Abs (_, _, t')) =>
        do_formula pos t'
      | (_, @{const "==>"} $ t1 $ t2) =>
        do_formula (not pos) t1 andalso
        (t2 = @{prop False} orelse do_formula pos t2)
      | (_, @{const "op -->"} $ t1 $ t2) =>
        do_formula (not pos) t1 andalso
        (t2 = @{const False} orelse do_formula pos t2)
      | (_, @{const Not} $ t1) => do_formula (not pos) t1
      | (true, @{const "op |"} $ t1 $ t2) => forall (do_formula pos) [t1, t2]
      | (false, @{const "op &"} $ t1 $ t2) => forall (do_formula pos) [t1, t2]
      | (true, Const (@{const_name "op ="}, _) $ t1 $ t2) => do_equals t1 t2
      | (true, Const (@{const_name "=="}, _) $ t1 $ t2) => do_equals t1 t2
      | _ => false
  in do_formula true end

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
  let val t = transform_elim_term t in
    has_bound_or_var_of_type dangerous_types t orelse
    is_exhaustive_finite t
  end

fun is_theorem_bad_for_atps full_types thm =
  let val t = prop_of thm in
    is_formula_too_complex t orelse exists_type type_has_top_sort t orelse
    is_dangerous_term full_types t orelse exists_sledgehammer_const t orelse
    is_strange_theorem thm
  end

fun all_name_thms_pairs ctxt reserved full_types add_thms chained_ths =
  let
    val is_chained = member Thm.eq_thm chained_ths
    val global_facts = PureThy.facts_of (ProofContext.theory_of ctxt)
    val local_facts = ProofContext.facts_of ctxt
    val named_locals = local_facts |> Facts.dest_static []
    (* Unnamed, not chained formulas with schematic variables are omitted,
       because they are rejected by the backticks (`...`) parser for some
       reason. *)
    fun is_good_unnamed_local th =
      forall (fn (_, ths) => not (member Thm.eq_thm ths th)) named_locals
      andalso (not (exists_subterm is_Var (prop_of th)) orelse (is_chained th))
    val unnamed_locals =
      local_facts |> Facts.props |> filter is_good_unnamed_local
                  |> map (pair "" o single)
    val full_space =
      Name_Space.merge (Facts.space_of global_facts, Facts.space_of local_facts)
    fun add_valid_facts foldx facts =
      foldx (fn (name0, ths) =>
        if name0 <> "" andalso
           forall (not o member Thm.eq_thm add_thms) ths andalso
           (Facts.is_concealed facts name0 orelse
            (respect_no_atp andalso is_package_def name0) orelse
            exists (fn s => String.isSuffix s name0) multi_base_blacklist orelse
            String.isSuffix "_def_raw" (* FIXME: crude hack *) name0) then
          I
        else
          let
            val multi = length ths > 1
            fun backquotify th =
              "`" ^ Print_Mode.setmp [Print_Mode.input]
                                 (Syntax.string_of_term ctxt) (prop_of th) ^ "`"
              |> String.translate (fn c => if Char.isPrint c then str c else "")
              |> simplify_spaces
            fun check_thms a =
              case try (ProofContext.get_thms ctxt) a of
                NONE => false
              | SOME ths' => Thm.eq_thms (ths, ths')
          in
            pair 1
            #> fold (fn th => fn (j, rest) =>
                 (j + 1,
                  if is_theorem_bad_for_atps full_types th andalso
                     not (member Thm.eq_thm add_thms th) then
                    rest
                  else
                    (fn () =>
                        (if name0 = "" then
                           th |> backquotify
                         else
                           let
                             val name1 = Facts.extern facts name0
                             val name2 = Name_Space.extern full_space name0
                           in
                             case find_first check_thms [name1, name2, name0] of
                               SOME name => repair_name reserved multi j name
                             | NONE => ""
                           end, is_chained th), (multi, th)) :: rest)) ths
            #> snd
          end)
  in
    [] |> add_valid_facts fold local_facts (unnamed_locals @ named_locals)
       |> add_valid_facts Facts.fold_static global_facts global_facts
  end

(* The single-name theorems go after the multiple-name ones, so that single
   names are preferred when both are available. *)
fun name_thm_pairs ctxt respect_no_atp =
  List.partition (fst o snd) #> op @ #> map (apsnd snd)
  #> respect_no_atp ? filter_out (No_ATPs.member ctxt o snd)

(***************************************************************)
(* ATP invocation methods setup                                *)
(***************************************************************)

fun relevant_facts full_types (threshold0, threshold1) max_relevant
                   theory_relevant (relevance_override as {add, del, only})
                   (ctxt, (chained_ths, _)) hyp_ts concl_t =
  let
    val decay = 1.0 - Math.pow ((1.0 - threshold1) / (1.0 - threshold0),
                                1.0 / Real.fromInt (max_relevant + 1))
    val add_thms = maps (ProofContext.get_fact ctxt) add
    val reserved = reserved_isar_keyword_table ()
    val axioms =
      (if only then
         maps (name_thm_pairs_from_ref ctxt reserved chained_ths) add
       else
         all_name_thms_pairs ctxt reserved full_types add_thms chained_ths)
      |> name_thm_pairs ctxt (respect_no_atp andalso not only)
      |> make_unique
  in
    trace_msg (fn () => "Considering " ^ Int.toString (length axioms) ^
                        " theorems");
    (if threshold0 > 1.0 orelse threshold0 > threshold1 then
       []
     else if threshold0 < 0.0 then
       axioms
     else
       relevance_filter ctxt threshold0 decay max_relevant theory_relevant
                        relevance_override axioms (concl_t :: hyp_ts))
    |> map (apfst (fn f => f ())) |> sort_wrt (fst o fst)
  end

end;
