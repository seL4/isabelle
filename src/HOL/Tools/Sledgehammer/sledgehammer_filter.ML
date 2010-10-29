(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_filter.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's relevance filter.
*)

signature SLEDGEHAMMER_FILTER =
sig
  datatype locality = General | Intro | Elim | Simp | Local | Assum | Chained

  type relevance_fudge =
    {worse_irrel_freq : real,
     higher_order_irrel_weight : real,
     abs_rel_weight : real,
     abs_irrel_weight : real,
     skolem_irrel_weight : real,
     theory_const_rel_weight : real,
     theory_const_irrel_weight : real,
     intro_bonus : real,
     elim_bonus : real,
     simp_bonus : real,
     local_bonus : real,
     assum_bonus : real,
     chained_bonus : real,
     max_imperfect : real,
     max_imperfect_exp : real,
     threshold_divisor : real,
     ridiculous_threshold : real}

  type relevance_override =
    {add : (Facts.ref * Attrib.src list) list,
     del : (Facts.ref * Attrib.src list) list,
     only : bool}

  val trace : bool Unsynchronized.ref
  val fact_from_ref :
    Proof.context -> unit Symtab.table -> thm list
    -> Facts.ref * Attrib.src list -> ((string * locality) * thm) list
  val relevant_facts :
    Proof.context -> bool -> real * real -> int -> string list
    -> relevance_fudge -> relevance_override -> thm list -> term list -> term
    -> ((string * locality) * thm) list
end;

structure Sledgehammer_Filter : SLEDGEHAMMER_FILTER =
struct

open Sledgehammer_Util

val trace = Unsynchronized.ref false
fun trace_msg msg = if !trace then tracing (msg ()) else ()

(* experimental features *)
val term_patterns = false
val respect_no_atp = true

datatype locality = General | Intro | Elim | Simp | Local | Assum | Chained

type relevance_fudge =
  {worse_irrel_freq : real,
   higher_order_irrel_weight : real,
   abs_rel_weight : real,
   abs_irrel_weight : real,
   skolem_irrel_weight : real,
   theory_const_rel_weight : real,
   theory_const_irrel_weight : real,
   intro_bonus : real,
   elim_bonus : real,
   simp_bonus : real,
   local_bonus : real,
   assum_bonus : real,
   chained_bonus : real,
   max_imperfect : real,
   max_imperfect_exp : real,
   threshold_divisor : real,
   ridiculous_threshold : real}

type relevance_override =
  {add : (Facts.ref * Attrib.src list) list,
   del : (Facts.ref * Attrib.src list) list,
   only : bool}

val sledgehammer_prefix = "Sledgehammer" ^ Long_Name.separator
val abs_name = sledgehammer_prefix ^ "abs"
val skolem_prefix = sledgehammer_prefix ^ "sko"
val theory_const_suffix = Long_Name.separator ^ " 1"

fun needs_quoting reserved s =
  Symtab.defined reserved s (* FIXME: orelse
  exists (not o Syntax.is_identifier) (Long_Name.explode s) *)

fun repair_name reserved multi j name =
  (name |> needs_quoting reserved name ? quote) ^
  (if multi then "(" ^ Int.toString j ^ ")" else "")

fun fact_from_ref ctxt reserved chained_ths (xthm as (xref, args)) =
  let
    val ths = Attrib.eval_thms ctxt [xthm]
    val bracket =
      implode (map (fn arg => "[" ^ Pretty.str_of (Args.pretty_src ctxt arg)
                               ^ "]") args)
    val name =
      case xref of
        Facts.Fact s => "`" ^ s ^ "`" ^ bracket
      | Facts.Named (("", _), _) => "[" ^ bracket ^ "]"
      | _ => Facts.string_of_ref xref ^ bracket
    val multi = length ths > 1
  in
    (ths, (1, []))
    |-> fold (fn th => fn (j, rest) =>
                 (j + 1, ((repair_name reserved multi j name,
                          if member Thm.eq_thm chained_ths th then Chained
                          else General), th) :: rest))
    |> snd
  end

(***************************************************************)
(* Relevance Filtering                                         *)
(***************************************************************)

(*** constants with types ***)

fun order_of_type (Type (@{type_name fun}, [T1, @{typ bool}])) =
    order_of_type T1 (* cheat: pretend sets are first-order *)
  | order_of_type (Type (@{type_name fun}, [T1, T2])) =
    Int.max (order_of_type T1 + 1, order_of_type T2)
  | order_of_type (Type (_, Ts)) = fold (Integer.max o order_of_type) Ts 0
  | order_of_type _ = 0

(* An abstraction of Isabelle types and first-order terms *)
datatype pattern = PVar | PApp of string * pattern list
datatype ptype = PType of int * pattern list

fun string_for_pattern PVar = "_"
  | string_for_pattern (PApp (s, ps)) =
    if null ps then s else s ^ string_for_patterns ps
and string_for_patterns ps = "(" ^ commas (map string_for_pattern ps) ^ ")"
fun string_for_ptype (PType (_, ps)) = string_for_patterns ps

(*Is the second type an instance of the first one?*)
fun match_pattern (PVar, _) = true
  | match_pattern (PApp _, PVar) = false
  | match_pattern (PApp (s, ps), PApp (t, qs)) =
    s = t andalso match_patterns (ps, qs)
and match_patterns (_, []) = true
  | match_patterns ([], _) = false
  | match_patterns (p :: ps, q :: qs) =
    match_pattern (p, q) andalso match_patterns (ps, qs)
fun match_ptype (PType (_, ps), PType (_, qs)) = match_patterns (ps, qs)

(* Is there a unifiable constant? *)
fun pconst_mem f consts (s, ps) =
  exists (curry (match_ptype o f) ps)
         (map snd (filter (curry (op =) s o fst) consts))
fun pconst_hyper_mem f const_tab (s, ps) =
  exists (curry (match_ptype o f) ps) (these (Symtab.lookup const_tab s))

fun pattern_for_type (Type (s, Ts)) = PApp (s, map pattern_for_type Ts)
  | pattern_for_type (TFree (s, _)) = PApp (s, [])
  | pattern_for_type (TVar _) = PVar

fun pterm thy t =
  case strip_comb t of
    (Const x, ts) => PApp (pconst thy true x ts)
  | (Free x, ts) => PApp (pconst thy false x ts)
  | (Var _, []) => PVar
  | _ => PApp ("?", [])  (* equivalence class of higher-order constructs *)
(* Pairs a constant with the list of its type instantiations. *)
and ptype thy const x ts =
  (if const then map pattern_for_type (these (try (Sign.const_typargs thy) x))
   else []) @
  (if term_patterns then map (pterm thy) ts else [])
and pconst thy const (s, T) ts = (s, ptype thy const (s, T) ts)
and rich_ptype thy const (s, T) ts =
  PType (order_of_type T, ptype thy const (s, T) ts)
and rich_pconst thy const (s, T) ts = (s, rich_ptype thy const (s, T) ts)

fun string_for_hyper_pconst (s, ps) =
  s ^ "{" ^ commas (map string_for_ptype ps) ^ "}"

(* Add a pconstant to the table, but a [] entry means a standard
   connective, which we ignore.*)
fun add_pconst_to_table irrelevant_consts also_skolem (c, p) =
  if member (op =) irrelevant_consts c orelse
     (not also_skolem andalso String.isPrefix skolem_prefix c) then
    I
  else
    Symtab.map_default (c, [p]) (insert (op =) p)

fun is_formula_type T = (T = HOLogic.boolT orelse T = propT)

fun pconsts_in_terms thy irrelevant_consts also_skolems pos ts =
  let
    val flip = Option.map not
    (* We include free variables, as well as constants, to handle locales. For
       each quantifiers that must necessarily be skolemized by the ATP, we
       introduce a fresh constant to simulate the effect of Skolemization. *)
    fun do_const const (s, T) ts =
      add_pconst_to_table irrelevant_consts also_skolems
                          (rich_pconst thy const (s, T) ts)
      #> fold do_term ts
    and do_term t =
      case strip_comb t of
        (Const x, ts) => do_const true x ts
      | (Free x, ts) => do_const false x ts
      | (Abs (_, T, t'), ts) =>
        (null ts
         ? add_pconst_to_table irrelevant_consts true
                               (abs_name, PType (order_of_type T + 1, [])))
        #> fold do_term (t' :: ts)
      | (_, ts) => fold do_term ts
    fun do_quantifier will_surely_be_skolemized abs_T body_t =
      do_formula pos body_t
      #> (if also_skolems andalso will_surely_be_skolemized then
            add_pconst_to_table irrelevant_consts true
                         (gensym skolem_prefix, PType (order_of_type abs_T, []))
          else
            I)
    and do_term_or_formula T =
      if is_formula_type T then do_formula NONE else do_term
    and do_formula pos t =
      case t of
        Const (@{const_name all}, _) $ Abs (_, T, t') =>
        do_quantifier (pos = SOME false) T t'
      | @{const "==>"} $ t1 $ t2 =>
        do_formula (flip pos) t1 #> do_formula pos t2
      | Const (@{const_name "=="}, Type (_, [T, _])) $ t1 $ t2 =>
        fold (do_term_or_formula T) [t1, t2]
      | @{const Trueprop} $ t1 => do_formula pos t1
      | @{const Not} $ t1 => do_formula (flip pos) t1
      | Const (@{const_name All}, _) $ Abs (_, T, t') =>
        do_quantifier (pos = SOME false) T t'
      | Const (@{const_name Ex}, _) $ Abs (_, T, t') =>
        do_quantifier (pos = SOME true) T t'
      | @{const HOL.conj} $ t1 $ t2 => fold (do_formula pos) [t1, t2]
      | @{const HOL.disj} $ t1 $ t2 => fold (do_formula pos) [t1, t2]
      | @{const HOL.implies} $ t1 $ t2 =>
        do_formula (flip pos) t1 #> do_formula pos t2
      | Const (@{const_name HOL.eq}, Type (_, [T, _])) $ t1 $ t2 =>
        fold (do_term_or_formula T) [t1, t2]
      | Const (@{const_name If}, Type (_, [_, Type (_, [T, _])]))
        $ t1 $ t2 $ t3 =>
        do_formula NONE t1 #> fold (do_term_or_formula T) [t2, t3]
      | Const (@{const_name Ex1}, _) $ Abs (_, T, t') =>
        do_quantifier (is_some pos) T t'
      | Const (@{const_name Ball}, _) $ t1 $ Abs (_, T, t') =>
        do_quantifier (pos = SOME false) T
                      (HOLogic.mk_imp (incr_boundvars 1 t1 $ Bound 0, t'))
      | Const (@{const_name Bex}, _) $ t1 $ Abs (_, T, t') =>
        do_quantifier (pos = SOME true) T
                      (HOLogic.mk_conj (incr_boundvars 1 t1 $ Bound 0, t'))
      | (t0 as Const (_, @{typ bool})) $ t1 =>
        do_term t0 #> do_formula pos t1  (* theory constant *)
      | _ => do_term t
  in Symtab.empty |> fold (do_formula pos) ts end

(*Inserts a dummy "constant" referring to the theory name, so that relevance
  takes the given theory into account.*)
fun theory_const_prop_of ({theory_const_rel_weight,
                           theory_const_irrel_weight, ...} : relevance_fudge)
                         th =
  if exists (curry (op <) 0.0) [theory_const_rel_weight,
                                theory_const_irrel_weight] then
    let
      val name = Context.theory_name (theory_of_thm th)
      val t = Const (name ^ theory_const_suffix, @{typ bool})
    in t $ prop_of th end
  else
    prop_of th

(**** Constant / Type Frequencies ****)

(* A two-dimensional symbol table counts frequencies of constants. It's keyed
   first by constant name and second by its list of type instantiations. For the
   latter, we need a linear ordering on "pattern list". *)

fun pattern_ord p =
  case p of
    (PVar, PVar) => EQUAL
  | (PVar, PApp _) => LESS
  | (PApp _, PVar) => GREATER
  | (PApp q1, PApp q2) =>
    prod_ord fast_string_ord (dict_ord pattern_ord) (q1, q2)
fun ptype_ord (PType p, PType q) =
  prod_ord (dict_ord pattern_ord) int_ord (swap p, swap q)

structure PType_Tab = Table(type key = ptype val ord = ptype_ord)

fun count_fact_consts thy fudge =
  let
    fun do_const const (s, T) ts =
      (* Two-dimensional table update. Constant maps to types maps to count. *)
      PType_Tab.map_default (rich_ptype thy const (s, T) ts, 0) (Integer.add 1)
      |> Symtab.map_default (s, PType_Tab.empty)
      #> fold do_term ts
    and do_term t =
      case strip_comb t of
        (Const x, ts) => do_const true x ts
      | (Free x, ts) => do_const false x ts
      | (Abs (_, _, t'), ts) => fold do_term (t' :: ts)
      | (_, ts) => fold do_term ts
  in do_term o theory_const_prop_of fudge o snd end


(**** Actual Filtering Code ****)

fun pow_int _ 0 = 1.0
  | pow_int x 1 = x
  | pow_int x n = if n > 0 then x * pow_int x (n - 1) else pow_int x (n + 1) / x

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun pconst_freq match const_tab (c, ps) =
  PType_Tab.fold (fn (qs, m) => match (ps, qs) ? Integer.add m)
                 (the (Symtab.lookup const_tab c)) 0


(* A surprising number of theorems contain only a few significant constants.
   These include all induction rules, and other general theorems. *)

(* "log" seems best in practice. A constant function of one ignores the constant
   frequencies. Rare constants give more points if they are relevant than less
   rare ones. *)
fun rel_weight_for _ freq = 1.0 + 2.0 / Math.ln (Real.fromInt freq + 1.0)

(* Irrelevant constants are treated differently. We associate lower penalties to
   very rare constants and very common ones -- the former because they can't
   lead to the inclusion of too many new facts, and the latter because they are
   so common as to be of little interest. *)
fun irrel_weight_for ({worse_irrel_freq, higher_order_irrel_weight, ...}
                      : relevance_fudge) order freq =
  let val (k, x) = worse_irrel_freq |> `Real.ceil in
    (if freq < k then Math.ln (Real.fromInt (freq + 1)) / Math.ln x
     else rel_weight_for order freq / rel_weight_for order k)
    * pow_int higher_order_irrel_weight (order - 1)
  end

(* Computes a constant's weight, as determined by its frequency. *)
fun generic_pconst_weight abs_weight skolem_weight theory_const_weight
                          weight_for f const_tab (c as (s, PType (m, _))) =
  if s = abs_name then abs_weight
  else if String.isPrefix skolem_prefix s then skolem_weight
  else if String.isSuffix theory_const_suffix s then theory_const_weight
  else weight_for m (pconst_freq (match_ptype o f) const_tab c)

fun rel_pconst_weight ({abs_rel_weight, theory_const_rel_weight, ...}
                       : relevance_fudge) const_tab =
  generic_pconst_weight abs_rel_weight 0.0 theory_const_rel_weight
                        rel_weight_for I const_tab
fun irrel_pconst_weight (fudge as {abs_irrel_weight, skolem_irrel_weight,
                                   theory_const_irrel_weight, ...}) const_tab =
  generic_pconst_weight abs_irrel_weight skolem_irrel_weight
                        theory_const_irrel_weight (irrel_weight_for fudge) swap
                        const_tab

fun locality_bonus (_ : relevance_fudge) General = 0.0
  | locality_bonus {intro_bonus, ...} Intro = intro_bonus
  | locality_bonus {elim_bonus, ...} Elim = elim_bonus
  | locality_bonus {simp_bonus, ...} Simp = simp_bonus
  | locality_bonus {local_bonus, ...} Local = local_bonus
  | locality_bonus {assum_bonus, ...} Assum = assum_bonus
  | locality_bonus {chained_bonus, ...} Chained = chained_bonus

fun fact_weight fudge loc const_tab relevant_consts fact_consts =
  case fact_consts |> List.partition (pconst_hyper_mem I relevant_consts)
                   ||> filter_out (pconst_hyper_mem swap relevant_consts) of
    ([], _) => 0.0
  | (rel, irrel) =>
    let
      val irrel = irrel |> filter_out (pconst_mem swap rel)
      val rel_weight =
        0.0 |> fold (curry (op +) o rel_pconst_weight fudge const_tab) rel
      val irrel_weight =
        ~ (locality_bonus fudge loc)
        |> fold (curry (op +) o irrel_pconst_weight fudge const_tab) irrel
      val res = rel_weight / (rel_weight + irrel_weight)
    in if Real.isFinite res then res else 0.0 end

fun pconsts_in_fact thy irrelevant_consts t =
  Symtab.fold (fn (s, pss) => fold (cons o pair s) pss)
              (pconsts_in_terms thy irrelevant_consts true (SOME true) [t]) []
fun pair_consts_fact thy irrelevant_consts fudge fact =
  case fact |> snd |> theory_const_prop_of fudge
            |> pconsts_in_fact thy irrelevant_consts of
    [] => NONE
  | consts => SOME ((fact, consts), NONE)

type annotated_thm =
  (((unit -> string) * locality) * thm) * (string * ptype) list

fun take_most_relevant max_relevant remaining_max
        ({max_imperfect, max_imperfect_exp, ...} : relevance_fudge) 
        (candidates : (annotated_thm * real) list) =
  let
    val max_imperfect =
      Real.ceil (Math.pow (max_imperfect,
                    Math.pow (Real.fromInt remaining_max
                              / Real.fromInt max_relevant, max_imperfect_exp)))
    val (perfect, imperfect) =
      candidates |> sort (Real.compare o swap o pairself snd)
                 |> take_prefix (fn (_, w) => w > 0.99999)
    val ((accepts, more_rejects), rejects) =
      chop max_imperfect imperfect |>> append perfect |>> chop remaining_max
  in
    trace_msg (fn () =>
        "Actually passed (" ^ Int.toString (length accepts) ^ " of " ^
        Int.toString (length candidates) ^ "): " ^
        (accepts |> map (fn ((((name, _), _), _), weight) =>
                            name () ^ " [" ^ Real.toString weight ^ "]")
                 |> commas));
    (accepts, more_rejects @ rejects)
  end

fun if_empty_replace_with_locality thy irrelevant_consts facts loc tab =
  if Symtab.is_empty tab then
    pconsts_in_terms thy irrelevant_consts false (SOME false)
        (map_filter (fn ((_, loc'), th) =>
                        if loc' = loc then SOME (prop_of th) else NONE) facts)
  else
    tab

fun relevance_filter ctxt threshold0 decay max_relevant irrelevant_consts
        (fudge as {threshold_divisor, ridiculous_threshold, ...})
        ({add, del, ...} : relevance_override) facts goal_ts =
  let
    val thy = ProofContext.theory_of ctxt
    val const_tab = fold (count_fact_consts thy fudge) facts Symtab.empty
    val goal_const_tab =
      pconsts_in_terms thy irrelevant_consts false (SOME false) goal_ts
      |> fold (if_empty_replace_with_locality thy irrelevant_consts facts)
              [Chained, Assum, Local]
    val add_ths = Attrib.eval_thms ctxt add
    val del_ths = Attrib.eval_thms ctxt del
    val facts = facts |> filter_out (member Thm.eq_thm del_ths o snd)
    fun iter j remaining_max threshold rel_const_tab hopeless hopeful =
      let
        fun relevant [] _ [] =
            (* Nothing has been added this iteration. *)
            if j = 0 andalso threshold >= ridiculous_threshold then
              (* First iteration? Try again. *)
              iter 0 max_relevant (threshold / threshold_divisor) rel_const_tab
                   hopeless hopeful
            else
              []
          | relevant candidates rejects [] =
            let
              val (accepts, more_rejects) =
                take_most_relevant max_relevant remaining_max fudge candidates
              val rel_const_tab' =
                rel_const_tab
                |> fold (add_pconst_to_table irrelevant_consts false)
                        (maps (snd o fst) accepts)
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
              val threshold =
                1.0 - (1.0 - threshold)
                      * Math.pow (decay, Real.fromInt (length accepts))
              val remaining_max = remaining_max - length accepts
            in
              trace_msg (fn () => "New or updated constants: " ^
                  commas (rel_const_tab' |> Symtab.dest
                          |> subtract (op =) (rel_const_tab |> Symtab.dest)
                          |> map string_for_hyper_pconst));
              map (fst o fst) accepts @
              (if remaining_max = 0 then
                 []
               else
                 iter (j + 1) remaining_max threshold rel_const_tab'
                      hopeless_rejects hopeful_rejects)
            end
          | relevant candidates rejects
                     (((ax as (((_, loc), _), fact_consts)), cached_weight)
                      :: hopeful) =
            let
              val weight =
                case cached_weight of
                  SOME w => w
                | NONE => fact_weight fudge loc const_tab rel_const_tab
                                      fact_consts
            in
              if weight >= threshold then
                relevant ((ax, weight) :: candidates) rejects hopeful
              else
                relevant candidates ((ax, weight) :: rejects) hopeful
            end
        in
          trace_msg (fn () =>
              "ITERATION " ^ string_of_int j ^ ": current threshold: " ^
              Real.toString threshold ^ ", constants: " ^
              commas (rel_const_tab |> Symtab.dest
                      |> filter (curry (op <>) [] o snd)
                      |> map string_for_hyper_pconst));
          relevant [] [] hopeful
        end
    fun add_add_ths accepts =
      (facts |> filter ((member Thm.eq_thm add_ths
                         andf (not o member (Thm.eq_thm o apsnd snd) accepts))
                        o snd))
      @ accepts
  in
    facts |> map_filter (pair_consts_fact thy irrelevant_consts fudge)
          |> iter 0 max_relevant threshold0 goal_const_tab []
          |> not (null add_ths) ? add_add_ths
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
  let val names = Long_Name.explode a in
    (length names > 2 andalso not (hd names = "local") andalso
     String.isSuffix "_def" a) orelse String.isSuffix "_defs" a
  end

fun mk_fact_table f xs =
  fold (Termtab.update o `(prop_of o f)) xs Termtab.empty
fun uniquify xs = Termtab.fold (cons o snd) (mk_fact_table snd xs) []

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

(* FIXME: Extend to "Meson" and "Metis" *)
val exists_sledgehammer_const =
  exists_Const (fn (s, _) => String.isPrefix sledgehammer_prefix s)

(* FIXME: make more reliable *)
val exists_low_level_class_const =
  exists_Const (fn (s, _) =>
     String.isSubstring (Long_Name.separator ^ "class" ^ Long_Name.separator) s)

fun is_metastrange_theorem th =
  case head_of (concl_of th) of
      Const (a, _) => (a <> @{const_name Trueprop} andalso
                       a <> @{const_name "=="})
    | _ => false

fun is_that_fact th =
  String.isSuffix (Long_Name.separator ^ Obtain.thatN) (Thm.get_name_hint th)
  andalso exists_subterm (fn Free (s, _) => s = Name.skolem Auto_Bind.thesisN
                           | _ => false) (prop_of th)

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
      | (_, @{const HOL.implies} $ t1 $ t2) =>
        do_formula (not pos) t1 andalso
        (t2 = @{const False} orelse do_formula pos t2)
      | (_, @{const Not} $ t1) => do_formula (not pos) t1
      | (true, @{const HOL.disj} $ t1 $ t2) => forall (do_formula pos) [t1, t2]
      | (false, @{const HOL.conj} $ t1 $ t2) => forall (do_formula pos) [t1, t2]
      | (true, Const (@{const_name HOL.eq}, _) $ t1 $ t2) => do_equals t1 t2
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
    exists_low_level_class_const t orelse is_metastrange_theorem thm orelse
    is_that_fact thm
  end

fun clasimpset_rules_of ctxt =
  let
    val {safeIs, safeEs, hazIs, hazEs, ...} = ctxt |> claset_of |> rep_cs
    val intros = safeIs @ hazIs
    val elims = map Classical.classical_rule (safeEs @ hazEs)
    val simps = ctxt |> simpset_of |> dest_ss |> #simps |> map snd
  in (mk_fact_table I intros, mk_fact_table I elims, mk_fact_table I simps) end

fun all_prefixes_of s =
  map (fn i => String.extract (s, 0, SOME i)) (1 upto size s - 1)

(* This is a terrible hack. Free variables are sometimes code as "M__" when they
   are displayed as "M" and we want to avoid clashes with these. But sometimes
   it's even worse: "Ma__" encodes "M". So we simply reserve all prefixes of all
   free variables. In the worse case scenario, where the fact won't be resolved
   correctly, the user can fix it manually, e.g., by naming the fact in
   question. Ideally we would need nothing of it, but backticks just don't work
   with schematic variables. *)
fun close_form t =
  (t, [] |> Term.add_free_names t |> maps all_prefixes_of)
  |> fold (fn ((s, i), T) => fn (t', taken) =>
              let val s' = Name.variant taken s in
                (Term.all T $ Abs (s', T, abstract_over (Var ((s, i), T), t')),
                 s' :: taken)
              end)
          (Term.add_vars t [] |> sort_wrt (fst o fst))
  |> fst

fun all_facts ctxt reserved full_types
              ({intro_bonus, elim_bonus, simp_bonus, ...} : relevance_fudge)
              add_ths chained_ths =
  let
    val thy = ProofContext.theory_of ctxt
    val global_facts = Global_Theory.facts_of thy
    val local_facts = ProofContext.facts_of ctxt
    val named_locals = local_facts |> Facts.dest_static []
    val assms = Assumption.all_assms_of ctxt
    fun is_assum th = exists (fn ct => prop_of th aconv term_of ct) assms
    val is_chained = member Thm.eq_thm chained_ths
    val (intros, elims, simps) =
      if exists (curry (op <) 0.0) [intro_bonus, elim_bonus, simp_bonus] then
        clasimpset_rules_of ctxt
      else
        (Termtab.empty, Termtab.empty, Termtab.empty)
    fun is_good_unnamed_local th =
      not (Thm.has_name_hint th) andalso
      forall (fn (_, ths) => not (member Thm.eq_thm ths th)) named_locals
    val unnamed_locals =
      union Thm.eq_thm (Facts.props local_facts) chained_ths
      |> filter is_good_unnamed_local |> map (pair "" o single)
    val full_space =
      Name_Space.merge (Facts.space_of global_facts, Facts.space_of local_facts)
    fun add_facts global foldx facts =
      foldx (fn (name0, ths) =>
        if name0 <> "" andalso
           forall (not o member Thm.eq_thm add_ths) ths andalso
           (Facts.is_concealed facts name0 orelse
            (respect_no_atp andalso is_package_def name0) orelse
            exists (fn s => String.isSuffix s name0) multi_base_blacklist orelse
            String.isSuffix "_def_raw" (* FIXME: crude hack *) name0) then
          I
        else
          let
            val multi = length ths > 1
            fun backquotify th =
              "`" ^ Print_Mode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                                             (print_mode_value ()))
                   (Syntax.string_of_term ctxt) (close_form (prop_of th)) ^ "`"
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
                     not (member Thm.eq_thm add_ths th) then
                    rest
                  else
                    (((fn () =>
                          if name0 = "" then
                            th |> backquotify
                          else
                            let
                              val name1 = Facts.extern facts name0
                              val name2 = Name_Space.extern full_space name0
                            in
                              case find_first check_thms [name1, name2, name0] of
                                SOME name => repair_name reserved multi j name
                              | NONE => ""
                            end),
                      let val t = prop_of th in
                        if is_chained th then
                          Chained
                        else if global then
                          if Termtab.defined intros t then Intro
                          else if Termtab.defined elims t then Elim
                          else if Termtab.defined simps t then Simp
                          else General
                        else
                          if is_assum th then Assum else Local
                      end),
                      (multi, th)) :: rest)) ths
            #> snd
          end)
  in
    [] |> add_facts false fold local_facts (unnamed_locals @ named_locals)
       |> add_facts true Facts.fold_static global_facts global_facts
  end

(* The single-name theorems go after the multiple-name ones, so that single
   names are preferred when both are available. *)
fun rearrange_facts ctxt respect_no_atp =
  List.partition (fst o snd) #> op @ #> map (apsnd snd)
  #> respect_no_atp ? filter_out (No_ATPs.member ctxt o snd)

(***************************************************************)
(* ATP invocation methods setup                                *)
(***************************************************************)

fun relevant_facts ctxt full_types (threshold0, threshold1) max_relevant
                   irrelevant_consts fudge (override as {add, only, ...})
                   chained_ths hyp_ts concl_t =
  let
    val decay = Math.pow ((1.0 - threshold1) / (1.0 - threshold0),
                          1.0 / Real.fromInt (max_relevant + 1))
    val add_ths = Attrib.eval_thms ctxt add
    val reserved = reserved_isar_keyword_table ()
    val facts =
      (if only then
         maps (map (fn ((name, loc), th) => ((K name, loc), (true, th)))
               o fact_from_ref ctxt reserved chained_ths) add
       else
         all_facts ctxt reserved full_types fudge add_ths chained_ths)
      |> rearrange_facts ctxt (respect_no_atp andalso not only)
      |> uniquify
  in
    trace_msg (fn () => "Considering " ^ Int.toString (length facts) ^
                        " facts");
    (if only orelse threshold1 < 0.0 then
       facts
     else if threshold0 > 1.0 orelse threshold0 > threshold1 orelse
             max_relevant = 0 then
       []
     else
       relevance_filter ctxt threshold0 decay max_relevant irrelevant_consts
                        fudge override facts (concl_t :: hyp_ts))
    |> map (apfst (apfst (fn f => f ())))
  end

end;
