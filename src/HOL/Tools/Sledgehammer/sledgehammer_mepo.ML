(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_mepo.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's iterative relevance filter (MePo = Meng-Paulson).
*)

signature SLEDGEHAMMER_MEPO =
sig
  type stature = ATP_Problem_Generate.stature
  type lazy_fact = Sledgehammer_Fact.lazy_fact
  type fact = Sledgehammer_Fact.fact
  type params = Sledgehammer_Prover.params

  type relevance_fudge =
    {local_const_multiplier : real,
     worse_irrel_freq : real,
     higher_order_irrel_weight : real,
     abs_rel_weight : real,
     abs_irrel_weight : real,
     theory_const_rel_weight : real,
     theory_const_irrel_weight : real,
     chained_const_irrel_weight : real,
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

  val trace : bool Config.T
  val pseudo_abs_name : string
  val default_relevance_fudge : relevance_fudge
  val mepo_suggested_facts : Proof.context -> params -> int -> relevance_fudge option ->
    term list -> term -> lazy_fact list -> fact list
end;

structure Sledgehammer_MePo : SLEDGEHAMMER_MEPO =
struct

open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Prover

val trace = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_mepo_trace\<close> (K false)

fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()

val sledgehammer_prefix = "Sledgehammer" ^ Long_Name.separator
val pseudo_abs_name = sledgehammer_prefix ^ "abs"
val theory_const_suffix = Long_Name.separator ^ " 1"

type relevance_fudge =
  {local_const_multiplier : real,
   worse_irrel_freq : real,
   higher_order_irrel_weight : real,
   abs_rel_weight : real,
   abs_irrel_weight : real,
   theory_const_rel_weight : real,
   theory_const_irrel_weight : real,
   chained_const_irrel_weight : real,
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

(* FUDGE *)
val default_relevance_fudge =
  {local_const_multiplier = 1.5,
   worse_irrel_freq = 100.0,
   higher_order_irrel_weight = 1.05,
   abs_rel_weight = 0.5,
   abs_irrel_weight = 2.0,
   theory_const_rel_weight = 0.5,
   theory_const_irrel_weight = 0.25,
   chained_const_irrel_weight = 0.25,
   intro_bonus = 0.15,
   elim_bonus = 0.15,
   simp_bonus = 0.15,
   local_bonus = 0.55,
   assum_bonus = 1.05,
   chained_bonus = 1.5,
   max_imperfect = 11.5,
   max_imperfect_exp = 1.0,
   threshold_divisor = 2.0,
   ridiculous_threshold = 0.1}

fun order_of_type (Type (\<^type_name>\<open>fun\<close>, [T1, T2])) =
    Int.max (order_of_type T1 + 1, order_of_type T2)
  | order_of_type (Type (_, Ts)) = fold (Integer.max o order_of_type) Ts 0
  | order_of_type _ = 0

(* An abstraction of Isabelle types and first-order terms *)
datatype pattern = PVar | PApp of string * pattern list
datatype ptype = PType of int * typ list

fun string_of_patternT (TVar _) = "_"
  | string_of_patternT (Type (s, ps)) = if null ps then s else s ^ string_of_patternsT ps
  | string_of_patternT (TFree (s, _)) = s
and string_of_patternsT ps = "(" ^ commas (map string_of_patternT ps) ^ ")"
fun string_of_ptype (PType (_, ps)) = string_of_patternsT ps

(*Is the second type an instance of the first one?*)
fun match_patternT (TVar _, _) = true
  | match_patternT (Type (s, ps), Type (t, qs)) = s = t andalso match_patternsT (ps, qs)
  | match_patternT (TFree (s, _), TFree (t, _)) = s = t
  | match_patternT (_, _) = false
and match_patternsT (_, []) = true
  | match_patternsT ([], _) = false
  | match_patternsT (p :: ps, q :: qs) = match_patternT (p, q) andalso match_patternsT (ps, qs)
fun match_ptype (PType (_, ps), PType (_, qs)) = match_patternsT (ps, qs)

(* Is there a unifiable constant? *)
fun pconst_mem f consts (s, ps) =
  exists (curry (match_ptype o f) ps) (map snd (filter (curry (op =) s o fst) consts))

fun pconst_hyper_mem f const_tab (s, ps) =
  exists (curry (match_ptype o f) ps) (these (Symtab.lookup const_tab s))

(* Pairs a constant with the list of its type instantiations. *)
fun ptype thy const x = (if const then these (try (Sign.const_typargs thy) x) else [])
fun rich_ptype thy const (s, T) = PType (order_of_type T, ptype thy const (s, T))
fun rich_pconst thy const (s, T) = (s, rich_ptype thy const (s, T))

fun string_of_hyper_pconst (s, ps) = s ^ "{" ^ commas (map string_of_ptype ps) ^ "}"

fun patternT_eq (TVar _, TVar _) = true
  | patternT_eq (Type (s, Ts), Type (t, Us)) = s = t andalso patternsT_eq (Ts, Us)
  | patternT_eq (TFree (s, _), TFree (t, _)) = (s = t)
  | patternT_eq _ = false
and patternsT_eq ([], []) = true
  | patternsT_eq ([], _) = false
  | patternsT_eq (_, []) = false
  | patternsT_eq (T :: Ts, U :: Us) = patternT_eq (T, U) andalso patternsT_eq (Ts, Us)

fun ptype_eq (PType (m, Ts), PType (n, Us)) = m = n andalso patternsT_eq (Ts, Us)

 (* Add a pconstant to the table, but a [] entry means a standard connective, which we ignore. *)
fun add_pconst_to_table (s, p) = Symtab.map_default (s, [p]) (insert ptype_eq p)

(* Set constants tend to pull in too many irrelevant facts. We limit the damage by treating them
   more or less as if they were built-in but add their axiomatization at the end. *)
val set_consts = [\<^const_name>\<open>Collect\<close>, \<^const_name>\<open>Set.member\<close>]
val set_thms = @{thms Collect_mem_eq mem_Collect_eq Collect_cong}

fun add_pconsts_in_term thy =
  let
    fun do_const const (x as (s, _)) ts =
      if member (op =) set_consts s then
        fold (do_term false) ts
      else
        (not (is_irrelevant_const s) ? add_pconst_to_table (rich_pconst thy const x))
        #> fold (do_term false) ts
    and do_term ext_arg t =
      (case strip_comb t of
        (Const x, ts) => do_const true x ts
      | (Free x, ts) => do_const false x ts
      | (Abs (_, T, t'), ts) =>
        ((null ts andalso not ext_arg)
         (* Since lambdas on the right-hand side of equalities are usually extensionalized later by
            "abs_extensionalize_term", we don't penalize them here. *)
         ? add_pconst_to_table (pseudo_abs_name, PType (order_of_type T + 1, [])))
        #> fold (do_term false) (t' :: ts)
      | (_, ts) => fold (do_term false) ts)
    and do_term_or_formula ext_arg T =
      if T = HOLogic.boolT then do_formula else do_term ext_arg
    and do_formula t =
      (case t of
        Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, t') => do_formula t'
      | \<^const>\<open>Pure.imp\<close> $ t1 $ t2 => do_formula t1 #> do_formula t2
      | Const (\<^const_name>\<open>Pure.eq\<close>, Type (_, [T, _])) $ t1 $ t2 =>
        do_term_or_formula false T t1 #> do_term_or_formula true T t2
      | \<^const>\<open>Trueprop\<close> $ t1 => do_formula t1
      | \<^const>\<open>False\<close> => I
      | \<^const>\<open>True\<close> => I
      | \<^const>\<open>Not\<close> $ t1 => do_formula t1
      | Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t') => do_formula t'
      | Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _, t') => do_formula t'
      | \<^const>\<open>HOL.conj\<close> $ t1 $ t2 => do_formula t1 #> do_formula t2
      | \<^const>\<open>HOL.disj\<close> $ t1 $ t2 => do_formula t1 #> do_formula t2
      | \<^const>\<open>HOL.implies\<close> $ t1 $ t2 => do_formula t1 #> do_formula t2
      | Const (\<^const_name>\<open>HOL.eq\<close>, Type (_, [T, _])) $ t1 $ t2 =>
        do_term_or_formula false T t1 #> do_term_or_formula true T t2
      | Const (\<^const_name>\<open>If\<close>, Type (_, [_, Type (_, [T, _])])) $ t1 $ t2 $ t3 =>
        do_formula t1 #> fold (do_term_or_formula false T) [t2, t3]
      | Const (\<^const_name>\<open>Ex1\<close>, _) $ Abs (_, _, t') => do_formula t'
      | Const (\<^const_name>\<open>Ball\<close>, _) $ t1 $ Abs (_, _, t') =>
        do_formula (t1 $ Bound ~1) #> do_formula t'
      | Const (\<^const_name>\<open>Bex\<close>, _) $ t1 $ Abs (_, _, t') =>
        do_formula (t1 $ Bound ~1) #> do_formula t'
      | (t0 as Const (_, \<^typ>\<open>bool\<close>)) $ t1 =>
        do_term false t0 #> do_formula t1  (* theory constant *)
      | _ => do_term false t)
  in
    do_formula
  end

fun pconsts_in_fact thy t =
  Symtab.fold (fn (s, pss) => fold (cons o pair s) pss) (Symtab.empty |> add_pconsts_in_term thy t)
    []

(* Inserts a dummy "constant" referring to the theory name, so that relevance
   takes the given theory into account. *)
fun theory_constify ({theory_const_rel_weight, theory_const_irrel_weight, ...} : relevance_fudge)
    thy_name t =
  if exists (curry (op <) 0.0) [theory_const_rel_weight, theory_const_irrel_weight] then
    Const (thy_name ^ theory_const_suffix, \<^typ>\<open>bool\<close>) $ t
  else
    t

fun theory_const_prop_of fudge th =
  theory_constify fudge (Thm.theory_name th) (Thm.prop_of th)

fun pair_consts_fact thy fudge fact =
  (case fact |> snd |> theory_const_prop_of fudge |> pconsts_in_fact thy of
    [] => NONE
  | consts => SOME ((fact, consts), NONE))

(* A two-dimensional symbol table counts frequencies of constants. It's keyed
   first by constant name and second by its list of type instantiations. For the
   latter, we need a linear ordering on "pattern list". *)

fun patternT_ord p =
  (case p of
    (Type (s, ps), Type (t, qs)) =>
    (case fast_string_ord (s, t) of
      EQUAL => dict_ord patternT_ord (ps, qs)
    | ord => ord)
  | (TVar _, TVar _) => EQUAL
  | (TVar _, _) => LESS
  | (Type _, TVar _) => GREATER
  | (Type _, TFree _) => LESS
  | (TFree (s, _), TFree (t, _)) => fast_string_ord (s, t)
  | (TFree _, _) => GREATER)

fun ptype_ord (PType (m, ps), PType (n, qs)) =
  (case dict_ord patternT_ord (ps, qs) of
    EQUAL => int_ord (m, n)
  | ord => ord)

structure PType_Tab = Table(type key = ptype val ord = ptype_ord)

fun count_fact_consts thy fudge =
  let
    fun do_const const (s, T) ts =
      (* Two-dimensional table update. Constant maps to types maps to count. *)
      PType_Tab.map_default (rich_ptype thy const (s, T), 0) (Integer.add 1)
      |> Symtab.map_default (s, PType_Tab.empty)
      #> fold do_term ts
    and do_term t =
      (case strip_comb t of
        (Const x, ts) => do_const true x ts
      | (Free x, ts) => do_const false x ts
      | (Abs (_, _, t'), ts) => fold do_term (t' :: ts)
      | (_, ts) => fold do_term ts)
  in do_term o theory_const_prop_of fudge o snd end

fun pow_int _ 0 = 1.0
  | pow_int x 1 = x
  | pow_int x n = if n > 0 then x * pow_int x (n - 1) else pow_int x (n + 1) / x

(*The frequency of a constant is the sum of those of all instances of its type.*)
fun pconst_freq match const_tab (c, ps) =
  PType_Tab.fold (fn (qs, m) => match (ps, qs) ? Integer.add m) (the (Symtab.lookup const_tab c)) 0

(* A surprising number of theorems contain only a few significant constants. These include all
   induction rules and other general theorems. *)

(* "log" seems best in practice. A constant function of one ignores the constant
   frequencies. Rare constants give more points if they are relevant than less
   rare ones. *)
fun rel_weight_for _ freq = 1.0 + 2.0 / Math.ln (Real.fromInt freq + 1.0)

(* Irrelevant constants are treated differently. We associate lower penalties to
   very rare constants and very common ones -- the former because they can't
   lead to the inclusion of too many new facts, and the latter because they are
   so common as to be of little interest. *)
fun irrel_weight_for ({worse_irrel_freq, higher_order_irrel_weight, ...} : relevance_fudge) order
    freq =
  let val (k, x) = worse_irrel_freq |> `Real.ceil in
    (if freq < k then Math.ln (Real.fromInt (freq + 1)) / Math.ln x
     else rel_weight_for order freq / rel_weight_for order k)
    * pow_int higher_order_irrel_weight (order - 1)
  end

fun multiplier_of_const_name local_const_multiplier s =
  if String.isSubstring "." s then 1.0 else local_const_multiplier

(* Computes a constant's weight, as determined by its frequency. *)
fun generic_pconst_weight local_const_multiplier abs_weight theory_const_weight chained_const_weight
    weight_for f const_tab chained_const_tab (c as (s, PType (m, _))) =
  if s = pseudo_abs_name then
    abs_weight
  else if String.isSuffix theory_const_suffix s then
    theory_const_weight
  else
    multiplier_of_const_name local_const_multiplier s
    * weight_for m (pconst_freq (match_ptype o f) const_tab c)
    |> (if chained_const_weight < 1.0 andalso pconst_hyper_mem I chained_const_tab c then
          curry (op *) chained_const_weight
        else
          I)

fun rel_pconst_weight ({local_const_multiplier, abs_rel_weight, theory_const_rel_weight,
    ...} : relevance_fudge) const_tab =
  generic_pconst_weight local_const_multiplier abs_rel_weight theory_const_rel_weight 0.0
    rel_weight_for I const_tab Symtab.empty

fun irrel_pconst_weight (fudge as {local_const_multiplier, abs_irrel_weight,
    theory_const_irrel_weight, chained_const_irrel_weight, ...}) const_tab chained_const_tab =
  generic_pconst_weight local_const_multiplier abs_irrel_weight theory_const_irrel_weight
    chained_const_irrel_weight (irrel_weight_for fudge) swap const_tab chained_const_tab

fun stature_bonus ({intro_bonus, ...} : relevance_fudge) (_, Intro) = intro_bonus
  | stature_bonus {elim_bonus, ...} (_, Elim) = elim_bonus
  | stature_bonus {simp_bonus, ...} (_, Simp) = simp_bonus
  | stature_bonus {local_bonus, ...} (Local, _) = local_bonus
  | stature_bonus {assum_bonus, ...} (Assum, _) = assum_bonus
  | stature_bonus {chained_bonus, ...} (Chained, _) = chained_bonus
  | stature_bonus _ _ = 0.0

fun is_odd_const_name s =
  s = pseudo_abs_name orelse String.isSuffix theory_const_suffix s

fun fact_weight fudge stature const_tab rel_const_tab chained_const_tab
                fact_consts =
  (case fact_consts |> List.partition (pconst_hyper_mem I rel_const_tab)
                   ||> filter_out (pconst_hyper_mem swap rel_const_tab) of
    ([], _) => 0.0
  | (rel, irrel) =>
    if forall (forall (is_odd_const_name o fst)) [rel, irrel] then
      0.0
    else
      let
        val irrel = irrel |> filter_out (pconst_mem swap rel)
        val rel_weight = 0.0 |> fold (curry (op +) o rel_pconst_weight fudge const_tab) rel
        val irrel_weight =
          ~ (stature_bonus fudge stature)
          |> fold (curry (op +) o irrel_pconst_weight fudge const_tab chained_const_tab) irrel
        val res = rel_weight / (rel_weight + irrel_weight)
      in
        if Real.isFinite res then res else 0.0
      end)

fun take_most_relevant ctxt max_facts remaining_max
    ({max_imperfect, max_imperfect_exp, ...} : relevance_fudge)
    (candidates : ((lazy_fact * (string * ptype) list) * real) list) =
  let
    val max_imperfect =
      Real.ceil (Math.pow (max_imperfect,
        Math.pow (Real.fromInt remaining_max / Real.fromInt max_facts, max_imperfect_exp)))
    val (perfect, imperfect) = candidates
      |> sort (Real.compare o swap o apply2 snd)
      |> chop_prefix (fn (_, w) => w > 0.99999)
    val ((accepts, more_rejects), rejects) =
      chop max_imperfect imperfect |>> append perfect |>> chop remaining_max
  in
    trace_msg ctxt (fn () =>
      "Actually passed (" ^ string_of_int (length accepts) ^ " of " ^
      string_of_int (length candidates) ^ "): " ^
      (accepts
       |> map (fn ((((name, _), _), _), weight) => name () ^ " [" ^ Real.toString weight ^ "]")
       |> commas));
    (accepts, more_rejects @ rejects)
  end

fun if_empty_replace_with_scope thy facts sc tab =
  if Symtab.is_empty tab then
    Symtab.empty
    |> fold (add_pconsts_in_term thy) (map_filter (fn ((_, (sc', _)), th) =>
      if sc' = sc then SOME (Thm.prop_of th) else NONE) facts)
  else
    tab

fun consider_arities th =
  let
    fun aux _ _ NONE = NONE
      | aux t args (SOME tab) =
        (case t of
          t1 $ t2 => SOME tab |> aux t1 (t2 :: args) |> aux t2 []
        | Const (s, _) =>
          (if is_widely_irrelevant_const s then
             SOME tab
           else
             (case Symtab.lookup tab s of
               NONE => SOME (Symtab.update (s, length args) tab)
             | SOME n => if n = length args then SOME tab else NONE))
        | _ => SOME tab)
  in
    aux (Thm.prop_of th) []
  end

(* FIXME: This is currently only useful for polymorphic type encodings. *)
fun could_benefit_from_ext facts =
  fold (consider_arities o snd) facts (SOME Symtab.empty) |> is_none

(* High enough so that it isn't wrongly considered as very relevant (e.g., for E
   weights), but low enough so that it is unlikely to be truncated away if few
   facts are included. *)
val special_fact_index = 45 (* FUDGE *)

fun eq_prod eqx eqy ((x1, y1), (x2, y2)) = eqx (x1, x2) andalso eqy (y1, y2)

val really_hopeless_get_kicked_out_iter = 5 (* FUDGE *)

fun relevance_filter ctxt thres0 decay max_facts
        (fudge as {threshold_divisor, ridiculous_threshold, ...}) facts hyp_ts concl_t =
  let
    val thy = Proof_Context.theory_of ctxt
    val const_tab = fold (count_fact_consts thy fudge) facts Symtab.empty
    val add_pconsts = add_pconsts_in_term thy
    val chained_ts =
      facts |> map_filter (try (fn ((_, (Chained, _)), th) => Thm.prop_of th))
    val chained_const_tab = Symtab.empty |> fold add_pconsts chained_ts
    val goal_const_tab =
      Symtab.empty
      |> fold add_pconsts hyp_ts
      |> add_pconsts concl_t
      |> (fn tab => if Symtab.is_empty tab then chained_const_tab else tab)
      |> fold (if_empty_replace_with_scope thy facts) [Chained, Assum, Local]

    fun iter j remaining_max thres rel_const_tab hopeless hopeful =
      let
        val hopeless =
          hopeless |> j = really_hopeless_get_kicked_out_iter ? filter_out (fn (_, w) => w < 0.001)
        fun relevant [] _ [] =
            (* Nothing has been added this iteration. *)
            if j = 0 andalso thres >= ridiculous_threshold then
              (* First iteration? Try again. *)
              iter 0 max_facts (thres / threshold_divisor) rel_const_tab hopeless hopeful
            else
              []
          | relevant candidates rejects [] =
            let
              val (accepts, more_rejects) =
                take_most_relevant ctxt max_facts remaining_max fudge candidates
              val sps = maps (snd o fst) accepts
              val rel_const_tab' =
                rel_const_tab |> fold add_pconst_to_table sps

              fun is_dirty (s, _) = Symtab.lookup rel_const_tab' s <> Symtab.lookup rel_const_tab s

              val (hopeful_rejects, hopeless_rejects) =
                 (rejects @ hopeless, ([], []))
                 |-> fold (fn (ax as (_, consts), old_weight) =>
                   if exists is_dirty consts then apfst (cons (ax, NONE))
                   else apsnd (cons (ax, old_weight)))
                 |>> append (more_rejects
                             |> map (fn (ax as (_, consts), old_weight) =>
                                        (ax, if exists is_dirty consts then NONE
                                             else SOME old_weight)))
              val thres = 1.0 - (1.0 - thres) * Math.pow (decay, Real.fromInt (length accepts))
              val remaining_max = remaining_max - length accepts
            in
              trace_msg ctxt (fn () => "New or updated constants: " ^
                commas (rel_const_tab'
                  |> Symtab.dest
                  |> subtract (eq_prod (op =) (eq_list ptype_eq)) (Symtab.dest rel_const_tab)
                  |> map string_of_hyper_pconst));
              map (fst o fst) accepts @
              (if remaining_max = 0 then
                 []
               else
                 iter (j + 1) remaining_max thres rel_const_tab' hopeless_rejects hopeful_rejects)
            end
          | relevant candidates rejects
              (((ax as (((_, stature), _), fact_consts)), cached_weight) :: hopeful) =
            let
              val weight =
                (case cached_weight of
                  SOME w => w
                | NONE =>
                  fact_weight fudge stature const_tab rel_const_tab chained_const_tab fact_consts)
            in
              if weight >= thres then
                relevant ((ax, weight) :: candidates) rejects hopeful
              else
                relevant candidates ((ax, weight) :: rejects) hopeful
            end
        in
          trace_msg ctxt (fn () =>
              "ITERATION " ^ string_of_int j ^ ": current threshold: " ^
              Real.toString thres ^ ", constants: " ^
              commas (rel_const_tab
                      |> Symtab.dest
                      |> filter (curry (op <>) [] o snd)
                      |> map string_of_hyper_pconst));
          relevant [] [] hopeful
        end
    fun uses_const s t =
      fold_aterms (curry (fn (Const (s', _), false) => s' = s | (_, b) => b)) t
                  false
    fun uses_const_anywhere accepts s =
      exists (uses_const s o Thm.prop_of o snd) accepts orelse
      exists (uses_const s) (concl_t :: hyp_ts)
    fun add_set_const_thms accepts =
      exists (uses_const_anywhere accepts) set_consts ? append set_thms
    fun insert_into_facts accepts [] = accepts
      | insert_into_facts accepts ths =
        let
          val add = facts |> filter (member Thm.eq_thm_prop ths o snd)
          val (bef, after) = accepts
            |> filter_out (member Thm.eq_thm_prop ths o snd)
            |> take (max_facts - length add)
            |> chop special_fact_index
        in
          bef @ add @ after
        end
    fun insert_special_facts accepts =
      (* FIXME: get rid of "ext" here once it is treated as a helper *)
      []
      |> could_benefit_from_ext accepts ? cons @{thm ext}
      |> add_set_const_thms accepts
      |> insert_into_facts accepts
  in
    facts
    |> map_filter (pair_consts_fact thy fudge)
    |> iter 0 max_facts thres0 goal_const_tab []
    |> insert_special_facts
    |> tap (fn accepts => trace_msg ctxt (fn () =>
      "Total relevant: " ^ string_of_int (length accepts)))
  end

fun mepo_suggested_facts ctxt ({fact_thresholds = (thres0, thres1), ...} : params) max_facts fudge
    hyp_ts concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val fudge = fudge |> the_default default_relevance_fudge
    val decay = Math.pow ((1.0 - thres1) / (1.0 - thres0), 1.0 / Real.fromInt (max_facts + 1))
  in
    trace_msg ctxt (fn () => "Considering " ^ string_of_int (length facts) ^ " facts");
    (if thres1 < 0.0 then
       facts
     else if thres0 > 1.0 orelse thres0 > thres1 orelse max_facts <= 0 then
       []
     else
       relevance_filter ctxt thres0 decay max_facts fudge facts hyp_ts
         (concl_t |> theory_constify fudge (Context.theory_name thy)))
    |> map fact_of_lazy_fact
  end

end;
