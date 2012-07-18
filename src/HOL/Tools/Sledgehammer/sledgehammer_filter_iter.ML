(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_filter_iter.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's iterative relevance filter.
*)

signature SLEDGEHAMMER_FILTER_ITER =
sig
  type stature = ATP_Problem_Generate.stature
  type relevance_override = Sledgehammer_Fact.relevance_override
  type params = Sledgehammer_Provers.params
  type relevance_fudge = Sledgehammer_Provers.relevance_fudge

  val trace : bool Config.T
  val pseudo_abs_name : string
  val pseudo_skolem_prefix : string
  val const_names_in_fact :
    theory -> (string * typ -> term list -> bool * term list) -> term
    -> string list
  val iterative_relevant_facts :
    Proof.context -> params -> string -> int -> relevance_fudge option
    -> relevance_override -> thm list -> term list -> term
    -> (((unit -> string) * stature) * thm) list
    -> ((string * stature) * thm) list
end;

structure Sledgehammer_Filter_Iter : SLEDGEHAMMER_FILTER_ITER =
struct

open ATP_Problem_Generate
open Sledgehammer_Fact
open Sledgehammer_Provers

val trace =
  Attrib.setup_config_bool @{binding sledgehammer_filter_trace} (K false)
fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()

val sledgehammer_prefix = "Sledgehammer" ^ Long_Name.separator
val pseudo_abs_name = sledgehammer_prefix ^ "abs"
val pseudo_skolem_prefix = sledgehammer_prefix ^ "sko"
val theory_const_suffix = Long_Name.separator ^ " 1"

fun order_of_type (Type (@{type_name fun}, [T1, T2])) =
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

(* Pairs a constant with the list of its type instantiations. *)
fun ptype thy const x =
  (if const then map pattern_for_type (these (try (Sign.const_typargs thy) x))
   else [])
fun rich_ptype thy const (s, T) =
  PType (order_of_type T, ptype thy const (s, T))
fun rich_pconst thy const (s, T) = (s, rich_ptype thy const (s, T))

fun string_for_hyper_pconst (s, ps) =
  s ^ "{" ^ commas (map string_for_ptype ps) ^ "}"

(* Add a pconstant to the table, but a [] entry means a standard
   connective, which we ignore.*)
fun add_pconst_to_table also_skolem (s, p) =
  if (not also_skolem andalso String.isPrefix pseudo_skolem_prefix s) then I
  else Symtab.map_default (s, [p]) (insert (op =) p)

(* Set constants tend to pull in too many irrelevant facts. We limit the damage
   by treating them more or less as if they were built-in but add their
   axiomatization at the end. *)
val set_consts = [@{const_name Collect}, @{const_name Set.member}]
val set_thms = @{thms Collect_mem_eq mem_Collect_eq Collect_cong}

fun add_pconsts_in_term thy is_built_in_const also_skolems pos =
  let
    val flip = Option.map not
    (* We include free variables, as well as constants, to handle locales. For
       each quantifiers that must necessarily be skolemized by the automatic
       prover, we introduce a fresh constant to simulate the effect of
       Skolemization. *)
    fun do_const const ext_arg (x as (s, _)) ts =
      let val (built_in, ts) = is_built_in_const x ts in
        if member (op =) set_consts s then
          fold (do_term ext_arg) ts
        else
          (not built_in
           ? add_pconst_to_table also_skolems (rich_pconst thy const x))
          #> fold (do_term false) ts
      end
    and do_term ext_arg t =
      case strip_comb t of
        (Const x, ts) => do_const true ext_arg x ts
      | (Free x, ts) => do_const false ext_arg x ts
      | (Abs (_, T, t'), ts) =>
        ((null ts andalso not ext_arg)
         (* Since lambdas on the right-hand side of equalities are usually
            extensionalized later by "abs_extensionalize_term", we don't
            penalize them here. *)
         ? add_pconst_to_table true (pseudo_abs_name,
                                     PType (order_of_type T + 1, [])))
        #> fold (do_term false) (t' :: ts)
      | (_, ts) => fold (do_term false) ts
    fun do_quantifier will_surely_be_skolemized abs_T body_t =
      do_formula pos body_t
      #> (if also_skolems andalso will_surely_be_skolemized then
            add_pconst_to_table true (pseudo_skolem_prefix ^ serial_string (),
                                      PType (order_of_type abs_T, []))
          else
            I)
    and do_term_or_formula ext_arg T =
      if T = HOLogic.boolT then do_formula NONE else do_term ext_arg
    and do_formula pos t =
      case t of
        Const (@{const_name all}, _) $ Abs (_, T, t') =>
        do_quantifier (pos = SOME false) T t'
      | @{const "==>"} $ t1 $ t2 =>
        do_formula (flip pos) t1 #> do_formula pos t2
      | Const (@{const_name "=="}, Type (_, [T, _])) $ t1 $ t2 =>
        do_term_or_formula false T t1 #> do_term_or_formula true T t2
      | @{const Trueprop} $ t1 => do_formula pos t1
      | @{const False} => I
      | @{const True} => I
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
        do_term_or_formula false T t1 #> do_term_or_formula true T t2
      | Const (@{const_name If}, Type (_, [_, Type (_, [T, _])]))
        $ t1 $ t2 $ t3 =>
        do_formula NONE t1 #> fold (do_term_or_formula false T) [t2, t3]
      | Const (@{const_name Ex1}, _) $ Abs (_, T, t') =>
        do_quantifier (is_some pos) T t'
      | Const (@{const_name Ball}, _) $ t1 $ Abs (_, T, t') =>
        do_quantifier (pos = SOME false) T
                      (HOLogic.mk_imp (incr_boundvars 1 t1 $ Bound 0, t'))
      | Const (@{const_name Bex}, _) $ t1 $ Abs (_, T, t') =>
        do_quantifier (pos = SOME true) T
                      (HOLogic.mk_conj (incr_boundvars 1 t1 $ Bound 0, t'))
      | (t0 as Const (_, @{typ bool})) $ t1 =>
        do_term false t0 #> do_formula pos t1  (* theory constant *)
      | _ => do_term false t
  in do_formula pos end

fun pconsts_in_fact thy is_built_in_const t =
  Symtab.fold (fn (s, pss) => fold (cons o pair s) pss)
              (Symtab.empty |> add_pconsts_in_term thy is_built_in_const true
                                                   (SOME true) t) []

val const_names_in_fact = map fst ooo pconsts_in_fact

(* Inserts a dummy "constant" referring to the theory name, so that relevance
   takes the given theory into account. *)
fun theory_constify ({theory_const_rel_weight, theory_const_irrel_weight, ...}
                     : relevance_fudge) thy_name t =
  if exists (curry (op <) 0.0) [theory_const_rel_weight,
                                theory_const_irrel_weight] then
    Const (thy_name ^ theory_const_suffix, @{typ bool}) $ t
  else
    t

fun theory_const_prop_of fudge th =
  theory_constify fudge (Context.theory_name (theory_of_thm th)) (prop_of th)

fun pair_consts_fact thy is_built_in_const fudge fact =
  case fact |> snd |> theory_const_prop_of fudge
            |> pconsts_in_fact thy is_built_in_const of
    [] => NONE
  | consts => SOME ((fact, consts), NONE)

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
      PType_Tab.map_default (rich_ptype thy const (s, T), 0) (Integer.add 1)
      |> Symtab.map_default (s, PType_Tab.empty)
      #> fold do_term ts
    and do_term t =
      case strip_comb t of
        (Const x, ts) => do_const true x ts
      | (Free x, ts) => do_const false x ts
      | (Abs (_, _, t'), ts) => fold do_term (t' :: ts)
      | (_, ts) => fold do_term ts
  in do_term o theory_const_prop_of fudge o snd end

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

fun multiplier_for_const_name local_const_multiplier s =
  if String.isSubstring "." s then 1.0 else local_const_multiplier

(* Computes a constant's weight, as determined by its frequency. *)
fun generic_pconst_weight local_const_multiplier abs_weight skolem_weight
                          theory_const_weight chained_const_weight weight_for f
                          const_tab chained_const_tab (c as (s, PType (m, _))) =
  if s = pseudo_abs_name then
    abs_weight
  else if String.isPrefix pseudo_skolem_prefix s then
    skolem_weight
  else if String.isSuffix theory_const_suffix s then
    theory_const_weight
  else
    multiplier_for_const_name local_const_multiplier s
    * weight_for m (pconst_freq (match_ptype o f) const_tab c)
    |> (if chained_const_weight < 1.0 andalso
           pconst_hyper_mem I chained_const_tab c then
          curry (op *) chained_const_weight
        else
          I)

fun rel_pconst_weight ({local_const_multiplier, abs_rel_weight,
                        theory_const_rel_weight, ...} : relevance_fudge)
                      const_tab =
  generic_pconst_weight local_const_multiplier abs_rel_weight 0.0
                        theory_const_rel_weight 0.0 rel_weight_for I const_tab
                        Symtab.empty

fun irrel_pconst_weight (fudge as {local_const_multiplier, abs_irrel_weight,
                                   skolem_irrel_weight,
                                   theory_const_irrel_weight,
                                   chained_const_irrel_weight, ...})
                        const_tab chained_const_tab =
  generic_pconst_weight local_const_multiplier abs_irrel_weight
                        skolem_irrel_weight theory_const_irrel_weight
                        chained_const_irrel_weight (irrel_weight_for fudge) swap
                        const_tab chained_const_tab

fun stature_bonus ({intro_bonus, ...} : relevance_fudge) (_, Intro) =
    intro_bonus
  | stature_bonus {elim_bonus, ...} (_, Elim) = elim_bonus
  | stature_bonus {simp_bonus, ...} (_, Simp) = simp_bonus
  | stature_bonus {local_bonus, ...} (Local, _) = local_bonus
  | stature_bonus {assum_bonus, ...} (Assum, _) = assum_bonus
  | stature_bonus {chained_bonus, ...} (Chained, _) = chained_bonus
  | stature_bonus _ _ = 0.0

fun is_odd_const_name s =
  s = pseudo_abs_name orelse String.isPrefix pseudo_skolem_prefix s orelse
  String.isSuffix theory_const_suffix s

fun fact_weight fudge stature const_tab relevant_consts chained_consts
                fact_consts =
  case fact_consts |> List.partition (pconst_hyper_mem I relevant_consts)
                   ||> filter_out (pconst_hyper_mem swap relevant_consts) of
    ([], _) => 0.0
  | (rel, irrel) =>
    if forall (forall (is_odd_const_name o fst)) [rel, irrel] then
      0.0
    else
      let
        val irrel = irrel |> filter_out (pconst_mem swap rel)
        val rel_weight =
          0.0 |> fold (curry (op +) o rel_pconst_weight fudge const_tab) rel
        val irrel_weight =
          ~ (stature_bonus fudge stature)
          |> fold (curry (op +)
                   o irrel_pconst_weight fudge const_tab chained_consts) irrel
        val res = rel_weight / (rel_weight + irrel_weight)
      in if Real.isFinite res then res else 0.0 end

type annotated_thm =
  (((unit -> string) * stature) * thm) * (string * ptype) list

fun take_most_relevant ctxt max_relevant remaining_max
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
    trace_msg ctxt (fn () =>
        "Actually passed (" ^ string_of_int (length accepts) ^ " of " ^
        string_of_int (length candidates) ^ "): " ^
        (accepts |> map (fn ((((name, _), _), _), weight) =>
                            name () ^ " [" ^ Real.toString weight ^ "]")
                 |> commas));
    (accepts, more_rejects @ rejects)
  end

fun if_empty_replace_with_scope thy is_built_in_const facts sc tab =
  if Symtab.is_empty tab then
    Symtab.empty
    |> fold (add_pconsts_in_term thy is_built_in_const false (SOME false))
            (map_filter (fn ((_, (sc', _)), th) =>
                            if sc' = sc then SOME (prop_of th) else NONE) facts)
  else
    tab

fun consider_arities is_built_in_const th =
  let
    fun aux _ _ NONE = NONE
      | aux t args (SOME tab) =
        case t of
          t1 $ t2 => SOME tab |> aux t1 (t2 :: args) |> aux t2 []
        | Const (x as (s, _)) =>
          (if is_built_in_const x args |> fst then
             SOME tab
           else case Symtab.lookup tab s of
             NONE => SOME (Symtab.update (s, length args) tab)
           | SOME n => if n = length args then SOME tab else NONE)
        | _ => SOME tab
  in aux (prop_of th) [] end

(* FIXME: This is currently only useful for polymorphic type encodings. *)
fun could_benefit_from_ext is_built_in_const facts =
  fold (consider_arities is_built_in_const o snd) facts (SOME Symtab.empty)
  |> is_none

(* High enough so that it isn't wrongly considered as very relevant (e.g., for E
   weights), but low enough so that it is unlikely to be truncated away if few
   facts are included. *)
val special_fact_index = 75

fun relevance_filter ctxt thres0 decay max_relevant is_built_in_const
        (fudge as {threshold_divisor, ridiculous_threshold, ...})
        ({del, ...} : relevance_override) facts chained_ts hyp_ts concl_t =
  let
    val thy = Proof_Context.theory_of ctxt
    val const_tab = fold (count_fact_consts thy fudge) facts Symtab.empty
    val add_pconsts = add_pconsts_in_term thy is_built_in_const false o SOME
    val chained_const_tab = Symtab.empty |> fold (add_pconsts true) chained_ts
    val goal_const_tab =
      Symtab.empty |> fold (add_pconsts true) hyp_ts
                   |> add_pconsts false concl_t
      |> (fn tab => if Symtab.is_empty tab then chained_const_tab else tab)
      |> fold (if_empty_replace_with_scope thy is_built_in_const facts)
              [Chained, Assum, Local]
    val del_ths = Attrib.eval_thms ctxt del
    val facts = facts |> filter_out (member Thm.eq_thm_prop del_ths o snd)
    fun iter j remaining_max thres rel_const_tab hopeless hopeful =
      let
        fun relevant [] _ [] =
            (* Nothing has been added this iteration. *)
            if j = 0 andalso thres >= ridiculous_threshold then
              (* First iteration? Try again. *)
              iter 0 max_relevant (thres / threshold_divisor) rel_const_tab
                   hopeless hopeful
            else
              []
          | relevant candidates rejects [] =
            let
              val (accepts, more_rejects) =
                take_most_relevant ctxt max_relevant remaining_max fudge
                                   candidates
              val rel_const_tab' =
                rel_const_tab
                |> fold (add_pconst_to_table false) (maps (snd o fst) accepts)
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
              val thres =
                1.0 - (1.0 - thres)
                      * Math.pow (decay, Real.fromInt (length accepts))
              val remaining_max = remaining_max - length accepts
            in
              trace_msg ctxt (fn () => "New or updated constants: " ^
                  commas (rel_const_tab' |> Symtab.dest
                          |> subtract (op =) (rel_const_tab |> Symtab.dest)
                          |> map string_for_hyper_pconst));
              map (fst o fst) accepts @
              (if remaining_max = 0 then
                 []
               else
                 iter (j + 1) remaining_max thres rel_const_tab'
                      hopeless_rejects hopeful_rejects)
            end
          | relevant candidates rejects
                     (((ax as (((_, stature), _), fact_consts)), cached_weight)
                      :: hopeful) =
            let
              val weight =
                case cached_weight of
                  SOME w => w
                | NONE => fact_weight fudge stature const_tab rel_const_tab
                                      chained_const_tab fact_consts
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
              commas (rel_const_tab |> Symtab.dest
                      |> filter (curry (op <>) [] o snd)
                      |> map string_for_hyper_pconst));
          relevant [] [] hopeful
        end
    fun uses_const s t =
      fold_aterms (curry (fn (Const (s', _), false) => s' = s | (_, b) => b)) t
                  false
    fun uses_const_anywhere accepts s =
      exists (uses_const s o prop_of o snd) accepts orelse
      exists (uses_const s) (concl_t :: hyp_ts)
    fun add_set_const_thms accepts =
      exists (uses_const_anywhere accepts) set_consts ? append set_thms
    fun insert_into_facts accepts [] = accepts
      | insert_into_facts accepts ths =
        let
          val add = facts |> filter (member Thm.eq_thm_prop ths o snd)
          val (bef, after) =
            accepts |> filter_out (member Thm.eq_thm_prop ths o snd)
                    |> take (max_relevant - length add)
                    |> chop special_fact_index
        in bef @ add @ after end
    fun insert_special_facts accepts =
       (* FIXME: get rid of "ext" here once it is treated as a helper *)
       [] |> could_benefit_from_ext is_built_in_const accepts ? cons @{thm ext}
          |> add_set_const_thms accepts
          |> insert_into_facts accepts
  in
    facts |> map_filter (pair_consts_fact thy is_built_in_const fudge)
          |> iter 0 max_relevant thres0 goal_const_tab []
          |> insert_special_facts
          |> tap (fn accepts => trace_msg ctxt (fn () =>
                      "Total relevant: " ^ string_of_int (length accepts)))
  end

fun iterative_relevant_facts ctxt
        ({relevance_thresholds = (thres0, thres1), ...} : params) prover
        max_relevant fudge override chained_ths hyp_ts concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val is_built_in_const =
      Sledgehammer_Provers.is_built_in_const_for_prover ctxt prover
    val fudge =
      case fudge of
        SOME fudge => fudge
      | NONE => Sledgehammer_Provers.relevance_fudge_for_prover ctxt prover
    val decay = Math.pow ((1.0 - thres1) / (1.0 - thres0),
                          1.0 / Real.fromInt (max_relevant + 1))
  in
    trace_msg ctxt (fn () => "Considering " ^ string_of_int (length facts) ^
                             " facts");
    (if thres1 < 0.0 then
       facts
     else if thres0 > 1.0 orelse thres0 > thres1 then
       []
     else
       relevance_filter ctxt thres0 decay max_relevant is_built_in_const
           fudge override facts (chained_ths |> map prop_of) hyp_ts
           (concl_t |> theory_constify fudge (Context.theory_name thy)))
    |> map (apfst (apfst (fn f => f ())))
  end

end;
