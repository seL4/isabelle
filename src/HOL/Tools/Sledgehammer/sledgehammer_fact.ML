(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer fact handling.
*)

signature SLEDGEHAMMER_FACT =
sig
  type status = ATP_Problem_Generate.status
  type stature = ATP_Problem_Generate.stature

  type raw_fact = ((unit -> string) * stature) * thm
  type fact = (string * stature) * thm

  type fact_override =
    {add : (Facts.ref * Attrib.src list) list,
     del : (Facts.ref * Attrib.src list) list,
     only : bool}

  val instantiate_inducts : bool Config.T
  val no_fact_override : fact_override

  val fact_of_ref : Proof.context -> unit Symtab.table -> thm list -> status Termtab.table ->
    Facts.ref * Attrib.src list -> ((string * stature) * thm) list
  val backquote_thm : Proof.context -> thm -> string
  val is_blacklisted_or_something : Proof.context -> bool -> string -> bool
  val clasimpset_rule_table_of : Proof.context -> status Termtab.table
  val build_name_tables : (thm -> string) -> ('a * thm) list ->
    string Symtab.table * string Symtab.table
  val maybe_instantiate_inducts : Proof.context -> term list -> term ->
    (((unit -> string) * 'a) * thm) list -> (((unit -> string) * 'a) * thm) list
  val fact_of_raw_fact : raw_fact -> fact

  val all_facts : Proof.context -> bool -> bool -> unit Symtab.table -> thm list -> thm list ->
    status Termtab.table -> raw_fact list
  val nearly_all_facts : Proof.context -> bool -> fact_override -> unit Symtab.table ->
    status Termtab.table -> thm list -> term list -> term -> raw_fact list
  val drop_duplicate_facts : raw_fact list -> raw_fact list
end;

structure Sledgehammer_Fact : SLEDGEHAMMER_FACT =
struct

open ATP_Util
open ATP_Problem_Generate
open Sledgehammer_Util

type raw_fact = ((unit -> string) * stature) * thm
type fact = (string * stature) * thm

type fact_override =
  {add : (Facts.ref * Attrib.src list) list,
   del : (Facts.ref * Attrib.src list) list,
   only : bool}

(* gracefully handle huge background theories *)
val max_facts_for_duplicates = 50000
val max_facts_for_complex_check = 25000
val max_simps_for_clasimpset = 10000

(* experimental feature *)
val instantiate_inducts =
  Attrib.setup_config_bool @{binding sledgehammer_instantiate_inducts} (K false)

val no_fact_override = {add = [], del = [], only = false}

fun needs_quoting reserved s =
  Symtab.defined reserved s orelse
  exists (not o Symbol_Pos.is_identifier) (Long_Name.explode s)

fun make_name reserved multi j name =
  (name |> needs_quoting reserved name ? quote) ^
  (if multi then "(" ^ string_of_int j ^ ")" else "")

fun explode_interval _ (Facts.FromTo (i, j)) = i upto j
  | explode_interval max (Facts.From i) = i upto i + max - 1
  | explode_interval _ (Facts.Single i) = [i]

val backquote = raw_explode #> map (fn "`" => "\\`" | s => s) #> implode #> enclose "`" "`"

(* unfolding these can yield really huge terms *)
val risky_defs = @{thms Bit0_def Bit1_def}

fun is_rec_eq lhs = Term.exists_subterm (curry (op =) (head_of lhs))

fun is_rec_def (@{const Trueprop} $ t) = is_rec_def t
  | is_rec_def (@{const Pure.imp} $ _ $ t2) = is_rec_def t2
  | is_rec_def (Const (@{const_name Pure.eq}, _) $ t1 $ t2) = is_rec_eq t1 t2
  | is_rec_def (Const (@{const_name HOL.eq}, _) $ t1 $ t2) = is_rec_eq t1 t2
  | is_rec_def _ = false

fun is_assum assms th = exists (fn ct => prop_of th aconv term_of ct) assms
fun is_chained chained = member Thm.eq_thm_prop chained

fun scope_of_thm global assms chained th =
  if is_chained chained th then Chained
  else if global then Global
  else if is_assum assms th then Assum
  else Local

val may_be_induction =
  exists_subterm (fn Var (_, Type (@{type_name fun}, [_, T])) =>
                     body_type T = @{typ bool}
                   | _ => false)

(* TODO: get rid of *)
fun normalize_vars t =
  let
    fun normT (Type (s, Ts)) = fold_map normT Ts #>> curry Type s
      | normT (TVar (z as (_, S))) =
        (fn ((knownT, nT), accum) =>
            (case find_index (equal z) knownT of
              ~1 => (TVar ((Name.uu, nT), S), ((z :: knownT, nT + 1), accum))
            | j => (TVar ((Name.uu, nT - j - 1), S), ((knownT, nT), accum))))
      | normT (T as TFree _) = pair T

    fun norm (t $ u) = norm t ##>> norm u #>> op $
      | norm (Const (s, T)) = normT T #>> curry Const s
      | norm (Var (z as (_, T))) =
        normT T
        #> (fn (T, (accumT, (known, n))) =>
               (case find_index (equal z) known of
                 ~1 => (Var ((Name.uu, n), T), (accumT, (z :: known, n + 1)))
               | j => (Var ((Name.uu, n - j - 1), T), (accumT, (known, n)))))
      | norm (Abs (_, T, t)) =
        norm t ##>> normT T #>> (fn (t, T) => Abs (Name.uu, T, t))
      | norm (Bound j) = pair (Bound j)
      | norm (Free (s, T)) = normT T #>> curry Free s
  in fst (norm t (([], 0), ([], 0))) end

fun status_of_thm css name th =
  if Termtab.is_empty css then
    General
  else
    let val t = prop_of th in
      (* FIXME: use structured name *)
      if String.isSubstring ".induct" name andalso may_be_induction t then
        Induction
      else
        let val t = normalize_vars t in
          (case Termtab.lookup css t of
            SOME status => status
          | NONE =>
            let val concl = Logic.strip_imp_concl t in
              (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) concl of
                SOME lrhss =>
                let
                  val prems = Logic.strip_imp_prems t
                  val t' = Logic.list_implies (prems, Logic.mk_equals lrhss)
                in
                  Termtab.lookup css t' |> the_default General
                end
              | NONE => General)
            end)
        end
    end

fun stature_of_thm global assms chained css name th =
  (scope_of_thm global assms chained th, status_of_thm css name th)

fun fact_of_ref ctxt reserved chained css (xthm as (xref, args)) =
  let
    val ths = Attrib.eval_thms ctxt [xthm]
    val bracket =
      map (enclose "[" "]" o Pretty.str_of o Args.pretty_src ctxt) args
      |> implode

    fun nth_name j =
      (case xref of
        Facts.Fact s => backquote s ^ bracket
      | Facts.Named (("", _), _) => "[" ^ bracket ^ "]"
      | Facts.Named ((name, _), NONE) =>
        make_name reserved (length ths > 1) (j + 1) name ^ bracket
      | Facts.Named ((name, _), SOME intervals) =>
        make_name reserved true
          (nth (maps (explode_interval (length ths)) intervals) j) name ^ bracket)

    fun add_nth th (j, rest) =
      let val name = nth_name j in
        (j + 1, ((name, stature_of_thm false [] chained css name th), th)
                :: rest)
      end
  in
    (0, []) |> fold add_nth ths |> snd
  end

(* Reject theorems with names like "List.filter.filter_list_def" or
  "Accessible_Part.acc.defs", as these are definitions arising from packages. *)
fun is_package_def s =
  let val ss = Long_Name.explode s in
    length ss > 2 andalso not (hd ss = "local") andalso
    exists (fn suf => String.isSuffix suf s)
           ["_case_def", "_rec_def", "_size_def", "_size_overloaded_def"]
  end

(* FIXME: put other record thms here, or declare as "no_atp" *)
fun multi_base_blacklist ctxt ho_atp =
  ["defs", "select_defs", "update_defs", "split", "splits", "split_asm",
   "ext_cases", "eq.simps", "eq.refl", "nchotomy", "case_cong",
   "weak_case_cong", "nat_of_char_simps", "nibble.simps",
   "nibble.distinct"]
  |> not (ho_atp orelse Config.get ctxt instantiate_inducts) ?
        append ["induct", "inducts"]
  |> map (prefix Long_Name.separator)

(* The maximum apply depth of any "metis" call in "Metis_Examples" (on
   2007-10-31) was 11. *)
val max_apply_depth = 18

fun apply_depth (f $ t) = Int.max (apply_depth f, apply_depth t + 1)
  | apply_depth (Abs (_, _, t)) = apply_depth t
  | apply_depth _ = 0

fun is_too_complex t = apply_depth t > max_apply_depth

(* FIXME: Ad hoc list *)
val technical_prefixes =
  ["ATP", "Code_Evaluation", "Datatype", "Enum", "Lazy_Sequence",
   "Limited_Sequence", "Meson", "Metis", "Nitpick",
   "Quickcheck_Random", "Quickcheck_Exhaustive", "Quickcheck_Narrowing",
   "Random_Sequence", "Sledgehammer", "SMT"]
  |> map (suffix Long_Name.separator)

fun is_technical_const (s, _) =
  exists (fn pref => String.isPrefix pref s) technical_prefixes

(* FIXME: make more reliable *)
val sep_class_sep = Long_Name.separator ^ "class" ^ Long_Name.separator

fun is_low_level_class_const (s, _) =
  s = @{const_name equal_class.equal} orelse String.isSubstring sep_class_sep s

val sep_that = Long_Name.separator ^ Obtain.thatN

val skolem_thesis = Name.skolem Auto_Bind.thesisN

fun is_that_fact th =
  exists_subterm (fn Free (s, _) => s = skolem_thesis | _ => false) (prop_of th)
  andalso String.isSuffix sep_that (Thm.get_name_hint th)

datatype interest = Deal_Breaker | Interesting | Boring

fun combine_interests Deal_Breaker _ = Deal_Breaker
  | combine_interests _ Deal_Breaker = Deal_Breaker
  | combine_interests Interesting _ = Interesting
  | combine_interests _ Interesting = Interesting
  | combine_interests Boring Boring = Boring

val type_has_top_sort =
  exists_subtype (fn TFree (_, []) => true | TVar (_, []) => true | _ => false)

fun is_likely_tautology_too_meta_or_too_technical th =
  let
    fun is_interesting_subterm (Const (s, _)) =
        not (member (op =) atp_widely_irrelevant_consts s)
      | is_interesting_subterm (Free _) = true
      | is_interesting_subterm _ = false

    fun interest_of_bool t =
      if exists_Const (is_technical_const orf is_low_level_class_const orf
                       type_has_top_sort o snd) t then
        Deal_Breaker
      else if exists_type (exists_subtype (curry (op =) @{typ prop})) t orelse
              not (exists_subterm is_interesting_subterm t) then
        Boring
      else
        Interesting

    fun interest_of_prop _ (@{const Trueprop} $ t) = interest_of_bool t
      | interest_of_prop Ts (@{const Pure.imp} $ t $ u) =
        combine_interests (interest_of_prop Ts t) (interest_of_prop Ts u)
      | interest_of_prop Ts (Const (@{const_name Pure.all}, _) $ Abs (_, T, t)) =
        if type_has_top_sort T then Deal_Breaker else interest_of_prop (T :: Ts) t
      | interest_of_prop Ts ((t as Const (@{const_name Pure.all}, _)) $ u) =
        interest_of_prop Ts (t $ eta_expand Ts u 1)
      | interest_of_prop _ (Const (@{const_name Pure.eq}, _) $ t $ u) =
        combine_interests (interest_of_bool t) (interest_of_bool u)
      | interest_of_prop _ _ = Deal_Breaker

    val t = prop_of th
  in
    (interest_of_prop [] t <> Interesting andalso
     not (Thm.eq_thm_prop (@{thm ext}, th))) orelse
    is_that_fact th
  end

fun is_blacklisted_or_something ctxt ho_atp =
  let val blist = multi_base_blacklist ctxt ho_atp in
    fn name => is_package_def name orelse exists (fn s => String.isSuffix s name) blist
  end

(* This is a terrible hack. Free variables are sometimes coded as "M__" when
   they are displayed as "M" and we want to avoid clashes with these. But
   sometimes it's even worse: "Ma__" encodes "M". So we simply reserve all
   prefixes of all free variables. In the worse case scenario, where the fact
   won't be resolved correctly, the user can fix it manually, e.g., by giving a
   name to the offending fact. *)
fun all_prefixes_of s =
  map (fn i => String.extract (s, 0, SOME i)) (1 upto size s - 1)

fun close_form t =
  (t, [] |> Term.add_free_names t |> maps all_prefixes_of)
  |> fold (fn ((s, i), T) => fn (t', taken) =>
              let val s' = singleton (Name.variant_list taken) s in
                ((if fastype_of t' = HOLogic.boolT then HOLogic.all_const
                  else Logic.all_const) T
                 $ Abs (s', T, abstract_over (Var ((s, i), T), t')),
                 s' :: taken)
              end)
          (Term.add_vars t [] |> sort_wrt (fst o fst))
  |> fst

fun backquote_term ctxt = close_form #> hackish_string_of_term ctxt #> backquote
fun backquote_thm ctxt = backquote_term ctxt o prop_of

(* TODO: rewrite to use nets and/or to reuse existing data structures *)
fun clasimpset_rule_table_of ctxt =
  let val simps = ctxt |> simpset_of |> dest_ss |> #simps in
    if length simps >= max_simps_for_clasimpset then
      Termtab.empty
    else
      let
        fun add stature th =
          Termtab.update (normalize_vars (prop_of th), stature)

        val {safeIs, (* safeEs, *) hazIs, (* hazEs, *) ...} =
          ctxt |> claset_of |> Classical.rep_cs
        val intros = Item_Net.content safeIs @ Item_Net.content hazIs
(* Add once it is used:
        val elims =
          Item_Net.content safeEs @ Item_Net.content hazEs
          |> map Classical.classical_rule
*)
        val specs = ctxt |> Spec_Rules.get
        val (rec_defs, nonrec_defs) =
          specs |> filter (curry (op =) Spec_Rules.Equational o fst)
                |> maps (snd o snd)
                |> filter_out (member Thm.eq_thm_prop risky_defs)
                |> List.partition (is_rec_def o prop_of)
        val spec_intros =
          specs |> filter (member (op =) [Spec_Rules.Inductive, Spec_Rules.Co_Inductive] o fst)
                |> maps (snd o snd)
      in
        Termtab.empty
        |> fold (add Simp o snd) simps
        |> fold (add Rec_Def) rec_defs
        |> fold (add Non_Rec_Def) nonrec_defs
(* Add once it is used:
        |> fold (add Elim) elims
*)
        |> fold (add Intro) intros
        |> fold (add Inductive) spec_intros
      end
  end

fun normalize_eq (@{const Trueprop} $ (t as (t0 as Const (@{const_name HOL.eq}, _)) $ t1 $ t2)) =
    if Term_Ord.fast_term_ord (t1, t2) <> GREATER then t else t0 $ t2 $ t1
  | normalize_eq (@{const Trueprop} $ (t as @{const Not}
        $ ((t0 as Const (@{const_name HOL.eq}, _)) $ t1 $ t2))) =
    if Term_Ord.fast_term_ord (t1, t2) <> GREATER then t else HOLogic.mk_not (t0 $ t2 $ t1)
  | normalize_eq (Const (@{const_name Pure.eq}, Type (_, [T, _])) $ t1 $ t2) =
    (if Term_Ord.fast_term_ord (t1, t2) <> GREATER then (t1, t2) else (t2, t1))
    |> (fn (t1, t2) => HOLogic.eq_const T $ t1 $ t2)
  | normalize_eq t = t

fun if_thm_before th th' =
  if Theory.subthy (pairself Thm.theory_of_thm (th, th')) then th else th'

(* Hack: Conflate the facts about a class as seen from the outside with the corresponding low-level
   facts, so that MaSh can learn from the low-level proofs. *)
fun un_class_ify s =
  (case first_field "_class" s of
    SOME (pref, suf) => [s, pref ^ suf]
  | NONE => [s])

fun build_name_tables name_of facts =
  let
    fun cons_thm (_, th) = Termtab.cons_list (normalize_vars (normalize_eq (prop_of th)), th)
    fun add_plain canon alias =
      Symtab.update (Thm.get_name_hint alias, name_of (if_thm_before canon alias))
    fun add_plains (_, aliases as canon :: _) = fold (add_plain canon) aliases
    fun add_inclass (name, target) = fold (fn s => Symtab.update (s, target)) (un_class_ify name)
    val prop_tab = fold cons_thm facts Termtab.empty
    val plain_name_tab = Termtab.fold add_plains prop_tab Symtab.empty
    val inclass_name_tab = Symtab.fold add_inclass plain_name_tab Symtab.empty
  in
    (plain_name_tab, inclass_name_tab)
  end

fun fact_distinct eq facts =
  fold (fn fact as (_, th) =>
      Net.insert_term_safe (eq o pairself (normalize_eq o prop_of o snd))
        (normalize_eq (prop_of th), fact))
    facts Net.empty
  |> Net.entries

fun struct_induct_rule_on th =
  (case Logic.strip_horn (prop_of th) of
    (prems, @{const Trueprop}
            $ ((p as Var ((p_name, 0), _)) $ (a as Var (_, ind_T)))) =>
    if not (is_TVar ind_T) andalso length prems > 1 andalso
       exists (exists_subterm (curry (op aconv) p)) prems andalso
       not (exists (exists_subterm (curry (op aconv) a)) prems) then
      SOME (p_name, ind_T)
    else
      NONE
  | _ => NONE)

val instantiate_induct_timeout = seconds 0.01

fun instantiate_induct_rule ctxt concl_prop p_name ((name, stature), th) ind_x =
  let
    fun varify_noninducts (t as Free (s, T)) =
        if (s, T) = ind_x orelse can dest_funT T then t else Var ((s, 0), T)
      | varify_noninducts t = t

    val p_inst =
      concl_prop |> map_aterms varify_noninducts |> close_form
                 |> lambda (Free ind_x)
                 |> hackish_string_of_term ctxt
  in
    ((fn () => name () ^ "[where " ^ p_name ^ " = " ^ quote p_inst ^ "]",
      stature), th |> Rule_Insts.read_instantiate ctxt [((p_name, 0), p_inst)] [])
  end

fun type_match thy (T1, T2) =
  (Sign.typ_match thy (T2, T1) Vartab.empty; true)
  handle Type.TYPE_MATCH => false

fun instantiate_if_induct_rule ctxt stmt stmt_xs (ax as (_, th)) =
  (case struct_induct_rule_on th of
    SOME (p_name, ind_T) =>
    let val thy = Proof_Context.theory_of ctxt in
      stmt_xs
      |> filter (fn (_, T) => type_match thy (T, ind_T))
      |> map_filter (try (TimeLimit.timeLimit instantiate_induct_timeout
           (instantiate_induct_rule ctxt stmt p_name ax)))
    end
  | NONE => [ax])

fun external_frees t =
  [] |> Term.add_frees t |> filter_out (Name.is_internal o fst)

fun maybe_instantiate_inducts ctxt hyp_ts concl_t =
  if Config.get ctxt instantiate_inducts then
    let
      val thy = Proof_Context.theory_of ctxt
      val ind_stmt =
        (hyp_ts |> filter_out (null o external_frees), concl_t)
        |> Logic.list_implies |> Object_Logic.atomize_term thy
      val ind_stmt_xs = external_frees ind_stmt
    in maps (instantiate_if_induct_rule ctxt ind_stmt ind_stmt_xs) end
  else
    I

fun fact_of_raw_fact ((name, stature), th) = ((name (), stature), th)

fun fact_count facts = Facts.fold_static (K (Integer.add 1)) facts 0

fun all_facts ctxt generous ho_atp reserved add_ths chained css =
  let
    val thy = Proof_Context.theory_of ctxt
    val global_facts = Global_Theory.facts_of thy
    val is_too_complex =
      if generous orelse fact_count global_facts >= max_facts_for_complex_check then
        K false
      else
        is_too_complex
    val local_facts = Proof_Context.facts_of ctxt
    val named_locals = local_facts |> Facts.dest_static true [global_facts]
    val assms = Assumption.all_assms_of ctxt

    fun is_good_unnamed_local th =
      not (Thm.has_name_hint th) andalso
      forall (fn (_, ths) => not (member Thm.eq_thm_prop ths th)) named_locals

    val unnamed_locals =
      union Thm.eq_thm_prop (Facts.props local_facts) chained
      |> filter is_good_unnamed_local |> map (pair "" o single)
    val full_space =
      Name_Space.merge (Facts.space_of global_facts, Facts.space_of local_facts)
    val is_blacklisted_or_something = is_blacklisted_or_something ctxt ho_atp

    fun add_facts global foldx facts =
      foldx (fn (name0, ths) => fn accum =>
        if name0 <> "" andalso
           forall (not o member Thm.eq_thm_prop add_ths) ths andalso
           (Facts.is_concealed facts name0 orelse
            Long_Name.is_hidden (Facts.intern facts name0) orelse
            (not generous andalso is_blacklisted_or_something name0)) then
          accum
        else
          let
            val n = length ths
            val multi = n > 1

            fun check_thms a =
              (case try (Proof_Context.get_thms ctxt) a of
                NONE => false
              | SOME ths' => eq_list Thm.eq_thm_prop (ths, ths'))
          in
            snd (fold_rev (fn th => fn (j, accum) =>
              (j - 1,
               if not (member Thm.eq_thm_prop add_ths th) andalso
                  (is_likely_tautology_too_meta_or_too_technical th orelse
                   is_too_complex (prop_of th)) then
                 accum
               else
                 let
                   fun get_name () =
                     if name0 = "" then
                       backquote_thm ctxt th
                     else
                       let val short_name = Facts.extern ctxt facts name0 in
                         if check_thms short_name then
                           short_name
                         else
                           let val long_name = Name_Space.extern ctxt full_space name0 in
                             if check_thms long_name then
                               long_name
                             else
                               name0
                           end
                       end
                       |> make_name reserved multi j
                   val stature = stature_of_thm global assms chained css name0 th
                   val new = ((get_name, stature), th)
                 in
                   (if multi then apsnd else apfst) (cons new) accum
                 end)) ths (n, accum))
          end)
  in
    (* The single-theorem names go before the multiple-theorem ones (e.g.,
       "xxx" vs. "xxx(3)"), so that single names are preferred when both are
       available. *)
    `I [] |> add_facts false fold local_facts (unnamed_locals @ named_locals)
          |> add_facts true Facts.fold_static global_facts global_facts
          |> op @
  end

fun nearly_all_facts ctxt ho_atp {add, del, only} reserved css chained hyp_ts concl_t =
  if only andalso null add then
    []
  else
    let
      val chained =
        chained
        |> maps (fn th => insert Thm.eq_thm_prop (zero_var_indexes th) [th])
    in
      (if only then
         maps (map (fn ((name, stature), th) => ((K name, stature), th))
               o fact_of_ref ctxt reserved chained css) add
       else
         let
           val (add, del) = pairself (Attrib.eval_thms ctxt) (add, del)
           val facts =
             all_facts ctxt false ho_atp reserved add chained css
             |> filter_out ((member Thm.eq_thm_prop del orf
               (No_ATPs.member ctxt andf not o member Thm.eq_thm_prop add)) o snd)
         in
           facts
         end)
      |> maybe_instantiate_inducts ctxt hyp_ts concl_t
    end

fun drop_duplicate_facts facts =
  let val num_facts = length facts in
    facts |> num_facts <= max_facts_for_duplicates ? fact_distinct (op aconv)
  end

end;
