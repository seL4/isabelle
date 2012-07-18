(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer fact handling.
*)

signature SLEDGEHAMMER_FACT =
sig
  type status = ATP_Problem_Generate.status
  type stature = ATP_Problem_Generate.stature

  type fact_override =
    {add : (Facts.ref * Attrib.src list) list,
     del : (Facts.ref * Attrib.src list) list,
     only : bool}

  val ignore_no_atp : bool Config.T
  val instantiate_inducts : bool Config.T
  val no_fact_override : fact_override
  val fact_from_ref :
    Proof.context -> unit Symtab.table -> thm list -> status Termtab.table
    -> Facts.ref * Attrib.src list -> ((string * stature) * thm) list
  val clasimpset_rule_table_of : Proof.context -> status Termtab.table
  val maybe_instantiate_inducts :
    Proof.context -> term list -> term -> (((unit -> string) * 'a) * thm) list
    -> (((unit -> string) * 'a) * thm) list
  val maybe_filter_no_atps : Proof.context -> ('a * thm) list -> ('a * thm) list
  val all_facts :
    Proof.context -> bool -> 'a Symtab.table -> bool -> thm list
    -> thm list -> status Termtab.table
    -> (((unit -> string) * stature) * thm) list
  val all_facts_of : theory -> (((unit -> string) * stature) * thm) list
  val nearly_all_facts :
    Proof.context -> bool -> fact_override -> thm list -> term list -> term
    -> (((unit -> string) * stature) * thm) list
end;

structure Sledgehammer_Fact : SLEDGEHAMMER_FACT =
struct

open ATP_Problem_Generate
open Metis_Tactic
open Sledgehammer_Util

type fact_override =
  {add : (Facts.ref * Attrib.src list) list,
   del : (Facts.ref * Attrib.src list) list,
   only : bool}

val sledgehammer_prefix = "Sledgehammer" ^ Long_Name.separator

(* experimental features *)
val ignore_no_atp =
  Attrib.setup_config_bool @{binding sledgehammer_ignore_no_atp} (K false)
val instantiate_inducts =
  Attrib.setup_config_bool @{binding sledgehammer_instantiate_inducts} (K false)

val no_fact_override = {add = [], del = [], only = false}

fun needs_quoting reserved s =
  Symtab.defined reserved s orelse
  exists (not o Lexicon.is_identifier) (Long_Name.explode s)

fun make_name reserved multi j name =
  (name |> needs_quoting reserved name ? quote) ^
  (if multi then "(" ^ string_of_int j ^ ")" else "")

fun explode_interval _ (Facts.FromTo (i, j)) = i upto j
  | explode_interval max (Facts.From i) = i upto i + max - 1
  | explode_interval _ (Facts.Single i) = [i]

val backquote =
  raw_explode #> map (fn "`" => "\\`" | s => s) #> implode #> enclose "`" "`"

(* unfolding these can yield really huge terms *)
val risky_defs = @{thms Bit0_def Bit1_def}

fun is_rec_eq lhs = Term.exists_subterm (curry (op =) (head_of lhs))
fun is_rec_def (@{const Trueprop} $ t) = is_rec_def t
  | is_rec_def (@{const ==>} $ _ $ t2) = is_rec_def t2
  | is_rec_def (Const (@{const_name "=="}, _) $ t1 $ t2) = is_rec_eq t1 t2
  | is_rec_def (Const (@{const_name HOL.eq}, _) $ t1 $ t2) = is_rec_eq t1 t2
  | is_rec_def _ = false

fun is_assum assms th = exists (fn ct => prop_of th aconv term_of ct) assms
fun is_chained chained_ths = member Thm.eq_thm_prop chained_ths

fun scope_of_thm global assms chained_ths th =
  if is_chained chained_ths th then Chained
  else if global then Global
  else if is_assum assms th then Assum
  else Local

val may_be_induction =
  exists_subterm (fn Var (_, Type (@{type_name fun}, [_, T])) =>
                     body_type T = @{typ bool}
                   | _ => false)

fun status_of_thm css_table name th =
  (* FIXME: use structured name *)
  if (String.isSubstring ".induct" name orelse
      String.isSubstring ".inducts" name) andalso
     may_be_induction (prop_of th) then
    Induction
  else case Termtab.lookup css_table (prop_of th) of
    SOME status => status
  | NONE => General

fun stature_of_thm global assms chained_ths css_table name th =
  (scope_of_thm global assms chained_ths th, status_of_thm css_table name th)

fun fact_from_ref ctxt reserved chained_ths css_table (xthm as (xref, args)) =
  let
    val ths = Attrib.eval_thms ctxt [xthm]
    val bracket =
      map (enclose "[" "]" o Pretty.str_of o Args.pretty_src ctxt) args
      |> implode
    fun nth_name j =
      case xref of
        Facts.Fact s => backquote s ^ bracket
      | Facts.Named (("", _), _) => "[" ^ bracket ^ "]"
      | Facts.Named ((name, _), NONE) =>
        make_name reserved (length ths > 1) (j + 1) name ^ bracket
      | Facts.Named ((name, _), SOME intervals) =>
        make_name reserved true
                 (nth (maps (explode_interval (length ths)) intervals) j) name ^
        bracket
  in
    (ths, (0, []))
    |-> fold (fn th => fn (j, rest) =>
                 let val name = nth_name j in
                   (j + 1, ((name, stature_of_thm false [] chained_ths
                                             css_table name th), th) :: rest)
                 end)
    |> snd
  end

(* Reject theorems with names like "List.filter.filter_list_def" or
  "Accessible_Part.acc.defs", as these are definitions arising from packages. *)
fun is_package_def a =
  let val names = Long_Name.explode a in
    (length names > 2 andalso not (hd names = "local") andalso
     String.isSuffix "_def" a) orelse String.isSuffix "_defs" a
  end

(* FIXME: put other record thms here, or declare as "no_atp" *)
fun multi_base_blacklist ctxt ho_atp =
  ["defs", "select_defs", "update_defs", "split", "splits", "split_asm",
   "cases", "ext_cases", "eq.simps", "eq.refl", "nchotomy", "case_cong",
   "weak_case_cong"]
  |> not (ho_atp orelse (Config.get ctxt instantiate_inducts)) ?
        append ["induct", "inducts"]
  |> map (prefix ".")

val max_lambda_nesting = 3 (*only applies if not ho_atp*)

fun term_has_too_many_lambdas max (t1 $ t2) =
    exists (term_has_too_many_lambdas max) [t1, t2]
  | term_has_too_many_lambdas max (Abs (_, _, t)) =
    max = 0 orelse term_has_too_many_lambdas (max - 1) t
  | term_has_too_many_lambdas _ _ = false

(* Don't count nested lambdas at the level of formulas, since they are
   quantifiers. *)
fun formula_has_too_many_lambdas true _ _ = false (*i.e. ho_atp*)
  | formula_has_too_many_lambdas _ Ts (Abs (_, T, t)) =
      formula_has_too_many_lambdas false (T :: Ts) t
  | formula_has_too_many_lambdas _ Ts t =
    if member (op =) [HOLogic.boolT, propT] (fastype_of1 (Ts, t)) then
      exists (formula_has_too_many_lambdas false Ts) (#2 (strip_comb t))
    else
      term_has_too_many_lambdas max_lambda_nesting t

(* The max apply depth of any "metis" call in "Metis_Examples" (on 2007-10-31)
   was 11. *)
val max_apply_depth = 15

fun apply_depth (f $ t) = Int.max (apply_depth f, apply_depth t + 1)
  | apply_depth (Abs (_, _, t)) = apply_depth t
  | apply_depth _ = 0

fun is_formula_too_complex ho_atp t =
  apply_depth t > max_apply_depth orelse formula_has_too_many_lambdas ho_atp [] t

(* FIXME: Extend to "Meson" and "Metis" *)
val exists_sledgehammer_const =
  exists_Const (fn (s, _) => String.isPrefix sledgehammer_prefix s)

(* FIXME: make more reliable *)
val exists_low_level_class_const =
  exists_Const (fn (s, _) =>
     s = @{const_name equal_class.equal} orelse
     String.isSubstring (Long_Name.separator ^ "class" ^ Long_Name.separator) s)

fun is_metastrange_theorem th =
  case head_of (concl_of th) of
    Const (s, _) => (s <> @{const_name Trueprop} andalso
                     s <> @{const_name "=="})
  | _ => false

fun is_that_fact th =
  String.isSuffix (Long_Name.separator ^ Obtain.thatN) (Thm.get_name_hint th)
  andalso exists_subterm (fn Free (s, _) => s = Name.skolem Auto_Bind.thesisN
                           | _ => false) (prop_of th)

fun is_theorem_bad_for_atps ho_atp exporter thm =
  is_metastrange_theorem thm orelse
  (not exporter andalso
   let val t = prop_of thm in
     is_formula_too_complex ho_atp t orelse exists_type type_has_top_sort t orelse
     exists_sledgehammer_const t orelse exists_low_level_class_const t orelse
     is_that_fact thm
   end)

fun hackish_string_for_term ctxt t =
  Print_Mode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                   (print_mode_value ())) (Syntax.string_of_term ctxt) t
  |> String.translate (fn c => if Char.isPrint c then str c else "")
  |> simplify_spaces

(* This is a terrible hack. Free variables are sometimes coded as "M__" when
   they are displayed as "M" and we want to avoid clashes with these. But
   sometimes it's even worse: "Ma__" encodes "M". So we simply reserve all
   prefixes of all free variables. In the worse case scenario, where the fact
   won't be resolved correctly, the user can fix it manually, e.g., by naming
   the fact in question. Ideally we would need nothing of it, but backticks
   simply don't work with schematic variables. *)
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

fun clasimpset_rule_table_of ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val atomize = HOLogic.mk_Trueprop o Object_Logic.atomize_term thy
    fun add stature normalizers get_th =
      fold (fn rule =>
               let
                 val th = rule |> get_th
                 val t =
                   th |> Thm.maxidx_of th > 0 ? zero_var_indexes |> prop_of
               in
                 fold (fn normalize => Termtab.update (normalize t, stature))
                      (I :: normalizers)
               end)
    val {safeIs, (* safeEs, *) hazIs, (* hazEs, *) ...} =
      ctxt |> claset_of |> Classical.rep_cs
    val intros = Item_Net.content safeIs @ Item_Net.content hazIs
(* Add once it is used:
    val elims =
      Item_Net.content safeEs @ Item_Net.content hazEs
      |> map Classical.classical_rule
*)
    val simps = ctxt |> simpset_of |> dest_ss |> #simps
    val specs = ctxt |> Spec_Rules.get
    val (rec_defs, nonrec_defs) =
      specs |> filter (curry (op =) Spec_Rules.Equational o fst)
            |> maps (snd o snd)
            |> filter_out (member Thm.eq_thm_prop risky_defs)
            |> List.partition (is_rec_def o prop_of)
    val spec_intros =
      specs |> filter (member (op =) [Spec_Rules.Inductive,
                                      Spec_Rules.Co_Inductive] o fst)
            |> maps (snd o snd)
  in
    Termtab.empty |> add Simp [atomize] snd simps
                  |> add Simp [] I rec_defs
                  |> add Def [] I nonrec_defs
(* Add once it is used:
                  |> add Elim [] I elims
*)
                  |> add Intro [] I intros
                  |> add Inductive [] I spec_intros
  end

fun uniquify xs =
  Termtab.fold (cons o snd)
               (fold (Termtab.update o `(prop_of o snd)) xs Termtab.empty) []

fun struct_induct_rule_on th =
  case Logic.strip_horn (prop_of th) of
    (prems, @{const Trueprop}
            $ ((p as Var ((p_name, 0), _)) $ (a as Var (_, ind_T)))) =>
    if not (is_TVar ind_T) andalso length prems > 1 andalso
       exists (exists_subterm (curry (op aconv) p)) prems andalso
       not (exists (exists_subterm (curry (op aconv) a)) prems) then
      SOME (p_name, ind_T)
    else
      NONE
  | _ => NONE

fun instantiate_induct_rule ctxt concl_prop p_name ((name, stature), th) ind_x =
  let
    fun varify_noninducts (t as Free (s, T)) =
        if (s, T) = ind_x orelse can dest_funT T then t else Var ((s, 0), T)
      | varify_noninducts t = t
    val p_inst =
      concl_prop |> map_aterms varify_noninducts |> close_form
                 |> lambda (Free ind_x)
                 |> hackish_string_for_term ctxt
  in
    ((fn () => name () ^ "[where " ^ p_name ^ " = " ^ quote p_inst ^ "]",
      stature), th |> read_instantiate ctxt [((p_name, 0), p_inst)])
  end

fun type_match thy (T1, T2) =
  (Sign.typ_match thy (T2, T1) Vartab.empty; true)
  handle Type.TYPE_MATCH => false

fun instantiate_if_induct_rule ctxt stmt stmt_xs (ax as (_, th)) =
  case struct_induct_rule_on th of
    SOME (p_name, ind_T) =>
    let val thy = Proof_Context.theory_of ctxt in
      stmt_xs |> filter (fn (_, T) => type_match thy (T, ind_T))
              |> map_filter (try (instantiate_induct_rule ctxt stmt p_name ax))
    end
  | NONE => [ax]

fun external_frees t =
  [] |> Term.add_frees t |> filter_out (can Name.dest_internal o fst)

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

fun maybe_filter_no_atps ctxt =
  not (Config.get ctxt ignore_no_atp) ? filter_out (No_ATPs.member ctxt o snd)

fun all_facts ctxt ho_atp reserved exporter add_ths chained_ths css_table =
  let
    val thy = Proof_Context.theory_of ctxt
    val global_facts = Global_Theory.facts_of thy
    val local_facts = Proof_Context.facts_of ctxt
    val named_locals = local_facts |> Facts.dest_static []
    val assms = Assumption.all_assms_of ctxt
    fun is_good_unnamed_local th =
      not (Thm.has_name_hint th) andalso
      forall (fn (_, ths) => not (member Thm.eq_thm_prop ths th)) named_locals
    val unnamed_locals =
      union Thm.eq_thm_prop (Facts.props local_facts) chained_ths
      |> filter is_good_unnamed_local |> map (pair "" o single)
    val full_space =
      Name_Space.merge (Facts.space_of global_facts, Facts.space_of local_facts)
    fun add_facts global foldx facts =
      foldx (fn (name0, ths) =>
        if not exporter andalso name0 <> "" andalso
           forall (not o member Thm.eq_thm_prop add_ths) ths andalso
           (Facts.is_concealed facts name0 orelse
            (not (Config.get ctxt ignore_no_atp) andalso
             is_package_def name0) orelse
            exists (fn s => String.isSuffix s name0)
                   (multi_base_blacklist ctxt ho_atp)) then
          I
        else
          let
            val multi = length ths > 1
            val backquote_thm =
              backquote o hackish_string_for_term ctxt o close_form o prop_of
            fun check_thms a =
              case try (Proof_Context.get_thms ctxt) a of
                NONE => false
              | SOME ths' => eq_list Thm.eq_thm_prop (ths, ths')
          in
            pair 1
            #> fold (fn th => fn (j, (multis, unis)) =>
                        (j + 1,
                         if not (member Thm.eq_thm_prop add_ths th) andalso
                            is_theorem_bad_for_atps ho_atp exporter th then
                           (multis, unis)
                         else
                           let
                             val new =
                               (((fn () =>
                                 if name0 = "" then
                                   th |> backquote_thm
                                 else
                                   [Facts.extern ctxt facts name0,
                                    Name_Space.extern ctxt full_space name0,
                                    name0]
                                   |> find_first check_thms
                                   |> (fn SOME name =>
                                          make_name reserved multi j name
                                        | NONE => "")),
                                stature_of_thm global assms chained_ths
                                               css_table name0 th), th)
                           in
                             if multi then (new :: multis, unis)
                             else (multis, new :: unis)
                           end)) ths
            #> snd
          end)
  in
    (* The single-name theorems go after the multiple-name ones, so that single
       names are preferred when both are available. *)
    ([], []) |> add_facts false fold local_facts (unnamed_locals @ named_locals)
             |> add_facts true Facts.fold_static global_facts global_facts
             |> op @
  end

fun all_facts_of thy =
  let val ctxt = Proof_Context.init_global thy in
    all_facts ctxt false Symtab.empty true [] []
              (clasimpset_rule_table_of ctxt)
    |> rev (* try to restore the original order of facts, for MaSh *)
  end

fun nearly_all_facts ctxt ho_atp {add, del, only} chained_ths hyp_ts concl_t =
  if only andalso null add then
    []
  else
    let
      val chained_ths =
        chained_ths
        |> maps (fn th => insert Thm.eq_thm_prop (zero_var_indexes th) [th])
      val reserved = reserved_isar_keyword_table ()
      val css_table = clasimpset_rule_table_of ctxt
    in
      (if only then
         maps (map (fn ((name, stature), th) => ((K name, stature), th))
               o fact_from_ref ctxt reserved chained_ths css_table) add
       else
         let val (add, del) = pairself (Attrib.eval_thms ctxt) (add, del) in
           all_facts ctxt ho_atp reserved false add chained_ths css_table
           |> filter_out (member Thm.eq_thm_prop del o snd)
           |> maybe_filter_no_atps ctxt
         end)
      |> maybe_instantiate_inducts ctxt hyp_ts concl_t
      |> uniquify
    end

end;
