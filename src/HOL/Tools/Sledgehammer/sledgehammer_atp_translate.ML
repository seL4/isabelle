(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_atp_translate.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Sledgehammer.
*)

signature SLEDGEHAMMER_ATP_TRANSLATE =
sig
  type 'a problem = 'a ATP_Problem.problem
  type translated_formula

  datatype type_system =
    Tags of bool |
    Preds of bool |
    Const_Args |
    No_Types

  val precise_overloaded_args : bool Unsynchronized.ref
  val fact_prefix : string
  val conjecture_prefix : string
  val types_dangerous_types : type_system -> bool
  val num_atp_type_args : theory -> type_system -> string -> int
  val translate_atp_fact :
    Proof.context -> (string * 'a) * thm
    -> translated_formula option * ((string * 'a) * thm)
  val prepare_atp_problem :
    Proof.context -> bool -> bool -> type_system -> bool -> term list -> term
    -> (translated_formula option * ((string * 'a) * thm)) list
    -> string problem * string Symtab.table * int * (string * 'a) list vector
end;

structure Sledgehammer_ATP_Translate : SLEDGEHAMMER_ATP_TRANSLATE =
struct

open ATP_Problem
open Metis_Translate
open Sledgehammer_Util

(* FIXME: Remove references once appropriate defaults have been determined
   empirically. *)
val precise_overloaded_args = Unsynchronized.ref false

val fact_prefix = "fact_"
val conjecture_prefix = "conj_"
val helper_prefix = "help_"
val class_rel_clause_prefix = "clrel_";
val arity_clause_prefix = "arity_"
val tfree_prefix = "tfree_"

(* Freshness almost guaranteed! *)
val sledgehammer_weak_prefix = "Sledgehammer:"

type translated_formula =
  {name: string,
   kind: kind,
   combformula: (name, combterm) formula,
   ctypes_sorts: typ list}

datatype type_system =
  Tags of bool |
  Preds of bool |
  Const_Args |
  No_Types

fun types_dangerous_types (Tags _) = true
  | types_dangerous_types (Preds _) = true
  | types_dangerous_types _ = false

(* This is an approximation. If it returns "true" for a constant that isn't
   overloaded (i.e., that has one uniform definition), needless clutter is
   generated; if it returns "false" for an overloaded constant, the ATP gets a
   license to do unsound reasoning if the type system is "overloaded_args". *)
fun is_overloaded thy s =
  not (!precise_overloaded_args) orelse
  s = @{const_name finite} orelse
  (s <> @{const_name HOL.eq} andalso
   length (Defs.specifications_of (Theory.defs_of thy) s) > 1)

fun needs_type_args thy type_sys s =
  case type_sys of
    Tags full_types => not full_types andalso is_overloaded thy s
  | Preds _ => is_overloaded thy s (* FIXME: could be more precise *)
  | Const_Args => is_overloaded thy s
  | No_Types => false

fun num_atp_type_args thy type_sys s =
  if needs_type_args thy type_sys s then num_type_args thy s else 0

fun atp_type_literals_for_types type_sys Ts =
  if type_sys = No_Types then [] else type_literals_for_types Ts

fun mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])
fun mk_ahorn [] phi = phi
  | mk_ahorn (phi :: phis) psi =
    AConn (AImplies, [fold (mk_aconn AAnd) phis phi, psi])

fun close_universally phi =
  let
    fun term_vars bounds (ATerm (name as (s, _), tms)) =
        (is_atp_variable s andalso not (member (op =) bounds name))
          ? insert (op =) name
        #> fold (term_vars bounds) tms
    fun formula_vars bounds (AQuant (_, xs, phi)) =
        formula_vars (xs @ bounds) phi
      | formula_vars bounds (AConn (_, phis)) = fold (formula_vars bounds) phis
      | formula_vars bounds (AAtom tm) = term_vars bounds tm
  in
    case formula_vars [] phi [] of [] => phi | xs => AQuant (AForall, xs, phi)
  end

fun combformula_for_prop thy eq_as_iff =
  let
    fun do_term bs t ts =
      combterm_from_term thy bs (Envir.eta_contract t)
      |>> AAtom ||> union (op =) ts
    fun do_quant bs q s T t' =
      let val s = Name.variant (map fst bs) s in
        do_formula ((s, T) :: bs) t'
        #>> (fn phi => AQuant (q, [`make_bound_var s], phi))
      end
    and do_conn bs c t1 t2 =
      do_formula bs t1 ##>> do_formula bs t2
      #>> (fn (phi1, phi2) => AConn (c, [phi1, phi2]))
    and do_formula bs t =
      case t of
        @{const Not} $ t1 =>
        do_formula bs t1 #>> (fn phi => AConn (ANot, [phi]))
      | Const (@{const_name All}, _) $ Abs (s, T, t') =>
        do_quant bs AForall s T t'
      | Const (@{const_name Ex}, _) $ Abs (s, T, t') =>
        do_quant bs AExists s T t'
      | @{const HOL.conj} $ t1 $ t2 => do_conn bs AAnd t1 t2
      | @{const HOL.disj} $ t1 $ t2 => do_conn bs AOr t1 t2
      | @{const HOL.implies} $ t1 $ t2 => do_conn bs AImplies t1 t2
      | Const (@{const_name HOL.eq}, Type (_, [@{typ bool}, _])) $ t1 $ t2 =>
        if eq_as_iff then do_conn bs AIff t1 t2 else do_term bs t
      | _ => do_term bs t
  in do_formula [] end

val presimplify_term = prop_of o Meson.presimplify oo Skip_Proof.make_thm

fun concealed_bound_name j = sledgehammer_weak_prefix ^ Int.toString j
fun conceal_bounds Ts t =
  subst_bounds (map (Free o apfst concealed_bound_name)
                    (0 upto length Ts - 1 ~~ Ts), t)
fun reveal_bounds Ts =
  subst_atomic (map (fn (j, T) => (Free (concealed_bound_name j, T), Bound j))
                    (0 upto length Ts - 1 ~~ Ts))

(* Removes the lambdas from an equation of the form "t = (%x. u)".
   (Cf. "extensionalize_theorem" in "Meson_Clausify".) *)
fun extensionalize_term t =
  let
    fun aux j (@{const Trueprop} $ t') = @{const Trueprop} $ aux j t'
      | aux j (t as Const (s, Type (_, [Type (_, [_, T']),
                                        Type (_, [_, res_T])]))
                    $ t2 $ Abs (var_s, var_T, t')) =
        if s = @{const_name HOL.eq} orelse s = @{const_name "=="} then
          let val var_t = Var ((var_s, j), var_T) in
            Const (s, T' --> T' --> res_T)
              $ betapply (t2, var_t) $ subst_bound (var_t, t')
            |> aux (j + 1)
          end
        else
          t
      | aux _ t = t
  in aux (maxidx_of_term t + 1) t end

fun introduce_combinators_in_term ctxt kind t =
  let val thy = ProofContext.theory_of ctxt in
    if Meson.is_fol_term thy t then
      t
    else
      let
        fun aux Ts t =
          case t of
            @{const Not} $ t1 => @{const Not} $ aux Ts t1
          | (t0 as Const (@{const_name All}, _)) $ Abs (s, T, t') =>
            t0 $ Abs (s, T, aux (T :: Ts) t')
          | (t0 as Const (@{const_name All}, _)) $ t1 =>
            aux Ts (t0 $ eta_expand Ts t1 1)
          | (t0 as Const (@{const_name Ex}, _)) $ Abs (s, T, t') =>
            t0 $ Abs (s, T, aux (T :: Ts) t')
          | (t0 as Const (@{const_name Ex}, _)) $ t1 =>
            aux Ts (t0 $ eta_expand Ts t1 1)
          | (t0 as @{const HOL.conj}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
          | (t0 as @{const HOL.disj}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
          | (t0 as @{const HOL.implies}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
          | (t0 as Const (@{const_name HOL.eq}, Type (_, [@{typ bool}, _])))
              $ t1 $ t2 =>
            t0 $ aux Ts t1 $ aux Ts t2
          | _ => if not (exists_subterm (fn Abs _ => true | _ => false) t) then
                   t
                 else
                   t |> conceal_bounds Ts
                     |> Envir.eta_contract
                     |> cterm_of thy
                     |> Meson_Clausify.introduce_combinators_in_cterm
                     |> prop_of |> Logic.dest_equals |> snd
                     |> reveal_bounds Ts
        val (t, ctxt') = Variable.import_terms true [t] ctxt |>> the_single
      in t |> aux [] |> singleton (Variable.export_terms ctxt' ctxt) end
      handle THM _ =>
             (* A type variable of sort "{}" will make abstraction fail. *)
             if kind = Conjecture then HOLogic.false_const
             else HOLogic.true_const
  end

(* Metis's use of "resolve_tac" freezes the schematic variables. We simulate the
   same in Sledgehammer to prevent the discovery of unreplable proofs. *)
fun freeze_term t =
  let
    fun aux (t $ u) = aux t $ aux u
      | aux (Abs (s, T, t)) = Abs (s, T, aux t)
      | aux (Var ((s, i), T)) =
        Free (sledgehammer_weak_prefix ^ s ^ "_" ^ string_of_int i, T)
      | aux t = t
  in t |> exists_subterm is_Var t ? aux end

(* "Object_Logic.atomize_term" isn't as powerful as it could be; for example,
    it leaves metaequalities over "prop"s alone. *)
val atomize_term =
  let
    fun aux (@{const Trueprop} $ t1) = t1
      | aux (Const (@{const_name all}, _) $ Abs (s, T, t')) =
        HOLogic.all_const T $ Abs (s, T, aux t')
      | aux (@{const "==>"} $ t1 $ t2) = HOLogic.mk_imp (pairself aux (t1, t2))
      | aux (Const (@{const_name "=="}, Type (_, [@{typ prop}, _])) $ t1 $ t2) =
        HOLogic.eq_const HOLogic.boolT $ aux t1 $ aux t2
      | aux (Const (@{const_name "=="}, Type (_, [T, _])) $ t1 $ t2) =
        HOLogic.eq_const T $ t1 $ t2
      | aux _ = raise Fail "aux"
  in perhaps (try aux) end

(* making fact and conjecture formulas *)
fun make_formula ctxt eq_as_iff presimp name kind t =
  let
    val thy = ProofContext.theory_of ctxt
    val t = t |> Envir.beta_eta_contract
              |> transform_elim_term
              |> atomize_term
    val need_trueprop = (fastype_of t = HOLogic.boolT)
    val t = t |> need_trueprop ? HOLogic.mk_Trueprop
              |> extensionalize_term
              |> presimp ? presimplify_term thy
              |> perhaps (try (HOLogic.dest_Trueprop))
              |> introduce_combinators_in_term ctxt kind
              |> kind <> Axiom ? freeze_term
    val (combformula, ctypes_sorts) = combformula_for_prop thy eq_as_iff t []
  in
    {name = name, combformula = combformula, kind = kind,
     ctypes_sorts = ctypes_sorts}
  end

fun make_fact ctxt eq_as_iff presimp ((name, _), th) =
  case make_formula ctxt eq_as_iff presimp name Axiom (prop_of th) of
    {combformula = AAtom (CombConst (("c_True", _), _, _)), ...} => NONE
  | formula => SOME formula
fun make_conjecture ctxt ts =
  let val last = length ts - 1 in
    map2 (fn j => make_formula ctxt true true (Int.toString j)
                               (if j = last then Conjecture else Hypothesis))
         (0 upto last) ts
  end

(** Helper facts **)

fun count_term (ATerm ((s, _), tms)) =
  (if is_atp_variable s then I
   else Symtab.map_entry s (Integer.add 1))
  #> fold count_term tms
fun count_formula (AQuant (_, _, phi)) = count_formula phi
  | count_formula (AConn (_, phis)) = fold count_formula phis
  | count_formula (AAtom tm) = count_term tm

val init_counters =
  metis_helpers |> map fst |> sort_distinct string_ord |> map (rpair 0)
  |> Symtab.make

fun get_helper_facts ctxt explicit_forall type_sys formulas =
  let
    val no_dangerous_types = types_dangerous_types type_sys
    val ct = init_counters |> fold count_formula formulas
    fun is_used s = the (Symtab.lookup ct s) > 0
    fun dub c needs_full_types (th, j) =
      ((c ^ "_" ^ string_of_int j ^ (if needs_full_types then "ft" else ""),
        false), th)
    fun make_facts eq_as_iff = map_filter (make_fact ctxt eq_as_iff false)
  in
    (metis_helpers
     |> filter (is_used o fst)
     |> maps (fn (c, (needs_full_types, ths)) =>
                 if needs_full_types andalso not no_dangerous_types then
                   []
                 else
                   ths ~~ (1 upto length ths)
                   |> map (dub c needs_full_types)
                   |> make_facts (not needs_full_types)),
     if type_sys = Tags false then
       let
         fun var s = ATerm (`I s, [])
         fun tag tm = ATerm (`I type_tag_name, [var "X", tm])
       in
         [Fof (helper_prefix ^ ascii_of "ti_ti", Axiom,
               AAtom (ATerm (`I "equal", [tag (tag (var "Y")), tag (var "Y")]))
               |> explicit_forall ? close_universally)]
       end
     else
       [])
  end

fun translate_atp_fact ctxt = `(make_fact ctxt true true)

fun translate_formulas ctxt type_sys hyp_ts concl_t rich_facts =
  let
    val thy = ProofContext.theory_of ctxt
    val fact_ts = map (prop_of o snd o snd) rich_facts
    val (facts, fact_names) =
      rich_facts
      |> map_filter (fn (NONE, _) => NONE
                      | (SOME fact, (name, _)) => SOME (fact, name))
      |> ListPair.unzip
    (* Remove existing facts from the conjecture, as this can dramatically
       boost an ATP's performance (for some reason). *)
    val hyp_ts = hyp_ts |> filter_out (member (op aconv) fact_ts)
    val goal_t = Logic.list_implies (hyp_ts, concl_t)
    val subs = tfree_classes_of_terms [goal_t]
    val supers = tvar_classes_of_terms fact_ts
    val tycons = type_consts_of_terms thy (goal_t :: fact_ts)
    (* TFrees in the conjecture; TVars in the facts *)
    val conjectures = make_conjecture ctxt (hyp_ts @ [concl_t])
    val (supers', arity_clauses) =
      if type_sys = No_Types then ([], [])
      else make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in
    (fact_names |> map single |> Vector.fromList,
     (conjectures, facts, class_rel_clauses, arity_clauses))
  end

fun tag_with_type ty t = ATerm (`I type_tag_name, [ty, t])

fun fo_term_for_combtyp (CombTVar name) = ATerm (name, [])
  | fo_term_for_combtyp (CombTFree name) = ATerm (name, [])
  | fo_term_for_combtyp (CombType (name, tys)) =
    ATerm (name, map fo_term_for_combtyp tys)

fun fo_literal_for_type_literal (TyLitVar (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))
  | fo_literal_for_type_literal (TyLitFree (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))

fun formula_for_fo_literal (pos, t) = AAtom t |> not pos ? mk_anot

(* Finite types such as "unit", "bool", "bool * bool", and "bool => bool" are
   considered dangerous because their "exhaust" properties can easily lead to
   unsound ATP proofs. The checks below are an (unsound) approximation of
   finiteness. *)

fun is_dtyp_dangerous _ (Datatype_Aux.DtTFree _) = true
  | is_dtyp_dangerous ctxt (Datatype_Aux.DtType (s, Us)) =
    is_type_constr_dangerous ctxt s andalso forall (is_dtyp_dangerous ctxt) Us
  | is_dtyp_dangerous _ (Datatype_Aux.DtRec _) = false
and is_type_dangerous ctxt (Type (s, Ts)) =
    is_type_constr_dangerous ctxt s andalso forall (is_type_dangerous ctxt) Ts
  | is_type_dangerous _ _ = false
and is_type_constr_dangerous ctxt s =
  let val thy = ProofContext.theory_of ctxt in
    case Datatype_Data.get_info thy s of
      SOME {descr, ...} =>
      forall (fn (_, (_, _, constrs)) =>
                 forall (forall (is_dtyp_dangerous ctxt) o snd) constrs) descr
    | NONE =>
      case Typedef.get_info ctxt s of
        ({rep_type, ...}, _) :: _ => is_type_dangerous ctxt rep_type
      | [] => true
  end

fun is_combtyp_dangerous ctxt (CombType ((s, _), tys)) =
    (case strip_prefix_and_unascii type_const_prefix s of
       SOME s' => forall (is_combtyp_dangerous ctxt) tys andalso
                  is_type_constr_dangerous ctxt (invert_const s')
     | NONE => false)
  | is_combtyp_dangerous _ _ = false

fun should_tag_with_type ctxt (Tags full_types) ty =
    full_types orelse is_combtyp_dangerous ctxt ty
  | should_tag_with_type _ _ _ = false

val fname_table =
  [("c_False", (0, ("c_fFalse", @{const_name Metis.fFalse}))),
   ("c_True", (0, ("c_fTrue", @{const_name Metis.fTrue}))),
   ("c_Not", (1, ("c_fNot", @{const_name Metis.fNot}))),
   ("c_conj", (2, ("c_fconj", @{const_name Metis.fconj}))),
   ("c_disj", (2, ("c_fdisj", @{const_name Metis.fdisj}))),
   ("c_implies", (2, ("c_fimplies", @{const_name Metis.fimplies}))),
   ("equal", (2, ("c_fequal", @{const_name Metis.fequal})))]

fun fo_term_for_combterm ctxt type_sys =
  let
    val thy = ProofContext.theory_of ctxt
    fun aux top_level u =
      let
        val (head, args) = strip_combterm_comb u
        val (x, ty_args) =
          case head of
            CombConst (name as (s, s'), _, ty_args) =>
            (case AList.lookup (op =) fname_table s of
               SOME (n, fname) =>
               (if top_level andalso length args = n then
                  case s of
                    "c_False" => ("$false", s')
                  | "c_True" => ("$true", s')
                  | _ => name
                else
                  fname, [])
             | NONE =>
               case strip_prefix_and_unascii const_prefix s of
                 NONE => (name, ty_args)
               | SOME s'' =>
                 let
                   val s'' = invert_const s''
                   val ty_args =
                     if needs_type_args thy type_sys s'' then ty_args else []
                  in (name, ty_args) end)
          | CombVar (name, _) => (name, [])
          | CombApp _ => raise Fail "impossible \"CombApp\""
        val t =
          ATerm (x, map fo_term_for_combtyp ty_args @ map (aux false) args)
        val ty = combtyp_of u
    in
      t |> (if should_tag_with_type ctxt type_sys ty then
              tag_with_type (fo_term_for_combtyp ty)
            else
              I)
    end
  in aux true end

fun formula_for_combformula ctxt type_sys =
  let
    fun aux (AQuant (q, xs, phi)) = AQuant (q, xs, aux phi)
      | aux (AConn (c, phis)) = AConn (c, map aux phis)
      | aux (AAtom tm) = AAtom (fo_term_for_combterm ctxt type_sys tm)
  in aux end

fun formula_for_fact ctxt type_sys
                     ({combformula, ctypes_sorts, ...} : translated_formula) =
  mk_ahorn (map (formula_for_fo_literal o fo_literal_for_type_literal)
                (atp_type_literals_for_types type_sys ctypes_sorts))
           (formula_for_combformula ctxt type_sys combformula)

fun problem_line_for_fact ctxt prefix type_sys (formula as {name, kind, ...}) =
  Fof (prefix ^ ascii_of name, kind, formula_for_fact ctxt type_sys formula)

fun problem_line_for_class_rel_clause (ClassRelClause {name, subclass,
                                                       superclass, ...}) =
  let val ty_arg = ATerm (("T", "T"), []) in
    Fof (class_rel_clause_prefix ^ ascii_of name, Axiom,
         AConn (AImplies, [AAtom (ATerm (subclass, [ty_arg])),
                           AAtom (ATerm (superclass, [ty_arg]))]))
  end

fun fo_literal_for_arity_literal (TConsLit (c, t, args)) =
    (true, ATerm (c, [ATerm (t, map (fn arg => ATerm (arg, [])) args)]))
  | fo_literal_for_arity_literal (TVarLit (c, sort)) =
    (false, ATerm (c, [ATerm (sort, [])]))

fun problem_line_for_arity_clause (ArityClause {name, conclLit, premLits,
                                                ...}) =
  Fof (arity_clause_prefix ^ ascii_of name, Axiom,
       mk_ahorn (map (formula_for_fo_literal o apfst not
                      o fo_literal_for_arity_literal) premLits)
                (formula_for_fo_literal
                     (fo_literal_for_arity_literal conclLit)))

fun problem_line_for_conjecture ctxt type_sys
        ({name, kind, combformula, ...} : translated_formula) =
  Fof (conjecture_prefix ^ name, kind,
       formula_for_combformula ctxt type_sys combformula)

fun free_type_literals_for_conjecture type_sys
        ({ctypes_sorts, ...} : translated_formula) =
  ctypes_sorts |> atp_type_literals_for_types type_sys
               |> map fo_literal_for_type_literal

fun problem_line_for_free_type j lit =
  Fof (tfree_prefix ^ string_of_int j, Hypothesis, formula_for_fo_literal lit)
fun problem_lines_for_free_types type_sys conjectures =
  let
    val litss = map (free_type_literals_for_conjecture type_sys) conjectures
    val lits = fold (union (op =)) litss []
  in map2 problem_line_for_free_type (0 upto length lits - 1) lits end

(** "hBOOL" and "hAPP" **)

type const_info = {min_arity: int, max_arity: int, sub_level: bool}

fun consider_term top_level (ATerm ((s, _), ts)) =
  (if is_atp_variable s then
     I
   else
     let val n = length ts in
       Symtab.map_default
           (s, {min_arity = n, max_arity = 0, sub_level = false})
           (fn {min_arity, max_arity, sub_level} =>
               {min_arity = Int.min (n, min_arity),
                max_arity = Int.max (n, max_arity),
                sub_level = sub_level orelse not top_level})
     end)
  #> fold (consider_term (top_level andalso s = type_tag_name)) ts
fun consider_formula (AQuant (_, _, phi)) = consider_formula phi
  | consider_formula (AConn (_, phis)) = fold consider_formula phis
  | consider_formula (AAtom tm) = consider_term true tm

fun consider_problem_line (Fof (_, _, phi)) = consider_formula phi
fun consider_problem problem = fold (fold consider_problem_line o snd) problem

(* needed for helper facts if the problem otherwise does not involve equality *)
val equal_entry = ("equal", {min_arity = 2, max_arity = 2, sub_level = false})

fun const_table_for_problem explicit_apply problem =
  if explicit_apply then
    NONE
  else
    SOME (Symtab.empty |> Symtab.default equal_entry |> consider_problem problem)

fun min_arity_of thy type_sys NONE s =
    (if s = "equal" orelse s = type_tag_name orelse
        String.isPrefix type_const_prefix s orelse
        String.isPrefix class_prefix s then
       16383 (* large number *)
     else case strip_prefix_and_unascii const_prefix s of
       SOME s' => num_atp_type_args thy type_sys (invert_const s')
     | NONE => 0)
  | min_arity_of _ _ (SOME the_const_tab) s =
    case Symtab.lookup the_const_tab s of
      SOME ({min_arity, ...} : const_info) => min_arity
    | NONE => 0

fun full_type_of (ATerm ((s, _), [ty, _])) =
    if s = type_tag_name then SOME ty else NONE
  | full_type_of _ = NONE

fun list_hAPP_rev _ t1 [] = t1
  | list_hAPP_rev NONE t1 (t2 :: ts2) =
    ATerm (`I "hAPP", [list_hAPP_rev NONE t1 ts2, t2])
  | list_hAPP_rev (SOME ty) t1 (t2 :: ts2) =
    case full_type_of t2 of
      SOME ty2 =>
      let val ty' = ATerm (`make_fixed_type_const @{type_name fun},
                           [ty2, ty]) in
        ATerm (`I "hAPP",
               [tag_with_type ty' (list_hAPP_rev (SOME ty') t1 ts2), t2])
      end
    | NONE => list_hAPP_rev NONE t1 (t2 :: ts2)

fun repair_applications_in_term thy type_sys const_tab =
  let
    fun aux opt_ty (ATerm (name as (s, _), ts)) =
      if s = type_tag_name then
        case ts of
          [t1, t2] => ATerm (name, [aux NONE t1, aux (SOME t1) t2])
        | _ => raise Fail "malformed type tag"
      else
        let
          val ts = map (aux NONE) ts
          val (ts1, ts2) = chop (min_arity_of thy type_sys const_tab s) ts
        in list_hAPP_rev opt_ty (ATerm (name, ts1)) (rev ts2) end
  in aux NONE end

fun boolify t = ATerm (`I "hBOOL", [t])

(* True if the constant ever appears outside of the top-level position in
   literals, or if it appears with different arities (e.g., because of different
   type instantiations). If false, the constant always receives all of its
   arguments and is used as a predicate. *)
fun is_predicate NONE s =
    s = "equal" orelse s = "$false" orelse s = "$true" orelse
    String.isPrefix type_const_prefix s orelse String.isPrefix class_prefix s
  | is_predicate (SOME the_const_tab) s =
    case Symtab.lookup the_const_tab s of
      SOME {min_arity, max_arity, sub_level} =>
      not sub_level andalso min_arity = max_arity
    | NONE => false

fun repair_predicates_in_term pred_const_tab (t as ATerm ((s, _), ts)) =
  if s = type_tag_name then
    case ts of
      [_, t' as ATerm ((s', _), _)] =>
      if is_predicate pred_const_tab s' then t' else boolify t
    | _ => raise Fail "malformed type tag"
  else
    t |> not (is_predicate pred_const_tab s) ? boolify

fun repair_formula thy explicit_forall type_sys const_tab =
  let
    val pred_const_tab = case type_sys of Tags _ => NONE | _ => const_tab
    fun aux (AQuant (q, xs, phi)) = AQuant (q, xs, aux phi)
      | aux (AConn (c, phis)) = AConn (c, map aux phis)
      | aux (AAtom tm) =
        AAtom (tm |> repair_applications_in_term thy type_sys const_tab
                  |> repair_predicates_in_term pred_const_tab)
  in aux #> explicit_forall ? close_universally end

fun repair_problem_line thy explicit_forall type_sys const_tab
                        (Fof (ident, kind, phi)) =
  Fof (ident, kind, repair_formula thy explicit_forall type_sys const_tab phi)
fun repair_problem thy = map o apsnd o map ooo repair_problem_line thy

fun dest_Fof (Fof z) = z

fun prepare_atp_problem ctxt readable_names explicit_forall type_sys
                        explicit_apply hyp_ts concl_t facts =
  let
    val thy = ProofContext.theory_of ctxt
    val (fact_names, (conjectures, facts, class_rel_clauses, arity_clauses)) =
      translate_formulas ctxt type_sys hyp_ts concl_t facts
    val fact_lines = map (problem_line_for_fact ctxt fact_prefix type_sys) facts
    val conjecture_lines =
      map (problem_line_for_conjecture ctxt type_sys) conjectures
    val tfree_lines = problem_lines_for_free_types type_sys conjectures
    val class_rel_lines =
      map problem_line_for_class_rel_clause class_rel_clauses
    val arity_lines = map problem_line_for_arity_clause arity_clauses
    (* Reordering these might or might not confuse the proof reconstruction
       code or the SPASS Flotter hack. *)
    val problem =
      [("Relevant facts", fact_lines),
       ("Class relationships", class_rel_lines),
       ("Arity declarations", arity_lines),
       ("Helper facts", []),
       ("Conjectures", conjecture_lines),
       ("Type variables", tfree_lines)]
    val const_tab = const_table_for_problem explicit_apply problem
    val problem =
      problem |> repair_problem thy explicit_forall type_sys const_tab
    val (helper_facts, raw_helper_lines) =
      get_helper_facts ctxt explicit_forall type_sys
                       (maps (map (#3 o dest_Fof) o snd) problem)
    val helper_lines =
      (helper_facts
       |> map (problem_line_for_fact ctxt helper_prefix type_sys
               #> repair_problem_line thy explicit_forall type_sys const_tab)) @
      raw_helper_lines
    val (problem, pool) =
      problem |> AList.update (op =) ("Helper facts", helper_lines)
              |> nice_atp_problem readable_names
    val conjecture_offset =
      length fact_lines + length class_rel_lines + length arity_lines
      + length helper_lines
  in
    (problem,
     case pool of SOME the_pool => snd the_pool | NONE => Symtab.empty,
     conjecture_offset, fact_names)
  end

end;
