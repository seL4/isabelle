(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_atp_translate.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Sledgehammer.
*)

signature SLEDGEHAMMER_ATP_TRANSLATE =
sig
  type 'a fo_term = 'a ATP_Problem.fo_term
  type 'a problem = 'a ATP_Problem.problem
  type translated_formula

  datatype type_system =
    Many_Typed |
    Mangled of bool |
    Args of bool |
    Tags of bool |
    No_Types

  val fact_prefix : string
  val conjecture_prefix : string
  val boolify_base : string
  val explicit_app_base : string
  val type_pred_base : string
  val tff_type_prefix : string
  val is_type_system_sound : type_system -> bool
  val type_system_types_dangerous_types : type_system -> bool
  val num_atp_type_args : theory -> type_system -> string -> int
  val unmangled_const : string -> string * string fo_term list
  val translate_atp_fact :
    Proof.context -> bool -> (string * 'a) * thm
    -> translated_formula option * ((string * 'a) * thm)
  val prepare_atp_problem :
    Proof.context -> bool -> type_system -> bool -> term list -> term
    -> (translated_formula option * ((string * 'a) * thm)) list
    -> string problem * string Symtab.table * int * int
       * (string * 'a) list vector
  val atp_problem_weights : string problem -> (string * real) list
end;

structure Sledgehammer_ATP_Translate : SLEDGEHAMMER_ATP_TRANSLATE =
struct

open ATP_Problem
open Metis_Translate
open Sledgehammer_Util

val type_decl_prefix = "type_"
val sym_decl_prefix = "sym_"
val fact_prefix = "fact_"
val conjecture_prefix = "conj_"
val helper_prefix = "help_"
val class_rel_clause_prefix = "crel_";
val arity_clause_prefix = "arity_"
val tfree_prefix = "tfree_"

val boolify_base = "hBOOL"
val explicit_app_base = "hAPP"
val type_pred_base = "is"
val tff_type_prefix = "ty_"

fun make_tff_type s = tff_type_prefix ^ ascii_of s

(* official TPTP TFF syntax *)
val tff_type_of_types = "$tType"
val tff_bool_type = "$o"

(* Freshness almost guaranteed! *)
val sledgehammer_weak_prefix = "Sledgehammer:"

type translated_formula =
  {name: string,
   kind: formula_kind,
   combformula: (name, typ, combterm) formula,
   atomic_types: typ list}

fun update_combformula f
        ({name, kind, combformula, atomic_types} : translated_formula) =
  {name = name, kind = kind, combformula = f combformula,
   atomic_types = atomic_types} : translated_formula

fun fact_lift f ({combformula, ...} : translated_formula) = f combformula

datatype type_system =
  Many_Typed |
  Mangled of bool |
  Args of bool |
  Tags of bool |
  No_Types

fun is_type_system_sound Many_Typed = true
  | is_type_system_sound (Mangled full_types) = full_types
  | is_type_system_sound (Args full_types) = full_types
  | is_type_system_sound (Tags full_types) = full_types
  | is_type_system_sound No_Types = false

fun type_system_types_dangerous_types (Tags _) = true
  | type_system_types_dangerous_types type_sys = is_type_system_sound type_sys

fun dont_need_type_args type_sys s =
  s <> type_pred_base andalso
  (member (op =) [@{const_name HOL.eq}] s orelse
   case type_sys of
     Many_Typed => false
   | Mangled _ => false
   | Args _ => s = explicit_app_base
   | Tags full_types => full_types orelse s = explicit_app_base
   | No_Types => true)

datatype type_arg_policy = No_Type_Args | Mangled_Types | Explicit_Type_Args

fun general_type_arg_policy Many_Typed = Mangled_Types
  | general_type_arg_policy (Mangled _) = Mangled_Types
  | general_type_arg_policy _ = Explicit_Type_Args

fun type_arg_policy type_sys s =
  if dont_need_type_args type_sys s then No_Type_Args
  else general_type_arg_policy type_sys

fun num_atp_type_args thy type_sys s =
  if type_arg_policy type_sys s = Explicit_Type_Args then num_type_args thy s
  else 0

fun atp_type_literals_for_types type_sys kind Ts =
  if type_sys = No_Types then
    []
  else
    Ts |> type_literals_for_types
       |> filter (fn TyLitVar _ => kind <> Conjecture
                   | TyLitFree _ => kind = Conjecture)

fun mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])
fun mk_aconns c phis =
  let val (phis', phi') = split_last phis in
    fold_rev (mk_aconn c) phis' phi'
  end
fun mk_ahorn [] phi = phi
  | mk_ahorn phis psi = AConn (AImplies, [mk_aconns AAnd phis, psi])
fun mk_aquant _ [] phi = phi
  | mk_aquant q xs (phi as AQuant (q', xs', phi')) =
    if q = q' then AQuant (q, xs @ xs', phi') else AQuant (q, xs, phi)
  | mk_aquant q xs phi = AQuant (q, xs, phi)

fun close_universally atom_vars phi =
  let
    fun formula_vars bounds (AQuant (_, xs, phi)) =
        formula_vars (map fst xs @ bounds) phi
      | formula_vars bounds (AConn (_, phis)) = fold (formula_vars bounds) phis
      | formula_vars bounds (AAtom tm) =
        union (op =) (atom_vars tm []
                      |> filter_out (member (op =) bounds o fst))
  in mk_aquant AForall (formula_vars [] phi []) phi end

fun combterm_vars (CombApp (tm1, tm2)) = fold combterm_vars [tm1, tm2]
  | combterm_vars (CombConst _) = I
  | combterm_vars (CombVar (name, ty)) = insert (op =) (name, SOME ty)
val close_combformula_universally = close_universally combterm_vars

fun term_vars (ATerm (name as (s, _), tms)) =
  is_atp_variable s ? insert (op =) (name, NONE)
  #> fold term_vars tms
val close_formula_universally = close_universally term_vars

fun fo_term_from_typ (Type (s, Ts)) =
    ATerm (`make_fixed_type_const s, map fo_term_from_typ Ts)
  | fo_term_from_typ (TFree (s, _)) =
    ATerm (`make_fixed_type_var s, [])
  | fo_term_from_typ (TVar ((x as (s, _)), _)) =
    ATerm ((make_schematic_type_var x, s), [])

(* This shouldn't clash with anything else. *)
val mangled_type_sep = "\000"

fun generic_mangled_type_name f (ATerm (name, [])) = f name
  | generic_mangled_type_name f (ATerm (name, tys)) =
    f name ^ "(" ^ commas (map (generic_mangled_type_name f) tys) ^ ")"
val mangled_type_name =
  fo_term_from_typ
  #> (fn ty => (make_tff_type (generic_mangled_type_name fst ty),
                generic_mangled_type_name snd ty))

fun generic_mangled_type_suffix f g tys =
  fold_rev (curry (op ^) o g o prefix mangled_type_sep
            o generic_mangled_type_name f) tys ""
fun mangled_const_name T_args (s, s') =
  let val ty_args = map fo_term_from_typ T_args in
    (s ^ generic_mangled_type_suffix fst ascii_of ty_args,
     s' ^ generic_mangled_type_suffix snd I ty_args)
  end

val parse_mangled_ident =
  Scan.many1 (not o member (op =) ["(", ")", ","]) >> implode

fun parse_mangled_type x =
  (parse_mangled_ident
   -- Scan.optional ($$ "(" |-- Scan.optional parse_mangled_types [] --| $$ ")")
                    [] >> ATerm) x
and parse_mangled_types x =
  (parse_mangled_type ::: Scan.repeat ($$ "," |-- parse_mangled_type)) x

fun unmangled_type s =
  s |> suffix ")" |> raw_explode
    |> Scan.finite Symbol.stopper
           (Scan.error (!! (fn _ => raise Fail ("unrecognized mangled type " ^
                                                quote s)) parse_mangled_type))
    |> fst

val unmangled_const_name = space_explode mangled_type_sep #> hd
fun unmangled_const s =
  let val ss = space_explode mangled_type_sep s in
    (hd ss, map unmangled_type (tl ss))
  end

fun combformula_from_prop thy eq_as_iff =
  let
    fun do_term bs t ts =
      combterm_from_term thy bs (Envir.eta_contract t)
      |>> AAtom ||> union (op =) ts
    fun do_quant bs q s T t' =
      let val s = Name.variant (map fst bs) s in
        do_formula ((s, T) :: bs) t'
        #>> mk_aquant q [(`make_bound_var s, SOME T)]
      end
    and do_conn bs c t1 t2 =
      do_formula bs t1 ##>> do_formula bs t2
      #>> uncurry (mk_aconn c)
    and do_formula bs t =
      case t of
        @{const Not} $ t1 => do_formula bs t1 #>> mk_anot
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

fun concealed_bound_name j = sledgehammer_weak_prefix ^ string_of_int j
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
  let val thy = Proof_Context.theory_of ctxt in
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
   same in Sledgehammer to prevent the discovery of unreplayable proofs. *)
fun freeze_term t =
  let
    fun aux (t $ u) = aux t $ aux u
      | aux (Abs (s, T, t)) = Abs (s, T, aux t)
      | aux (Var ((s, i), T)) =
        Free (sledgehammer_weak_prefix ^ s ^ "_" ^ string_of_int i, T)
      | aux t = t
  in t |> exists_subterm is_Var t ? aux end

(* making fact and conjecture formulas *)
fun make_formula ctxt eq_as_iff presimp name kind t =
  let
    val thy = Proof_Context.theory_of ctxt
    val t = t |> Envir.beta_eta_contract
              |> transform_elim_term
              |> Object_Logic.atomize_term thy
    val need_trueprop = (fastype_of t = @{typ bool})
    val t = t |> need_trueprop ? HOLogic.mk_Trueprop
              |> extensionalize_term
              |> presimp ? presimplify_term thy
              |> perhaps (try (HOLogic.dest_Trueprop))
              |> introduce_combinators_in_term ctxt kind
              |> kind <> Axiom ? freeze_term
    val (combformula, atomic_types) =
      combformula_from_prop thy eq_as_iff t []
  in
    {name = name, combformula = combformula, kind = kind,
     atomic_types = atomic_types}
  end

fun make_fact ctxt keep_trivial eq_as_iff presimp ((name, _), t) =
  case (keep_trivial, make_formula ctxt eq_as_iff presimp name Axiom t) of
    (false, {combformula = AAtom (CombConst (("c_True", _), _, _)), ...}) =>
    NONE
  | (_, formula) => SOME formula

fun make_conjecture ctxt ts =
  let val last = length ts - 1 in
    map2 (fn j => make_formula ctxt true true (string_of_int j)
                               (if j = last then Conjecture else Hypothesis))
         (0 upto last) ts
  end

(** Helper facts **)

fun formula_map f (AQuant (q, xs, phi)) = AQuant (q, xs, formula_map f phi)
  | formula_map f (AConn (c, phis)) = AConn (c, map (formula_map f) phis)
  | formula_map f (AAtom tm) = AAtom (f tm)

fun formula_fold f (AQuant (_, _, phi)) = formula_fold f phi
  | formula_fold f (AConn (_, phis)) = fold (formula_fold f) phis
  | formula_fold f (AAtom tm) = f tm

type sym_table_info =
  {pred_sym : bool, min_ary : int, max_ary : int, typ : typ option}

fun ti_ti_helper_fact () =
  let
    fun var s = ATerm (`I s, [])
    fun tag tm = ATerm (`I type_tag_name, [var "X", tm])
  in
    Formula (Fof, helper_prefix ^ ascii_of "ti_ti", Axiom,
             AAtom (ATerm (`I "equal", [tag (tag (var "Y")), tag (var "Y")]))
             |> close_formula_universally, NONE, NONE)
  end

fun helper_facts_for_sym ctxt type_sys (s, {typ, ...} : sym_table_info) =
  case strip_prefix_and_unascii const_prefix s of
    SOME mangled_s =>
    let
      val thy = Proof_Context.theory_of ctxt
      val unmangled_s = mangled_s |> unmangled_const_name
      fun dub_and_inst c needs_full_types (th, j) =
        ((c ^ "_" ^ string_of_int j ^ (if needs_full_types then "ft" else ""),
          false),
         th |> prop_of
            |> general_type_arg_policy type_sys = Mangled_Types
               ? (case typ of
                    SOME T =>
                    specialize_type thy (safe_invert_const unmangled_s, T)
                  | NONE => I))
      fun make_facts eq_as_iff =
        map_filter (make_fact ctxt false eq_as_iff false)
    in
      metis_helpers
      |> maps (fn (metis_s, (needs_full_types, ths)) =>
                  if metis_s <> unmangled_s orelse
                     (needs_full_types andalso
                      not (type_system_types_dangerous_types type_sys)) then
                    []
                  else
                    ths ~~ (1 upto length ths)
                    |> map (dub_and_inst mangled_s needs_full_types)
                    |> make_facts (not needs_full_types))
    end
  | NONE => []
fun helper_facts_for_sym_table ctxt type_sys sym_tab =
  Symtab.fold_rev (append o helper_facts_for_sym ctxt type_sys) sym_tab []

fun translate_atp_fact ctxt keep_trivial =
  `(make_fact ctxt keep_trivial true true o apsnd prop_of)

fun translate_formulas ctxt type_sys hyp_ts concl_t rich_facts =
  let
    val thy = Proof_Context.theory_of ctxt
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
    val all_ts = goal_t :: fact_ts
    val subs = tfree_classes_of_terms all_ts
    val supers = tvar_classes_of_terms all_ts
    val tycons = type_consts_of_terms thy all_ts
    val conjs = make_conjecture ctxt (hyp_ts @ [concl_t])
    val (supers', arity_clauses) =
      if type_sys = No_Types then ([], [])
      else make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in
    (fact_names |> map single, (conjs, facts, class_rel_clauses, arity_clauses))
  end

fun repair_combterm_consts type_sys =
  let
    fun aux top_level (CombApp (tm1, tm2)) =
        CombApp (aux top_level tm1, aux false tm2)
      | aux top_level (CombConst (name as (s, _), ty, ty_args)) =
        (case strip_prefix_and_unascii const_prefix s of
           NONE => (name, ty_args)
         | SOME s'' =>
           let val s'' = invert_const s'' in
             case type_arg_policy type_sys s'' of
               No_Type_Args => (name, [])
             | Mangled_Types => (mangled_const_name ty_args name, [])
             | Explicit_Type_Args => (name, ty_args)
           end)
        |> (fn (name as (s, s'), ty_args) =>
               case AList.lookup (op =) metis_proxies s of
                 SOME proxy_base =>
                 if top_level then
                   (case s of
                      "c_False" => ("$false", s')
                    | "c_True" => ("$true", s')
                    | _ => name, [])
                  else
                    (proxy_base |>> prefix const_prefix, ty_args)
                | NONE => (name, ty_args))
        |> (fn (name, ty_args) => CombConst (name, ty, ty_args))
      | aux _ tm = tm
  in aux true end

fun tag_with_type ty t = ATerm (`I type_tag_name, [ty, t])

fun fo_literal_from_type_literal (TyLitVar (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))
  | fo_literal_from_type_literal (TyLitFree (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))

fun formula_from_fo_literal (pos, t) = AAtom t |> not pos ? mk_anot

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
  let val thy = Proof_Context.theory_of ctxt in
    case Datatype_Data.get_info thy s of
      SOME {descr, ...} =>
      forall (fn (_, (_, _, constrs)) =>
                 forall (forall (is_dtyp_dangerous ctxt) o snd) constrs) descr
    | NONE =>
      case Typedef.get_info ctxt s of
        ({rep_type, ...}, _) :: _ => is_type_dangerous ctxt rep_type
      | [] => true
  end

fun should_tag_with_type ctxt (Tags full_types) T =
    full_types orelse is_type_dangerous ctxt T
  | should_tag_with_type _ _ _ = false

fun type_pred_combatom type_sys T tm =
  CombApp (CombConst (`make_fixed_const type_pred_base, T --> @{typ bool}, [T]),
           tm)
  |> repair_combterm_consts type_sys
  |> AAtom

fun formula_from_combformula ctxt type_sys =
  let
    fun do_term top_level u =
      let
        val (head, args) = strip_combterm_comb u
        val (x, ty_args) =
          case head of
            CombConst (name, _, ty_args) => (name, ty_args)
          | CombVar (name, _) => (name, [])
          | CombApp _ => raise Fail "impossible \"CombApp\""
        val t = ATerm (x, map fo_term_from_typ ty_args @
                          map (do_term false) args)
        val ty = combtyp_of u
      in
        t |> (if not top_level andalso
                 should_tag_with_type ctxt type_sys ty then
                tag_with_type (fo_term_from_typ ty)
              else
                I)
      end
    val do_bound_type =
      if type_sys = Many_Typed then SOME o mangled_type_name else K NONE
    val do_out_of_bound_type =
      if member (op =) [Mangled true, Args true] type_sys then
        (fn (s, ty) =>
            type_pred_combatom type_sys ty (CombVar (s, ty))
            |> formula_from_combformula ctxt type_sys |> SOME)
      else
        K NONE
    fun do_formula (AQuant (q, xs, phi)) =
        AQuant (q, xs |> map (apsnd (fn NONE => NONE
                                      | SOME ty => do_bound_type ty)),
                (if q = AForall then mk_ahorn else fold_rev (mk_aconn AAnd))
                    (map_filter
                         (fn (_, NONE) => NONE
                           | (s, SOME ty) => do_out_of_bound_type (s, ty)) xs)
                    (do_formula phi))
      | do_formula (AConn (c, phis)) = AConn (c, map do_formula phis)
      | do_formula (AAtom tm) = AAtom (do_term true tm)
  in do_formula end

fun formula_for_fact ctxt type_sys
                     ({combformula, atomic_types, ...} : translated_formula) =
  mk_ahorn (map (formula_from_fo_literal o fo_literal_from_type_literal)
                (atp_type_literals_for_types type_sys Axiom atomic_types))
           (formula_from_combformula ctxt type_sys
                (close_combformula_universally combformula))
  |> close_formula_universally

fun logic_for_type_sys Many_Typed = Tff
  | logic_for_type_sys _ = Fof

(* Each fact is given a unique fact number to avoid name clashes (e.g., because
   of monomorphization). The TPTP explicitly forbids name clashes, and some of
   the remote provers might care. *)
fun formula_line_for_fact ctxt prefix type_sys
                          (j, formula as {name, kind, ...}) =
  Formula (logic_for_type_sys type_sys,
           prefix ^ string_of_int j ^ "_" ^ ascii_of name, kind,
           formula_for_fact ctxt type_sys formula, NONE, NONE)

fun formula_line_for_class_rel_clause (ClassRelClause {name, subclass,
                                                       superclass, ...}) =
  let val ty_arg = ATerm (`I "T", []) in
    Formula (Fof, class_rel_clause_prefix ^ ascii_of name, Axiom,
             AConn (AImplies, [AAtom (ATerm (subclass, [ty_arg])),
                               AAtom (ATerm (superclass, [ty_arg]))])
             |> close_formula_universally, NONE, NONE)
  end

fun fo_literal_from_arity_literal (TConsLit (c, t, args)) =
    (true, ATerm (c, [ATerm (t, map (fn arg => ATerm (arg, [])) args)]))
  | fo_literal_from_arity_literal (TVarLit (c, sort)) =
    (false, ATerm (c, [ATerm (sort, [])]))

fun formula_line_for_arity_clause (ArityClause {name, conclLit, premLits,
                                                ...}) =
  Formula (Fof, arity_clause_prefix ^ ascii_of name, Axiom,
           mk_ahorn (map (formula_from_fo_literal o apfst not
                          o fo_literal_from_arity_literal) premLits)
                    (formula_from_fo_literal
                         (fo_literal_from_arity_literal conclLit))
           |> close_formula_universally, NONE, NONE)

fun formula_line_for_conjecture ctxt type_sys
        ({name, kind, combformula, ...} : translated_formula) =
  Formula (logic_for_type_sys type_sys, conjecture_prefix ^ name, kind,
           formula_from_combformula ctxt type_sys
                                    (close_combformula_universally combformula)
           |> close_formula_universally, NONE, NONE)

fun free_type_literals type_sys ({atomic_types, ...} : translated_formula) =
  atomic_types |> atp_type_literals_for_types type_sys Conjecture
               |> map fo_literal_from_type_literal

fun formula_line_for_free_type j lit =
  Formula (Fof, tfree_prefix ^ string_of_int j, Hypothesis,
           formula_from_fo_literal lit, NONE, NONE)
fun formula_lines_for_free_types type_sys facts =
  let
    val litss = map (free_type_literals type_sys) facts
    val lits = fold (union (op =)) litss []
  in map2 formula_line_for_free_type (0 upto length lits - 1) lits end

(** "hBOOL" and "hAPP" **)

fun add_combterm_to_sym_table explicit_apply =
  let
    fun aux top_level tm =
      let val (head, args) = strip_combterm_comb tm in
        (case head of
           CombConst ((s, _), T, _) =>
           if String.isPrefix bound_var_prefix s then
             I
           else
             let val ary = length args in
               Symtab.map_default
                   (s, {pred_sym = true,
                        min_ary = if explicit_apply then 0 else ary,
                        max_ary = 0, typ = SOME T})
                   (fn {pred_sym, min_ary, max_ary, typ} =>
                       {pred_sym = pred_sym andalso top_level,
                        min_ary = Int.min (ary, min_ary),
                        max_ary = Int.max (ary, max_ary),
                        typ = if typ = SOME T then typ else NONE})
            end
         | _ => I)
        #> fold (aux false) args
      end
  in aux true end

val add_fact_to_sym_table = fact_lift o formula_fold o add_combterm_to_sym_table

(* The "equal" entry is needed for helper facts if the problem otherwise does
   not involve equality. The "$false" and $"true" entries are needed to ensure
   that no "hBOOL" is introduced for them. The "hBOOL" entry is needed to ensure
   that no "hAPP"s are introduced for passing arguments to it. *)
val default_sym_table_entries =
  [("equal", {pred_sym = true, min_ary = 2, max_ary = 2, typ = NONE}),
   (make_fixed_const boolify_base,
    {pred_sym = true, min_ary = 1, max_ary = 1, typ = NONE})] @
  (["$false", "$true"]
   |> map (rpair {pred_sym = true, min_ary = 0, max_ary = 0, typ = NONE}))

fun sym_table_for_facts explicit_apply facts =
  Symtab.empty |> fold (add_fact_to_sym_table explicit_apply) facts
               |> fold Symtab.default default_sym_table_entries

fun min_arity_of sym_tab s =
  case Symtab.lookup sym_tab s of
    SOME ({min_ary, ...} : sym_table_info) => min_ary
  | NONE =>
    case strip_prefix_and_unascii const_prefix s of
      SOME s =>
      let val s = s |> unmangled_const_name |> invert_const in
        if s = boolify_base then 1
        else if s = explicit_app_base then 2
        else if s = type_pred_base then 1
        else 0
      end
    | NONE => 0

(* True if the constant ever appears outside of the top-level position in
   literals, or if it appears with different arities (e.g., because of different
   type instantiations). If false, the constant always receives all of its
   arguments and is used as a predicate. *)
fun is_pred_sym sym_tab s =
  case Symtab.lookup sym_tab s of
    SOME {pred_sym, min_ary, max_ary, ...} => pred_sym andalso min_ary = max_ary
  | NONE => false

val boolify_combconst =
  CombConst (`make_fixed_const boolify_base, @{typ "bool => bool"}, [])
fun boolify tm = CombApp (boolify_combconst, tm)

fun repair_pred_syms_in_combterm sym_tab tm =
  case strip_combterm_comb tm of
    (CombConst ((s, _), _, _), _) =>
    if is_pred_sym sym_tab s then tm else boolify tm
  | _ => boolify tm

fun list_app head args = fold (curry (CombApp o swap)) args head

fun explicit_app arg head =
  let
    val head_T = combtyp_of head
    val (arg_T, res_T) = dest_funT head_T
    val explicit_app =
      CombConst (`make_fixed_const explicit_app_base, head_T --> head_T,
                 [arg_T, res_T])
  in list_app explicit_app [head, arg] end
fun list_explicit_app head args = fold explicit_app args head

fun repair_apps_in_combterm sym_tab =
  let
    fun aux tm =
      case strip_combterm_comb tm of
        (head as CombConst ((s, _), _, _), args) =>
        args |> map aux
             |> chop (min_arity_of sym_tab s)
             |>> list_app head
             |-> list_explicit_app
      | (head, args) => list_explicit_app head (map aux args)
  in aux end

fun repair_combterm type_sys sym_tab =
  repair_pred_syms_in_combterm sym_tab
  #> repair_apps_in_combterm sym_tab
  #> repair_combterm_consts type_sys
val repair_combformula = formula_map oo repair_combterm
val repair_fact = update_combformula oo repair_combformula

fun is_const_relevant type_sys sym_tab s =
  not (String.isPrefix bound_var_prefix s) andalso s <> "equal" andalso
  (type_sys = Many_Typed orelse not (is_pred_sym sym_tab s))

fun consider_combterm_consts type_sys sym_tab tm =
  let val (head, args) = strip_combterm_comb tm in
    (case head of
       CombConst ((s, s'), ty, ty_args) =>
       (* FIXME: exploit type subsumption *)
       is_const_relevant type_sys sym_tab s
       ? Symtab.insert_list (op =) (s, (s', ty_args, ty))
     | _ => I)
    #> fold (consider_combterm_consts type_sys sym_tab) args
  end

fun consider_fact_consts type_sys sym_tab =
  fact_lift (formula_fold (consider_combterm_consts type_sys sym_tab))

(* FIXME: needed? *)
fun typed_const_table_for_facts type_sys sym_tab facts =
  Symtab.empty |> member (op =) [Many_Typed, Mangled true, Args true] type_sys
                  ? fold (consider_fact_consts type_sys sym_tab) facts

fun strip_and_map_type 0 f T = ([], f T)
  | strip_and_map_type n f (Type (@{type_name fun}, [dom_T, ran_T])) =
    strip_and_map_type (n - 1) f ran_T |>> cons (f dom_T)
  | strip_and_map_type _ _ _ = raise Fail "unexpected non-function"

fun problem_line_for_typed_const ctxt type_sys sym_tab s j (s', ty_args, T) =
  let val ary = min_arity_of sym_tab s in
    if type_sys = Many_Typed then
      let val (arg_Ts, res_T) = strip_and_map_type ary mangled_type_name T in
        Decl (sym_decl_prefix ^ ascii_of s, (s, s'), arg_Ts,
              (* ### FIXME: put that in typed_const_tab *)
              if is_pred_sym sym_tab s then `I tff_bool_type else res_T)
      end
    else
      let
        val (arg_Ts, res_T) = strip_and_map_type ary I T
        val bound_names =
          1 upto length arg_Ts |> map (`I o make_bound_var o string_of_int)
        val bound_tms =
          bound_names ~~ arg_Ts |> map (fn (name, T) => CombConst (name, T, []))
        val bound_Ts =
          arg_Ts |> map (case type_sys of Mangled _ => K NONE | _ => SOME)
        val freshener =
          case type_sys of Args _ => string_of_int j ^ "_" | _ => ""
      in
        Formula (Fof, sym_decl_prefix ^ freshener ^ "_" ^ ascii_of s, Axiom,
                 CombConst ((s, s'), T, ty_args)
                 |> fold (curry (CombApp o swap)) bound_tms
                 |> type_pred_combatom type_sys res_T
                 |> mk_aquant AForall (bound_names ~~ bound_Ts)
                 |> formula_from_combformula ctxt type_sys,
                 NONE, NONE)
      end
  end
fun problem_lines_for_sym_decl ctxt type_sys sym_tab (s, xs) =
  map2 (problem_line_for_typed_const ctxt type_sys sym_tab s)
       (0 upto length xs - 1) xs
fun problem_lines_for_sym_decls ctxt type_sys sym_tab typed_const_tab =
  Symtab.fold_rev (append o problem_lines_for_sym_decl ctxt type_sys sym_tab)
                  typed_const_tab []

fun add_tff_types_in_formula (AQuant (_, xs, phi)) =
    union (op =) (map_filter snd xs) #> add_tff_types_in_formula phi
  | add_tff_types_in_formula (AConn (_, phis)) =
    fold add_tff_types_in_formula phis
  | add_tff_types_in_formula (AAtom _) = I

fun add_tff_types_in_problem_line (Decl (_, _, arg_Ts, res_T)) =
    union (op =) (res_T :: arg_Ts)
  | add_tff_types_in_problem_line (Formula (_, _, _, phi, _, _)) =
    add_tff_types_in_formula phi

fun tff_types_in_problem problem =
  fold (fold add_tff_types_in_problem_line o snd) problem []

fun decl_line_for_tff_type (s, s') =
  Decl (type_decl_prefix ^ ascii_of s, (s, s'), [], `I tff_type_of_types)

val type_declsN = "Types"
val sym_declsN = "Symbol types"
val factsN = "Relevant facts"
val class_relsN = "Class relationships"
val aritiesN = "Arities"
val helpersN = "Helper facts"
val conjsN = "Conjectures"
val free_typesN = "Type variables"

fun offset_of_heading_in_problem _ [] j = j
  | offset_of_heading_in_problem needle ((heading, lines) :: problem) j =
    if heading = needle then j
    else offset_of_heading_in_problem needle problem (j + length lines)

fun prepare_atp_problem ctxt readable_names type_sys explicit_apply hyp_ts
                        concl_t facts =
  let
    val (fact_names, (conjs, facts, class_rel_clauses, arity_clauses)) =
      translate_formulas ctxt type_sys hyp_ts concl_t facts
    val sym_tab = conjs @ facts |> sym_table_for_facts explicit_apply
    val conjs = conjs |> map (repair_fact type_sys sym_tab)
    val facts = facts |> map (repair_fact type_sys sym_tab)
    val sym_tab' = conjs @ facts |> sym_table_for_facts false
    val typed_const_tab =
      conjs @ facts |> typed_const_table_for_facts type_sys sym_tab'
    val sym_decl_lines =
      typed_const_tab |> problem_lines_for_sym_decls ctxt type_sys sym_tab'
    val helpers = helper_facts_for_sym_table ctxt type_sys sym_tab'
                  |> map (repair_fact type_sys sym_tab')
    (* Reordering these might confuse the proof reconstruction code or the SPASS
       Flotter hack. *)
    val problem =
      [(sym_declsN, sym_decl_lines),
       (factsN, map (formula_line_for_fact ctxt fact_prefix type_sys)
                    (0 upto length facts - 1 ~~ facts)),
       (class_relsN, map formula_line_for_class_rel_clause class_rel_clauses),
       (aritiesN, map formula_line_for_arity_clause arity_clauses),
       (helpersN, map (formula_line_for_fact ctxt helper_prefix type_sys)
                      (0 upto length helpers - 1 ~~ helpers)
                  |> (if type_sys = Tags false then cons (ti_ti_helper_fact ())
                      else I)),
       (conjsN, map (formula_line_for_conjecture ctxt type_sys) conjs),
       (free_typesN, formula_lines_for_free_types type_sys (facts @ conjs))]
    val problem =
      problem
      |> (if type_sys = Many_Typed then
            cons (type_declsN,
                  map decl_line_for_tff_type (tff_types_in_problem problem))
          else
            I)
    val (problem, pool) = problem |> nice_atp_problem readable_names
  in
    (problem,
     case pool of SOME the_pool => snd the_pool | NONE => Symtab.empty,
     offset_of_heading_in_problem factsN problem 0,
     offset_of_heading_in_problem conjsN problem 0,
     fact_names |> Vector.fromList)
  end

(* FUDGE *)
val conj_weight = 0.0
val hyp_weight = 0.1
val fact_min_weight = 0.2
val fact_max_weight = 1.0

fun add_term_weights weight (ATerm (s, tms)) =
  (not (is_atp_variable s) andalso s <> "equal") ? Symtab.default (s, weight)
  #> fold (add_term_weights weight) tms
fun add_problem_line_weights weight (Formula (_, _, _, phi, _, _)) =
    formula_fold (add_term_weights weight) phi
  | add_problem_line_weights _ _ = I

fun add_conjectures_weights [] = I
  | add_conjectures_weights conjs =
    let val (hyps, conj) = split_last conjs in
      add_problem_line_weights conj_weight conj
      #> fold (add_problem_line_weights hyp_weight) hyps
    end

fun add_facts_weights facts =
  let
    val num_facts = length facts
    fun weight_of j =
      fact_min_weight + (fact_max_weight - fact_min_weight) * Real.fromInt j
                        / Real.fromInt num_facts
  in
    map weight_of (0 upto num_facts - 1) ~~ facts
    |> fold (uncurry add_problem_line_weights)
  end

(* Weights are from 0.0 (most important) to 1.0 (least important). *)
fun atp_problem_weights problem =
  Symtab.empty
  |> add_conjectures_weights (these (AList.lookup (op =) problem conjsN))
  |> add_facts_weights (these (AList.lookup (op =) problem factsN))
  |> Symtab.dest
  |> sort (prod_ord Real.compare string_ord o pairself swap)

end;
