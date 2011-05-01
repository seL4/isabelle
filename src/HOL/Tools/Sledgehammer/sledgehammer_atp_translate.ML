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
    Tags of bool |
    Args of bool |
    Mangled of bool |
    No_Types

  val fact_prefix : string
  val conjecture_prefix : string
  val is_type_system_sound : type_system -> bool
  val type_system_types_dangerous_types : type_system -> bool
  val num_atp_type_args : theory -> type_system -> string -> int
  val translate_atp_fact :
    Proof.context -> bool -> (string * 'a) * thm
    -> translated_formula option * ((string * 'a) * thm)
  val unmangled_const : string -> string * string fo_term list
  val prepare_atp_problem :
    Proof.context -> bool -> type_system -> bool -> term list -> term
    -> (translated_formula option * ((string * 'a) * thm)) list
    -> string problem * string Symtab.table * int * (string * 'a) list vector
  val atp_problem_weights : string problem -> (string * real) list
end;

structure Sledgehammer_ATP_Translate : SLEDGEHAMMER_ATP_TRANSLATE =
struct

open ATP_Problem
open Metis_Translate
open Sledgehammer_Util

val fact_prefix = "fact_"
val conjecture_prefix = "conj_"
val helper_prefix = "help_"
val type_decl_prefix = "type_"
val class_rel_clause_prefix = "clrel_";
val arity_clause_prefix = "arity_"
val tfree_prefix = "tfree_"

val is_base = "is"
val type_prefix = "ty_"

fun make_type ty = type_prefix ^ ascii_of ty

(* Freshness almost guaranteed! *)
val sledgehammer_weak_prefix = "Sledgehammer:"

type translated_formula =
  {name: string,
   kind: formula_kind,
   combformula: (name, combtyp, combterm) formula,
   ctypes_sorts: typ list}

datatype type_system =
  Many_Typed |
  Tags of bool |
  Args of bool |
  Mangled of bool |
  No_Types

fun is_type_system_sound Many_Typed = true
  | is_type_system_sound (Tags full_types) = full_types
  | is_type_system_sound (Args full_types) = full_types
  | is_type_system_sound (Mangled full_types) = full_types
  | is_type_system_sound No_Types = false

fun type_system_types_dangerous_types (Tags _) = true
  | type_system_types_dangerous_types type_sys = is_type_system_sound type_sys

fun dont_need_type_args type_sys s =
  s <> is_base andalso
  (member (op =) [@{const_name HOL.eq}, @{const_name Metis.fequal}] s orelse
   case type_sys of
     Many_Typed => false
   | Tags full_types => full_types
   | Args _ => false
   | Mangled _ => false
   | No_Types => true)

datatype type_arg_policy = No_Type_Args | Explicit_Type_Args | Mangled_Types

fun type_arg_policy type_sys s =
  if dont_need_type_args type_sys s then
    No_Type_Args
  else
    case type_sys of
      Many_Typed => Mangled_Types
    | Mangled _ => Mangled_Types
    | _ => Explicit_Type_Args

fun num_atp_type_args thy type_sys s =
  if type_arg_policy type_sys s = Explicit_Type_Args then
    if s = is_base then 1 else num_type_args thy s
  else
    0

fun atp_type_literals_for_types type_sys kind Ts =
  if type_sys = No_Types then
    []
  else
    Ts |> type_literals_for_types
       |> filter (fn TyLitVar _ => kind <> Conjecture
                   | TyLitFree _ => kind = Conjecture)

fun mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])
fun mk_ahorn [] phi = phi
  | mk_ahorn (phi :: phis) psi =
    AConn (AImplies, [fold (mk_aconn AAnd) phis phi, psi])
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

fun combformula_for_prop thy eq_as_iff =
  let
    fun do_term bs t ts =
      combterm_from_term thy bs (Envir.eta_contract t)
      |>> AAtom ||> union (op =) ts
    fun do_quant bs q s T t' =
      let val s = Name.variant (map fst bs) s in
        do_formula ((s, T) :: bs) t'
        #>> mk_aquant q [(`make_bound_var s, SOME (combtyp_from_typ T))]
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

fun make_fact ctxt keep_trivial eq_as_iff presimp ((name, _), th) =
  case (keep_trivial,
        make_formula ctxt eq_as_iff presimp name Axiom (prop_of th)) of
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

fun fold_formula f (AQuant (_, _, phi)) = fold_formula f phi
  | fold_formula f (AConn (_, phis)) = fold (fold_formula f) phis
  | fold_formula f (AAtom tm) = f tm

fun count_term (ATerm ((s, _), tms)) =
  (if is_atp_variable s then I
   else Symtab.map_entry s (Integer.add 1))
  #> fold count_term tms
fun count_formula x = fold_formula count_term x

val init_counters =
  metis_helpers |> map fst |> sort_distinct string_ord |> map (rpair 0)
  |> Symtab.make

fun get_helper_facts ctxt type_sys formulas =
  let
    val no_dangerous_types = type_system_types_dangerous_types type_sys
    val ct = init_counters |> fold count_formula formulas
    fun is_used s = the (Symtab.lookup ct s) > 0
    fun dub c needs_full_types (th, j) =
      ((c ^ "_" ^ string_of_int j ^ (if needs_full_types then "ft" else ""),
        false), th)
    fun make_facts eq_as_iff = map_filter (make_fact ctxt false eq_as_iff false)
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
         [Formula (helper_prefix ^ ascii_of "ti_ti", Axiom,
                   AAtom (ATerm (`I "equal",
                                 [tag (tag (var "Y")), tag (var "Y")]))
                   |> close_formula_universally, NONE, NONE)]
       end
     else
       [])
  end

fun translate_atp_fact ctxt keep_trivial =
  `(make_fact ctxt keep_trivial true true)

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

(* We are crossing our fingers that it doesn't clash with anything else. *)
val mangled_type_sep = "\000"

fun mangled_combtyp_component f (CombTFree name) = f name
  | mangled_combtyp_component f (CombTVar name) =
    f name (* FIXME: shouldn't happen *)
    (* raise Fail "impossible schematic type variable" *)
  | mangled_combtyp_component f (CombType (name, tys)) =
    "(" ^ commas (map (mangled_combtyp_component f) tys) ^ ")" ^ f name

fun mangled_combtyp ty =
  (make_type (mangled_combtyp_component fst ty),
   mangled_combtyp_component snd ty)

fun mangled_type_suffix f g tys =
  fold_rev (curry (op ^) o g o prefix mangled_type_sep
            o mangled_combtyp_component f) tys ""

fun mangled_const (s, s') ty_args =
  (s ^ mangled_type_suffix fst ascii_of ty_args,
   s' ^ mangled_type_suffix snd I ty_args)

val parse_mangled_ident =
  Scan.many1 (not o member (op =) ["(", ")", ","]) >> implode

fun parse_mangled_type x =
  ($$ "(" |-- Scan.optional parse_mangled_types [] --| $$ ")"
      -- parse_mangled_ident >> (ATerm o swap)
   || parse_mangled_ident >> (ATerm o rpair [])) x
and parse_mangled_types x =
  (parse_mangled_type ::: Scan.repeat ($$ "," |-- parse_mangled_type)) x

fun unmangled_type s =
  s |> suffix ")" |> raw_explode
    |> Scan.finite Symbol.stopper
           (Scan.error (!! (fn _ => raise Fail ("unrecognized mangled type " ^
                                                quote s)) parse_mangled_type))
    |> fst

fun unmangled_const s =
  let val ss = space_explode mangled_type_sep s in
    (hd ss, map unmangled_type (tl ss))
  end

fun pred_combtyp ty =
  case combtyp_from_typ @{typ "unit => bool"} of
    CombType (name, [_, bool_ty]) => CombType (name, [ty, bool_ty])
  | _ => raise Fail "expected two-argument type constructor"

fun formula_for_combformula ctxt type_sys =
  let
    fun do_term top_level u =
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
                 let val s'' = invert_const s'' in
                   case type_arg_policy type_sys s'' of
                     No_Type_Args => (name, [])
                   | Explicit_Type_Args => (name, ty_args)
                   | Mangled_Types => (mangled_const name ty_args, [])
                 end)
          | CombVar (name, _) => (name, [])
          | CombApp _ => raise Fail "impossible \"CombApp\""
        val t = ATerm (x, map fo_term_for_combtyp ty_args @
                          map (do_term false) args)
        val ty = combtyp_of u
      in
        t |> (if should_tag_with_type ctxt type_sys ty then
                tag_with_type (fo_term_for_combtyp ty)
              else
                I)
      end
    val do_bound_type =
      if type_sys = Many_Typed then SOME o mangled_combtyp else K NONE
    val do_out_of_bound_type =
      if member (op =) [Args true, Mangled true] type_sys then
        (fn (s, ty) =>
            CombApp (CombConst ((const_prefix ^ is_base, is_base),
                                pred_combtyp ty, [ty]),
                     CombVar (s, ty))
            |> AAtom |> formula_for_combformula ctxt type_sys |> SOME)
      else
        K NONE
    fun do_formula (AQuant (q, xs, phi)) =
        AQuant (q, xs |> map (apsnd (fn NONE => NONE
                                      | SOME ty => do_bound_type ty)),
                (if q = AForall then mk_ahorn else fold (mk_aconn AAnd))
                    (map_filter
                         (fn (_, NONE) => NONE
                           | (s, SOME ty) => do_out_of_bound_type (s, ty)) xs)
                    (do_formula phi))
      | do_formula (AConn (c, phis)) = AConn (c, map do_formula phis)
      | do_formula (AAtom tm) = AAtom (do_term true tm)
  in do_formula end

fun formula_for_fact ctxt type_sys
                     ({combformula, ctypes_sorts, ...} : translated_formula) =
  mk_ahorn (map (formula_for_fo_literal o fo_literal_for_type_literal)
                (atp_type_literals_for_types type_sys Axiom ctypes_sorts))
           (formula_for_combformula ctxt type_sys
                                    (close_combformula_universally combformula))

(* Each fact is given a unique fact number to avoid name clashes (e.g., because
   of monomorphization). The TPTP explicitly forbids name clashes, and some of
   the remote provers might care. *)
fun problem_line_for_fact ctxt prefix type_sys
                          (j, formula as {name, kind, ...}) =
  Formula (prefix ^ string_of_int j ^ "_" ^ ascii_of name,
           kind, formula_for_fact ctxt type_sys formula, NONE, NONE)

fun problem_line_for_class_rel_clause (ClassRelClause {name, subclass,
                                                       superclass, ...}) =
  let val ty_arg = ATerm (("T", "T"), []) in
    Formula (class_rel_clause_prefix ^ ascii_of name, Axiom,
             AConn (AImplies, [AAtom (ATerm (subclass, [ty_arg])),
                               AAtom (ATerm (superclass, [ty_arg]))]),
             NONE, NONE)
  end

fun fo_literal_for_arity_literal (TConsLit (c, t, args)) =
    (true, ATerm (c, [ATerm (t, map (fn arg => ATerm (arg, [])) args)]))
  | fo_literal_for_arity_literal (TVarLit (c, sort)) =
    (false, ATerm (c, [ATerm (sort, [])]))

fun problem_line_for_arity_clause (ArityClause {name, conclLit, premLits,
                                                ...}) =
  Formula (arity_clause_prefix ^ ascii_of name, Axiom,
           mk_ahorn (map (formula_for_fo_literal o apfst not
                          o fo_literal_for_arity_literal) premLits)
                    (formula_for_fo_literal
                         (fo_literal_for_arity_literal conclLit)), NONE, NONE)

fun problem_line_for_conjecture ctxt type_sys
        ({name, kind, combformula, ...} : translated_formula) =
  Formula (conjecture_prefix ^ name, kind,
           formula_for_combformula ctxt type_sys
                                   (close_combformula_universally combformula),
           NONE, NONE)

fun free_type_literals type_sys ({ctypes_sorts, ...} : translated_formula) =
  ctypes_sorts |> atp_type_literals_for_types type_sys Conjecture
               |> map fo_literal_for_type_literal

fun problem_line_for_free_type j lit =
  Formula (tfree_prefix ^ string_of_int j, Hypothesis,
           formula_for_fo_literal lit, NONE, NONE)
fun problem_lines_for_free_types type_sys facts =
  let
    val litss = map (free_type_literals type_sys) facts
    val lits = fold (union (op =)) litss []
  in map2 problem_line_for_free_type (0 upto length lits - 1) lits end

(** "hBOOL" and "hAPP" **)

type sym_info = {min_arity: int, max_arity: int, fun_sym: bool}

fun consider_term_syms top_level (ATerm ((s, _), ts)) =
  (if is_atp_variable s then
     I
   else
     let val n = length ts in
       Symtab.map_default
           (s, {min_arity = n, max_arity = 0, fun_sym = false})
           (fn {min_arity, max_arity, fun_sym} =>
               {min_arity = Int.min (n, min_arity),
                max_arity = Int.max (n, max_arity),
                fun_sym = fun_sym orelse not top_level})
     end)
  #> fold (consider_term_syms (top_level andalso s = type_tag_name)) ts
val consider_formula_syms = fold_formula (consider_term_syms true)

fun consider_problem_line_syms (Type_Decl _) = I
  | consider_problem_line_syms (Formula (_, _, phi, _, _)) =
    consider_formula_syms phi
fun consider_problem_syms problem =
  fold (fold consider_problem_line_syms o snd) problem

(* needed for helper facts if the problem otherwise does not involve equality *)
val equal_entry = ("equal", {min_arity = 2, max_arity = 2, fun_sym = false})

fun sym_table_for_problem explicit_apply problem =
  if explicit_apply then
    NONE
  else
    SOME (Symtab.empty |> Symtab.default equal_entry
                       |> consider_problem_syms problem)

fun min_arity_of thy type_sys NONE s =
    (if s = "equal" orelse s = type_tag_name orelse
        String.isPrefix type_const_prefix s orelse
        String.isPrefix class_prefix s then
       16383 (* large number *)
     else case strip_prefix_and_unascii const_prefix s of
       SOME s' => s' |> unmangled_const |> fst |> invert_const
                     |> num_atp_type_args thy type_sys
     | NONE => 0)
  | min_arity_of _ _ (SOME sym_tab) s =
    case Symtab.lookup sym_tab s of
      SOME ({min_arity, ...} : sym_info) => min_arity
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

fun repair_applications_in_term thy type_sys sym_tab =
  let
    fun aux opt_ty (ATerm (name as (s, _), ts)) =
      if s = type_tag_name then
        case ts of
          [t1, t2] => ATerm (name, [aux NONE t1, aux (SOME t1) t2])
        | _ => raise Fail "malformed type tag"
      else
        let
          val ts = map (aux NONE) ts
          val (ts1, ts2) = chop (min_arity_of thy type_sys sym_tab s) ts
        in list_hAPP_rev opt_ty (ATerm (name, ts1)) (rev ts2) end
  in aux NONE end

fun boolify t = ATerm (`I "hBOOL", [t])

(* True if the constant ever appears outside of the top-level position in
   literals, or if it appears with different arities (e.g., because of different
   type instantiations). If false, the constant always receives all of its
   arguments and is used as a predicate. *)
fun is_pred_sym NONE s =
    s = "equal" orelse s = "$false" orelse s = "$true" orelse
    String.isPrefix type_const_prefix s orelse String.isPrefix class_prefix s
  | is_pred_sym (SOME sym_tab) s =
    case Symtab.lookup sym_tab s of
      SOME {min_arity, max_arity, fun_sym} =>
      not fun_sym andalso min_arity = max_arity
    | NONE => false

fun repair_predicates_in_term pred_sym_tab (t as ATerm ((s, _), ts)) =
  if s = type_tag_name then
    case ts of
      [_, t' as ATerm ((s', _), _)] =>
      if is_pred_sym pred_sym_tab s' then t' else boolify t
    | _ => raise Fail "malformed type tag"
  else
    t |> not (is_pred_sym pred_sym_tab s) ? boolify

fun repair_formula thy type_sys sym_tab =
  let
    val pred_sym_tab = case type_sys of Tags _ => NONE | _ => sym_tab
    fun aux (AQuant (q, xs, phi)) = AQuant (q, xs, aux phi)
      | aux (AConn (c, phis)) = AConn (c, map aux phis)
      | aux (AAtom tm) =
        AAtom (tm |> repair_applications_in_term thy type_sys sym_tab
                  |> repair_predicates_in_term pred_sym_tab)
  in aux #> close_formula_universally end

fun repair_problem_line thy type_sys sym_tab
                        (Formula (ident, kind, phi, source, useful_info)) =
    Formula (ident, kind, repair_formula thy type_sys sym_tab phi, source,
             useful_info)
  | repair_problem_line _ _ _ _ = raise Fail "unexpected non-formula"
fun repair_problem thy = map o apsnd o map oo repair_problem_line thy

fun is_const_relevant s =
  case strip_prefix_and_unascii const_prefix s of
    SOME @{const_name HOL.eq} => false
  | opt => is_some opt

fun consider_combterm_consts sym_tab (*FIXME: use*) tm =
  let val (head, args) = strip_combterm_comb tm in
    (case head of
       CombConst ((s, s'), ty, ty_args) =>
       (* FIXME: exploit type subsumption *)
       is_const_relevant s ? Symtab.insert_list (op =) (s, (s', ty_args, ty))
     | _ => I) (* FIXME: hAPP on var *)
    #> fold (consider_combterm_consts sym_tab) args
  end

fun consider_fact_consts sym_tab ({combformula, ...} : translated_formula) =
  fold_formula (consider_combterm_consts sym_tab) combformula

fun const_table_for_facts type_sys sym_tab facts =
  Symtab.empty |> member (op =) [Many_Typed, Args true, Mangled true] type_sys
                  ? fold (consider_fact_consts sym_tab) facts

fun fo_type_from_combtyp (ty as CombType ((s, _), tys)) =
    (case (strip_prefix_and_unascii type_const_prefix s, tys) of
       (SOME @{type_name fun}, [dom_ty, ran_ty]) =>
       fo_type_from_combtyp ran_ty |>> cons (mangled_combtyp dom_ty)
     | _ => ([], mangled_combtyp ty))
  | fo_type_from_combtyp ty = ([], mangled_combtyp ty)

fun type_decl_line_for_const_entry Many_Typed s (s', ty_args, ty) =
    let
      val (s, s') = mangled_const (s, s') ty_args
      val (arg_tys, res_ty) = fo_type_from_combtyp ty
    in Type_Decl (type_decl_prefix ^ ascii_of s, (s, s'), arg_tys, res_ty) end
  | type_decl_line_for_const_entry _ _ _ = raise Fail "not implemented yet"
fun type_decl_lines_for_const type_sys (s, xs) =
  map (type_decl_line_for_const_entry type_sys s) xs

val factsN = "Relevant facts"
val class_relsN = "Class relationships"
val aritiesN = "Arity declarations"
val helpersN = "Helper facts"
val type_declsN = "Type declarations"
val conjsN = "Conjectures"
val free_typesN = "Type variables"

fun offset_of_heading_in_problem _ [] j = j
  | offset_of_heading_in_problem needle ((heading, lines) :: problem) j =
    if heading = needle then j
    else offset_of_heading_in_problem needle problem (j + length lines)

fun prepare_atp_problem ctxt readable_names type_sys explicit_apply hyp_ts
                        concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val (fact_names, (conjs, facts, class_rel_clauses, arity_clauses)) =
      translate_formulas ctxt type_sys hyp_ts concl_t facts
    (* Reordering these might confuse the proof reconstruction code or the SPASS
       Flotter hack. *)
    val problem =
      [(factsN, map (problem_line_for_fact ctxt fact_prefix type_sys)
                    (0 upto length facts - 1 ~~ facts)),
       (class_relsN, map problem_line_for_class_rel_clause class_rel_clauses),
       (aritiesN, map problem_line_for_arity_clause arity_clauses),
       (helpersN, []),
       (type_declsN, []),
       (conjsN, map (problem_line_for_conjecture ctxt type_sys) conjs),
       (free_typesN, problem_lines_for_free_types type_sys (facts @ conjs))]
    val sym_tab = sym_table_for_problem explicit_apply problem
    val problem = problem |> repair_problem thy type_sys sym_tab
    val helper_facts =
      problem |> maps (map_filter (fn Formula (_, _, phi, _, _) => SOME phi
                                    | _ => NONE) o snd)
              |> get_helper_facts ctxt type_sys
    val const_tab = const_table_for_facts type_sys sym_tab (conjs @ facts)
    val type_decl_lines =
      Symtab.fold_rev (append o type_decl_lines_for_const type_sys) const_tab []
    val helper_lines =
      helper_facts
      |>> map (pair 0
               #> problem_line_for_fact ctxt helper_prefix type_sys
               #> repair_problem_line thy type_sys sym_tab)
      |> op @
    val (problem, pool) =
      problem |> fold (AList.update (op =))
                      [(helpersN, helper_lines), (type_declsN, type_decl_lines)]
              |> nice_atp_problem readable_names
  in
    (problem,
     case pool of SOME the_pool => snd the_pool | NONE => Symtab.empty,
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
fun add_problem_line_weights weight (Formula (_, _, phi, _, _)) =
    fold_formula (add_term_weights weight) phi
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
