(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_translate.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Sledgehammer.
*)

signature SLEDGEHAMMER_TRANSLATE =
sig
  type 'a problem = 'a ATP_Problem.problem
  type fol_formula

  val axiom_prefix : string
  val conjecture_prefix : string
  val helper_prefix : string
  val class_rel_clause_prefix : string
  val arity_clause_prefix : string
  val tfrees_name : string
  val prepare_axiom :
    Proof.context -> (string * 'a) * thm
    -> term * ((string * 'a) * fol_formula) option
  val prepare_problem :
    Proof.context -> bool -> bool -> bool -> bool -> term list -> term
    -> (term * ((string * 'a) * fol_formula) option) list
    -> string problem * string Symtab.table * int * (string * 'a) list vector
end;

structure Sledgehammer_Translate : SLEDGEHAMMER_TRANSLATE =
struct

open ATP_Problem
open Metis_Translate
open Sledgehammer_Util

val axiom_prefix = "ax_"
val conjecture_prefix = "conj_"
val helper_prefix = "help_"
val class_rel_clause_prefix = "clrel_";
val arity_clause_prefix = "arity_"
val tfrees_name = "tfrees"

(* Freshness almost guaranteed! *)
val sledgehammer_weak_prefix = "Sledgehammer:"

type fol_formula =
  {name: string,
   kind: kind,
   combformula: (name, combterm) formula,
   ctypes_sorts: typ list}

fun mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])
fun mk_ahorn [] phi = phi
  | mk_ahorn (phi :: phis) psi =
    AConn (AImplies, [fold (mk_aconn AAnd) phis phi, psi])

fun combformula_for_prop thy =
  let
    val do_term = combterm_from_term thy ~1
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
        do_conn bs AIff t1 t2
      | _ => (fn ts => do_term bs (Envir.eta_contract t)
                       |>> AAtom ||> union (op =) ts)
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

(* making axiom and conjecture formulas *)
fun make_formula ctxt presimp name kind t =
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
    val (combformula, ctypes_sorts) = combformula_for_prop thy t []
  in
    {name = name, combformula = combformula, kind = kind,
     ctypes_sorts = ctypes_sorts}
  end

fun make_axiom ctxt presimp ((name, loc), th) =
  case make_formula ctxt presimp name Axiom (prop_of th) of
    {combformula = AAtom (CombConst (("c_True", _), _, _)), ...} => NONE
  | formula => SOME ((name, loc), formula)
fun make_conjecture ctxt ts =
  let val last = length ts - 1 in
    map2 (fn j => make_formula ctxt true (Int.toString j)
                               (if j = last then Conjecture else Hypothesis))
         (0 upto last) ts
  end

(** Helper facts **)

fun count_combterm (CombConst ((s, _), _, _)) =
    Symtab.map_entry s (Integer.add 1)
  | count_combterm (CombVar _) = I
  | count_combterm (CombApp (t1, t2)) = fold count_combterm [t1, t2]
fun count_combformula (AQuant (_, _, phi)) = count_combformula phi
  | count_combformula (AConn (_, phis)) = fold count_combformula phis
  | count_combformula (AAtom tm) = count_combterm tm
fun count_fol_formula ({combformula, ...} : fol_formula) =
  count_combformula combformula

val optional_helpers =
  [(["c_COMBI"], @{thms COMBI_def}),
   (["c_COMBK"], @{thms COMBK_def}),
   (["c_COMBB"], @{thms COMBB_def}),
   (["c_COMBC"], @{thms COMBC_def}),
   (["c_COMBS"], @{thms COMBS_def})]
val optional_typed_helpers =
  [(["c_True", "c_False", "c_If"], @{thms True_or_False}),
   (["c_If"], @{thms if_True if_False})]
val mandatory_helpers = @{thms fequal_def}

val init_counters =
  [optional_helpers, optional_typed_helpers] |> maps (maps fst)
  |> sort_distinct string_ord |> map (rpair 0) |> Symtab.make

fun get_helper_facts ctxt is_FO full_types conjectures axioms =
  let
    val ct = fold (fold count_fol_formula) [conjectures, axioms] init_counters
    fun is_needed c = the (Symtab.lookup ct c) > 0
    fun baptize th = ((Thm.get_name_hint th, false), th)
  in
    (optional_helpers
     |> full_types ? append optional_typed_helpers
     |> maps (fn (ss, ths) =>
                 if exists is_needed ss then map baptize ths else [])) @
    (if is_FO then [] else map baptize mandatory_helpers)
    |> map_filter (Option.map snd o make_axiom ctxt false)
  end

fun prepare_axiom ctxt (ax as (_, th)) = (prop_of th, make_axiom ctxt true ax)

fun prepare_formulas ctxt full_types hyp_ts concl_t axioms =
  let
    val thy = ProofContext.theory_of ctxt
    val (axiom_ts, prepared_axioms) = ListPair.unzip axioms
    (* Remove existing axioms from the conjecture, as this can dramatically
       boost an ATP's performance (for some reason). *)
    val hyp_ts = hyp_ts |> filter_out (member (op aconv) axiom_ts)
    val goal_t = Logic.list_implies (hyp_ts, concl_t)
    val is_FO = Meson.is_fol_term thy goal_t
    val subs = tfree_classes_of_terms [goal_t]
    val supers = tvar_classes_of_terms axiom_ts
    val tycons = type_consts_of_terms thy (goal_t :: axiom_ts)
    (* TFrees in the conjecture; TVars in the axioms *)
    val conjectures = make_conjecture ctxt (hyp_ts @ [concl_t])
    val (axiom_names, axioms) = ListPair.unzip (map_filter I prepared_axioms)
    val helper_facts = get_helper_facts ctxt is_FO full_types conjectures axioms
    val (supers', arity_clauses) = make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in
    (axiom_names |> map single |> Vector.fromList,
     (conjectures, axioms, helper_facts, class_rel_clauses, arity_clauses))
  end

fun wrap_type ty t = ATerm ((type_wrapper_name, type_wrapper_name), [ty, t])

fun fo_term_for_combtyp (CombTVar name) = ATerm (name, [])
  | fo_term_for_combtyp (CombTFree name) = ATerm (name, [])
  | fo_term_for_combtyp (CombType (name, tys)) =
    ATerm (name, map fo_term_for_combtyp tys)

fun fo_literal_for_type_literal (TyLitVar (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))
  | fo_literal_for_type_literal (TyLitFree (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))

fun formula_for_fo_literal (pos, t) = AAtom t |> not pos ? mk_anot

fun fo_term_for_combterm full_types =
  let
    fun aux top_level u =
      let
        val (head, args) = strip_combterm_comb u
        val (x, ty_args) =
          case head of
            CombConst (name as (s, s'), _, ty_args) =>
            let val ty_args = if full_types then [] else ty_args in
              if s = "equal" then
                if top_level andalso length args = 2 then (name, [])
                else (("c_fequal", @{const_name fequal}), ty_args)
              else if top_level then
                case s of
                  "c_False" => (("$false", s'), [])
                | "c_True" => (("$true", s'), [])
                | _ => (name, ty_args)
              else
                (name, ty_args)
            end
          | CombVar (name, _) => (name, [])
          | CombApp _ => raise Fail "impossible \"CombApp\""
        val t = ATerm (x, map fo_term_for_combtyp ty_args @
                          map (aux false) args)
    in
      if full_types then wrap_type (fo_term_for_combtyp (combtyp_of u)) t else t
    end
  in aux true end

fun formula_for_combformula full_types =
  let
    fun aux (AQuant (q, xs, phi)) = AQuant (q, xs, aux phi)
      | aux (AConn (c, phis)) = AConn (c, map aux phis)
      | aux (AAtom tm) = AAtom (fo_term_for_combterm full_types tm)
  in aux end

fun formula_for_axiom full_types
                      ({combformula, ctypes_sorts, ...} : fol_formula) =
  mk_ahorn (map (formula_for_fo_literal o fo_literal_for_type_literal)
                (type_literals_for_types ctypes_sorts))
           (formula_for_combformula full_types combformula)

fun problem_line_for_fact prefix full_types (formula as {name, kind, ...}) =
  Fof (prefix ^ ascii_of name, kind, formula_for_axiom full_types formula)

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

fun problem_line_for_conjecture full_types
                                ({name, kind, combformula, ...} : fol_formula) =
  Fof (conjecture_prefix ^ name, kind,
       formula_for_combformula full_types combformula)

fun free_type_literals_for_conjecture ({ctypes_sorts, ...} : fol_formula) =
  map fo_literal_for_type_literal (type_literals_for_types ctypes_sorts)

fun problem_line_for_free_type lit =
  Fof (tfrees_name, Hypothesis, formula_for_fo_literal lit)
fun problem_lines_for_free_types conjectures =
  let
    val litss = map free_type_literals_for_conjecture conjectures
    val lits = fold (union (op =)) litss []
  in map problem_line_for_free_type lits end

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
  #> fold (consider_term (top_level andalso s = type_wrapper_name)) ts
fun consider_formula (AQuant (_, _, phi)) = consider_formula phi
  | consider_formula (AConn (_, phis)) = fold consider_formula phis
  | consider_formula (AAtom tm) = consider_term true tm

fun consider_problem_line (Fof (_, _, phi)) = consider_formula phi
fun consider_problem problem = fold (fold consider_problem_line o snd) problem

fun const_table_for_problem explicit_apply problem =
  if explicit_apply then NONE
  else SOME (Symtab.empty |> consider_problem problem)

fun min_arity_of thy full_types NONE s =
    (if s = "equal" orelse s = type_wrapper_name orelse
        String.isPrefix type_const_prefix s orelse
        String.isPrefix class_prefix s then
       16383 (* large number *)
     else if full_types then
       0
     else case strip_prefix_and_unascii const_prefix s of
       SOME s' => num_type_args thy (invert_const s')
     | NONE => 0)
  | min_arity_of _ _ (SOME the_const_tab) s =
    case Symtab.lookup the_const_tab s of
      SOME ({min_arity, ...} : const_info) => min_arity
    | NONE => 0

fun full_type_of (ATerm ((s, _), [ty, _])) =
    if s = type_wrapper_name then ty else raise Fail "expected type wrapper"
  | full_type_of _ = raise Fail "expected type wrapper"

fun list_hAPP_rev _ t1 [] = t1
  | list_hAPP_rev NONE t1 (t2 :: ts2) =
    ATerm (`I "hAPP", [list_hAPP_rev NONE t1 ts2, t2])
  | list_hAPP_rev (SOME ty) t1 (t2 :: ts2) =
    let val ty' = ATerm (`make_fixed_type_const @{type_name fun},
                         [full_type_of t2, ty]) in
      ATerm (`I "hAPP", [wrap_type ty' (list_hAPP_rev (SOME ty') t1 ts2), t2])
    end

fun repair_applications_in_term thy full_types const_tab =
  let
    fun aux opt_ty (ATerm (name as (s, _), ts)) =
      if s = type_wrapper_name then
        case ts of
          [t1, t2] => ATerm (name, [aux NONE t1, aux (SOME t1) t2])
        | _ => raise Fail "malformed type wrapper"
      else
        let
          val ts = map (aux NONE) ts
          val (ts1, ts2) = chop (min_arity_of thy full_types const_tab s) ts
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

fun repair_predicates_in_term const_tab (t as ATerm ((s, _), ts)) =
  if s = type_wrapper_name then
    case ts of
      [_, t' as ATerm ((s', _), _)] =>
      if is_predicate const_tab s' then t' else boolify t
    | _ => raise Fail "malformed type wrapper"
  else
    t |> not (is_predicate const_tab s) ? boolify

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

fun repair_formula thy explicit_forall full_types const_tab =
  let
    fun aux (AQuant (q, xs, phi)) = AQuant (q, xs, aux phi)
      | aux (AConn (c, phis)) = AConn (c, map aux phis)
      | aux (AAtom tm) =
        AAtom (tm |> repair_applications_in_term thy full_types const_tab
                  |> repair_predicates_in_term const_tab)
  in aux #> explicit_forall ? close_universally end

fun repair_problem_line thy explicit_forall full_types const_tab
                        (Fof (ident, kind, phi)) =
  Fof (ident, kind, repair_formula thy explicit_forall full_types const_tab phi)
fun repair_problem_with_const_table thy =
  map o apsnd o map ooo repair_problem_line thy

fun repair_problem thy explicit_forall full_types explicit_apply problem =
  repair_problem_with_const_table thy explicit_forall full_types
      (const_table_for_problem explicit_apply problem) problem

fun prepare_problem ctxt readable_names explicit_forall full_types
                    explicit_apply hyp_ts concl_t axioms =
  let
    val thy = ProofContext.theory_of ctxt
    val (axiom_names, (conjectures, axioms, helper_facts, class_rel_clauses,
                       arity_clauses)) =
      prepare_formulas ctxt full_types hyp_ts concl_t axioms
    val axiom_lines = map (problem_line_for_fact axiom_prefix full_types) axioms
    val helper_lines =
      map (problem_line_for_fact helper_prefix full_types) helper_facts
    val conjecture_lines =
      map (problem_line_for_conjecture full_types) conjectures
    val tfree_lines = problem_lines_for_free_types conjectures
    val class_rel_lines =
      map problem_line_for_class_rel_clause class_rel_clauses
    val arity_lines = map problem_line_for_arity_clause arity_clauses
    (* Reordering these might or might not confuse the proof reconstruction
       code or the SPASS Flotter hack. *)
    val problem =
      [("Relevant facts", axiom_lines),
       ("Class relationships", class_rel_lines),
       ("Arity declarations", arity_lines),
       ("Helper facts", helper_lines),
       ("Conjectures", conjecture_lines),
       ("Type variables", tfree_lines)]
      |> repair_problem thy explicit_forall full_types explicit_apply
    val (problem, pool) = nice_atp_problem readable_names problem
    val conjecture_offset =
      length axiom_lines + length class_rel_lines + length arity_lines
      + length helper_lines
  in
    (problem,
     case pool of SOME the_pool => snd the_pool | NONE => Symtab.empty,
     conjecture_offset, axiom_names)
  end

end;
