(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_atp_translate.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Sledgehammer.
*)

signature SLEDGEHAMMER_ATP_TRANSLATE =
sig
  type 'a fo_term = 'a ATP_Problem.fo_term
  type format = ATP_Problem.format
  type formula_kind = ATP_Problem.formula_kind
  type 'a problem = 'a ATP_Problem.problem
  type locality = Sledgehammer_Filter.locality

  datatype polymorphism = Polymorphic | Monomorphic | Mangled_Monomorphic
  datatype type_level =
    All_Types | Nonmonotonic_Types | Finite_Types | Const_Arg_Types | No_Types
  datatype type_heaviness = Heavy | Light

  datatype type_system =
    Simple_Types of type_level |
    Preds of polymorphism * type_level * type_heaviness |
    Tags of polymorphism * type_level * type_heaviness

  type translated_formula

  val readable_names : bool Config.T
  val fact_prefix : string
  val conjecture_prefix : string
  val helper_prefix : string
  val typed_helper_suffix : string
  val predicator_base : string
  val explicit_app_base : string
  val type_pred_base : string
  val tff_type_prefix : string
  val type_sys_from_string : string -> type_system
  val polymorphism_of_type_sys : type_system -> polymorphism
  val level_of_type_sys : type_system -> type_level
  val is_type_sys_virtually_sound : type_system -> bool
  val is_type_sys_fairly_sound : type_system -> bool
  val unmangled_const : string -> string * string fo_term list
  val translate_atp_fact :
    Proof.context -> bool -> (string * locality) * thm
    -> translated_formula option * ((string * locality) * thm)
  val prepare_atp_problem :
    Proof.context -> format -> formula_kind -> formula_kind -> type_system
    -> bool -> term list -> term
    -> (translated_formula option * ((string * 'a) * thm)) list
    -> string problem * string Symtab.table * int * int
       * (string * 'a) list vector * int list * int Symtab.table
  val atp_problem_weights : string problem -> (string * real) list
end;

structure Sledgehammer_ATP_Translate : SLEDGEHAMMER_ATP_TRANSLATE =
struct

open ATP_Problem
open Metis_Translate
open Sledgehammer_Util
open Sledgehammer_Filter

(* experimental *)
val generate_useful_info = false

fun useful_isabelle_info s =
  if generate_useful_info then
    SOME (ATerm ("[]", [ATerm ("isabelle_" ^ s, [])]))
  else
    NONE

val intro_info = useful_isabelle_info "intro"
val elim_info = useful_isabelle_info "elim"
val simp_info = useful_isabelle_info "simp"

(* Readable names are often much shorter, especially if types are mangled in
   names. Also, the logic for generating legal SNARK sort names is only
   implemented for readable names. Finally, readable names are, well, more
   readable. For these reason, they are enabled by default. *)
val readable_names =
  Attrib.setup_config_bool @{binding sledgehammer_atp_readable_names} (K true)

val type_decl_prefix = "type_"
val sym_decl_prefix = "sym_"
val fact_prefix = "fact_"
val conjecture_prefix = "conj_"
val helper_prefix = "help_"
val class_rel_clause_prefix = "crel_";
val arity_clause_prefix = "arity_"
val tfree_prefix = "tfree_"

val typed_helper_suffix = "_T"
val untyped_helper_suffix = "_U"

val predicator_base = "hBOOL"
val explicit_app_base = "hAPP"
val type_pred_base = "is"
val tff_type_prefix = "ty_"

fun make_tff_type s = tff_type_prefix ^ ascii_of s

(* Freshness almost guaranteed! *)
val sledgehammer_weak_prefix = "Sledgehammer:"

datatype polymorphism = Polymorphic | Monomorphic | Mangled_Monomorphic
datatype type_level =
  All_Types | Nonmonotonic_Types | Finite_Types | Const_Arg_Types | No_Types
datatype type_heaviness = Heavy | Light

datatype type_system =
  Simple_Types of type_level |
  Preds of polymorphism * type_level * type_heaviness |
  Tags of polymorphism * type_level * type_heaviness

fun try_unsuffixes ss s =
  fold (fn s' => fn NONE => try (unsuffix s') s | some => some) ss NONE

fun type_sys_from_string s =
  (case try (unprefix "poly_") s of
     SOME s => (SOME Polymorphic, s)
   | NONE =>
     case try (unprefix "mono_") s of
       SOME s => (SOME Monomorphic, s)
     | NONE =>
       case try (unprefix "mangled_") s of
         SOME s => (SOME Mangled_Monomorphic, s)
       | NONE => (NONE, s))
  ||> (fn s =>
          (* "_query" and "_bang" are for the ASCII-challenged Mirabelle. *)
          case try_unsuffixes ["?", "_query"] s of
            SOME s => (Nonmonotonic_Types, s)
          | NONE =>
            case try_unsuffixes ["!", "_bang"] s of
              SOME s => (Finite_Types, s)
            | NONE => (All_Types, s))
  ||> apsnd (fn s =>
                case try (unsuffix "_heavy") s of
                  SOME s => (Heavy, s)
                | NONE => (Light, s))
  |> (fn (poly, (level, (heaviness, core))) =>
         case (core, (poly, level, heaviness)) of
           ("simple", (NONE, _, Light)) => Simple_Types level
         | ("preds", (SOME poly, _, _)) => Preds (poly, level, heaviness)
         | ("tags", (SOME Polymorphic, All_Types, _)) =>
           Tags (Polymorphic, All_Types, heaviness)
         | ("tags", (SOME Polymorphic, _, _)) =>
           (* The actual light encoding is very unsound. *)
           Tags (Polymorphic, level, Heavy)
         | ("tags", (SOME poly, _, _)) => Tags (poly, level, heaviness)
         | ("args", (SOME poly, All_Types (* naja *), Light)) =>
           Preds (poly, Const_Arg_Types, Light)
         | ("erased", (NONE, All_Types (* naja *), Light)) =>
           Preds (Polymorphic, No_Types, Light)
         | _ => raise Same.SAME)
  handle Same.SAME => error ("Unknown type system: " ^ quote s ^ ".")

fun polymorphism_of_type_sys (Simple_Types _) = Mangled_Monomorphic
  | polymorphism_of_type_sys (Preds (poly, _, _)) = poly
  | polymorphism_of_type_sys (Tags (poly, _, _)) = poly

fun level_of_type_sys (Simple_Types level) = level
  | level_of_type_sys (Preds (_, level, _)) = level
  | level_of_type_sys (Tags (_, level, _)) = level

fun heaviness_of_type_sys (Simple_Types _) = Heavy
  | heaviness_of_type_sys (Preds (_, _, heaviness)) = heaviness
  | heaviness_of_type_sys (Tags (_, _, heaviness)) = heaviness

fun is_type_level_virtually_sound level =
  level = All_Types orelse level = Nonmonotonic_Types
val is_type_sys_virtually_sound =
  is_type_level_virtually_sound o level_of_type_sys

fun is_type_level_fairly_sound level =
  is_type_level_virtually_sound level orelse level = Finite_Types
val is_type_sys_fairly_sound = is_type_level_fairly_sound o level_of_type_sys

fun formula_map f (AQuant (q, xs, phi)) = AQuant (q, xs, formula_map f phi)
  | formula_map f (AConn (c, phis)) = AConn (c, map (formula_map f) phis)
  | formula_map f (AAtom tm) = AAtom (f tm)

fun aconn_fold pos f (ANot, [phi]) = f (Option.map not pos) phi
  | aconn_fold pos f (AImplies, [phi1, phi2]) =
    f (Option.map not pos) phi1 #> f pos phi2
  | aconn_fold pos f (AAnd, phis) = fold (f pos) phis
  | aconn_fold pos f (AOr, phis) = fold (f pos) phis
  | aconn_fold _ f (_, phis) = fold (f NONE) phis

fun aconn_map pos f (ANot, [phi]) = AConn (ANot, [f (Option.map not pos) phi])
  | aconn_map pos f (AImplies, [phi1, phi2]) =
    AConn (AImplies, [f (Option.map not pos) phi1, f pos phi2])
  | aconn_map pos f (AAnd, phis) = AConn (AAnd, map (f pos) phis)
  | aconn_map pos f (AOr, phis) = AConn (AOr, map (f pos) phis)
  | aconn_map _ f (c, phis) = AConn (c, map (f NONE) phis)

fun formula_fold pos f =
  let
    fun aux pos (AQuant (_, _, phi)) = aux pos phi
      | aux pos (AConn conn) = aconn_fold pos aux conn
      | aux pos (AAtom tm) = f pos tm
  in aux pos end

type translated_formula =
  {name: string,
   locality: locality,
   kind: formula_kind,
   combformula: (name, typ, combterm) formula,
   atomic_types: typ list}

fun update_combformula f ({name, locality, kind, combformula, atomic_types}
                          : translated_formula) =
  {name = name, locality = locality, kind = kind, combformula = f combformula,
   atomic_types = atomic_types} : translated_formula

fun fact_lift f ({combformula, ...} : translated_formula) = f combformula


(* The Booleans indicate whether all type arguments should be kept. *)
datatype type_arg_policy =
  Explicit_Type_Args of bool |
  Mangled_Type_Args of bool |
  No_Type_Args

fun should_drop_arg_type_args (Simple_Types _) =
    false (* since TFF doesn't support overloading *)
  | should_drop_arg_type_args type_sys =
    level_of_type_sys type_sys = All_Types andalso
    heaviness_of_type_sys type_sys = Heavy

fun general_type_arg_policy type_sys =
  if level_of_type_sys type_sys = No_Types then
    No_Type_Args
  else if polymorphism_of_type_sys type_sys = Mangled_Monomorphic then
    Mangled_Type_Args (should_drop_arg_type_args type_sys)
  else
    Explicit_Type_Args (should_drop_arg_type_args type_sys)

fun type_arg_policy _ @{const_name HOL.eq} = No_Type_Args
  | type_arg_policy type_sys _ = general_type_arg_policy type_sys

fun atp_type_literals_for_types type_sys kind Ts =
  if level_of_type_sys type_sys = No_Types then
    []
  else
    Ts |> type_literals_for_types
       |> filter (fn TyLitVar _ => kind <> Conjecture
                   | TyLitFree _ => kind = Conjecture)

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
  | combterm_vars (CombVar (name, T)) = insert (op =) (name, SOME T)
fun close_combformula_universally phi = close_universally combterm_vars phi

fun term_vars (ATerm (name as (s, _), tms)) =
  is_atp_variable s ? insert (op =) (name, NONE)
  #> fold term_vars tms
fun close_formula_universally phi = close_universally term_vars phi

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
    f name ^ "(" ^ space_implode "," (map (generic_mangled_type_name f) tys)
    ^ ")"
val mangled_type_name =
  fo_term_from_typ
  #> (fn ty => (make_tff_type (generic_mangled_type_name fst ty),
                generic_mangled_type_name snd ty))

fun generic_mangled_type_suffix f g Ts =
  fold_rev (curry (op ^) o g o prefix mangled_type_sep
            o generic_mangled_type_name f) Ts ""
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

fun introduce_proxies tm =
  let
    fun aux top_level (CombApp (tm1, tm2)) =
        CombApp (aux top_level tm1, aux false tm2)
      | aux top_level (CombConst (name as (s, s'), T, T_args)) =
        (case proxify_const s of
           SOME proxy_base =>
           if top_level then
             (case s of
                "c_False" => (tptp_false, s')
              | "c_True" => (tptp_true, s')
              | _ => name, [])
           else
             (proxy_base |>> prefix const_prefix, T_args)
          | NONE => (name, T_args))
        |> (fn (name, T_args) => CombConst (name, T, T_args))
      | aux _ tm = tm
  in aux true tm end

fun combformula_from_prop thy eq_as_iff =
  let
    fun do_term bs t atomic_types =
      combterm_from_term thy bs (Envir.eta_contract t)
      |>> (introduce_proxies #> AAtom)
      ||> union (op =) atomic_types
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

fun presimplify_term ctxt =
  Skip_Proof.make_thm (Proof_Context.theory_of ctxt)
  #> Meson.presimplify ctxt
  #> prop_of

fun concealed_bound_name j = sledgehammer_weak_prefix ^ string_of_int j
fun conceal_bounds Ts t =
  subst_bounds (map (Free o apfst concealed_bound_name)
                    (0 upto length Ts - 1 ~~ Ts), t)
fun reveal_bounds Ts =
  subst_atomic (map (fn (j, T) => (Free (concealed_bound_name j, T), Bound j))
                    (0 upto length Ts - 1 ~~ Ts))

fun extensionalize_term ctxt t =
  let val thy = Proof_Context.theory_of ctxt in
    t |> cterm_of thy |> Meson.extensionalize_conv ctxt
      |> prop_of |> Logic.dest_equals |> snd
  end

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
fun make_formula ctxt eq_as_iff presimp name loc kind t =
  let
    val thy = Proof_Context.theory_of ctxt
    val t = t |> Envir.beta_eta_contract
              |> transform_elim_term
              |> Object_Logic.atomize_term thy
    val need_trueprop = (fastype_of t = @{typ bool})
    val t = t |> need_trueprop ? HOLogic.mk_Trueprop
              |> Raw_Simplifier.rewrite_term thy
                     (Meson.unfold_set_const_simps ctxt) []
              |> extensionalize_term ctxt
              |> presimp ? presimplify_term ctxt
              |> perhaps (try (HOLogic.dest_Trueprop))
              |> introduce_combinators_in_term ctxt kind
              |> kind <> Axiom ? freeze_term
    val (combformula, atomic_types) = combformula_from_prop thy eq_as_iff t []
  in
    {name = name, locality = loc, kind = kind, combformula = combformula,
     atomic_types = atomic_types}
  end

fun make_fact ctxt keep_trivial eq_as_iff presimp ((name, loc), t) =
  case (keep_trivial, make_formula ctxt eq_as_iff presimp name loc Axiom t) of
    (false, {combformula = AAtom (CombConst (("c_True", _), _, _)), ...}) =>
    NONE
  | (_, formula) => SOME formula

fun make_conjecture ctxt prem_kind ts =
  let val last = length ts - 1 in
    map2 (fn j => fn t =>
             let
               val (kind, maybe_negate) =
                 if j = last then
                   (Conjecture, I)
                 else
                   (prem_kind,
                    if prem_kind = Conjecture then update_combformula mk_anot
                    else I)
              in
                make_formula ctxt true true (string_of_int j) General kind t
                |> maybe_negate
              end)
         (0 upto last) ts
  end

(** Finite and infinite type inference **)

fun deep_freeze_atyp (TVar (_, S)) = TFree ("v", S)
  | deep_freeze_atyp T = T
val deep_freeze_type = map_atyps deep_freeze_atyp

val type_instance = Sign.typ_instance o Proof_Context.theory_of

(* Finite types such as "unit", "bool", "bool * bool", and "bool => bool" are
   dangerous because their "exhaust" properties can easily lead to unsound ATP
   proofs. On the other hand, all HOL infinite types can be given the same
   models in first-order logic (via Löwenheim-Skolem). *)

fun should_encode_type ctxt (nonmono_Ts as _ :: _) _ T =
    exists (curry (type_instance ctxt) (deep_freeze_type T)) nonmono_Ts
  | should_encode_type _ _ All_Types _ = true
  | should_encode_type ctxt _ Finite_Types T = is_type_surely_finite ctxt T
  | should_encode_type _ _ _ _ = false

fun should_predicate_on_type ctxt nonmono_Ts (Preds (_, level, heaviness))
                             should_predicate_on_var T =
    (heaviness = Heavy orelse should_predicate_on_var ()) andalso
    should_encode_type ctxt nonmono_Ts level T
  | should_predicate_on_type _ _ _ _ _ = false

fun is_var_or_bound_var (CombConst ((s, _), _, _)) =
    String.isPrefix bound_var_prefix s
  | is_var_or_bound_var (CombVar _) = true
  | is_var_or_bound_var _ = false

datatype tag_site = Top_Level | Eq_Arg | Elsewhere

fun should_tag_with_type _ _ _ Top_Level _ _ = false
  | should_tag_with_type ctxt nonmono_Ts (Tags (_, level, heaviness)) site u T =
    (case heaviness of
       Heavy => should_encode_type ctxt nonmono_Ts level T
     | Light =>
       case (site, is_var_or_bound_var u) of
         (Eq_Arg, true) => should_encode_type ctxt nonmono_Ts level T
       | _ => false)
  | should_tag_with_type _ _ _ _ _ _ = false

val homo_infinite_T = @{typ ind} (* any infinite type *)

fun homogenized_type ctxt nonmono_Ts level T =
  if should_encode_type ctxt nonmono_Ts level T then T else homo_infinite_T

(** "hBOOL" and "hAPP" **)

type sym_info =
  {pred_sym : bool, min_ary : int, max_ary : int, typ : typ option}

fun add_combterm_syms_to_table explicit_apply =
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
fun add_fact_syms_to_table explicit_apply =
  fact_lift (formula_fold NONE (K (add_combterm_syms_to_table explicit_apply)))

val default_sym_table_entries : (string * sym_info) list =
  [("equal", {pred_sym = true, min_ary = 2, max_ary = 2, typ = NONE}),
   (make_fixed_const predicator_base,
    {pred_sym = true, min_ary = 1, max_ary = 1, typ = NONE})] @
  ([tptp_false, tptp_true]
   |> map (rpair {pred_sym = true, min_ary = 0, max_ary = 0, typ = NONE}))

fun sym_table_for_facts explicit_apply facts =
  Symtab.empty |> fold Symtab.default default_sym_table_entries
               |> fold (add_fact_syms_to_table explicit_apply) facts

fun min_arity_of sym_tab s =
  case Symtab.lookup sym_tab s of
    SOME ({min_ary, ...} : sym_info) => min_ary
  | NONE =>
    case strip_prefix_and_unascii const_prefix s of
      SOME s =>
      let val s = s |> unmangled_const_name |> invert_const in
        if s = predicator_base then 1
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
    SOME ({pred_sym, min_ary, max_ary, ...} : sym_info) =>
    pred_sym andalso min_ary = max_ary
  | NONE => false

val predicator_combconst =
  CombConst (`make_fixed_const predicator_base, @{typ "bool => bool"}, [])
fun predicator tm = CombApp (predicator_combconst, tm)

fun introduce_predicators_in_combterm sym_tab tm =
  case strip_combterm_comb tm of
    (CombConst ((s, _), _, _), _) =>
    if is_pred_sym sym_tab s then tm else predicator tm
  | _ => predicator tm

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

fun introduce_explicit_apps_in_combterm sym_tab =
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

fun chop_fun 0 T = ([], T)
  | chop_fun n (Type (@{type_name fun}, [dom_T, ran_T])) =
    chop_fun (n - 1) ran_T |>> cons dom_T
  | chop_fun _ _ = raise Fail "unexpected non-function"

fun filter_type_args _ _ _ [] = []
  | filter_type_args thy s arity T_args =
    let
      (* will throw "TYPE" for pseudo-constants *)
      val U = if s = explicit_app_base then
                @{typ "('a => 'b) => 'a => 'b"} |> Logic.varifyT_global
              else
                s |> Sign.the_const_type thy
    in
      case Term.add_tvarsT (U |> chop_fun arity |> snd) [] of
        [] => []
      | res_U_vars =>
        let val U_args = (s, U) |> Sign.const_typargs thy in
          U_args ~~ T_args
          |> map_filter (fn (U, T) =>
                            if member (op =) res_U_vars (dest_TVar U) then
                              SOME T
                            else
                              NONE)
        end
    end
    handle TYPE _ => T_args

fun enforce_type_arg_policy_in_combterm ctxt nonmono_Ts type_sys =
  let
    val thy = Proof_Context.theory_of ctxt
    fun aux arity (CombApp (tm1, tm2)) =
        CombApp (aux (arity + 1) tm1, aux 0 tm2)
      | aux arity (CombConst (name as (s, _), T, T_args)) =
        let
          val level = level_of_type_sys type_sys
          val (T, T_args) =
            (* Aggressively merge most "hAPPs" if the type system is unsound
               anyway, by distinguishing overloads only on the homogenized
               result type. Don't do it for lightweight type systems, though,
               since it leads to too many unsound proofs. *)
            if s = const_prefix ^ explicit_app_base andalso
               length T_args = 2 andalso
               not (is_type_sys_virtually_sound type_sys) andalso
               heaviness_of_type_sys type_sys = Heavy then
              T_args |> map (homogenized_type ctxt nonmono_Ts level)
                     |> (fn Ts => let val T = hd Ts --> nth Ts 1 in
                                    (T --> T, tl Ts)
                                  end)
            else
              (T, T_args)
        in
          (case strip_prefix_and_unascii const_prefix s of
             NONE => (name, T_args)
           | SOME s'' =>
             let
               val s'' = invert_const s''
               fun filtered_T_args false = T_args
                 | filtered_T_args true = filter_type_args thy s'' arity T_args
             in
               case type_arg_policy type_sys s'' of
                 Explicit_Type_Args drop_args =>
                 (name, filtered_T_args drop_args)
               | Mangled_Type_Args drop_args =>
                 (mangled_const_name (filtered_T_args drop_args) name, [])
               | No_Type_Args => (name, [])
             end)
          |> (fn (name, T_args) => CombConst (name, T, T_args))
        end
      | aux _ tm = tm
  in aux 0 end

fun repair_combterm ctxt nonmono_Ts type_sys sym_tab =
  introduce_explicit_apps_in_combterm sym_tab
  #> introduce_predicators_in_combterm sym_tab
  #> enforce_type_arg_policy_in_combterm ctxt nonmono_Ts type_sys
fun repair_fact ctxt nonmono_Ts type_sys sym_tab =
  update_combformula (formula_map
      (repair_combterm ctxt nonmono_Ts type_sys sym_tab))

(** Helper facts **)

fun ti_ti_helper_fact () =
  let
    fun var s = ATerm (`I s, [])
    fun tag tm = ATerm (`make_fixed_const type_tag_name, [var "X", tm])
  in
    Formula (helper_prefix ^ "ti_ti", Axiom,
             AAtom (ATerm (`I "equal", [tag (tag (var "Y")), tag (var "Y")]))
             |> close_formula_universally, simp_info, NONE)
  end

fun helper_facts_for_sym ctxt type_sys (s, {typ, ...} : sym_info) =
  case strip_prefix_and_unascii const_prefix s of
    SOME mangled_s =>
    let
      val thy = Proof_Context.theory_of ctxt
      val unmangled_s = mangled_s |> unmangled_const_name
      fun dub_and_inst c needs_fairly_sound (th, j) =
        ((c ^ "_" ^ string_of_int j ^
          (if needs_fairly_sound then typed_helper_suffix
           else untyped_helper_suffix),
          General),
         let val t = th |> prop_of in
           t |> ((case general_type_arg_policy type_sys of
                    Mangled_Type_Args _ => true
                  | _ => false) andalso
                 not (null (Term.hidden_polymorphism t)))
                ? (case typ of
                     SOME T => specialize_type thy (invert_const unmangled_s, T)
                   | NONE => I)
         end)
      fun make_facts eq_as_iff =
        map_filter (make_fact ctxt false eq_as_iff false)
      val fairly_sound = is_type_sys_fairly_sound type_sys
    in
      metis_helpers
      |> maps (fn (metis_s, (needs_fairly_sound, ths)) =>
                  if metis_s <> unmangled_s orelse
                     (needs_fairly_sound andalso not fairly_sound) then
                    []
                  else
                    ths ~~ (1 upto length ths)
                    |> map (dub_and_inst mangled_s needs_fairly_sound)
                    |> make_facts (not needs_fairly_sound))
    end
  | NONE => []
fun helper_facts_for_sym_table ctxt type_sys sym_tab =
  Symtab.fold_rev (append o helper_facts_for_sym ctxt type_sys) sym_tab []

fun translate_atp_fact ctxt keep_trivial =
  `(make_fact ctxt keep_trivial true true o apsnd prop_of)

fun translate_formulas ctxt prem_kind type_sys hyp_ts concl_t rich_facts =
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
    val conjs = make_conjecture ctxt prem_kind (hyp_ts @ [concl_t])
    val (supers', arity_clauses) =
      if level_of_type_sys type_sys = No_Types then ([], [])
      else make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in
    (fact_names |> map single, (conjs, facts, class_rel_clauses, arity_clauses))
  end

fun fo_literal_from_type_literal (TyLitVar (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))
  | fo_literal_from_type_literal (TyLitFree (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))

fun formula_from_fo_literal (pos, t) = AAtom t |> not pos ? mk_anot

fun type_pred_combterm ctxt nonmono_Ts type_sys T tm =
  CombApp (CombConst (`make_fixed_const type_pred_base, T --> @{typ bool}, [T])
           |> enforce_type_arg_policy_in_combterm ctxt nonmono_Ts type_sys,
           tm)

fun var_occurs_positively_naked_in_term _ (SOME false) _ accum = accum
  | var_occurs_positively_naked_in_term name _ (ATerm ((s, _), tms)) accum =
    accum orelse (s = "equal" andalso member (op =) tms (ATerm (name, [])))
fun is_var_nonmonotonic_in_formula _ _ (SOME false) _ = false
  | is_var_nonmonotonic_in_formula pos phi _ name =
    formula_fold pos (var_occurs_positively_naked_in_term name) phi false

fun tag_with_type ctxt nonmono_Ts type_sys T tm =
  CombConst (`make_fixed_const type_tag_name, T --> T, [T])
  |> enforce_type_arg_policy_in_combterm ctxt nonmono_Ts type_sys
  |> term_from_combterm ctxt nonmono_Ts type_sys Top_Level
  |> (fn ATerm (s, tms) => ATerm (s, tms @ [tm]))
and term_from_combterm ctxt nonmono_Ts type_sys site u =
  let
    val (head, args) = strip_combterm_comb u
    val (x as (s, _), T_args) =
      case head of
        CombConst (name, _, T_args) => (name, T_args)
      | CombVar (name, _) => (name, [])
      | CombApp _ => raise Fail "impossible \"CombApp\""
    val arg_site = if site = Top_Level andalso s = "equal" then Eq_Arg
                   else Elsewhere
    val t = ATerm (x, map fo_term_from_typ T_args @
                      map (term_from_combterm ctxt nonmono_Ts type_sys arg_site)
                          args)
    val T = combtyp_of u
  in
    t |> (if should_tag_with_type ctxt nonmono_Ts type_sys site u T then
            tag_with_type ctxt nonmono_Ts type_sys T
          else
            I)
  end
and formula_from_combformula ctxt nonmono_Ts type_sys should_predicate_on_var =
  let
    val do_term = term_from_combterm ctxt nonmono_Ts type_sys Top_Level
    val do_bound_type =
      case type_sys of
        Simple_Types level =>
        SOME o mangled_type_name o homogenized_type ctxt nonmono_Ts level
      | _ => K NONE
    fun do_out_of_bound_type pos phi universal (name, T) =
      if should_predicate_on_type ctxt nonmono_Ts type_sys
             (fn () => should_predicate_on_var pos phi universal name) T then
        CombVar (name, T)
        |> type_pred_combterm ctxt nonmono_Ts type_sys T
        |> do_term |> AAtom |> SOME
      else
        NONE
    fun do_formula pos (AQuant (q, xs, phi)) =
        let
          val phi = phi |> do_formula pos
          val universal = Option.map (q = AExists ? not) pos
        in
          AQuant (q, xs |> map (apsnd (fn NONE => NONE
                                        | SOME T => do_bound_type T)),
                  (if q = AForall then mk_ahorn else fold_rev (mk_aconn AAnd))
                      (map_filter
                           (fn (_, NONE) => NONE
                             | (s, SOME T) =>
                               do_out_of_bound_type pos phi universal (s, T))
                           xs)
                      phi)
        end
      | do_formula pos (AConn conn) = aconn_map pos do_formula conn
      | do_formula _ (AAtom tm) = AAtom (do_term tm)
  in do_formula o SOME end

fun bound_atomic_types type_sys Ts =
  mk_ahorn (map (formula_from_fo_literal o fo_literal_from_type_literal)
                (atp_type_literals_for_types type_sys Axiom Ts))

fun formula_for_fact ctxt nonmono_Ts type_sys
                     ({combformula, atomic_types, ...} : translated_formula) =
  combformula
  |> close_combformula_universally
  |> formula_from_combformula ctxt nonmono_Ts type_sys
                              is_var_nonmonotonic_in_formula true
  |> bound_atomic_types type_sys atomic_types
  |> close_formula_universally

(* Each fact is given a unique fact number to avoid name clashes (e.g., because
   of monomorphization). The TPTP explicitly forbids name clashes, and some of
   the remote provers might care. *)
fun formula_line_for_fact ctxt prefix nonmono_Ts type_sys
                          (j, formula as {name, locality, kind, ...}) =
  Formula (prefix ^ (if polymorphism_of_type_sys type_sys = Polymorphic then ""
                     else string_of_int j ^ "_") ^
           ascii_of name,
           kind, formula_for_fact ctxt nonmono_Ts type_sys formula, NONE,
           case locality of
             Intro => intro_info
           | Elim => elim_info
           | Simp => simp_info
           | _ => NONE)

fun formula_line_for_class_rel_clause
        (ClassRelClause {name, subclass, superclass, ...}) =
  let val ty_arg = ATerm (`I "T", []) in
    Formula (class_rel_clause_prefix ^ ascii_of name, Axiom,
             AConn (AImplies, [AAtom (ATerm (subclass, [ty_arg])),
                               AAtom (ATerm (superclass, [ty_arg]))])
             |> close_formula_universally, intro_info, NONE)
  end

fun fo_literal_from_arity_literal (TConsLit (c, t, args)) =
    (true, ATerm (c, [ATerm (t, map (fn arg => ATerm (arg, [])) args)]))
  | fo_literal_from_arity_literal (TVarLit (c, sort)) =
    (false, ATerm (c, [ATerm (sort, [])]))

fun formula_line_for_arity_clause
        (ArityClause {name, prem_lits, concl_lits, ...}) =
  Formula (arity_clause_prefix ^ ascii_of name, Axiom,
           mk_ahorn (map (formula_from_fo_literal o apfst not
                          o fo_literal_from_arity_literal) prem_lits)
                    (formula_from_fo_literal
                         (fo_literal_from_arity_literal concl_lits))
           |> close_formula_universally, intro_info, NONE)

fun formula_line_for_conjecture ctxt nonmono_Ts type_sys
        ({name, kind, combformula, ...} : translated_formula) =
  Formula (conjecture_prefix ^ name, kind,
           formula_from_combformula ctxt nonmono_Ts type_sys
               is_var_nonmonotonic_in_formula false
               (close_combformula_universally combformula)
           |> close_formula_universally, NONE, NONE)

fun free_type_literals type_sys ({atomic_types, ...} : translated_formula) =
  atomic_types |> atp_type_literals_for_types type_sys Conjecture
               |> map fo_literal_from_type_literal

fun formula_line_for_free_type j lit =
  Formula (tfree_prefix ^ string_of_int j, Hypothesis,
           formula_from_fo_literal lit, NONE, NONE)
fun formula_lines_for_free_types type_sys facts =
  let
    val litss = map (free_type_literals type_sys) facts
    val lits = fold (union (op =)) litss []
  in map2 formula_line_for_free_type (0 upto length lits - 1) lits end

(** Symbol declarations **)

fun insert_type ctxt get_T x xs =
  let val T = get_T x in
    if exists (curry (type_instance ctxt) T o get_T) xs then xs
    else x :: filter_out (curry (type_instance ctxt o swap) T o get_T) xs
  end

fun should_declare_sym type_sys pred_sym s =
  not (String.isPrefix bound_var_prefix s) andalso s <> "equal" andalso
  not (String.isPrefix tptp_special_prefix s) andalso
  (case type_sys of
     Simple_Types _ => true
   | Tags (_, _, Light) => true
   | _ => not pred_sym)

fun sym_decl_table_for_facts ctxt type_sys repaired_sym_tab (conjs, facts) =
  let
    fun add_combterm in_conj tm =
      let val (head, args) = strip_combterm_comb tm in
        (case head of
           CombConst ((s, s'), T, T_args) =>
           let val pred_sym = is_pred_sym repaired_sym_tab s in
             if should_declare_sym type_sys pred_sym s then
               Symtab.map_default (s, [])
                   (insert_type ctxt #3 (s', T_args, T, pred_sym, length args,
                                         in_conj))
             else
               I
           end
         | _ => I)
        #> fold (add_combterm in_conj) args
      end
    fun add_fact in_conj =
      fact_lift (formula_fold NONE (K (add_combterm in_conj)))
  in
    Symtab.empty
    |> is_type_sys_fairly_sound type_sys
       ? (fold (add_fact true) conjs #> fold (add_fact false) facts)
  end

(* These types witness that the type classes they belong to allow infinite
   models and hence that any types with these type classes is monotonic. *)
val known_infinite_types = [@{typ nat}, @{typ int}, @{typ "nat => bool"}]

(* This inference is described in section 2.3 of Claessen et al.'s "Sorting it
   out with monotonicity" paper presented at CADE 2011. *)
fun add_combterm_nonmonotonic_types _ _ (SOME false) _ = I
  | add_combterm_nonmonotonic_types ctxt level _
        (CombApp (CombApp (CombConst (("equal", _), Type (_, [T, _]), _), tm1),
                  tm2)) =
    (exists is_var_or_bound_var [tm1, tm2] andalso
     (case level of
        Nonmonotonic_Types =>
        not (is_type_surely_infinite ctxt known_infinite_types T)
      | Finite_Types => is_type_surely_finite ctxt T
      | _ => true)) ? insert_type ctxt I (deep_freeze_type T)
  | add_combterm_nonmonotonic_types _ _ _ _ = I
fun add_fact_nonmonotonic_types ctxt level ({kind, combformula, ...}
                                            : translated_formula) =
  formula_fold (SOME (kind <> Conjecture))
               (add_combterm_nonmonotonic_types ctxt level) combformula
fun nonmonotonic_types_for_facts ctxt type_sys facts =
  let val level = level_of_type_sys type_sys in
    if level = Nonmonotonic_Types orelse level = Finite_Types then
      [] |> fold (add_fact_nonmonotonic_types ctxt level) facts
         (* We must add "bool" in case the helper "True_or_False" is added
            later. In addition, several places in the code rely on the list of
            nonmonotonic types not being empty. *)
         |> insert_type ctxt I @{typ bool}
    else
      []
  end

fun decl_line_for_sym ctxt nonmono_Ts level s (s', _, T, pred_sym, ary, _) =
  let
    val translate_type =
      mangled_type_name o homogenized_type ctxt nonmono_Ts level
    val (arg_tys, res_ty) =
      T |> chop_fun ary |>> map translate_type ||> translate_type
  in
    Decl (sym_decl_prefix ^ s, (s, s'), arg_tys,
          if pred_sym then `I tptp_tff_bool_type else res_ty)
  end

fun is_polymorphic_type T = fold_atyps (fn TVar _ => K true | _ => I) T false

fun formula_line_for_pred_sym_decl ctxt conj_sym_kind nonmono_Ts type_sys n s j
                                   (s', T_args, T, _, ary, in_conj) =
  let
    val (kind, maybe_negate) =
      if in_conj then (conj_sym_kind, conj_sym_kind = Conjecture ? mk_anot)
      else (Axiom, I)
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names =
      1 upto length arg_Ts |> map (`I o make_bound_var o string_of_int)
    val bounds =
      bound_names ~~ arg_Ts |> map (fn (name, T) => CombConst (name, T, []))
    val bound_Ts =
      arg_Ts |> map (fn T => if n > 1 orelse is_polymorphic_type T then SOME T
                             else NONE)
  in
    Formula (sym_decl_prefix ^ s ^
             (if n > 1 then "_" ^ string_of_int j else ""), kind,
             CombConst ((s, s'), T, T_args)
             |> fold (curry (CombApp o swap)) bounds
             |> type_pred_combterm ctxt nonmono_Ts type_sys res_T
             |> AAtom
             |> mk_aquant AForall (bound_names ~~ bound_Ts)
             |> formula_from_combformula ctxt nonmono_Ts type_sys
                                         (K (K (K (K true)))) true
             |> n > 1 ? bound_atomic_types type_sys (atyps_of T)
             |> close_formula_universally
             |> maybe_negate,
             intro_info, NONE)
  end

fun formula_lines_for_tag_sym_decl ctxt conj_sym_kind nonmono_Ts type_sys n s
                                  (j, (s', T_args, T, pred_sym, ary, in_conj)) =
  let
    val ident_base =
      sym_decl_prefix ^ s ^ (if n > 1 then "_" ^ string_of_int j else "")
    val (kind, maybe_negate) =
      if in_conj then (conj_sym_kind, conj_sym_kind = Conjecture ? mk_anot)
      else (Axiom, I)
    val (arg_Ts, res_T) = chop_fun ary T
    val bound_names =
      1 upto length arg_Ts |> map (`I o make_bound_var o string_of_int)
    val bounds = bound_names |> map (fn name => ATerm (name, []))
    fun const args = ATerm ((s, s'), map fo_term_from_typ T_args @ args)
    val atomic_Ts = atyps_of T
    fun eq tms =
      (if pred_sym then AConn (AIff, map AAtom tms)
       else AAtom (ATerm (`I "equal", tms)))
      |> bound_atomic_types type_sys atomic_Ts
      |> close_formula_universally
      |> maybe_negate
    val should_encode = should_encode_type ctxt nonmono_Ts All_Types
    val tag_with = tag_with_type ctxt nonmono_Ts type_sys
    val add_formula_for_res =
      if should_encode res_T then
        cons (Formula (ident_base ^ "_res", kind,
                       eq [tag_with res_T (const bounds), const bounds],
                       simp_info, NONE))
      else
        I
    fun add_formula_for_arg k =
      let val arg_T = nth arg_Ts k in
        if should_encode arg_T then
          case chop k bounds of
            (bounds1, bound :: bounds2) =>
            cons (Formula (ident_base ^ "_arg" ^ string_of_int (k + 1), kind,
                           eq [const (bounds1 @ tag_with arg_T bound ::
                                      bounds2),
                               const bounds],
                           simp_info, NONE))
          | _ => raise Fail "expected nonempty tail"
        else
          I
      end
  in
    [] |> not pred_sym ? add_formula_for_res
       |> fold add_formula_for_arg (ary - 1 downto 0)
  end

fun result_type_of_decl (_, _, T, _, ary, _) = chop_fun ary T |> snd

fun problem_lines_for_sym_decls ctxt conj_sym_kind nonmono_Ts type_sys
                                (s, decls) =
  case type_sys of
    Simple_Types level => map (decl_line_for_sym ctxt nonmono_Ts level s) decls
  | Preds _ =>
    let
      val decls =
        case decls of
          decl :: (decls' as _ :: _) =>
          let val T = result_type_of_decl decl in
            if forall (curry (type_instance ctxt o swap) T
                       o result_type_of_decl) decls' then
              [decl]
            else
              decls
          end
        | _ => decls
      val n = length decls
      val decls =
        decls
        |> filter (should_predicate_on_type ctxt nonmono_Ts type_sys (K true)
                   o result_type_of_decl)
    in
      (0 upto length decls - 1, decls)
      |-> map2 (formula_line_for_pred_sym_decl ctxt conj_sym_kind nonmono_Ts
                                               type_sys n s)
    end
  | Tags (_, _, heaviness) =>
    (case heaviness of
       Heavy => []
     | Light =>
       let val n = length decls in
         (0 upto n - 1 ~~ decls)
         |> maps (formula_lines_for_tag_sym_decl ctxt conj_sym_kind nonmono_Ts
                                                 type_sys n s)
       end)

fun problem_lines_for_sym_decl_table ctxt conj_sym_kind nonmono_Ts type_sys
                                     sym_decl_tab =
  Symtab.fold_rev (append o problem_lines_for_sym_decls ctxt conj_sym_kind
                                                        nonmono_Ts type_sys)
                  sym_decl_tab []

fun add_tff_types_in_formula (AQuant (_, xs, phi)) =
    union (op =) (map_filter snd xs) #> add_tff_types_in_formula phi
  | add_tff_types_in_formula (AConn (_, phis)) =
    fold add_tff_types_in_formula phis
  | add_tff_types_in_formula (AAtom _) = I

fun add_tff_types_in_problem_line (Decl (_, _, arg_Ts, res_T)) =
    union (op =) (res_T :: arg_Ts)
  | add_tff_types_in_problem_line (Formula (_, _, phi, _, _)) =
    add_tff_types_in_formula phi

fun tff_types_in_problem problem =
  fold (fold add_tff_types_in_problem_line o snd) problem []

fun decl_line_for_tff_type (s, s') =
  Decl (type_decl_prefix ^ ascii_of s, (s, s'), [], `I tptp_tff_type_of_types)

fun should_add_ti_ti_helper (Tags (Polymorphic, level, Heavy)) =
    level = Nonmonotonic_Types orelse level = Finite_Types
  | should_add_ti_ti_helper _ = false

fun offset_of_heading_in_problem _ [] j = j
  | offset_of_heading_in_problem needle ((heading, lines) :: problem) j =
    if heading = needle then j
    else offset_of_heading_in_problem needle problem (j + length lines)

val type_declsN = "Types"
val sym_declsN = "Symbol types"
val factsN = "Relevant facts"
val class_relsN = "Class relationships"
val aritiesN = "Arities"
val helpersN = "Helper facts"
val conjsN = "Conjectures"
val free_typesN = "Type variables"

fun prepare_atp_problem ctxt format conj_sym_kind prem_kind type_sys
                        explicit_apply hyp_ts concl_t facts =
  let
    val (fact_names, (conjs, facts, class_rel_clauses, arity_clauses)) =
      translate_formulas ctxt prem_kind type_sys hyp_ts concl_t facts
    val sym_tab = conjs @ facts |> sym_table_for_facts explicit_apply
    val nonmono_Ts = conjs @ facts |> nonmonotonic_types_for_facts ctxt type_sys
    val repair = repair_fact ctxt nonmono_Ts type_sys sym_tab
    val (conjs, facts) = (conjs, facts) |> pairself (map repair)
    val repaired_sym_tab = conjs @ facts |> sym_table_for_facts false
    val helpers =
      repaired_sym_tab |> helper_facts_for_sym_table ctxt type_sys |> map repair
    val lavish_nonmono_Ts =
      if null nonmono_Ts orelse
         polymorphism_of_type_sys type_sys <> Polymorphic then
        nonmono_Ts
      else
        [TVar (("'a", 0), HOLogic.typeS)]
    val sym_decl_lines =
      (conjs, helpers @ facts)
      |> sym_decl_table_for_facts ctxt type_sys repaired_sym_tab
      |> problem_lines_for_sym_decl_table ctxt conj_sym_kind lavish_nonmono_Ts
                                          type_sys
    val helper_lines =
      map (formula_line_for_fact ctxt helper_prefix lavish_nonmono_Ts type_sys)
          (0 upto length helpers - 1 ~~ helpers)
      |> (if should_add_ti_ti_helper type_sys then
            cons (ti_ti_helper_fact ())
          else
            I)
    (* Reordering these might confuse the proof reconstruction code or the SPASS
       Flotter hack. *)
    val problem =
      [(sym_declsN, sym_decl_lines),
       (factsN, map (formula_line_for_fact ctxt fact_prefix nonmono_Ts type_sys)
                    (0 upto length facts - 1 ~~ facts)),
       (class_relsN, map formula_line_for_class_rel_clause class_rel_clauses),
       (aritiesN, map formula_line_for_arity_clause arity_clauses),
       (helpersN, helper_lines),
       (conjsN, map (formula_line_for_conjecture ctxt nonmono_Ts type_sys)
                    conjs),
       (free_typesN, formula_lines_for_free_types type_sys (facts @ conjs))]
    val problem =
      problem
      |> (case type_sys of
            Simple_Types _ =>
            cons (type_declsN,
                  map decl_line_for_tff_type (tff_types_in_problem problem))
          | _ => I)
    val problem =
      problem |> (if format = CNF_UEQ then filter_cnf_ueq_problem else I)
    val (problem, pool) =
      problem |> nice_atp_problem (Config.get ctxt readable_names)
    val helpers_offset = offset_of_heading_in_problem helpersN problem 0
    val typed_helpers =
      map_filter (fn (j, {name, ...}) =>
                     if String.isSuffix typed_helper_suffix name then SOME j
                     else NONE)
                 ((helpers_offset + 1 upto helpers_offset + length helpers)
                  ~~ helpers)
    fun add_sym_arity (s, {min_ary, ...} : sym_info) =
      if min_ary > 0 then
        case strip_prefix_and_unascii const_prefix s of
          SOME s => Symtab.insert (op =) (s, min_ary)
        | NONE => I
      else
        I
  in
    (problem,
     case pool of SOME the_pool => snd the_pool | NONE => Symtab.empty,
     offset_of_heading_in_problem conjsN problem 0,
     offset_of_heading_in_problem factsN problem 0,
     fact_names |> Vector.fromList,
     typed_helpers,
     Symtab.empty |> Symtab.fold add_sym_arity sym_tab)
  end

(* FUDGE *)
val conj_weight = 0.0
val hyp_weight = 0.1
val fact_min_weight = 0.2
val fact_max_weight = 1.0
val type_info_default_weight = 0.8

fun add_term_weights weight (ATerm (s, tms)) =
  (not (is_atp_variable s) andalso s <> "equal" andalso
   not (String.isPrefix tptp_special_prefix s)) ? Symtab.default (s, weight)
  #> fold (add_term_weights weight) tms
fun add_problem_line_weights weight (Formula (_, _, phi, _, _)) =
    formula_fold NONE (K (add_term_weights weight)) phi
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
  let val get = these o AList.lookup (op =) problem in
    Symtab.empty
    |> add_conjectures_weights (get free_typesN @ get conjsN)
    |> add_facts_weights (get factsN)
    |> fold (fold (add_problem_line_weights type_info_default_weight) o get)
            [sym_declsN, class_relsN, aritiesN]
    |> Symtab.dest
    |> sort (prod_ord Real.compare string_ord o pairself swap)
  end

end;
