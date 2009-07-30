(*  Title:      Pure/Isar/overloading.ML
    Author:     Florian Haftmann, TU Muenchen

Overloaded definitions without any discipline.
*)

signature OVERLOADING =
sig
  val init: (string * (string * typ) * bool) list -> theory -> local_theory
  val conclude: local_theory -> local_theory
  val declare: string * typ -> theory -> term * theory
  val confirm: binding -> local_theory -> local_theory
  val define: bool -> binding -> string * term -> theory -> thm * theory
  val operation: Proof.context -> binding -> (string * bool) option
  val pretty: Proof.context -> Pretty.T
  
  type improvable_syntax
  val add_improvable_syntax: Proof.context -> Proof.context
  val map_improvable_syntax: (improvable_syntax -> improvable_syntax)
    -> Proof.context -> Proof.context
  val set_primary_constraints: Proof.context -> Proof.context
end;

structure Overloading: OVERLOADING =
struct

(** generic check/uncheck combinators for improvable constants **)

type improvable_syntax = ((((string * typ) list * (string * typ) list) *
  ((((string * typ -> (typ * typ) option) * (string * typ -> (typ * term) option)) * bool) *
    (term * term) list)) * bool);

structure ImprovableSyntax = ProofDataFun(
  type T = {
    primary_constraints: (string * typ) list,
    secondary_constraints: (string * typ) list,
    improve: string * typ -> (typ * typ) option,
    subst: string * typ -> (typ * term) option,
    consider_abbrevs: bool,
    unchecks: (term * term) list,
    passed: bool
  };
  fun init _ = {
    primary_constraints = [],
    secondary_constraints = [],
    improve = K NONE,
    subst = K NONE,
    consider_abbrevs = false,
    unchecks = [],
    passed = true
  };
);

fun map_improvable_syntax f = ImprovableSyntax.map (fn { primary_constraints,
  secondary_constraints, improve, subst, consider_abbrevs, unchecks, passed } => let
    val (((primary_constraints', secondary_constraints'),
      (((improve', subst'), consider_abbrevs'), unchecks')), passed')
        = f (((primary_constraints, secondary_constraints),
            (((improve, subst), consider_abbrevs), unchecks)), passed)
  in { primary_constraints = primary_constraints', secondary_constraints = secondary_constraints',
    improve = improve', subst = subst', consider_abbrevs = consider_abbrevs',
    unchecks = unchecks', passed = passed'
  } end);

val mark_passed = (map_improvable_syntax o apsnd) (K true);

fun improve_term_check ts ctxt =
  let
    val { primary_constraints, secondary_constraints, improve, subst,
      consider_abbrevs, passed, ... } = ImprovableSyntax.get ctxt;
    val tsig = (Sign.tsig_of o ProofContext.theory_of) ctxt;
    val is_abbrev = consider_abbrevs andalso ProofContext.abbrev_mode ctxt;
    val passed_or_abbrev = passed orelse is_abbrev;
    fun accumulate_improvements (Const (c, ty)) = (case improve (c, ty)
         of SOME ty_ty' => Type.typ_match tsig ty_ty'
          | _ => I)
      | accumulate_improvements _ = I;
    val improvements = (fold o fold_aterms) accumulate_improvements ts Vartab.empty;
    val ts' = (map o map_types) (Envir.subst_type improvements) ts;
    fun apply_subst t = Envir.expand_term (fn Const (c, ty) => (case subst (c, ty)
         of SOME (ty', t') =>
              if Type.typ_instance tsig (ty, ty')
              then SOME (ty', apply_subst t') else NONE
          | NONE => NONE)
        | _ => NONE) t;
    val ts'' = if is_abbrev then ts' else map apply_subst ts';
  in if eq_list (op aconv) (ts, ts'') andalso passed_or_abbrev then NONE else
    if passed_or_abbrev then SOME (ts'', ctxt)
    else SOME (ts'', ctxt
      |> fold (ProofContext.add_const_constraint o apsnd SOME) secondary_constraints
      |> mark_passed)
  end;

fun rewrite_liberal thy unchecks t =
  case try (Pattern.rewrite_term thy unchecks []) t
   of NONE => NONE
    | SOME t' => if t aconv t' then NONE else SOME t';

fun improve_term_uncheck ts ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val unchecks = (#unchecks o ImprovableSyntax.get) ctxt;
    val ts' = map (rewrite_liberal thy unchecks) ts;
  in if exists is_some ts' then SOME (map2 the_default ts ts', ctxt) else NONE end;

fun set_primary_constraints ctxt =
  let
    val { primary_constraints, ... } = ImprovableSyntax.get ctxt;
  in fold (ProofContext.add_const_constraint o apsnd SOME) primary_constraints ctxt end;

val add_improvable_syntax =
  Context.proof_map
    (Syntax.add_term_check 0 "improvement" improve_term_check
    #> Syntax.add_term_uncheck 0 "improvement" improve_term_uncheck)
  #> set_primary_constraints;


(** overloading target **)

(* bookkeeping *)

structure OverloadingData = ProofDataFun
(
  type T = ((string * typ) * (string * bool)) list;
  fun init _ = [];
);

val get_overloading = OverloadingData.get o LocalTheory.target_of;
val map_overloading = LocalTheory.target o OverloadingData.map;

fun operation lthy b = get_overloading lthy
  |> get_first (fn ((c, _), (v, checked)) =>
      if Binding.name_of b = v then SOME (c, checked) else NONE);


(* target *)

fun synchronize_syntax ctxt =
  let
    val overloading = OverloadingData.get ctxt;
    fun subst (c, ty) = case AList.lookup (op =) overloading (c, ty)
     of SOME (v, _) => SOME (ty, Free (v, ty))
      | NONE => NONE;
    val unchecks =
      map (fn (c_ty as (_, ty), (v, _)) => (Free (v, ty), Const c_ty)) overloading;
  in 
    ctxt
    |> map_improvable_syntax (K ((([], []), (((K NONE, subst), false), unchecks)), false))
  end

fun init raw_overloading thy =
  let
    val _ = if null raw_overloading then error "At least one parameter must be given" else ();
    val overloading = map (fn (v, c_ty, checked) => (c_ty, (v, checked))) raw_overloading;
  in
    thy
    |> ProofContext.init
    |> OverloadingData.put overloading
    |> fold (fn ((_, ty), (v, _)) => Variable.declare_names (Free (v, ty))) overloading
    |> add_improvable_syntax
    |> synchronize_syntax
  end;

fun declare c_ty = pair (Const c_ty);

fun define checked b (c, t) = Thm.add_def (not checked) true
  (b, Logic.mk_equals (Const (c, Term.fastype_of t), t));

fun confirm b = map_overloading (filter_out (fn (_, (c', _)) => c' = Binding.name_of b))
  #> LocalTheory.target synchronize_syntax

fun conclude lthy =
  let
    val overloading = get_overloading lthy;
    val _ = if null overloading then () else
      error ("Missing definition(s) for parameter(s) " ^ commas (map (quote
        o Syntax.string_of_term lthy o Const o fst) overloading));
  in
    lthy
  end;

fun pretty lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val overloading = get_overloading lthy;
    fun pr_operation ((c, ty), (v, _)) =
      (Pretty.block o Pretty.breaks) [Pretty.str v, Pretty.str "==",
        Pretty.str (Sign.extern_const thy c), Pretty.str "::", Syntax.pretty_typ lthy ty];
  in
    (Pretty.block o Pretty.fbreaks)
      (Pretty.str "overloading" :: map pr_operation overloading)
  end;

end;
