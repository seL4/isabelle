(*  Title:      Pure/Isar/overloading.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Overloaded definitions without any discipline.
*)

signature OVERLOADING =
sig
  val init: (string * (string * typ) * bool) list -> theory -> local_theory
  val conclude: local_theory -> local_theory
  val declare: string * typ -> theory -> term * theory
  val confirm: string -> local_theory -> local_theory
  val define: bool -> string -> string * term -> theory -> thm * theory
  val operation: Proof.context -> string -> (string * bool) option
  val pretty: Proof.context -> Pretty.T
end;

structure Overloading: OVERLOADING =
struct

(* bookkeeping *)

structure OverloadingData = ProofDataFun
(
  type T = ((string * typ) * (string * bool)) list;
  fun init _ = [];
);

val get_overloading = OverloadingData.get o LocalTheory.target_of;
val map_overloading = LocalTheory.target o OverloadingData.map;

fun operation lthy v = get_overloading lthy
  |> get_first (fn ((c, _), (v', checked)) => if v = v' then SOME (c, checked) else NONE);

fun confirm c = map_overloading (filter_out (fn (_, (c', _)) => c' = c));


(* overloaded declarations and definitions *)

fun declare c_ty = pair (Const c_ty);

fun define checked name (c, t) =
  Thm.add_def (not checked) true (name, Logic.mk_equals (Const (c, Term.fastype_of t), t));


(* syntax *)

fun subst_operation overloading = map_aterms (fn t as Const (c, ty) =>
    (case AList.lookup (op =) overloading (c, ty)
     of SOME (v, _) => Free (v, ty)
      | NONE => t)
  | t => t);

fun term_check ts lthy =
  let
    val overloading = get_overloading lthy;
    val ts' = map (subst_operation overloading) ts;
  in if eq_list (op aconv) (ts, ts') then NONE else SOME (ts', lthy) end;

fun term_uncheck ts lthy =
  let
    val overloading = get_overloading lthy;
    fun subst (t as Free (v, ty)) = (case get_first (fn ((c, _), (v', _)) =>
        if v = v' then SOME c else NONE) overloading
         of SOME c => Const (c, ty)
          | NONE => t)
      | subst t = t;
    val ts' = (map o map_aterms) subst ts;
  in if eq_list (op aconv) (ts, ts') then NONE else SOME (ts', lthy) end;


(* target *)

fun init overloading thy =
  let
    val _ = if null overloading then error "At least one parameter must be given" else ();
  in
    thy
    |> ProofContext.init
    |> OverloadingData.put (map (fn (v, c_ty, checked) => (c_ty, (v, checked))) overloading)
    |> fold (fn (v, (_, ty), _) => Variable.declare_term (Free (v, ty))) overloading
    |> Context.proof_map (
        Syntax.add_term_check 0 "overloading" term_check
        #> Syntax.add_term_uncheck 0 "overloading" term_uncheck)
  end;

fun conclude lthy =
  let
    val overloading = get_overloading lthy;
    val _ = if null overloading then () else
      error ("Missing definition(s) for parameters " ^ commas (map (quote
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
        Pretty.str (Sign.extern_const thy c), Pretty.str "::", Sign.pretty_typ thy ty];
  in
    (Pretty.block o Pretty.fbreaks)
      (Pretty.str "overloading" :: map pr_operation overloading)
  end;

end;
