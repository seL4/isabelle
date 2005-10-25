(*  Title:      Pure/goal.ML
    ID:         $Id$
    Author:     Makarius and Lawrence C Paulson

Internal goals.  NB: by attaching the Goal constant the conclusion of
a goal state is guaranteed to be atomic.
*)

signature BASIC_GOAL =
sig
  val SELECT_GOAL: tactic -> int -> tactic
end;

signature GOAL =
sig
  include BASIC_GOAL
  val init: cterm -> thm
  val conclude: thm -> thm
  val finish: thm -> thm
  val norm_hhf_rule: thm -> thm
  val prove_raw: cterm list -> cterm -> (thm list -> tactic) -> thm
  val prove: theory -> string list -> term list -> term -> (thm list -> tactic) -> thm
  val prove_multi: theory -> string list -> term list -> term list ->
    (thm list -> tactic) -> thm list

  (* FIXME remove *)
  val norm_hhf_plain: thm -> thm
  val prove_multi_plain: theory -> string list -> term list -> term list ->
    (thm list -> tactic) -> thm list
  val prove_plain: theory -> string list -> term list -> term -> (thm list -> tactic) -> thm
end;

structure Goal: GOAL =
struct

(* managing goal states *)

(*
  ------------ (init)
  C ==> Goal C
*)
fun init ct = Drule.instantiate' [] [SOME ct] Drule.goalI;

(*
  A ==> ... ==> Goal C
  -------------------- (conclude)
  A ==> ... ==> C
*)
fun conclude th =
  (case SINGLE (Thm.bicompose false (false, th, Thm.nprems_of th) 1)
      (Drule.incr_indexes_wrt [] [] [] [th] Drule.goalD) of
    SOME th' => th'
  | NONE => raise THM ("Failed to conclude goal", 0, [th]));

(*
  Goal C
  ------ (finish)
    C
*)
fun finish th =
  (case Thm.nprems_of th of
    0 => conclude th
  | n => raise THM ("Proof failed.\n" ^
      Pretty.string_of (Pretty.chunks (Display.pretty_goals n th)) ^
      ("\n" ^ string_of_int n ^ " unsolved goal(s)!"), 0, [th]));


(* prove_raw -- minimal result checks, no normalization *)

val norm_hhf_plain =  (* FIXME remove *)
  (not o Drule.is_norm_hhf o Thm.prop_of) ?
    MetaSimplifier.simplify_aux (K (K NONE)) true [Drule.norm_hhf_eq];

val norm_hhf_rule =
  norm_hhf_plain
  #> Thm.adjust_maxidx_thm
  #> Drule.gen_all;

fun prove_raw casms cprop tac =
  (case SINGLE (tac (map (norm_hhf_rule o Thm.assume) casms)) (init cprop) of
    SOME th => Drule.implies_intr_list casms (finish th)
  | NONE => raise ERROR_MESSAGE "Tactic failed.");


(* tactical proving *)

local

fun gen_prove finish_thm thy xs asms props tac =
  let
    val prop = Logic.mk_conjunction_list props;
    val statement = Logic.list_implies (asms, prop);
    val frees = map Term.dest_Free (Term.term_frees statement);
    val fixed_frees = filter_out (member (op =) xs o #1) frees;
    val fixed_tfrees = foldr Term.add_typ_tfrees [] (map #2 fixed_frees);
    val params = List.mapPartial (fn x => Option.map (pair x) (AList.lookup (op =) frees x)) xs;

    fun err msg = raise ERROR_MESSAGE
      (msg ^ "\nThe error(s) above occurred for the goal statement:\n" ^
        Sign.string_of_term thy (Term.list_all_free (params, statement)));

    fun cert_safe t = Thm.cterm_of thy (Envir.beta_norm t)
      handle TERM (msg, _) => err msg | TYPE (msg, _, _) => err msg;

    val _ = cert_safe statement;
    val _ = Term.no_dummy_patterns statement handle TERM (msg, _) => err msg;

    val cparams = map (cert_safe o Free) params;
    val casms = map cert_safe asms;
    val prems = map (norm_hhf_rule o Thm.assume) casms;

    val goal = init (cert_safe prop);
    val goal' = (case SINGLE (tac prems) goal of SOME goal' => goal' | _ => err "Tactic failed.");
    val raw_result = finish goal' handle THM (msg, _, _) => err msg;

    val prop' = Thm.prop_of raw_result;
    val _ = conditional (not (Pattern.matches thy (Envir.beta_norm prop, prop'))) (fn () =>
      err ("Proved a different theorem: " ^ Sign.string_of_term thy prop'));
  in
    Drule.conj_elim_precise (length props) raw_result
    |> map
      (Drule.implies_intr_list casms
        #> Drule.forall_intr_list cparams
        #> finish_thm fixed_tfrees)
  end;

in

fun prove_multi thy xs asms prop tac =
  gen_prove (fn fixed_tfrees => Drule.zero_var_indexes o
      (#1 o Thm.varifyT' fixed_tfrees) o norm_hhf_rule)
    thy xs asms prop tac;

fun prove thy xs asms prop tac = hd (prove_multi thy xs asms [prop] tac);

fun prove_multi_plain thy xs asms prop tac = gen_prove (K norm_hhf_plain) thy xs asms prop tac;
fun prove_plain thy xs asms prop tac = hd (prove_multi_plain thy xs asms [prop] tac);

end;


(* SELECT_GOAL *)

(*Tactical for restricting the effect of a tactic to subgoal i.  Works
  by making a new state from subgoal i, applying tac to it, and
  composing the resulting thm with the original state.*)

fun SELECT tac i st =
  init (Thm.adjust_maxidx (List.nth (Drule.cprems_of st, i - 1)))
  |> tac
  |> Seq.maps (fn st' => Thm.bicompose false (false, conclude st', Thm.nprems_of st') i st);

fun SELECT_GOAL tac i st =
  let val n = Thm.nprems_of st in
    if 1 <= i andalso i <= n then
      if n = 1 then tac st else SELECT tac i st
    else Seq.empty
  end;

end;

structure BasicGoal: BASIC_GOAL = Goal;
open BasicGoal;
