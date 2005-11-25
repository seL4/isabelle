(*  Title:      Pure/goal.ML
    ID:         $Id$
    Author:     Makarius and Lawrence C Paulson

Goals in tactical theorem proving.
*)

signature BASIC_GOAL =
sig
  val SELECT_GOAL: tactic -> int -> tactic
end;

signature GOAL =
sig
  include BASIC_GOAL
  val init: cterm -> thm
  val protect: thm -> thm
  val conclude: thm -> thm
  val finish: thm -> thm
  val norm_hhf: thm -> thm
  val norm_hhf_protect: thm -> thm
  val compose_hhf: thm -> int -> thm -> thm Seq.seq
  val compose_hhf_tac: thm -> int -> tactic
  val comp_hhf: thm -> thm -> thm
  val prove_multi: theory -> string list -> term list -> term list ->
    (thm list -> tactic) -> thm list
  val prove: theory -> string list -> term list -> term -> (thm list -> tactic) -> thm
  val prove_raw: cterm list -> cterm -> (thm list -> tactic) -> thm
end;

structure Goal: GOAL =
struct

(** goals **)

(*
  -------- (init)
  C ==> #C
*)
fun init ct = Drule.instantiate' [] [SOME ct] Drule.protectI;

(*
   C
  --- (protect)
  #C
*)
fun protect th = th COMP Drule.incr_indexes th Drule.protectI;

(*
  A ==> ... ==> #C
  ---------------- (conclude)
  A ==> ... ==> C
*)
fun conclude th =
  (case SINGLE (Thm.bicompose false (false, th, Thm.nprems_of th) 1)
      (Drule.incr_indexes th Drule.protectD) of
    SOME th' => th'
  | NONE => raise THM ("Failed to conclude goal", 0, [th]));

(*
  #C
  --- (finish)
   C
*)
fun finish th =
  (case Thm.nprems_of th of
    0 => conclude th
  | n => raise THM ("Proof failed.\n" ^
      Pretty.string_of (Pretty.chunks (Display.pretty_goals n th)) ^
      ("\n" ^ string_of_int n ^ " unsolved goal(s)!"), 0, [th]));



(** results **)

(* HHF normal form: !! before ==>, outermost !! generalized *)

local

fun gen_norm_hhf ss =
  (not o Drule.is_norm_hhf o Thm.prop_of) ?
    Drule.fconv_rule (MetaSimplifier.rewrite_cterm (true, false, false) (K (K NONE)) ss)
  #> Thm.adjust_maxidx_thm
  #> Drule.gen_all;

val ss =
  MetaSimplifier.theory_context ProtoPure.thy MetaSimplifier.empty_ss
    addsimps [Drule.norm_hhf_eq];

in

val norm_hhf = gen_norm_hhf ss;
val norm_hhf_protect = gen_norm_hhf (ss addeqcongs [Drule.protect_cong]);

end;


(* composition of normal results *)

fun compose_hhf tha i thb =
  Thm.bicompose false (false, Drule.lift_all (Thm.cprem_of thb i) tha, 0) i thb;

fun compose_hhf_tac th i = PRIMSEQ (compose_hhf th i);

fun comp_hhf tha thb =
  (case Seq.chop (2, compose_hhf tha 1 thb) of
    ([th], _) => th
  | ([], _) => raise THM ("comp_hhf: no unifiers", 1, [tha, thb])
  | _  => raise THM ("comp_hhf: multiple unifiers", 1, [tha, thb]));



(** tactical theorem proving **)

(* prove_multi *)

fun prove_multi thy xs asms props tac =
  let
    val prop = Logic.mk_conjunction_list props;
    val statement = Logic.list_implies (asms, prop);
    val frees = Term.add_frees statement [];
    val fixed_frees = filter_out (member (op =) xs o #1) frees;
    val fixed_tfrees = fold (Term.add_tfreesT o #2) fixed_frees [];
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
    val prems = map (norm_hhf o Thm.assume) casms;

    val goal = init (cert_safe prop);
    val goal' = case SINGLE (tac prems) goal of SOME goal' => goal' | _ => err "Tactic failed.";
    val raw_result = finish goal' handle THM (msg, _, _) => err msg;

    val prop' = Thm.prop_of raw_result;
    val _ = conditional (not (Pattern.matches thy (Envir.beta_norm prop, prop'))) (fn () =>
      err ("Proved a different theorem: " ^ Sign.string_of_term thy prop'));
  in
    Drule.conj_elim_precise (length props) raw_result
    |> map
      (Drule.implies_intr_list casms
        #> Drule.forall_intr_list cparams
        #> norm_hhf
        #> Thm.varifyT' fixed_tfrees
        #-> K Drule.zero_var_indexes)
  end;


(* prove *)

fun prove thy xs asms prop tac = hd (prove_multi thy xs asms [prop] tac);


(* prove_raw -- no checks, no normalization of result! *)

fun prove_raw casms cprop tac =
  (case SINGLE (tac (map (norm_hhf o Thm.assume) casms)) (init cprop) of
    SOME th => Drule.implies_intr_list casms (finish th)
  | NONE => raise ERROR_MESSAGE "Tactic failed.");


(* SELECT_GOAL *)

(*Tactical for restricting the effect of a tactic to subgoal i.  Works
  by making a new state from subgoal i, applying tac to it, and
  composing the resulting thm with the original state.*)

local

fun SELECT tac i st =
  init (Thm.adjust_maxidx (Thm.cprem_of st i))
  |> tac
  |> Seq.maps (fn st' => Thm.bicompose false (false, conclude st', Thm.nprems_of st') i st);

in

fun SELECT_GOAL tac i st =
  let val n = Thm.nprems_of st in
    if 1 <= i andalso i <= n then
      if n = 1 then tac st else SELECT tac i st
    else Seq.empty
  end;

end;

end;

structure BasicGoal: BASIC_GOAL = Goal;
open BasicGoal;
