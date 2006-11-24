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
  val compose_hhf: thm -> int -> thm -> thm Seq.seq
  val compose_hhf_tac: thm -> int -> tactic
  val comp_hhf: thm -> thm -> thm
  val prove_raw: cterm list -> cterm -> (thm list -> tactic) -> thm
  val prove_multi: Proof.context -> string list -> term list -> term list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm list
  val prove: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove_global: theory -> string list -> term list -> term -> (thm list -> tactic) -> thm
  val extract: int -> int -> thm -> thm Seq.seq
  val retrofit: int -> int -> thm -> thm -> thm Seq.seq
end;

structure Goal: GOAL =
struct

(** goals **)

(*
  -------- (init)
  C ==> #C
*)
val init =
  let val A = #1 (Drule.dest_implies (Thm.cprop_of Drule.protectI))
  in fn C => Thm.instantiate ([], [(A, C)]) Drule.protectI end;

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
  (case SINGLE (Thm.compose_no_flatten false (th, Thm.nprems_of th) 1)
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

(* composition of normal results *)

fun compose_hhf tha i thb =
  Thm.bicompose false (false, Drule.lift_all (Thm.cprem_of thb i) tha, 0) i thb;

fun compose_hhf_tac th i = PRIMSEQ (compose_hhf th i);

fun comp_hhf tha thb =
  (case Seq.chop 2 (compose_hhf tha 1 thb) of
    ([th], _) => th
  | ([], _) => raise THM ("comp_hhf: no unifiers", 1, [tha, thb])
  | _  => raise THM ("comp_hhf: multiple unifiers", 1, [tha, thb]));



(** tactical theorem proving **)

(* prove_raw -- no checks, no normalization of result! *)

fun prove_raw casms cprop tac =
  (case SINGLE (tac (map Assumption.assume casms)) (init cprop) of
    SOME th => Drule.implies_intr_list casms (finish th)
  | NONE => error "Tactic failed.");


(* prove_multi *)

fun prove_multi ctxt xs asms props tac =
  let
    val thy = ProofContext.theory_of ctxt;
    val string_of_term = Sign.string_of_term thy;

    fun err msg = cat_error msg
      ("The error(s) above occurred for the goal statement:\n" ^
        string_of_term (Logic.list_implies (asms, Logic.mk_conjunction_list props)));

    fun cert_safe t = Thm.cterm_of thy (Envir.beta_norm (Term.no_dummy_patterns t))
      handle TERM (msg, _) => err msg | TYPE (msg, _, _) => err msg;
    val casms = map cert_safe asms;
    val cprops = map cert_safe props;

    val (prems, ctxt') = ctxt
      |> Variable.add_fixes_direct xs
      |> fold Variable.declare_internal (asms @ props)
      |> Assumption.add_assumes casms;

    val goal = init (Conjunction.mk_conjunction_list cprops);
    val res =
      (case SINGLE (tac {prems = prems, context = ctxt'}) goal of
        NONE => err "Tactic failed."
      | SOME res => res);
    val [results] = Conjunction.elim_precise [length props] (finish res)
      handle THM (msg, _, _) => err msg;
    val _ = Unify.matches_list thy (map Thm.term_of cprops) (map Thm.prop_of results)
      orelse err ("Proved a different theorem: " ^ string_of_term (Thm.prop_of res));
  in
    results
    |> map (Assumption.export false ctxt' ctxt)
    |> Variable.export ctxt' ctxt
    |> map Drule.zero_var_indexes
  end;


(* prove *)

fun prove ctxt xs asms prop tac = hd (prove_multi ctxt xs asms [prop] tac);

fun prove_global thy xs asms prop tac =
  Drule.standard (prove (ProofContext.init thy) xs asms prop (fn {prems, ...} => tac prems));



(** local goal states **)

fun extract i n st =
  (if i < 1 orelse n < 1 orelse i + n - 1 > Thm.nprems_of st then Seq.empty
   else if n = 1 then Seq.single (Thm.cprem_of st i)
   else Seq.single (foldr1 Conjunction.mk_conjunction (map (Thm.cprem_of st) (i upto i + n - 1))))
  |> Seq.map (Thm.adjust_maxidx_cterm ~1 #> init);

fun retrofit i n st' st =
  (if n = 1 then st
   else st |> Drule.rotate_prems (i - 1) |> Conjunction.uncurry n |> Drule.rotate_prems (1 - i))
  |> Thm.compose_no_flatten false (conclude st', Thm.nprems_of st') i;

fun SELECT_GOAL tac i st =
  if Thm.nprems_of st = 1 andalso i = 1 then tac st
  else Seq.lifts (retrofit i 1) (Seq.maps tac (extract i 1 st)) st;

end;

structure BasicGoal: BASIC_GOAL = Goal;
open BasicGoal;
