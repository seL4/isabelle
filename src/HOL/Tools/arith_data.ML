(*  Title:      HOL/Tools/arith_data.ML
    Author:     Markus Wenzel, Stefan Berghofer, and Tobias Nipkow

Common arithmetic proof auxiliary.
*)

signature ARITH_DATA =
sig
  val arith_tac: Proof.context -> int -> tactic
  val verbose_arith_tac: Proof.context -> int -> tactic
  val add_tactic: string -> (bool -> Proof.context -> int -> tactic) -> theory -> theory
  val get_arith_facts: Proof.context -> thm list

  val prove_conv_nohyps: tactic list -> Proof.context -> term * term -> thm option
  val prove_conv: tactic list -> Proof.context -> thm list -> term * term -> thm option
  val prove_conv2: tactic -> (simpset -> tactic) -> simpset -> term * term -> thm
  val simp_all_tac: thm list -> simpset -> tactic
  val simplify_meta_eq: thm list -> simpset -> thm -> thm
  val trans_tac: thm option -> tactic
  val prep_simproc: theory -> string * string list * (theory -> simpset -> term -> thm option)
    -> simproc

  val setup: theory -> theory
end;

structure Arith_Data: ARITH_DATA =
struct

(* slots for plugging in arithmetic facts and tactics *)

structure Arith_Facts = Named_Thms
(
  val name = "arith"
  val description = "arith facts - only ground formulas"
);

val get_arith_facts = Arith_Facts.get;

structure Arith_Tactics = TheoryDataFun
(
  type T = (serial * (string * (bool -> Proof.context -> int -> tactic))) list;
  val empty = [];
  val copy = I;
  val extend = I;
  fun merge _ = AList.merge (op =) (K true);
);

fun add_tactic name tac = Arith_Tactics.map (cons (serial (), (name, tac)));

fun gen_arith_tac verbose ctxt =
  let
    val tactics = (Arith_Tactics.get o ProofContext.theory_of) ctxt
    fun invoke (_, (name, tac)) k st = (if verbose
      then warning ("Trying " ^ name ^ "...") else ();
      tac verbose ctxt k st);
  in FIRST' (map invoke (rev tactics)) end;

val arith_tac = gen_arith_tac false;
val verbose_arith_tac = gen_arith_tac true;

val setup =
  Arith_Facts.setup #>
  Method.setup @{binding arith}
    (Args.bang_facts >> (fn prems => fn ctxt =>
      METHOD (fn facts => HEADGOAL (Method.insert_tac (prems @ get_arith_facts ctxt @ facts)
        THEN' verbose_arith_tac ctxt))))
    "various arithmetic decision procedures";


(* various auxiliary and legacy *)

fun prove_conv_nohyps tacs ctxt (t, u) =
  if t aconv u then NONE
  else let val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u))
  in SOME (Goal.prove ctxt [] [] eq (K (EVERY tacs))) end;

fun prove_conv tacs ctxt (_: thm list) = prove_conv_nohyps tacs ctxt;

fun prove_conv2 expand_tac norm_tac ss tu = (*FIXME avoid standard*)
  mk_meta_eq (Drule.standard (Goal.prove (Simplifier.the_context ss) [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq tu))
    (K (EVERY [expand_tac, norm_tac ss]))));

fun simp_all_tac rules =
  let val ss0 = HOL_ss addsimps rules
  in fn ss => ALLGOALS (simp_tac (Simplifier.inherit_context ss ss0)) end;

fun simplify_meta_eq rules =
  let val ss0 = HOL_basic_ss addeqcongs [eq_cong2] addsimps rules
  in fn ss => simplify (Simplifier.inherit_context ss ss0) o mk_meta_eq end

fun trans_tac NONE  = all_tac
  | trans_tac (SOME th) = ALLGOALS (rtac (th RS trans));

fun prep_simproc thy (name, pats, proc) =
  Simplifier.simproc thy name pats proc;

end;
