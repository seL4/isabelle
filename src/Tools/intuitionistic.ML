(*  Title:      Tools/intuitionistic.ML
    Author:     Stefan Berghofer, TU Muenchen

Simple intuitionistic proof search.
*)

signature INTUITIONISTIC =
sig
  val prover_tac: Proof.context -> int option -> int -> tactic
  val method_setup: binding -> theory -> theory
end;

structure Intuitionistic: INTUITIONISTIC =
struct

(* main tactic *)

local

fun remdups_tac ctxt = SUBGOAL (fn (g, i) =>
  let val prems = Logic.strip_assums_hyp g in
    REPEAT_DETERM_N (length prems - length (distinct op aconv prems))
    (ematch_tac ctxt [Drule.remdups_rl] i THEN Tactic.eq_assume_tac i)
  end);

fun REMDUPS tac ctxt = tac ctxt THEN_ALL_NEW remdups_tac ctxt;

fun bires_tac ctxt = Bires.biresolution_from_nets_tac ctxt Bires.tag_ord NONE;

fun safe_step_tac ctxt =
  Context_Rules.Swrap ctxt
   (eq_assume_tac ORELSE'
    bires_tac ctxt true (Context_Rules.netpair_bang ctxt));

fun unsafe_step_tac ctxt =
  Context_Rules.wrap ctxt
   (assume_tac ctxt APPEND'
    bires_tac ctxt false (Context_Rules.netpair_bang ctxt) APPEND'
    bires_tac ctxt false (Context_Rules.netpair ctxt));

fun step_tac ctxt i =
  REPEAT_DETERM1 (REMDUPS safe_step_tac ctxt i) ORELSE
  REMDUPS unsafe_step_tac ctxt i;

fun intprover_tac ctxt gs d lim = SUBGOAL (fn (g, i) =>
  if d > lim then no_tac
  else
    let
      val ps = Logic.strip_assums_hyp g;
      val c = Logic.strip_assums_concl g;
    in
      if member (fn ((ps1, c1), (ps2, c2)) =>
          c1 aconv c2 andalso
          length ps1 = length ps2 andalso
          eq_set (op aconv) (ps1, ps2)) gs (ps, c)
      then no_tac
      else (step_tac ctxt THEN_ALL_NEW intprover_tac ctxt ((ps, c) :: gs) (d + 1) lim) i
    end);

in

fun prover_tac ctxt opt_lim =
  SELECT_GOAL (DEEPEN (2, the_default 20 opt_lim) (intprover_tac ctxt [] 0) 4 1);

end;


(* method setup *)

local

val introN = "intro";
val elimN = "elim";
val destN = "dest";

fun modifier name kind kind' att pos =
  Args.$$$ name |-- (kind >> K NONE || kind' |-- Parse.nat --| Args.colon >> SOME)
    >> (fn arg => Method.modifier (att arg) pos);

val modifiers =
 [modifier destN Args.bang_colon Args.bang Context_Rules.dest_bang \<^here>,
  modifier destN Args.colon (Scan.succeed ()) Context_Rules.dest \<^here>,
  modifier elimN Args.bang_colon Args.bang Context_Rules.elim_bang \<^here>,
  modifier elimN Args.colon (Scan.succeed ()) Context_Rules.elim \<^here>,
  modifier introN Args.bang_colon Args.bang Context_Rules.intro_bang \<^here>,
  modifier introN Args.colon (Scan.succeed ()) Context_Rules.intro \<^here>,
  Args.del -- Args.colon >> K (Method.modifier Context_Rules.rule_del \<^here>)];

in

fun method_setup name =
  Method.setup name
    (Scan.lift (Scan.option Parse.nat) --| Method.sections modifiers >>
      (fn opt_lim => fn ctxt =>
        SIMPLE_METHOD' (Object_Logic.atomize_prems_tac ctxt THEN' prover_tac ctxt opt_lim)))
    "intuitionistic proof search";

end;

end;

