(*  Title:      Pure/ML-Systems/polyml_common.ML

Compatibility file for Poly/ML -- common part for 5.x.
*)

fun op before (a, _: unit) = a;

exception Interrupt = SML90.Interrupt;

use "General/exn.ML";

if List.exists (fn s => s = "SingleAssignment") (PolyML.Compiler.structureNames ())
then ()
else use "ML-Systems/single_assignment_polyml.ML";

use "ML-Systems/multithreading.ML";
use "ML-Systems/ml_pretty.ML";
use "ML-Systems/use_context.ML";

val seconds = Time.fromReal;



(** ML system and platform related **)

val _ = PolyML.Compiler.forgetValue "isSome";
val _ = PolyML.Compiler.forgetValue "getOpt";
val _ = PolyML.Compiler.forgetValue "valOf";
val _ = PolyML.Compiler.forgetValue "foldl";
val _ = PolyML.Compiler.forgetValue "foldr";
val _ = PolyML.Compiler.forgetValue "print";
val _ = PolyML.Compiler.forgetValue "explode";
val _ = PolyML.Compiler.forgetValue "concat";


(* Compiler options *)

PolyML.Compiler.printInAlphabeticalOrder := false;
PolyML.Compiler.maxInlineSize := 80;


(* old Poly/ML emulation *)

fun quit () = exit 0;


(* restore old-style character / string functions *)

val ord = SML90.ord;
val chr = SML90.chr;
val raw_explode = SML90.explode;
val implode = SML90.implode;


(* prompts *)

fun ml_prompts p1 p2 = (PolyML.Compiler.prompt1 := p1; PolyML.Compiler.prompt2 := p2);


(* toplevel printing *)

local
  val depth = ref 10;
in
  fun get_print_depth () = ! depth;
  fun print_depth n = (depth := n; PolyML.print_depth n);
end;

val error_depth = PolyML.error_depth;

val ml_make_string = "PolyML.makestring";



(** Runtime system **)

val exception_trace = PolyML.exception_trace;
val timing = PolyML.timing;
val profiling = PolyML.profiling;

fun profile 0 f x = f x
  | profile n f x =
      let
        val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler n;
        val res = Exn.capture f x;
        val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler 0;
      in Exn.release res end;

