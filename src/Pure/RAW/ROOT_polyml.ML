(*  Title:      Pure/RAW/ROOT_polyml.ML
    Author:     Makarius

Compatibility wrapper for Poly/ML.
*)

(* initial ML name space *)

use "RAW/ml_system.ML";
use "RAW/ml_name_space.ML";

if List.exists (fn (a, _) => a = "FixedInt") (#allStruct ML_Name_Space.global ()) then ()
else use "RAW/fixed_int_dummy.ML";

structure ML_Name_Space =
struct
  open ML_Name_Space;
  val initial_val =
    List.filter (fn (a, _) => a <> "use" andalso a <> "exit" andalso a <> "commit")
      (#allVal global ());
  val initial_type = #allType global ();
  val initial_fixity = #allFix global ();
  val initial_structure = #allStruct global ();
  val initial_signature = #allSig global ();
  val initial_functor = #allFunct global ();
end;


(* exceptions *)

fun reraise exn =
  (case PolyML.exceptionLocation exn of
    NONE => raise exn
  | SOME location => PolyML.raiseWithLocation (exn, location));

exception Interrupt = SML90.Interrupt;

use "RAW/exn.ML";
use "RAW/exn_trace.ML";


(* multithreading *)

val seconds = Time.fromReal;

open Thread;
use "RAW/multithreading.ML";

use "RAW/unsynchronized.ML";
val _ = PolyML.Compiler.forgetValue "ref";
val _ = PolyML.Compiler.forgetType "ref";


(* pervasive environment *)

val _ = PolyML.Compiler.forgetValue "isSome";
val _ = PolyML.Compiler.forgetValue "getOpt";
val _ = PolyML.Compiler.forgetValue "valOf";
val _ = PolyML.Compiler.forgetValue "foldl";
val _ = PolyML.Compiler.forgetValue "foldr";
val _ = PolyML.Compiler.forgetValue "print";
val _ = PolyML.Compiler.forgetValue "explode";
val _ = PolyML.Compiler.forgetValue "concat";

val ord = SML90.ord;
val chr = SML90.chr;
val raw_explode = SML90.explode;
val implode = SML90.implode;

fun quit () = exit 0;


(* ML runtime system *)

use "RAW/ml_heap.ML";
use "RAW/ml_profiling.ML";

val pointer_eq = PolyML.pointerEq;


(* ML toplevel pretty printing *)

use "RAW/ml_pretty.ML";

local
  val depth = Unsynchronized.ref 10;
in
  fun get_default_print_depth () = ! depth;
  fun default_print_depth n = (depth := n; PolyML.print_depth n);
  val _ = default_print_depth 10;
end;

val error_depth = PolyML.error_depth;

val pretty_ml =
  let
    fun convert _ (PolyML.PrettyBreak (width, offset)) = ML_Pretty.Break (false, width, offset)
      | convert _ (PolyML.PrettyBlock (_, _,
            [PolyML.ContextProperty ("fbrk", _)], [PolyML.PrettyString " "])) =
          ML_Pretty.Break (true, 1, 0)
      | convert len (PolyML.PrettyBlock (ind, consistent, context, prts)) =
          let
            fun property name default =
              (case List.find (fn PolyML.ContextProperty (a, _) => name = a | _ => false) context of
                SOME (PolyML.ContextProperty (_, b)) => b
              | _ => default);
            val bg = property "begin" "";
            val en = property "end" "";
            val len' = property "length" len;
          in ML_Pretty.Block ((bg, en), consistent, ind, map (convert len') prts) end
      | convert len (PolyML.PrettyString s) =
          ML_Pretty.String
            (s, FixedInt.fromInt (case Int.fromString len of SOME i => i | NONE => size s))
  in convert "" end;

fun ml_pretty (ML_Pretty.Break (false, width, offset)) = PolyML.PrettyBreak (width, offset)
  | ml_pretty (ML_Pretty.Break (true, _, _)) =
      PolyML.PrettyBlock (0, false, [PolyML.ContextProperty ("fbrk", "")],
        [PolyML.PrettyString " "])
  | ml_pretty (ML_Pretty.Block ((bg, en), consistent, ind, prts)) =
      let val context =
        (if bg = "" then [] else [PolyML.ContextProperty ("begin", bg)]) @
        (if en = "" then [] else [PolyML.ContextProperty ("end", en)])
      in PolyML.PrettyBlock (ind, consistent, context, map ml_pretty prts) end
  | ml_pretty (ML_Pretty.String (s, len)) =
      if len = FixedInt.fromInt (size s) then PolyML.PrettyString s
      else
        PolyML.PrettyBlock
          (0, false,
            [PolyML.ContextProperty ("length", FixedInt.toString len)], [PolyML.PrettyString s]);


(* ML compiler *)

use "RAW/secure.ML";

structure ML_Name_Space =
struct
  open ML_Name_Space;
  val display_val = pretty_ml o displayVal;
end;

use "RAW/ml_positions.ML";
use "RAW/ml_compiler0.ML";

PolyML.Compiler.reportUnreferencedIds := true;
PolyML.Compiler.printInAlphabeticalOrder := false;
PolyML.Compiler.maxInlineSize := 80;
PolyML.Compiler.prompt1 := "ML> ";
PolyML.Compiler.prompt2 := "ML# ";

fun ml_make_string struct_name =
  "(fn x => Pretty.string_of (Pretty.from_ML (pretty_ml (PolyML.prettyRepresentation (x, FixedInt.fromInt (" ^
    struct_name ^ ".ML_print_depth ()))))))";


(* ML debugger *)

use_no_debug "RAW/ml_debugger.ML";
