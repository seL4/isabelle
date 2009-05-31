(*  Title:      Pure/ML-Systems/polyml-experimental.ML

Compatibility wrapper for Poly/ML 5.3 (SVN experimental).
*)

open Thread;

structure ML_Name_Space =
struct
  open PolyML.NameSpace;
  type T = PolyML.NameSpace.nameSpace;
  val global = PolyML.globalNameSpace;
end;

use "ML-Systems/polyml_common.ML";
use "ML-Systems/multithreading_polyml.ML";

val pointer_eq = PolyML.pointerEq;

fun share_common_data () = PolyML.shareCommonData PolyML.rootFunction;

use "ML-Systems/compiler_polyml-5.3.ML";


(* toplevel pretty printing *)

val pretty_ml =
  let
    fun convert len (PrettyBlock (ind, _, context, prts)) =
          let
            fun property name default =
              (case List.find (fn ContextProperty (a, _) => name = a | _ => false) context of
                SOME (ContextProperty (_, b)) => b
              | NONE => default);
            val bg = property "begin" "";
            val en = property "end" "";
            val len' = property "length" len;
          in ML_Pretty.Block ((bg, en), map (convert len') prts, ind) end
      | convert len (PrettyString s) =
          ML_Pretty.String (s, case Int.fromString len of SOME i => i | NONE => size s)
      | convert _ (PrettyBreak (wd, _)) =
          ML_Pretty.Break (if wd < 99999 then (false, wd) else (true, 2));
  in convert "" end;

fun ml_pretty (ML_Pretty.Block ((bg, en), prts, ind)) =
      let val context =
        (if bg = "" then [] else [ContextProperty ("begin", bg)]) @
        (if en = "" then [] else [ContextProperty ("end", en)])
      in PrettyBlock (ind, false, context, map ml_pretty prts) end
  | ml_pretty (ML_Pretty.String (s, len)) =
      if len = size s then PrettyString s
      else PrettyBlock (0, false, [ContextProperty ("length", Int.toString len)], [PrettyString s])
  | ml_pretty (ML_Pretty.Break (false, wd)) = PrettyBreak (wd, 0)
  | ml_pretty (ML_Pretty.Break (true, _)) = PrettyBreak (99999, 0);

fun toplevel_pp context (_: string list) pp =
  use_text context (1, "pp") false
    ("addPrettyPrinter (fn _ => fn _ => ml_pretty o Pretty.to_ML o (" ^ pp ^ "))");

