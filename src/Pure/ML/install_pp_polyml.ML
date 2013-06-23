(*  Title:      Pure/ML/install_pp_polyml.ML
    Author:     Makarius

Extra toplevel pretty-printing for Poly/ML.
*)

PolyML.addPrettyPrinter (fn depth => fn _ => fn str =>
  ml_pretty (Pretty.to_ML (ML_Syntax.pretty_string (depth * 100) str)));

PolyML.addPrettyPrinter (fn depth => fn _ => fn tree =>
  ml_pretty (Pretty.to_ML (XML.pretty depth tree)));

PolyML.addPrettyPrinter (fn depth => fn pretty => fn var =>
  pretty (Synchronized.value var, depth));

PolyML.addPrettyPrinter (fn depth => fn pretty => fn x =>
  (case Future.peek x of
    NONE => PolyML.PrettyString "<future>"
  | SOME (Exn.Exn _) => PolyML.PrettyString "<failed>"
  | SOME (Exn.Res y) => pretty (y, depth)));

PolyML.addPrettyPrinter (fn depth => fn pretty => fn x =>
  (case Lazy.peek x of
    NONE => PolyML.PrettyString "<lazy>"
  | SOME (Exn.Exn _) => PolyML.PrettyString "<failed>"
  | SOME (Exn.Res y) => pretty (y, depth)));

PolyML.addPrettyPrinter (fn depth => fn _ => fn tm =>
  let
    open PolyML;
    val from_ML = Pretty.from_ML o pretty_ml;
    fun prt_app name prt = Pretty.block [Pretty.str (name ^ " "), prt];
    fun prt_apps name = Pretty.enum "," (name ^ " (") ")";
    fun prt_term parens dp t =
      if dp <= 0 then Pretty.str "..."
      else
        (case t of
          _ $ _ =>
            op :: (strip_comb t)
            |> map_index (fn (i, u) => prt_term true (dp - i - 1) u)
            |> Pretty.separate " $"
            |> (if parens then Pretty.enclose "(" ")" else Pretty.block)
        | Abs (a, T, b) =>
            prt_apps "Abs"
             [from_ML (prettyRepresentation (a, dp - 1)),
              from_ML (prettyRepresentation (T, dp - 2)),
              prt_term false (dp - 3) b]
        | Const const => prt_app "Const" (from_ML (prettyRepresentation (const, dp - 1)))
        | Free free => prt_app "Free" (from_ML (prettyRepresentation (free, dp - 1)))
        | Var var => prt_app "Var" (from_ML (prettyRepresentation (var, dp - 1)))
        | Bound i => prt_app "Bound" (from_ML (prettyRepresentation (i, dp - 1))));
  in ml_pretty (Pretty.to_ML (prt_term false depth tm)) end);

