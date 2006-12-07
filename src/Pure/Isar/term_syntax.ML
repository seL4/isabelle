(*  Title:      Pure/Isar/term_syntax.ML
    ID:         $Id$
    Author:     Makarius

Common term syntax declarations.
*)

signature TERM_SYNTAX =
sig
  val notation: Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val abbrevs: Syntax.mode -> ((bstring * mixfix) * term) list -> local_theory -> local_theory
end;

structure TermSyntax: TERM_SYNTAX =
struct

(* notation *)  (* FIXME dynamic scoping!? *)

fun target_notation mode args phi =
  let val args' = filter (fn (t, _) => t aconv Morphism.term phi t) args
  in Context.mapping (Sign.add_notation mode args') (ProofContext.add_notation mode args') end;

fun notation mode raw_args lthy =
  let val args = map (apfst (Morphism.term (LocalTheory.target_morphism lthy))) raw_args
  in LocalTheory.term_syntax (target_notation mode args) lthy end;


(* abbrevs *)

fun morph_abbrev phi ((c, mx), rhs) = ((Morphism.name phi c, mx), Morphism.term phi rhs);

fun abbrevs prmode raw_args lthy =
  let
    val mode = #1 prmode;
    val args = map (morph_abbrev (LocalTheory.target_morphism lthy)) raw_args;
  in
    lthy |> LocalTheory.term_syntax (fn phi =>
      let
        val args' = map (morph_abbrev phi) args;
        val (abbrs, mxs) = (args ~~ args') |> map_filter (fn ((_, rhs), ((c', mx'), rhs')) =>
            if rhs aconv rhs' then SOME ((c', rhs'), mx') else NONE)
          |> split_list;
      in
        Context.mapping_result (Sign.add_abbrevs mode abbrs) (ProofContext.add_abbrevs mode abbrs)
        #-> (fn res => target_notation prmode (map (Const o #1) res ~~ mxs) phi)
      end)
  end;

end;
