(*  Title:      Pure/Isar/term_syntax.ML
    ID:         $Id$
    Author:     Makarius

Common term syntax declarations.
*)

signature TERM_SYNTAX =
sig
  val notation: Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val abbrev: Syntax.mode -> (bstring * mixfix) * term -> local_theory -> local_theory
end;

structure TermSyntax: TERM_SYNTAX =
struct


(* notation *)  (* FIXME avoid dynamic scoping!? *)

fun target_notation mode args phi =
  let val args' = filter (fn (t, _) => t aconv Morphism.term phi t) args
  in Context.mapping (Sign.add_notation mode args') (ProofContext.add_notation mode args') end;

fun notation mode raw_args lthy =
  let val args = map (apfst (Morphism.term (LocalTheory.target_morphism lthy))) raw_args
  in LocalTheory.term_syntax (target_notation mode args) lthy end;


(* abbrevs *)

fun morph_abbrev phi ((c, mx), rhs) = ((Morphism.name phi c, mx), Morphism.term phi rhs);

fun target_abbrev (prmode, arg) phi =
  let
    val mode = #1 prmode;
    val ((c, mx), rhs) = arg;
    val ((c', _), rhs') = morph_abbrev phi arg;
    val abbr = (c', rhs');
  in
    if rhs aconv rhs' then   (* FIXME !? *)
      Context.mapping_result (Sign.add_abbrev mode abbr) (ProofContext.add_abbrev mode abbr)
        #-> (fn (lhs, _) =>
          if rhs aconv rhs' then target_notation prmode [(Const lhs, mx)] Morphism.identity
          else I)
    else I
  end;

fun abbrev prmode raw_arg lthy =
  let
    val is_local = is_none o Sign.const_constraint (ProofContext.theory_of lthy);
    val local_term = Term.exists_subterm (fn Const (c, _) => is_local c | _ => false);
    val input_only = (#1 Syntax.input_mode, #2 prmode);
    val expand = ProofContext.cert_term (ProofContext.set_expand_abbrevs true lthy);
    val arg = raw_arg |> (morph_abbrev (LocalTheory.target_morphism lthy) #>
      (fn (lhs, rhs) =>  (*avoid dynamic references to local names*)
        if local_term rhs then (input_only, (lhs, expand rhs))
        else (prmode, (lhs, rhs))));
  in LocalTheory.term_syntax (fn phi => target_abbrev arg phi) lthy end;

end;
