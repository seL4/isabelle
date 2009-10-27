(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_set.ML
    Author:     Lukas Bulwahn, TU Muenchen

Preprocessing sets to predicates.
*)

signature PREDICATE_COMPILE_SET =
sig
(*
  val preprocess_intro : thm -> theory -> thm * theory
  val preprocess_clause : term -> theory -> term * theory
*)
  val unfold_set_notation : thm -> thm;
end;

structure Predicate_Compile_Set : PREDICATE_COMPILE_SET =
struct
(*FIXME: unfolding Ball in pretty adhoc here *)
val unfold_set_lemmas = [@{thm Collect_def}, @{thm mem_def},
@{thm Ball_def}, @{thm Bex_def}]

val unfold_set_notation = Simplifier.rewrite_rule unfold_set_lemmas

(*
fun find_set_theorems ctxt cname =
  let
    val _ = cname 
*)

(*
fun preprocess_term t ctxt =
  case t of
    Const ("op :", _) $ x $ A => 
      case strip_comb A of
        (Const (cname, T), params) =>
          let 
            val _ = find_set_theorems
          in
            (t, ctxt)
          end
      | _ => (t, ctxt)  
  | _ => (t, ctxt)
*) 
(*
fun preprocess_intro th thy =
  let
    val cnames = find_heads_of_prems
    val set_cname = filter (has_set_definition
    val _ = define_preds
    val _ = prep_pred_def
  in
*)
end;
