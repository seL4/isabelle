(*  Title:      Tools/code/code_simp.ML
    Author:     Florian Haftmann, TU Muenchen

Connecting the simplifier and the code generator.
*)

signature CODE_SIMP =
sig
  val no_frees_conv: conv -> conv
  val map_ss: (simpset -> simpset) -> theory -> theory
  val current_conv: theory -> conv
  val current_tac: theory -> int -> tactic
  val make_conv: theory -> simpset option -> string list -> conv
  val make_tac: theory -> simpset option -> string list -> int -> tactic
  val setup: theory -> theory
end;

structure Code_Simp : CODE_SIMP =
struct

(* avoid free variables during conversion *)

fun no_frees_conv conv ct =
  let
    val frees = Thm.add_cterm_frees ct [];
    fun apply_beta free thm = Thm.combination thm (Thm.reflexive free)
      |> Conv.fconv_rule (Conv.arg_conv (Conv.try_conv (Thm.beta_conversion false)))
      |> Conv.fconv_rule (Conv.arg1_conv (Thm.beta_conversion false));
  in
    ct
    |> fold_rev Thm.cabs frees
    |> conv
    |> fold apply_beta frees
  end;


(* dedicated simpset *)

structure Simpset = Theory_Data (
  type T = simpset;
  val empty = empty_ss;
  fun extend ss = MetaSimplifier.inherit_context empty_ss ss;
  val merge = merge_ss;
);

val map_ss = Simpset.map;


(* build simpset and conversion from program *)

fun add_stmt (Code_Thingol.Fun (_, ((_, eqs), some_cong))) ss =
      ss addsimps (map_filter (fst o snd)) eqs addcongs (the_list some_cong)
  | add_stmt (Code_Thingol.Classinst (_, (_, classparam_insts))) ss =
      ss addsimps (map (fst o snd) classparam_insts)
  | add_stmt _ ss = ss;

val add_program = Graph.fold (add_stmt o fst o snd)

fun rewrite_modulo thy some_ss program = Simplifier.full_rewrite
  (add_program program (Simplifier.global_context thy
    (the_default (Simpset.get thy) some_ss)));


(* evaluation with current code context *)

fun current_conv thy = no_frees_conv (Code_Thingol.eval_conv thy
  (fn naming => fn program => fn t => fn deps => rewrite_modulo thy NONE program));

fun current_tac thy = CONVERSION (current_conv thy);

val setup = Method.setup (Binding.name "code_simp")
  (Scan.succeed (SIMPLE_METHOD' o current_tac o ProofContext.theory_of))
  "simplification with code equations"


(* evaluation with freezed code context *)

fun make_conv thy some_ss consts = no_frees_conv (Code_Preproc.pre_post_conv thy
  ((rewrite_modulo thy some_ss o snd o snd o Code_Thingol.consts_program thy false) consts));

fun make_tac thy some_ss consts = CONVERSION (make_conv thy some_ss consts);

end;
