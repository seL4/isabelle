(*  Title:      Pure/Isar/subclass.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

User interface for proving subclass relationship between type classes.
*)

signature SUBCLASS =
sig
  val subclass: class -> local_theory -> Proof.state
  val subclass_cmd: xstring -> local_theory -> Proof.state
  val prove_subclass: tactic -> class -> local_theory -> local_theory
end;

structure Subclass : SUBCLASS =
struct

local

fun gen_subclass prep_class do_proof raw_sup lthy =
  let
    (*FIXME make more use of local context; drop redundancies*)
    val ctxt = LocalTheory.target_of lthy;
    val thy = ProofContext.theory_of ctxt;
    val sup = prep_class thy raw_sup;
    val sub = case TheoryTarget.peek lthy
     of {is_class = false, ...} => error "No class context"
      | {target, ...} => target;
    val sub_params = map fst (Class.these_params thy [sub]);
    val sup_params = map fst (Class.these_params thy [sup]);
    val err_params = subtract (op =) sub_params sup_params;
    val _ = if null err_params then [] else
      error ("Class " ^ Sign.string_of_sort thy [sub] ^ " lacks parameter(s) " ^
          commas_quote err_params ^ " of " ^ Sign.string_of_sort thy [sup]);
    val sublocale_prop =
      Locale.global_asms_of thy sup
      |> maps snd
      |> map (ObjectLogic.ensure_propT thy);
    fun after_qed thms =
      LocalTheory.theory (Class.prove_subclass (sub, sup) thms ctxt)
      #> (fn lthy => LocalTheory.reinit lthy (ProofContext.theory_of (LocalTheory.target_of lthy)));
  in
    do_proof after_qed sublocale_prop lthy
  end;

fun user_proof after_qed props =
  Proof.theorem_i NONE (after_qed o the_single) [map (rpair []) props];

fun tactic_proof tac after_qed props lthy =
  after_qed (Goal.prove_multi (LocalTheory.target_of lthy) [] [] props
    (K tac)) lthy;

in

val subclass = gen_subclass (K I) user_proof;
val subclass_cmd = gen_subclass Sign.read_class user_proof;
fun prove_subclass tac = gen_subclass (K I) (tactic_proof tac);

end; (*local*)

end;
